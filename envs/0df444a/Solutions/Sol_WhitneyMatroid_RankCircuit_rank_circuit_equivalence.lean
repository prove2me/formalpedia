-- Prove2me | solution 1 for WhitneyMatroid.RankCircuit.rank_circuit_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-05T18:07:38.392282+00:00
-- url     : https://prove2.me/submissions/c60f9e20-c2d0-41fa-a97e-76d658ed0ed0

import Mathlib
import Definitions.Def_WhitneyMatroid_RankCircuit_IsRankSystem
import Definitions.Def_WhitneyMatroid_RankCircuit_IsCircuitSystem

open WhitneyMatroid.RankCircuit

namespace WhitneyRC

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### Rank systems: basic facts -/

section rank

variable {r : Finset α → ℤ} (hr : IsRankSystem r)
include hr

lemma r_insert_cases (N : Finset α) (e : α) : r (insert e N) = r N ∨ r (insert e N) = r N + 1 := by
  by_cases he : e ∈ N
  · left; rw [Finset.insert_eq_of_mem he]
  · exact hr.R2 N e he

lemma r_mono_union (M D : Finset α) : r M ≤ r (M ∪ D) := by
  induction D using Finset.induction_on with
  | empty => simp
  | insert d D _ ih =>
    rw [Finset.union_insert]
    rcases r_insert_cases hr (M ∪ D) d with h | h <;> omega

lemma r_mono {M N : Finset α} (h : M ⊆ N) : r M ≤ r N := by
  have := r_mono_union hr M N
  rwa [Finset.union_eq_right.2 h] at this

lemma r_le_card (N : Finset α) : r N ≤ N.card := by
  induction N using Finset.induction_on with
  | empty => simp [hr.R1]
  | insert e N he ih =>
    rw [Finset.card_insert_of_notMem he]
    rcases hr.R2 N e he with h | h <;> push_cast <;> omega

/-- `r(B) ≤ r(A) + |B \ A|` for `A ⊆ B`; equivalently the nullity is monotone. -/
lemma r_le_add_card (A D : Finset α) : r (A ∪ D) ≤ r A + D.card := by
  induction D using Finset.induction_on with
  | empty => simp
  | insert d D hd ih =>
    rw [Finset.union_insert, Finset.card_insert_of_notMem hd]
    rcases r_insert_cases hr (A ∪ D) d with h | h <;> push_cast <;> omega

lemma nullity_mono {A B : Finset α} (h : A ⊆ B) :
    WhitneyMatroid.RankIndep.nullity r A ≤ WhitneyMatroid.RankIndep.nullity r B := by
  unfold WhitneyMatroid.RankIndep.nullity
  have h1 := r_le_add_card hr A (B \ A)
  rw [Finset.union_sdiff_of_subset h] at h1
  have h2 : (B \ A).card + A.card = B.card := Finset.card_sdiff_add_card_eq_card h
  omega

lemma nullity_nonneg (A : Finset α) : 0 ≤ WhitneyMatroid.RankIndep.nullity r A := by
  unfold WhitneyMatroid.RankIndep.nullity; have := r_le_card hr A; omega

/-- If `e` is dependent on `A`, it is dependent on every superset of `A`. -/
lemma dep_lift {e : α} {A : Finset α} (hA : r (insert e A) = r A) (D : Finset α) :
    r (insert e (A ∪ D)) = r (A ∪ D) := by
  induction D using Finset.induction_on with
  | empty => simpa using hA
  | insert f D _ ih =>
    rw [Finset.union_insert]
    set A' := A ∪ D
    by_cases hf : f ∈ A'
    · rw [Finset.insert_eq_of_mem hf]; exact ih
    by_cases he : e ∈ A'
    · rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem he)]
    by_cases hef : e = f
    · subst hef; rw [Finset.insert_idem]
    rcases hr.R2 A' f hf with h | h
    · have h3 := hr.R3 A' e f he hf ih h
      rw [Finset.insert_comm] at h3
      rw [h3, h]
    · have hef' : e ∉ insert f A' := by simp [hef, he]
      have h4 := hr.R2 (insert f A') e hef'
      have h5 := r_insert_cases hr (insert e A') f
      rw [Finset.insert_comm] at h5
      omega

lemma dep_mono {e : α} {A B : Finset α} (hA : r (insert e A) = r A) (hAB : A ⊆ B) :
    r (insert e B) = r B := by
  have := dep_lift hr hA B
  rwa [Finset.union_eq_right.2 hAB] at this

/-- A set of positive nullity has an element dependent on the rest. -/
lemma exists_dep_of_lt {Q : Finset α} (hQ : r Q < Q.card) : ∃ f ∈ Q, r (Q.erase f) = r Q := by
  induction Q using Finset.induction_on with
  | empty => simp [hr.R1] at hQ
  | insert g Q0 hg ih =>
    rw [Finset.card_insert_of_notMem hg] at hQ
    rcases hr.R2 Q0 g hg with h | h
    · exact ⟨g, Finset.mem_insert_self _ _, by rw [Finset.erase_insert hg, h]⟩
    · obtain ⟨f, hf, hfe⟩ := ih (by push_cast at hQ; omega)
      have hfg : f ≠ g := fun h => hg (h ▸ hf)
      refine ⟨f, Finset.mem_insert_of_mem hf, ?_⟩
      have hdep : r (insert f (Q0.erase f)) = r (Q0.erase f) := by
        rw [Finset.insert_erase hf, hfe]
      have := dep_mono hr hdep (show Q0.erase f ⊆ (insert g Q0).erase f from
        Finset.erase_subset_erase _ (Finset.subset_insert _ _))
      rw [Finset.insert_erase (Finset.mem_insert_of_mem hf)] at this
      exact this.symm

/-- Lemma 5: each element of a circuit is dependent on the rest of the circuit. -/
lemma circuit_dep {P : Finset α} (hP : circuitsOfRank r P) {e : α} (he : e ∈ P) :
    r (insert e (P.erase e)) = r (P.erase e) := by
  obtain ⟨hpos, hsub⟩ := hP
  have h0 := hsub (P.erase e) (Finset.erase_ssubset he)
  unfold WhitneyMatroid.RankIndep.nullity at hpos h0
  rw [Finset.insert_erase he]
  have hc := Finset.card_erase_add_one he
  have hm := r_mono hr (Finset.erase_subset e P)
  omega

/-- Lemma 6: if `e ∉ N` is dependent on `N`, some circuit in `N + e` contains `e`. -/
lemma circuit_of_dep {N : Finset α} {e : α} (he : e ∉ N) (hdep : r (insert e N) = r N) :
    ∃ P, circuitsOfRank r P ∧ P ⊆ insert e N ∧ e ∈ P := by
  classical
  let F := N.powerset.filter (fun Q => r (insert e Q) = r Q)
  obtain ⟨Q, hQF, hQmin⟩ := F.exists_min_image Finset.card ⟨N, by simp [F, hdep]⟩
  have hQ : Q ⊆ N ∧ r (insert e Q) = r Q := by simpa [F] using hQF
  have heQ : e ∉ Q := fun h => he (hQ.1 h)
  -- minimality: `e` is not dependent on any proper subset of `Q`
  have hmin : ∀ g ∈ Q, r (insert e (Q.erase g)) = r (Q.erase g) + 1 := by
    intro g hg
    rcases hr.R2 (Q.erase g) e (fun h => heQ (Finset.mem_of_mem_erase h)) with h | h
    · have := hQmin (Q.erase g) (by
        simp only [F, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨(Finset.erase_subset g Q).trans hQ.1, h⟩)
      have := Finset.card_erase_lt_of_mem hg
      omega
    · exact h
  -- `Q` is independent
  have hQind : r Q = Q.card := by
    by_contra hne
    have hlt : r Q < Q.card := lt_of_le_of_ne (r_le_card hr Q) hne
    obtain ⟨f, hf, hfe⟩ := exists_dep_of_lt hr hlt
    have h1 := hmin f hf
    have h2 := r_mono hr (show insert e (Q.erase f) ⊆ insert e Q from
      Finset.insert_subset_insert _ (Finset.erase_subset _ _))
    omega
  refine ⟨insert e Q, ⟨?_, ?_⟩, Finset.insert_subset_insert _ hQ.1, Finset.mem_insert_self _ _⟩
  · unfold WhitneyMatroid.RankIndep.nullity
    rw [Finset.card_insert_of_notMem heQ, hQ.2]
    push_cast; omega
  · intro M hM
    obtain ⟨g, hgP, hgM⟩ := Finset.exists_of_ssubset hM
    have hMsub : M ⊆ (insert e Q).erase g := fun x hx =>
      Finset.mem_erase.2 ⟨fun h => hgM (h ▸ hx), hM.1 hx⟩
    have hz : WhitneyMatroid.RankIndep.nullity r ((insert e Q).erase g) = 0 := by
      unfold WhitneyMatroid.RankIndep.nullity
      by_cases hge : g = e
      · subst hge; rw [Finset.erase_insert heQ, hQind]; ring
      · have hgQ : g ∈ Q := by simpa [hge] using hgP
        rw [Finset.erase_insert_of_ne (Ne.symm hge), hmin g hgQ,
          Finset.card_insert_of_notMem (fun h => heQ (Finset.mem_of_mem_erase h))]
        have hQg : r (Q.erase g) = (Q.erase g).card := by
          have h1 := nullity_mono hr (Finset.erase_subset g Q)
          have h2 := nullity_nonneg hr (Q.erase g)
          unfold WhitneyMatroid.RankIndep.nullity at h1 h2
          have h3 := Finset.card_erase_add_one hgQ
          omega
        rw [hQg]; push_cast; ring
    have h1 := nullity_mono hr hMsub
    have h2 := nullity_nonneg hr M
    omega

/-- A circuit in `N + e` through `e` makes `e` dependent on `N`. -/
lemma dep_of_circuit {N : Finset α} {e : α} {P : Finset α} (hP : circuitsOfRank r P)
    (hPN : P ⊆ insert e N) (heP : e ∈ P) : r (insert e N) = r N := by
  have h := circuit_dep hr hP heP
  refine dep_mono hr h ?_
  intro x hx
  have hx' := Finset.mem_erase.1 hx
  have := hPN hx'.2
  rw [Finset.mem_insert] at this
  exact this.resolve_left hx'.1

theorem circuits_isCircuitSystem : IsCircuitSystem (circuitsOfRank r) := by
  refine ⟨fun P Q hP hQP hQ => ?_, fun P₁ P₂ e₁ e₂ h1 h2 he1 he1' he2 he2' => ?_⟩
  · have := hP.2 Q hQP
    have := hQ.1
    omega
  · have hne : e₁ ≠ e₂ := fun h => he2' (h ▸ he1')
    let N := ((P₁ ∪ P₂).erase e₁).erase e₂
    have hNe1 : e₁ ∉ N := by simp [N]
    have hNe2 : e₂ ∉ N := by simp [N]
    -- `e₁` is dependent on `N`
    have d1 : r (insert e₁ N) = r N := by
      refine dep_mono hr (circuit_dep hr h2 he1') ?_
      intro x hx
      have hx' := Finset.mem_erase.1 hx
      simp only [N, Finset.mem_erase, Finset.mem_union]
      exact ⟨fun h => he2' (h ▸ hx'.2), hx'.1, Or.inr hx'.2⟩
    -- `e₂` is dependent on `N + e₁`
    have d2 : r (insert e₂ (insert e₁ N)) = r (insert e₁ N) := by
      refine dep_mono hr (circuit_dep hr h1 he2) ?_
      intro x hx
      have hx' := Finset.mem_erase.1 hx
      by_cases hx1 : x = e₁
      · exact hx1 ▸ Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (by simp [N, hx1, hx'.1, hx'.2])
    have d3 : r (insert e₂ N) = r N := by
      have h4 := r_mono hr (show insert e₂ N ⊆ insert e₂ (insert e₁ N) from
        Finset.insert_subset_insert _ (Finset.subset_insert _ _))
      have h5 := r_mono hr (Finset.subset_insert e₂ N)
      omega
    obtain ⟨P, hP, hPN, he2P⟩ := circuit_of_dep hr hNe2 d3
    refine ⟨P, hP, fun x hx => ?_, he2P, fun h => ?_⟩
    · have := hPN hx
      rw [Finset.mem_insert] at this
      rcases this with rfl | h
      · exact Finset.mem_union_left _ he2
      · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h)
    · have := hPN h
      rw [Finset.mem_insert] at this
      rcases this with h' | h'
      · exact hne h'
      · exact hNe1 h'

end rank

/-! ### Whitney's ordered rank from circuits -/

section circ

variable (C : Finset α → Prop)

/-- Some circuit inside `S` contains `a`. -/
def Cl (S : Finset α) (a : α) : Prop := ∃ P, C P ∧ P ⊆ S ∧ a ∈ P

open Classical in
/-- `Γ = 0` if `a` closes a circuit in `S`, `1` otherwise. -/
noncomputable def G (S : Finset α) (a : α) : ℤ := if Cl C S a then 0 else 1

variable {C}

lemma Cl_mono {S S' : Finset α} {a : α} (h : Cl C S a) (hS : S ⊆ S') : Cl C S' a := by
  obtain ⟨P, hP, hPS, ha⟩ := h
  exact ⟨P, hP, hPS.trans hS, ha⟩

lemma rankSeq_concat (l : List α) (a : α) :
    rankSeq C (l ++ [a]) = rankSeq C l + G C (insert a l.toFinset) a := by
  classical
  unfold rankSeq
  have hlen : l.length + 1 = (l ++ [a]).length := by simp
  rw [← Fin.sum_congr' _ hlen, Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hc : ClosesCircuit C (l ++ [a]) (Fin.cast hlen i.castSucc) ↔ ClosesCircuit C l i := by
      unfold ClosesCircuit
      have ht : (l ++ [a]).take (i.val + 1) = l.take (i.val + 1) :=
        List.take_append_of_le_length (by omega)
      have hg : (l ++ [a]).get (Fin.cast hlen i.castSucc) = l.get i := by
        simp [List.getElem_append_left]
      simp only [Fin.coe_cast, Fin.coe_castSucc, ht, hg]
    by_cases h : ClosesCircuit C l i
    · rw [if_pos (hc.2 h), if_pos h]
    · rw [if_neg (mt hc.1 h), if_neg h]
  · have hc : ClosesCircuit C (l ++ [a]) (Fin.cast hlen (Fin.last _)) ↔ Cl C (insert a l.toFinset) a := by
      unfold ClosesCircuit Cl
      have ht : (l ++ [a]).take ((Fin.cast hlen (Fin.last l.length)).val + 1) = l ++ [a] := by
        simp
      have hg : (l ++ [a]).get (Fin.cast hlen (Fin.last _)) = a := by simp
      have hs : (l ++ [a]).toFinset = insert a l.toFinset := by
        ext x; simp [or_comm]
      rw [ht, hg, hs]
    unfold G
    by_cases h : Cl C (insert a l.toFinset) a
    · rw [if_pos (hc.2 h), if_pos h]
    · rw [if_neg (mt hc.1 h), if_neg h]

/-- `rankSeq` of the reversed list, which grows at the head. -/
noncomputable def s (C : Finset α → Prop) (l : List α) : ℤ := rankSeq C l.reverse

lemma s_cons (a : α) (l : List α) : s C (a :: l) = s C l + G C (insert a l.toFinset) a := by
  unfold s
  rw [List.reverse_cons, rankSeq_concat, List.toFinset_reverse]

/-- Lemma 7: interchanging the last two elements leaves the rank unchanged. -/
lemma swap_last (hC : IsCircuitSystem C) {x y : α} {L : Finset α} (hxy : x ≠ y) (hx : x ∉ L)
    (hy : y ∉ L) :
    G C (insert x L) x + G C (insert y (insert x L)) y =
      G C (insert y L) y + G C (insert x (insert y L)) x := by
  rw [Finset.insert_comm x y L]
  set S := insert y (insert x L)
  -- F1: closing through `x` in `S` but not in `L + x` uses `y`
  have F1 : ∀ {u v : α}, u ≠ v → u ∉ L → v ∉ L → Cl C (insert v (insert u L)) u →
      ¬Cl C (insert u L) u → ∃ P, C P ∧ P ⊆ insert v (insert u L) ∧ u ∈ P ∧ v ∈ P := by
    intro u v _ _ _ h hn
    obtain ⟨P, hP, hPS, hu⟩ := h
    refine ⟨P, hP, hPS, hu, ?_⟩
    by_contra hv
    exact hn ⟨P, hP, fun z hz => by
      have := hPS hz
      rw [Finset.mem_insert] at this
      exact this.resolve_left (fun h => hv (h ▸ hz)), hu⟩
  have F2 : ∀ {u v : α}, u ≠ v → u ∉ L → v ∉ L → Cl C (insert v (insert u L)) u →
      ¬Cl C (insert u L) u → ¬Cl C (insert v L) v := by
    intro u v huv hu hv h hn hB
    obtain ⟨P₁, hP₁, hP₁S, hu1, hv1⟩ := F1 huv hu hv h hn
    obtain ⟨P₂, hP₂, hP₂S, hv2⟩ := hB
    have hu2 : u ∉ P₂ := fun h => by
      have := hP₂S h
      rw [Finset.mem_insert] at this
      rcases this with h' | h'
      · exact huv h'
      · exact hu h'
    obtain ⟨P₃, hP₃, hP₃S, hu3, hv3⟩ := hC.C2 P₁ P₂ v u hP₁ hP₂ hv1 hv2 hu1 hu2
    refine hn ⟨P₃, hP₃, fun z hz => ?_, hu3⟩
    have hz' := hP₃S hz
    have hzv : z ≠ v := fun h => hv3 (h ▸ hz)
    rcases Finset.mem_union.1 hz' with h' | h'
    · have := hP₁S h'
      simp only [Finset.mem_insert] at this ⊢
      tauto
    · have := hP₂S h'
      simp only [Finset.mem_insert] at this ⊢
      tauto
  have SA : S = insert y (insert x L) := rfl
  have SB : S = insert x (insert y L) := Finset.insert_comm y x L
  have monoA : Cl C (insert x L) x → Cl C S x := fun h => Cl_mono h (Finset.subset_insert _ _)
  have monoB : Cl C (insert y L) y → Cl C S y := fun h =>
    Cl_mono h (SB ▸ Finset.subset_insert _ _)
  have f1xy : Cl C S x → ¬Cl C (insert x L) x → Cl C S y := fun h hn => by
    obtain ⟨P, hP, hPS, -, hyP⟩ := F1 hxy hx hy h hn
    exact ⟨P, hP, hPS, hyP⟩
  have f1yx : Cl C S y → ¬Cl C (insert y L) y → Cl C S x := fun h hn => by
    rw [SB] at h ⊢
    obtain ⟨P, hP, hPS, -, hxP⟩ := F1 hxy.symm hy hx h hn
    exact ⟨P, hP, hPS, hxP⟩
  have f2xy : Cl C S x → ¬Cl C (insert x L) x → ¬Cl C (insert y L) y :=
    fun h hn => F2 hxy hx hy h hn
  have f2yx : Cl C S y → ¬Cl C (insert y L) y → ¬Cl C (insert x L) x := fun h hn => by
    rw [SB] at h
    exact F2 hxy.symm hy hx h hn
  unfold G
  by_cases hA : Cl C (insert x L) x <;> by_cases hB : Cl C (insert y L) y <;>
    by_cases hA' : Cl C S x <;> by_cases hB' : Cl C S y <;> simp_all

/-- Lemma 8 (for `s`): the rank does not depend on the ordering. -/
lemma s_perm (hC : IsCircuitSystem C) {l₁ l₂ : List α} (h : l₁.Perm l₂) :
    l₁.Nodup → s C l₁ = s C l₂ := by
  induction h with
  | nil => intro; rfl
  | cons x h ih =>
    intro hn
    rw [s_cons, s_cons, ih (List.nodup_cons.1 hn).2, List.toFinset_eq_of_perm _ _ h]
  | swap x y l =>
    intro hn
    rw [s_cons, s_cons, s_cons, s_cons, List.toFinset_cons, List.toFinset_cons]
    have h1 := List.nodup_cons.1 hn
    have h2 := List.nodup_cons.1 h1.2
    have hxy : x ≠ y := fun h => h1.1 (h ▸ List.mem_cons_self)
    have hyl : y ∉ l.toFinset := by simpa using fun h => h1.1 (List.mem_cons_of_mem _ h)
    have hxl : x ∉ l.toFinset := by simpa using h2.1
    have := swap_last hC hxy hxl hyl
    linarith
  | trans h₁ _ ih₁ ih₂ =>
    intro hn
    rw [ih₁ hn, ih₂ (h₁.nodup_iff.1 hn)]

lemma rankOfCircuits_eq_s (N : Finset α) : rankOfCircuits C N = s C N.toList.reverse := by
  unfold rankOfCircuits s; rw [List.reverse_reverse]

lemma rank_insert (hC : IsCircuitSystem C) {N : Finset α} {e : α} (he : e ∉ N) :
    rankOfCircuits C (insert e N) = rankOfCircuits C N + G C (insert e N) e := by
  rw [rankOfCircuits_eq_s, rankOfCircuits_eq_s]
  have hp : (insert e N).toList.reverse.Perm (e :: N.toList.reverse) :=
    (List.reverse_perm _).trans ((Finset.toList_insert he).trans
      (List.Perm.cons e (List.reverse_perm _).symm))
  rw [s_perm hC hp (List.nodup_reverse.2 (Finset.nodup_toList _)), s_cons,
    List.toFinset_reverse, Finset.toList_toFinset]

lemma rank_empty : rankOfCircuits C (∅ : Finset α) = 0 := by
  unfold rankOfCircuits; rw [Finset.toList_empty]; simp [rankSeq]

lemma G_cases (S : Finset α) (a : α) : G C S a = 0 ∨ G C S a = 1 := by
  unfold G; split_ifs <;> simp

theorem rankOfCircuits_isRankSystem (hC : IsCircuitSystem C) : IsRankSystem (rankOfCircuits C) := by
  refine ⟨rank_empty, fun N e he => ?_, fun N e₁ e₂ he₁ he₂ h₁ h₂ => ?_⟩
  · rw [rank_insert hC he]
    rcases G_cases (C := C) (insert e N) e with h | h <;> simp [h]
  · rw [rank_insert hC he₂] at h₂
    have hcl : Cl C (insert e₂ N) e₂ := by
      by_contra hn; unfold G at h₂; rw [if_neg hn] at h₂; omega
    by_cases h12 : e₂ = e₁
    · subst h12; rw [Finset.insert_idem]; exact h₁
    have he₂' : e₂ ∉ insert e₁ N := by simp [h12, he₂]
    rw [rank_insert hC he₂', h₁]
    unfold G
    rw [if_pos (Cl_mono hcl (Finset.insert_subset_insert _ (Finset.subset_insert _ _)))]
    ring

/-- `r(N) ≤ |N|`, with equality iff `N` contains no circuit. -/
lemma rank_card (hC : IsCircuitSystem C) (h0 : ¬C ∅) (N : Finset α) :
    rankOfCircuits C N ≤ N.card ∧ (rankOfCircuits C N = N.card ↔ ¬∃ Q, C Q ∧ Q ⊆ N) := by
  induction N using Finset.induction_on with
  | empty =>
    rw [rank_empty]
    refine ⟨by simp, ⟨fun _ => ?_, fun _ => by simp⟩⟩
    rintro ⟨Q, hQ, hQ0⟩
    rw [Finset.subset_empty.1 hQ0] at hQ
    exact h0 hQ
  | insert e N he ih =>
    rw [rank_insert hC he, Finset.card_insert_of_notMem he]
    unfold G
    by_cases hcl : Cl C (insert e N) e
    · rw [if_pos hcl]
      obtain ⟨P, hP, hPS, -⟩ := hcl
      refine ⟨by push_cast; omega, ⟨fun h => by push_cast at h; omega, fun h => absurd ⟨P, hP, hPS⟩ h⟩⟩
    · rw [if_neg hcl]
      refine ⟨by push_cast; omega, ?_⟩
      have key : (¬∃ Q, C Q ∧ Q ⊆ insert e N) ↔ ¬∃ Q, C Q ∧ Q ⊆ N := by
        constructor
        · rintro h ⟨Q, hQ, hQN⟩; exact h ⟨Q, hQ, hQN.trans (Finset.subset_insert _ _)⟩
        · rintro h ⟨Q, hQ, hQN⟩
          by_cases heQ : e ∈ Q
          · exact hcl ⟨Q, hQ, hQN, heQ⟩
          · exact h ⟨Q, hQ, fun x hx => by
              have := hQN hx
              rw [Finset.mem_insert] at this
              exact this.resolve_left (fun h => heQ (h ▸ hx))⟩
      rw [key, ← ih.2]
      push_cast
      omega

theorem circuitsOfRank_rankOfCircuits (hC : IsCircuitSystem C) (h0 : ¬C ∅) :
    circuitsOfRank (rankOfCircuits C) = C := by
  have npos : ∀ N, 0 < WhitneyMatroid.RankIndep.nullity (rankOfCircuits C) N ↔
      ∃ Q, C Q ∧ Q ⊆ N := by
    intro N
    unfold WhitneyMatroid.RankIndep.nullity
    have := rank_card hC h0 N
    constructor
    · intro h; by_contra hn; have := this.2.2 hn; omega
    · intro h; have := mt this.2.1 (not_not.2 h); omega
  have nzero : ∀ N, WhitneyMatroid.RankIndep.nullity (rankOfCircuits C) N = 0 ↔
      ¬∃ Q, C Q ∧ Q ⊆ N := by
    intro N
    unfold WhitneyMatroid.RankIndep.nullity
    have := rank_card hC h0 N
    constructor
    · intro h; exact this.2.1 (by omega)
    · intro h; have := this.2.2 h; omega
  funext P
  apply propext
  unfold circuitsOfRank
  rw [npos]
  constructor
  · rintro ⟨⟨Q, hQ, hQP⟩, hmin⟩
    rcases hQP.ssubset_or_eq with hlt | heq
    · exact absurd ⟨Q, hQ, subset_rfl⟩ ((nzero Q).1 (hmin Q hlt))
    · exact heq ▸ hQ
  · intro hP
    refine ⟨⟨P, hP, subset_rfl⟩, fun N hN => (nzero N).2 ?_⟩
    rintro ⟨Q, hQ, hQN⟩
    exact hC.C1 P Q hP (lt_of_le_of_lt hQN hN) hQ

end circ

/-- Rank from the circuits of a rank system gives back the rank. -/
theorem rank_of_circuits_of_rank {r : Finset α → ℤ} (hr : IsRankSystem r) :
    rankOfCircuits (circuitsOfRank r) = r := by
  have hC := circuits_isCircuitSystem hr
  funext N
  induction N using Finset.induction_on with
  | empty => rw [rank_empty, hr.R1]
  | insert e N he ih =>
    rw [rank_insert hC he, ih]
    unfold G
    by_cases hcl : Cl (circuitsOfRank r) (insert e N) e
    · rw [if_pos hcl]
      obtain ⟨P, hP, hPS, heP⟩ := hcl
      rw [dep_of_circuit hr hP hPS heP]; ring
    · rw [if_neg hcl]
      rcases hr.R2 N e he with h | h
      · exact absurd (circuit_of_dep hr he h) hcl
      · exact h.symm

end WhitneyRC

open WhitneyRC in
theorem solution (α : Type*) [Fintype α] [DecidableEq α] :
    (∀ r : Finset α → ℤ, IsRankSystem r →
      IsCircuitSystem (circuitsOfRank r) ∧ ¬ circuitsOfRank r ∅ ∧
        rankOfCircuits (circuitsOfRank r) = r) ∧
    (∀ C : Finset α → Prop, IsCircuitSystem C → ¬ C ∅ →
      IsRankSystem (rankOfCircuits C) ∧ circuitsOfRank (rankOfCircuits C) = C) := by
  refine ⟨fun r hr => ⟨circuits_isCircuitSystem hr, fun h => ?_, rank_of_circuits_of_rank hr⟩,
    fun C hC h0 => ⟨rankOfCircuits_isRankSystem hC, circuitsOfRank_rankOfCircuits hC h0⟩⟩
  have := h.1
  simp [WhitneyMatroid.RankIndep.nullity, hr.R1] at this
