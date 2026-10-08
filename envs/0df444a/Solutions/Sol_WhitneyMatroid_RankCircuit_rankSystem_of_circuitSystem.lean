-- Prove2me | solution 1 for WhitneyMatroid.RankCircuit.rankSystem_of_circuitSystem
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-05T18:22:13.654065+00:00
-- url     : https://prove2.me/submissions/5fa27713-84a2-4244-98d8-6204cab95604

import Mathlib
import Definitions.Def_WhitneyMatroid_RankCircuit_IsRankSystem
import Definitions.Def_WhitneyMatroid_RankCircuit_IsCircuitSystem


open WhitneyMatroid.RankCircuit

namespace WhitneyRC

variable {α : Type*} [Fintype α] [DecidableEq α]


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

end circ

end WhitneyRC

open WhitneyRC in
theorem solution {α : Type*} [Fintype α] [DecidableEq α]
    (C : Finset α → Prop) (hC : IsCircuitSystem C) :
    IsRankSystem (rankOfCircuits C) :=
  rankOfCircuits_isRankSystem hC
