-- Prove2me | solution 1 for WhitneyMatroid.RankCircuit.circuitSystem_of_rankSystem
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-05T18:22:08.453435+00:00
-- url     : https://prove2.me/submissions/127ef09f-5353-4319-8a31-b9ddd978b971

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

/-- Lemma 6 (core): if `e ∉ Q` is dependent on `Q` but on no `Q - g`, then `Q + e` is a circuit. -/
lemma circuit_of_min {Q : Finset α} {e : α} (heQ : e ∉ Q) (hdep : r (insert e Q) = r Q)
    (hmin : ∀ g ∈ Q, r (insert e (Q.erase g)) = r (Q.erase g) + 1) :
    circuitsOfRank r (insert e Q) := by
  -- `Q` is independent
  have hQind : r Q = Q.card := by
    by_contra hne
    have hlt : r Q < Q.card := lt_of_le_of_ne (r_le_card hr Q) hne
    obtain ⟨f, hf, hfe⟩ := exists_dep_of_lt hr hlt
    have h1 := hmin f hf
    have h2 := r_mono hr (show insert e (Q.erase f) ⊆ insert e Q from
      Finset.insert_subset_insert _ (Finset.erase_subset _ _))
    omega
  refine ⟨?_, ?_⟩
  · unfold WhitneyMatroid.RankIndep.nullity
    rw [Finset.card_insert_of_notMem heQ, hdep]
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
  exact ⟨insert e Q, circuit_of_min hr heQ hQ.2 hmin, Finset.insert_subset_insert _ hQ.1,
    Finset.mem_insert_self _ _⟩

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

end WhitneyRC

open WhitneyRC in
theorem solution {α : Type*} [Fintype α] [DecidableEq α]
    (r : Finset α → ℤ) (hr : IsRankSystem r) :
    IsCircuitSystem (circuitsOfRank r) :=
  circuits_isCircuitSystem hr
