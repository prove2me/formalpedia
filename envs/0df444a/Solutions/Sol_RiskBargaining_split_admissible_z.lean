-- Prove2me | solution 1 for RiskBargaining.split_admissible_z
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:42:13.092087+00:00
-- url     : https://prove2.me/submissions/65e04c41-ce45-4528-b87b-70489b467f2d

import Mathlib
import Definitions.Def_RiskBargaining_Instance_z
import Definitions.Def_RiskBargaining_Instance_Admissible
import Definitions.Def_RiskBargaining_Instance_split

set_option autoImplicit false

open MeasureTheory RiskBargaining
open scoped ENNReal

namespace RiskBargaining.SplitProof

theorem sum_eq_add_ne {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid M]
    (i : ι) (g : ι → M) :
    ∑ x : ι, g x = g i + ∑ j : {j : ι // j ≠ i}, g j.1 := by
  rw [← Finset.add_sum_erase Finset.univ g (Finset.mem_univ i)]
  congr 1
  have hset : Finset.univ.erase i =
      (Finset.univ : Finset {j : ι // j ≠ i}).map ⟨Subtype.val, Subtype.val_injective⟩ := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_map, Function.Embedding.coeFn_mk]
    exact ⟨fun hx => ⟨⟨x, hx.1⟩, Finset.mem_univ _, rfl⟩,
      by rintro ⟨⟨y, hy⟩, -, rfl⟩; exact ⟨hy, Finset.mem_univ y⟩⟩
  rw [hset, Finset.sum_map]
  rfl

theorem coherent_sum_le {Ω α : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {A : Lp ℝ p μ → ℝ} (hA : IsCoherentAcceptability A)
    (s : Finset α) (f : α → Lp ℝ p μ) :
    ∑ k ∈ s, A (f k) ≤ A (∑ k ∈ s, f k) := by
  classical
  have hA0 : A 0 = 0 := by
    simpa using hA.pos_homog 0 0 le_rfl
  induction s using Finset.induction_on with
  | empty =>
    simp [hA0]
  | @insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk]
    linarith [hA.super_add (f k) (∑ m ∈ s, f m)]

end RiskBargaining.SplitProof

open RiskBargaining.SplitProof in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (X : Type*) [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (I : Instance μ p X ι) (hI : I.Admissible)
    (i : ι) (ℓ : ℕ+) :
    (I.split i ℓ).Admissible ∧ (I.split i ℓ).z = I.z ∧
      (∀ j : {j // j ≠ i}, (I.split i ℓ).v (Sum.inl j) = I.v j) ∧
      (∀ k : Fin ℓ, (I.split i ℓ).v (Sum.inr k) = I.v i / ((ℓ : ℕ) : ℝ)) := by
  have hℓ_pos : (0 : ℝ) < (ℓ : ℕ) := Nat.cast_pos.mpr ℓ.pos
  have hℓ_inv_nn : 0 ≤ ((ℓ : ℕ) : ℝ)⁻¹ := inv_nonneg.mpr hℓ_pos.le
  have hv_inl : ∀ j : {j // j ≠ i}, (I.split i ℓ).v (Sum.inl j) = I.v j := fun _ => rfl
  have hv_inr : ∀ k : Fin ℓ, (I.split i ℓ).v (Sum.inr k) = I.v i / ((ℓ : ℕ) : ℝ) := by
    intro k
    change I.A i (((ℓ : ℕ) : ℝ)⁻¹ • I.R i) = I.v i / ((ℓ : ℕ) : ℝ)
    rw [(I.coherent i).pos_homog _ _ hℓ_inv_nn, div_eq_inv_mul]
    rfl
  have hv_pos : ∀ q : {j // j ≠ i} ⊕ Fin ℓ, 0 < (I.split i ℓ).v q := by
    rintro (j | k)
    · rw [hv_inl j]; exact hI.1 j.1
    · rw [hv_inr k]; exact div_pos (hI.1 i) hℓ_pos
  obtain ⟨z₀, hz₀⟩ := hI.2
  have hz_eq : I.z = z₀ :=
    le_antisymm (csSup_le ⟨z₀, hz₀.1⟩ hz₀.2) (le_csSup ⟨z₀, hz₀.2⟩ hz₀.1)
  have hgreat : IsGreatest I.totals I.z := hz_eq ▸ hz₀
  obtain ⟨ustar, Lstar, xstar, hz_sum, hL_sum, huv_star⟩ := hgreat.1
  have hz_mem_split : I.z ∈ (I.split i ℓ).totals := by
    let u' : {j // j ≠ i} ⊕ Fin ℓ → ℝ :=
      Sum.elim (fun j => ustar j.1) (fun _ => ustar i / ((ℓ : ℕ) : ℝ))
    let L' : {j // j ≠ i} ⊕ Fin ℓ → Lp ℝ p μ :=
      Sum.elim (fun j => Lstar j.1) (fun _ => ((ℓ : ℕ) : ℝ)⁻¹ • Lstar i)
    have hu'_sum : I.z = ∑ q, u' q := by
      rw [hz_sum, sum_eq_add_ne i ustar, Fintype.sum_sum_type]
      simp only [u', Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_div_cancel₀ _ hℓ_pos.ne']
      ring
    have hL'_sum : ∑ q, L' q = (I.split i ℓ).M xstar := by
      change ∑ q, L' q = I.M xstar
      rw [← hL_sum, sum_eq_add_ne i Lstar, Fintype.sum_sum_type]
      simp only [L', Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
        mul_inv_cancel₀ hℓ_pos.ne', one_smul]
      exact add_comm _ _
    refine ⟨u', L', xstar, hu'_sum, hL'_sum, ?_⟩
    rintro (j | k)
    · exact huv_star j.1
    · rw [hv_inr k]
      simp only [u', L', Sum.elim_inr]
      refine ⟨div_le_div_of_nonneg_right (huv_star i).1 hℓ_pos.le, ?_⟩
      change ustar i / ((ℓ : ℕ) : ℝ) ≤ I.A i (((ℓ : ℕ) : ℝ)⁻¹ • Lstar i)
      rw [(I.coherent i).pos_homog _ _ hℓ_inv_nn, div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left (huv_star i).2 hℓ_inv_nn
  have hz_ub_split : ∀ t ∈ (I.split i ℓ).totals, t ≤ I.z := by
    rintro t ⟨u', L', x', rfl, hL', huv'⟩
    let u : ι → ℝ := fun x =>
      if hx : x = i then ∑ k : Fin ℓ, u' (Sum.inr k) else u' (Sum.inl ⟨x, hx⟩)
    let L : ι → Lp ℝ p μ := fun x =>
      if hx : x = i then ∑ k : Fin ℓ, L' (Sum.inr k) else L' (Sum.inl ⟨x, hx⟩)
    have hu_sum : ∑ q, u' q = ∑ x : ι, u x := by
      rw [sum_eq_add_ne i u, Fintype.sum_sum_type]
      have hinl : ∑ j : {j : ι // j ≠ i}, u j.1 = ∑ j : {j : ι // j ≠ i}, u' (Sum.inl j) := by
        apply Finset.sum_congr rfl
        intro ⟨j, hj⟩ _
        simp [u, hj]
      simp only [u, dite_true, hinl]
      ring
    have hL_merged : ∑ x : ι, L x = I.M x' := by
      change ∑ q, L' q = I.M x' at hL'
      rw [sum_eq_add_ne i L]
      have hinl : ∑ j : {j : ι // j ≠ i}, L j.1 = ∑ j : {j : ι // j ≠ i}, L' (Sum.inl j) := by
        apply Finset.sum_congr rfl
        intro ⟨j, hj⟩ _
        simp [L, hj]
      simp only [L, dite_true, hinl]
      rw [add_comm, ← Fintype.sum_sum_type]
      exact hL'
    refine hgreat.2 ⟨u, L, x', hu_sum, hL_merged, fun x => ?_⟩
    by_cases hx : x = i
    · subst hx
      simp only [u, L, dite_true]
      refine ⟨?_, ?_⟩
      · have hv_eq : I.v x = ∑ _ : Fin ℓ, (I.v x / ((ℓ : ℕ) : ℝ)) := by
          simp [mul_div_cancel₀ _ hℓ_pos.ne']
        rw [hv_eq]
        exact Finset.sum_le_sum fun k _ => by
          simpa [hv_inr k] using (huv' (Sum.inr k)).1
      · exact (Finset.sum_le_sum fun k _ => (huv' (Sum.inr k)).2).trans
          (coherent_sum_le (I.coherent x) Finset.univ fun k => L' (Sum.inr k))
    · simp only [u, L, dif_neg hx]
      exact huv' (Sum.inl ⟨x, hx⟩)
  have hgreat_split : IsGreatest (I.split i ℓ).totals I.z := ⟨hz_mem_split, hz_ub_split⟩
  have hz_split_eq : (I.split i ℓ).z = I.z :=
    le_antisymm (csSup_le ⟨I.z, hgreat_split.1⟩ hgreat_split.2)
      (le_csSup ⟨I.z, hgreat_split.2⟩ hgreat_split.1)
  exact ⟨⟨hv_pos, ⟨I.z, hgreat_split⟩⟩, hz_split_eq, hv_inl, hv_inr⟩
