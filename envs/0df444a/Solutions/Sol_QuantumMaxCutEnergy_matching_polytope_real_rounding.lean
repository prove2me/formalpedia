-- Prove2me | solution 1 for QuantumMaxCutEnergy.matching_polytope_real_rounding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T02:33:01.398603+00:00
-- url     : https://prove2.me/submissions/63ad8db3-d858-4c4e-a9b8-191e66b57f13

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Theorems.Thm_QuantumMaxCutEnergy_matching_polytope_integral_rounding

open scoped BigOperators

private theorem approx_nnrat (a η : ℝ) (ha : 0 ≤ a) (hη : 0 < η) :
    ∃ q : ℚ≥0, a - η ≤ (q : ℝ) ∧ (q : ℝ) ≤ a := by
  rcases ha.eq_or_lt with h | h
  · exact ⟨0, by simp [← h, hη.le], by simp [← h]⟩
  · obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show max (a - η) 0 < a from max_lt (by linarith) h)
    have hr0 : (0:ℝ) < r := lt_of_le_of_lt (le_max_right _ _) hr1
    have hr0' : (0:ℚ) ≤ r := by exact_mod_cast hr0.le
    have hc : ((r.toNNRat : ℚ≥0) : ℝ) = (r : ℝ) := by
      conv_rhs => rw [← Rat.coe_toNNRat r hr0']
      norm_cast
    refine ⟨r.toNNRat, ?_, ?_⟩
    · rw [hc]; exact ((le_max_left _ _).trans hr1.le)
    · rw [hc]; exact hr2.le

theorem solution {n : ℕ}
    (w : QuantumMaxCutEnergy.Edge n → ℝ) (hw : ∀ e, 0 ≤ w e)
    (x : QuantumMaxCutEnergy.Edge n → ℝ) (hx : ∀ e, 0 ≤ x e)
    (hload : ∀ v : Fin n, (∑ e, if v = e.val.1 ∨ v = e.val.2 then x e else 0) ≤ 1)
    (hodd : ∀ S : Finset (Fin n), Odd S.card →
      (∑ e ∈ (Finset.univ.filter (fun e : QuantumMaxCutEnergy.Edge n =>
        e.val.1 ∈ S ∧ e.val.2 ∈ S)), x e) ≤ ((S.card : ℝ) - 1) / 2) :
    ∃ M : Finset (QuantumMaxCutEnergy.Edge n),
      (∀ e ∈ M, ∀ e' ∈ M, e ≠ e' →
        e.val.1 ≠ e'.val.1 ∧ e.val.1 ≠ e'.val.2 ∧ e.val.2 ≠ e'.val.1 ∧ e.val.2 ≠ e'.val.2) ∧
      (∑ e, w e * x e) ≤ ∑ e ∈ M, w e := by
  classical
  let P : Finset (QuantumMaxCutEnergy.Edge n) → Prop := fun M => ∀ e ∈ M, ∀ e' ∈ M, e ≠ e' →
        e.val.1 ≠ e'.val.1 ∧ e.val.1 ≠ e'.val.2 ∧ e.val.2 ≠ e'.val.1 ∧ e.val.2 ≠ e'.val.2
  have hne : ((Finset.univ : Finset (QuantumMaxCutEnergy.Edge n)).powerset.filter P).Nonempty :=
    ⟨∅, by simp [P]⟩
  obtain ⟨Ms, hMs, hmax⟩ := Finset.exists_max_image _ (fun M => ∑ e ∈ M, w e) hne
  refine ⟨Ms, (Finset.mem_filter.mp hMs).2, ?_⟩
  have hX : 0 ≤ ∑ e, x e := Finset.sum_nonneg (fun e _ => hx e)
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  set X := ∑ e, x e with hXdef
  have hη : 0 < ε / (X + 1) := by positivity
  choose q hq1 hq2 using fun e => approx_nnrat (w e) (ε / (X + 1)) (hw e) hη
  obtain ⟨M, hM, hMle⟩ :=
    QuantumMaxCutEnergy.matching_polytope_integral_rounding q x hx hload hodd
  have h1 : ∑ e ∈ M, (q e : ℝ) ≤ ∑ e ∈ M, w e := Finset.sum_le_sum (fun e _ => hq2 e)
  have h2 : ∑ e ∈ M, w e ≤ ∑ e ∈ Ms, w e :=
    hmax M (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hM⟩)
  have h3 : ∑ e, w e * x e ≤ ∑ e, ((q e : ℝ) * x e + ε / (X + 1) * x e) := by
    refine Finset.sum_le_sum (fun e _ => ?_)
    have := mul_le_mul_of_nonneg_right (hq1 e) (hx e)
    nlinarith
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h3
  have h4 : ε / (X + 1) * X ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith
