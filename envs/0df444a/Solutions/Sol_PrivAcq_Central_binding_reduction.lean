-- Prove2me | solution 1 for PrivAcq.Central.binding_reduction
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:16:30.803231+00:00
-- url     : https://prove2.me/submissions/01476765-402c-425d-8aa5-066feb373308

import Mathlib
import Definitions.Def_PrivAcq_Central_Model

open PrivAcq.Central in
theorem solution {n : ℕ} (S : Setting n) (hS : S.Standing) (c : Fin n → ℝ)
    (hc : c ∈ S.types) :
    (∀ (w ε : Fin n → ℝ) (η : ℝ), 0 < η → (∀ i, 0 ≤ w i) → ∑ i, w i = 1 →
      (∀ i, η * w i ≤ ε i) →
        (fun i => η * w i) ∈ (feas23 : Set (Fin n → ℝ)) ∧
        obj23 S c (fun i => η * w i) ≤
          2 * ((n : ℝ) + 1) / η ^ 2 +
            ∑ i, (((n : ℝ) + 1) * S.var * (w i) ^ 2 + S.ψ i (c i) * ε i)) ∧
    (∀ y ∈ (feas23 : Set (Fin n → ℝ)),
      0 < ∑ j, y j ∧ (∀ i, 0 ≤ y i / ∑ j, y j) ∧ ∑ i, y i / ∑ j, y j = 1 ∧
        (∀ i, (∑ j, y j) * (y i / ∑ j, y j) = y i) ∧
        2 * ((n : ℝ) + 1) / (∑ j, y j) ^ 2 +
            ∑ i, (((n : ℝ) + 1) * S.var * (y i / ∑ j, y j) ^ 2 + S.ψ i (c i) * y i) =
          obj23 S c y) := by
  have hψ : ∀ i, 0 ≤ S.ψ i (c i) := by
    intro i
    obtain ⟨ha, hab, -, hpos, -⟩ := hS.2.2 i
    have hci : c i ∈ Set.Icc (S.a i) (S.b i) := hc i (Set.mem_univ _)
    have hf : 0 < S.f i (c i) := hpos _ hci
    have hcdf : 0 ≤ S.cdf i (c i) := by
      unfold Setting.cdf
      refine intervalIntegral.integral_nonneg hci.1 fun u hu => (hpos u ⟨hu.1, hu.2.trans hci.2⟩).le
    unfold Setting.ψ
    have : 0 ≤ S.cdf i (c i) / S.f i (c i) := div_nonneg hcdf hf.le
    linarith [hci.1]
  refine ⟨fun w ε η hη hw hsum hε => ?_, fun y hy => ?_⟩
  · have hs : ∑ i, η * w i = η := by rw [← Finset.mul_sum, hsum, mul_one]
    refine ⟨⟨fun i => mul_nonneg hη.le (hw i), by rw [hs]; exact hη⟩, ?_⟩
    unfold obj23
    rw [hs]
    have hsq : ∑ i, (η * w i) ^ 2 * S.var = η ^ 2 * (S.var * ∑ i, w i ^ 2) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hsq]
    have hη2 : η ^ 2 ≠ 0 := by positivity
    have e1 : ((n : ℝ) + 1) / η ^ 2 * (2 + η ^ 2 * (S.var * ∑ i, w i ^ 2))
        = 2 * ((n : ℝ) + 1) / η ^ 2 + ((n : ℝ) + 1) * S.var * ∑ i, w i ^ 2 := by
      field_simp
    rw [e1, Finset.sum_add_distrib, ← Finset.mul_sum]
    have : ∑ i, S.ψ i (c i) * (η * w i) ≤ ∑ i, S.ψ i (c i) * ε i :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hε i) (hψ i)
    linarith
  · obtain ⟨hy0, hspos⟩ := hy
    set s := ∑ j, y j with hs
    have hsne : s ≠ 0 := hspos.ne'
    refine ⟨hspos, fun i => div_nonneg (hy0 i) hspos.le, ?_, fun i => mul_div_cancel₀ _ hsne, ?_⟩
    · rw [← Finset.sum_div, ← hs, div_self hsne]
    · unfold obj23
      rw [← hs, Finset.sum_add_distrib]
      have e : ∑ i, ((n : ℝ) + 1) * S.var * (y i / s) ^ 2
          = ((n : ℝ) + 1) / s ^ 2 * ∑ i, y i ^ 2 * S.var := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        field_simp
      rw [e]
      ring
