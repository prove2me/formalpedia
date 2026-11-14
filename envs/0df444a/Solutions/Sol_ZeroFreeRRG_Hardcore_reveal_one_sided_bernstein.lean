-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.reveal_one_sided_bernstein
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:38:50.533109+00:00
-- url     : https://prove2.me/submissions/eb068afb-47b8-4532-abf3-7f36b6416556

import Theorems.Thm_ZeroFreeRRG_Hardcore_reveal_centered_mgf
import Mathlib
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (n : ℕ) (s η : ℝ) (z : Fin n → ℝ)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1)
    (hz : ∀ v, |z v| ≤ 1) :
    (∑ U : Finset (Fin n), revealProb s U *
      (if s*η*n/2 ≤ (∑ v ∈ U, z v) - s*(∑ v : Fin n, z v) then 1 else 0)) ≤
        Real.exp (-(s*η^2/12)*n) := by
  classical
  let θ := η/3
  let a := s*η*n/2
  let X := fun U : Finset (Fin n) => (∑ v ∈ U, z v) - s*(∑ v : Fin n, z v)
  have hθ : 0 ≤ θ := by dsimp [θ]; linarith
  have hθ1 : θ ≤ 1/3 := by dsimp [θ]; linarith
  have hmgf := reveal_centered_mgf n s θ z hs hs1 hθ hθ1 hz
  have hprob (U : Finset (Fin n)) : 0 ≤ revealProb s U := by
    unfold revealProb
    exact mul_nonneg (pow_nonneg hs _) (pow_nonneg (sub_nonneg.mpr hs1) _)
  have hpoint (U : Finset (Fin n)) :
      revealProb s U * (if a ≤ X U then 1 else 0) ≤
        revealProb s U * Real.exp (θ*(X U-a)) := by
    apply mul_le_mul_of_nonneg_left _ (hprob U)
    split_ifs with hU
    · have hnonneg : 0 ≤ θ*(X U-a) := mul_nonneg hθ (sub_nonneg.mpr hU)
      have hh := Real.add_one_le_exp (θ*(X U-a))
      linarith
    · exact (Real.exp_pos _).le
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Finset (Fin n)))) (fun U _ => hpoint U)
  have hfactor : (∑ U : Finset (Fin n), revealProb s U * Real.exp (θ*(X U-a))) =
      Real.exp (-θ*a) * (∑ U : Finset (Fin n), revealProb s U * Real.exp (θ*X U)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro U hU
    have he : Real.exp (θ*(X U-a)) = Real.exp (-θ*a) * Real.exp (θ*X U) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    ring
  rw [hfactor] at hsum
  have hprod := mul_le_mul_of_nonneg_left hmgf (Real.exp_pos (-θ*a)).le
  have hexp : Real.exp (-θ*a) * Real.exp ((3/4)*s*θ^2*n) = Real.exp (-(s*η^2/12)*n) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [θ,a]
    ring
  rw [hexp] at hprod
  exact hsum.trans hprod
