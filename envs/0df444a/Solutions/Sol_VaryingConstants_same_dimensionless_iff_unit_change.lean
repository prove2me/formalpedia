-- Prove2me | solution 1 for VaryingConstants.same_dimensionless_iff_unit_change
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T15:52:46.746643+00:00
-- url     : https://prove2.me/submissions/aa5c2d48-800e-41be-88e5-ad01776905c6

import Mathlib
import Definitions.Def_VaryingConstants_units

namespace VaryingConstants21f0

open VaryingConstants

lemma range_of_orth {n d : ℕ} (D : Matrix (Fin n) (Fin d) ℝ) (u : Fin n → ℝ)
    (h : ∀ a : Fin n → ℝ, Matrix.vecMul a D = 0 → ∑ i, a i * u i = 0) :
    ∃ t : Fin d → ℝ, ∀ i, u i = ∑ j, D i j * t j := by
  let φ : Module.Dual ℝ (Fin n → ℝ) :=
    { toFun := fun a => ∑ i, a i * u i
      map_add' := by intro a b; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro c a; simp [Finset.mul_sum, mul_assoc] }
  have hφ : φ ∈ (LinearMap.ker (Matrix.vecMulLinear D)).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro a ha
    rw [LinearMap.mem_ker] at ha
    exact h a ha
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hφ
  obtain ⟨g, hg⟩ := hφ
  refine ⟨fun j => g (fun k => if j = k then 1 else 0), fun i => ?_⟩
  have hi := LinearMap.congr_fun hg (Pi.single i 1)
  simp only [LinearMap.dualMap_apply, Matrix.vecMulLinear_apply, Matrix.single_one_vecMul] at hi
  have hφi : φ (Pi.single i 1) = u i := by
    simp [φ, Pi.single_apply]
  rw [hφi] at hi
  rw [← hi, LinearMap.pi_apply_eq_sum_univ g]
  simp [Matrix.row, smul_eq_mul]

lemma pm_pos {n : ℕ} (a x : Fin n → ℝ) (hx : IsPositive x) : 0 < powerMonomial a x :=
  Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hx i) _

lemma log_pm {n : ℕ} (a x : Fin n → ℝ) (hx : IsPositive x) :
    Real.log (powerMonomial a x) = ∑ i, a i * Real.log (x i) := by
  unfold powerMonomial
  rw [Real.log_prod]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.log_rpow (hx i)]
  · intro i _
    exact (Real.rpow_pos_of_pos (hx i) _).ne'

end VaryingConstants21f0

open VaryingConstants in
theorem solution {n d : ℕ} (D : Matrix (Fin n) (Fin d) ℝ)
    (x y : Fin n → ℝ) (hx : IsPositive x) (hy : IsPositive y) :
    (∀ a ∈ dimensionlessExponents D, powerMonomial a x = powerMonomial a y) ↔
      ∃ s : Fin d → ℝ, IsPositive s ∧ y = unitRescale D s x := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := VaryingConstants21f0.range_of_orth D (fun i => Real.log (y i) - Real.log (x i)) (by
      intro a ha
      have hmem : a ∈ dimensionlessExponents D := by
        simp only [dimensionlessExponents, LinearMap.mem_ker, Matrix.vecMulLinear_apply]
        exact ha
      have e := congrArg Real.log (h a hmem)
      rw [VaryingConstants21f0.log_pm a x hx, VaryingConstants21f0.log_pm a y hy] at e
      simp only [mul_sub, Finset.sum_sub_distrib]
      linarith)
    refine ⟨fun j => Real.exp (t j), fun j => Real.exp_pos _, ?_⟩
    funext i
    simp only [unitRescale]
    have hprod : ∏ j, Real.exp (t j) ^ D i j = Real.exp (∑ j, D i j * t j) := by
      rw [Real.exp_sum]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm]
    rw [hprod, ← ht i, Real.exp_sub, Real.exp_log (hy i), Real.exp_log (hx i)]
    field_simp [(hx i).ne']
  · rintro ⟨s, hs, rfl⟩ a ha
    simp only [dimensionlessExponents, LinearMap.mem_ker, Matrix.vecMulLinear_apply] at ha
    have hpos : IsPositive (unitRescale D s x) := fun i =>
      mul_pos (hx i) (Finset.prod_pos fun j _ => Real.rpow_pos_of_pos (hs j) _)
    apply Real.log_injOn_pos (Set.mem_Ioi.2 (VaryingConstants21f0.pm_pos a x hx)) (Set.mem_Ioi.2 (VaryingConstants21f0.pm_pos a _ hpos))
    rw [VaryingConstants21f0.log_pm a x hx, VaryingConstants21f0.log_pm a _ hpos]
    have hlog : ∀ i, Real.log (unitRescale D s x i) =
        Real.log (x i) + ∑ j, D i j * Real.log (s j) := by
      intro i
      simp only [unitRescale]
      rw [Real.log_mul (hx i).ne' (Finset.prod_pos fun j _ => Real.rpow_pos_of_pos (hs j) _).ne',
        Real.log_prod]
      · congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Real.log_rpow (hs j)]
      · intro j _
        exact (Real.rpow_pos_of_pos (hs j) _).ne'
    simp only [hlog, mul_add, Finset.sum_add_distrib]
    have hz : ∑ i, a i * ∑ j, D i j * Real.log (s j) = 0 := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro j _
      have hj := congrFun ha j
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at hj
      rw [show ∑ i, a i * (D i j * Real.log (s j)) = (∑ i, a i * D i j) * Real.log (s j) by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring, hj, zero_mul]
    linarith
