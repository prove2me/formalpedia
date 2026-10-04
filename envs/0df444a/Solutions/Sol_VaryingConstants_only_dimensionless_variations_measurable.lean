-- Prove2me | solution 1 for VaryingConstants.only_dimensionless_variations_measurable
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T20:09:26.589889+00:00
-- url     : https://prove2.me/submissions/b1b2b8ed-4490-416a-b311-1e2d02b9a8d8

import Mathlib
import Definitions.Def_VaryingConstants_units

open VaryingConstants in
lemma cc54_powerMonomial_eq {n : ℕ} (a x : Fin n → ℝ) (hx : IsPositive x) :
    powerMonomial a x = Real.exp (∑ i, a i * Real.log (x i)) := by
  unfold powerMonomial
  rw [Real.exp_sum]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [Real.rpow_def_of_pos (hx i), mul_comm]

open VaryingConstants Matrix in
lemma cc54_mem_range {n d : ℕ} (D : Matrix (Fin n) (Fin d) ℝ) (u : Fin n → ℝ)
    (hu : ∀ a ∈ dimensionlessExponents D, ∑ i, a i * u i = 0) :
    u ∈ LinearMap.range D.mulVecLin := by
  by_contra hnot
  obtain ⟨φ, hφu, hφp⟩ :=
    Submodule.exists_dual_map_eq_bot_of_notMem hnot (inferInstance)
  set a : Fin n → ℝ := fun i => φ (fun j => if i = j then 1 else 0) with ha
  have hφ : ∀ v : Fin n → ℝ, φ v = ∑ i, a i * v i := by
    intro v
    rw [LinearMap.pi_apply_eq_sum_univ φ v]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [ha, smul_eq_mul, mul_comm]
  have hzero : ∀ t : Fin d → ℝ, φ (D *ᵥ t) = 0 := by
    intro t
    have hmem : φ (D *ᵥ t) ∈ (LinearMap.range D.mulVecLin).map φ :=
      Submodule.mem_map_of_mem ⟨t, rfl⟩
    rw [hφp] at hmem
    simpa using hmem
  have hamem : a ∈ dimensionlessExponents D := by
    show a ∈ LinearMap.ker (Matrix.vecMulLinear D)
    rw [LinearMap.mem_ker, Matrix.coe_vecMulLinear]
    funext j
    have h1 := hzero (Pi.single j 1)
    rw [hφ] at h1
    have h2 : a ⬝ᵥ (D *ᵥ Pi.single j 1) = 0 := by
      simpa [dotProduct] using h1
    rw [Matrix.dotProduct_mulVec, dotProduct_single, mul_one] at h2
    simpa using h2
  have := hu a hamem
  exact hφu (by rw [hφ]; exact this)

open VaryingConstants in
theorem solution {n d : ℕ} (D : Matrix (Fin n) (Fin d) ℝ)
    (f : (Fin n → ℝ) → ℝ) (hf : IsUnitInvariant D f)
    (x y : Fin n → ℝ) (hx : IsPositive x) (hy : IsPositive y)
    (hxy : ∀ a ∈ dimensionlessExponents D, powerMonomial a x = powerMonomial a y) :
    f x = f y := by
  set u : Fin n → ℝ := fun i => Real.log (x i) - Real.log (y i) with hu
  have hmem : u ∈ LinearMap.range D.mulVecLin := by
    apply cc54_mem_range
    intro a ha
    have h := hxy a ha
    rw [cc54_powerMonomial_eq a x hx, cc54_powerMonomial_eq a y hy] at h
    have h' := Real.exp_injective h
    simp only [hu, mul_sub, Finset.sum_sub_distrib]
    linarith
  obtain ⟨t, ht⟩ := hmem
  set s : Fin d → ℝ := fun j => Real.exp (t j) with hs
  have hspos : IsPositive s := fun j => Real.exp_pos _
  have hresc : unitRescale D s y = x := by
    funext i
    unfold unitRescale
    have hprod : ∏ j, s j ^ D i j = Real.exp (u i) := by
      rw [← ht, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Real.exp_sum]
      refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [hs, ← Real.exp_mul, mul_comm]
    rw [hprod, hu]
    simp only
    rw [Real.exp_sub, Real.exp_log (hx i), Real.exp_log (hy i)]
    field_simp [(hy i).ne']
  rw [← hresc]
  exact hf y hy s hspos
