-- Prove2me | solution 1 for Planks.stationary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:43:26.377717+00:00
-- url     : https://prove2.me/submissions/5d6dcfa8-19c9-4bed-849d-eb0f71ff1351

module
public import Mathlib
public import Definitions.Def_BallPlank_Planks
public import Theorems.Thm_Planks_rot_zero
public import Theorems.Thm_Planks_rot_orthonormal

set_option autoImplicit true
@[expose] public section
public section
open scoped RealInnerProductSpace
open Classical
noncomputable section
open Planks
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι]
omit [FiniteDimensional ℝ E]
namespace Planks
theorem _root_.solution (ℓ : ι → E →L[ℝ] ℝ) (y : ι → E) (hy : y ∈ admissible ℓ)
    (hmin : IsMinOn (objF ℓ) (admissible ℓ) y) (hF : objF ℓ y ≤ Fintype.card ι)
    (i j : ι) (hij : i ≠ j) :
    ((ℓ i (y i))⁻¹) ^ 3 * ℓ i (y j) = ((ℓ j (y j))⁻¹) ^ 3 * ℓ j (y i) := by
  have hji : j ≠ i := Ne.symm hij
  let du : ι → ℝ := fun k => if k = i then ℓ i (y j) else if k = j then -ℓ j (y i) else 0
  have hu : ∀ k, HasDerivAt (fun t => ℓ k (rot y i j t k)) (du k) 0 := by
    intro k
    by_cases hki : k = i
    · subst hki
      have e : (fun t => ℓ k (rot y k j t k)) =
          (fun t => Real.cos t * ℓ k (y k)) + fun t => Real.sin t * ℓ k (y j) := by
        ext t; simp [rot]
      rw [e]
      have := ((Real.hasDerivAt_cos 0).mul_const (ℓ k (y k))).add
        ((Real.hasDerivAt_sin 0).mul_const (ℓ k (y j)))
      simpa [du] using this
    · by_cases hkj : k = j
      · subst hkj
        have e : (fun t => ℓ k (rot y i k t k)) =
            (-fun t => Real.sin t * ℓ k (y i)) + fun t => Real.cos t * ℓ k (y k) := by
          ext t; simp [rot, hki]
        rw [e]
        have := (((Real.hasDerivAt_sin 0).mul_const (ℓ k (y i))).neg).add
          ((Real.hasDerivAt_cos 0).mul_const (ℓ k (y k)))
        simpa [du, hki] using this
      · have e : (fun t => ℓ k (rot y i j t k)) = fun _ => ℓ k (y k) := by
          funext t; simp [rot, hki, hkj]
        rw [e]
        simpa [du, hki, hkj] using hasDerivAt_const (0 : ℝ) (ℓ k (y k))
  have hy0 : ∀ k, ℓ k (y k) ≠ 0 := fun k h0 => by
    have := hy.2 k
    rw [h0] at this
    norm_num at this
  have hr0 : ∀ k, rot y i j 0 k = y k := fun k => by rw [rot_zero]
  have hg : ∀ k, HasDerivAt (fun t => ((ℓ k (rot y i j t k))⁻¹) ^ 2)
      (((2 : ℕ) : ℝ) * ((ℓ k (rot y i j 0 k))⁻¹) ^ (2 - 1) *
        (-(du k) / (ℓ k (rot y i j 0 k)) ^ 2)) 0 := fun k =>
    ((hu k).inv (by rw [hr0]; exact hy0 k)).pow 2
  have hFd : HasDerivAt (fun t => objF ℓ (rot y i j t)) (∑ k, (((2 : ℕ) : ℝ) *
      ((ℓ k (rot y i j 0 k))⁻¹) ^ (2 - 1) * (-(du k) / (ℓ k (rot y i j 0 k)) ^ 2))) 0 :=
    HasDerivAt.fun_sum fun k _ => hg k
  have hmem : ∀ᶠ t in nhds (0 : ℝ), rot y i j t ∈ admissible ℓ := by
    have hk : ∀ k, ∀ᶠ t in nhds (0 : ℝ),
        1 < 2 * (Fintype.card ι : ℝ) * (ℓ k (rot y i j t k)) ^ 2 := by
      intro k
      have hc : ContinuousAt (fun t => 2 * (Fintype.card ι : ℝ) * (ℓ k (rot y i j t k)) ^ 2) 0 :=
        ((hu k).continuousAt.pow 2).const_mul _
      have hv : 1 < 2 * (Fintype.card ι : ℝ) * (ℓ k (rot y i j 0 k)) ^ 2 := by
        rw [hr0]
        have hle : ((ℓ k (y k))⁻¹) ^ 2 ≤ Fintype.card ι :=
          le_trans (Finset.single_le_sum (f := fun k => ((ℓ k (y k))⁻¹) ^ 2)
            (fun _ _ => sq_nonneg _) (Finset.mem_univ k)) hF
        have hpos : 0 < (ℓ k (y k)) ^ 2 := by have := hy0 k; positivity
        have : ((ℓ k (y k))⁻¹) ^ 2 * (ℓ k (y k)) ^ 2 = 1 := by
          rw [← mul_pow, inv_mul_cancel₀ (hy0 k), one_pow]
        nlinarith
      exact Filter.Tendsto.eventually hc (lt_mem_nhds hv)
    filter_upwards [Filter.eventually_all.mpr hk] with t ht
    exact ⟨rot_orthonormal y hy.1 i j hij t, fun k => (ht k).le⟩
  have hlm : IsLocalMin (fun t => objF ℓ (rot y i j t)) 0 := by
    filter_upwards [hmem] with t ht
    simp only [rot_zero]
    exact hmin ht
  have h0 := hlm.hasDerivAt_eq_zero hFd
  rw [Fintype.sum_eq_add i j hij (fun k hk => by simp [du, hk.1, hk.2])] at h0
  simp [hr0, du, hji] at h0
  linear_combination (-1 / 2 : ℝ) * h0
end Planks
