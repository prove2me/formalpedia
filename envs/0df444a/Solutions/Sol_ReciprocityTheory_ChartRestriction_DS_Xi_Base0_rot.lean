-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.rot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:25:41.214698+00:00
-- url     : https://prove2.me/submissions/6ff7d8ce-98a2-4073-b727-4fc95c039e22

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixedUnitaryApplyFixedIndexRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HalfLeNormOneSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_NormFixedUnitaryEntryLeOne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_ae_mem_fixedUnitary
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_lint_lmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_exists_fixedUnitary_sending_basis
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_fixedUnitary_apply_fixedIndex_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_fixedUnitary_apply_fixedIndex_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_fixedUnitary_conjTranspose_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_fixedUnitary_projection_identities

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k : ℕ}
private lemma mulVec_bvec_eq_fun_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    M *ᵥ bvec j = fun i => M i j := by
  funext i
  first
  | simp [Matrix.mulVec, bvec, Pi.single_apply]
  | simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]
  | simp [Matrix.mulVec, Matrix.dotProduct, bvec, Pi.single_apply]
private lemma iW_ne_iK' (hk : 1 ≤ k) : iW k ≠ iK k := by
  intro h
  have h' := congrArg Fin.val h
  simp [iW, iK, wI] at h'
  omega
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
end
end

set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.Base0
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0
theorem _root_.solution (hk : 1 ≤ k) {ν : Measure (Mt k 0)} (hν : IsHaarOn (U0 k) ν) {φ : ℂ → ℝ≥0∞}
    (hφ : Measurable φ) (v : Fin (2 * 0 + k + 1) → ℂ) (c : ℂ) (hc : c ≠ 0)
    (hvc : tW (iK k) v ^ 2 = Complex.normSq c) :
    ∫⁻ x, φ (((Matrix.of x)ᴴ *ᵥ v) (iW k)) ∂ν = ∫⁻ x, φ (star c * star (x (iW k) (iW k))) ∂ν := by
  have hWK := iW_ne_iK' hk
  have hcs : star c ≠ 0 := by
    intro h; apply hc; rw [← star_star c, h, star_zero]
  have hc2 : Complex.normSq c ≠ 0 := (Complex.normSq_pos.mpr hc).ne'
  have hS0 : 0 ≤ ∑ i, (if i = iK k then (0:ℝ) else Complex.normSq (v i)) :=
    Finset.sum_nonneg fun i _ => by split_ifs <;> simp [Complex.normSq_nonneg]
  have hS : (∑ i, if i = iK k then (0:ℝ) else Complex.normSq (v i)) = Complex.normSq c := by
    rw [← hvc]; unfold tW; rw [Real.sq_sqrt hS0]
  obtain ⟨u, hudef⟩ : ∃ u : Fin (2 * 0 + k + 1) → ℂ,
      u = fun i => if i = iK k then 0 else (star c)⁻¹ * v i := ⟨_, rfl⟩
  have hu0 : u (iK k) = 0 := by rw [hudef]; simp
  have hterm : ∀ i, star (u i) * u i =
      (((if i = iK k then (0:ℝ) else Complex.normSq (v i)) / Complex.normSq c : ℝ) : ℂ) := by
    intro i
    rw [show star (u i) * u i = ((Complex.normSq (u i) : ℝ) : ℂ) from
      (Complex.normSq_eq_conj_mul_self).symm]
    congr 1
    by_cases h : i = iK k
    · simp [hudef, h]
    · simp only [hudef, h, if_false]
      rw [Complex.normSq_mul, Complex.normSq_inv,
        show Complex.normSq (star c) = Complex.normSq c from Complex.normSq_conj c]
      ring
  have hu1 : star u ⬝ᵥ u = 1 := by
    first
    | simp only [dotProduct, Pi.star_apply, hterm]
    | simp only [Matrix.dotProduct, Pi.star_apply, hterm]
    rw [← Complex.ofReal_sum, ← Finset.sum_div, hS, div_self hc2, Complex.ofReal_one]
  obtain ⟨R, hR, hRe⟩ := exists_fixedUnitary_sending_basis hk u hu0 hu1
  have hRv : Rᴴ *ᵥ v = star c • bvec (iW k) + v (iK k) • bvec (iK k) := by
    have hv : v = star c • u + v (iK k) • bvec (iK k) := by
      funext i
      by_cases h : i = iK k
      · subst h; simp [hudef, bvec]
      · rw [hudef]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, if_neg h, bvec, Pi.single_apply,
          mul_zero, add_zero]
        rw [mul_inv_cancel_left₀ hcs]
    have h1 : Rᴴ *ᵥ u = bvec (iW k) := by
      rw [← hRe, Matrix.mulVec_mulVec, (fixedUnitary_projection_identities hR).1, Matrix.one_mulVec]
    have h2 : Rᴴ *ᵥ bvec (iK k) = bvec (iK k) := by
      rw [mulVec_bvec_eq_fun_apply]
      ext i
      rw [fixedUnitary_apply_fixedIndex_right (fixedUnitary_conjTranspose_mem hR) i]
      simp [bvec, Pi.single_apply]
    conv_lhs => rw [hv]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, h1, h2]
  have key : ∀ x : Mt k 0, (Matrix.of x : Mat k 0) ∈ U0 k →
      ((Matrix.of (lmulM R x))ᴴ *ᵥ v) (iW k) = star c * star (x (iW k) (iW k)) := by
    intro x hx
    have hx0 : x (iK k) (iW k) = 0 := by
      have h := fixedUnitary_apply_fixedIndex_left hx (iW k)
      rw [if_neg hWK] at h
      exact h
    show ((R * Matrix.of x)ᴴ *ᵥ v) (iW k) = _
    rw [Matrix.conjTranspose_mul, ← Matrix.mulVec_mulVec, hRv, Matrix.mulVec_add,
      Matrix.mulVec_smul, Matrix.mulVec_smul, mulVec_bvec_eq_fun_apply, mulVec_bvec_eq_fun_apply]
    simp [Matrix.conjTranspose_apply, hx0]
  have hcont : Continuous (fun x : Mt k 0 => ((Matrix.of x)ᴴ *ᵥ v) (iW k)) := by
    first
    | (simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Matrix.of_apply]
       exact continuous_finset_sum _ fun j _ =>
        (continuous_star.comp ((continuous_apply (iW k)).comp (continuous_apply j))).mul
          continuous_const)
    | (simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.conjTranspose_apply, Matrix.of_apply]
       exact continuous_finset_sum _ fun j _ =>
        (continuous_star.comp ((continuous_apply (iW k)).comp (continuous_apply j))).mul
          continuous_const)
    | fun_prop
  have hmeasF : Measurable (fun x : Mt k 0 => φ (((Matrix.of x)ᴴ *ᵥ v) (iW k))) :=
    hφ.comp hcont.measurable
  calc ∫⁻ x, φ (((Matrix.of x)ᴴ *ᵥ v) (iW k)) ∂ν
      = ∫⁻ x, φ (((Matrix.of (lmulM R x))ᴴ *ᵥ v) (iW k)) ∂ν := (lint_lmul hν hR hmeasF).symm
    _ = ∫⁻ x, φ (star c * star (x (iW k) (iW k))) ∂ν := by
        apply lintegral_congr_ae
        filter_upwards [ae_mem_fixedUnitary hν] with x hx
        rw [key x hx]
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
