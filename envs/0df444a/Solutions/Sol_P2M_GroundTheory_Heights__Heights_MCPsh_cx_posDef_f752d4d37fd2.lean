-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCPsh_cx_posDef_f752d4d37fd2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:04:13.720329+00:00
-- url     : https://prove2.me/submissions/7c6582a5-21ba-4edf-ba59-f2ef9cbde1bf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshCore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCPsh
open Matrix Metric Real
open scoped MatrixOrder ComplexOrder
noncomputable section
set_option linter.unusedSectionVars false
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
namespace GroundTheory.Heights₂.Heights.MCPsh
theorem _root_.solution {Y : Matrix ι ι ℝ} (hY : Y.PosDef) : (cx Y).PosDef := by
  have hsymm : ∀ i j, Y j i = Y i j := fun i j => by
    have := congrFun (congrFun hY.isHermitian i) j
    simpa [conjTranspose_apply] using this
  refine PosDef.of_dotProduct_mulVec_pos (hY.isHermitian.map _ fun x => by simp) fun x hx => ?_
  set a : ι → ℝ := fun i => (x i).re
  set b : ι → ℝ := fun i => (x i).im
  have hre : ∀ (u v : ℂ) (y : ℝ), (star u * ((y : ℂ) * v)).re = y * (u.re * v.re + u.im * v.im) :=
    fun u v y => by simp [Complex.mul_re, Complex.mul_im]; ring
  have him : ∀ (u v : ℂ) (y : ℝ), (star u * ((y : ℂ) * v)).im = y * (u.re * v.im - u.im * v.re) :=
    fun u v y => by simp [Complex.mul_re, Complex.mul_im]; ring
  have e1 : star x ⬝ᵥ (cx Y *ᵥ x) = ∑ i, ∑ j, star (x i) * ((Y i j : ℂ) * x j) := by
    simp [dotProduct, mulVec, Finset.mul_sum]
  have e2 : a ⬝ᵥ (Y *ᵥ a) + b ⬝ᵥ (Y *ᵥ b) =
      ∑ i, ∑ j, Y i j * ((x i).re * (x j).re + (x i).im * (x j).im) := by
    simp only [dotProduct, mulVec, Finset.mul_sum, ← Finset.sum_add_distrib, a, b]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have e3 : ∑ i, ∑ j, Y i j * ((x i).re * (x j).im - (x i).im * (x j).re) = 0 := by
    have hswap : ∑ i, ∑ j, Y i j * ((x i).im * (x j).re) =
        ∑ i, ∑ j, Y i j * ((x i).re * (x j).im) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hsymm]; ring
    simp only [mul_sub, Finset.sum_sub_distrib, hswap, sub_self]
  have key : star x ⬝ᵥ (cx Y *ᵥ x) = ((a ⬝ᵥ (Y *ᵥ a) + b ⬝ᵥ (Y *ᵥ b) : ℝ) : ℂ) := by
    rw [e1]
    apply Complex.ext
    · simp only [Complex.re_sum, hre, Complex.ofReal_re, e2]
    · simp only [Complex.im_sum, him, Complex.ofReal_im, e3]
  rw [key]
  have ha := hY.posSemidef.dotProduct_mulVec_nonneg a
  have hb := hY.posSemidef.dotProduct_mulVec_nonneg b
  simp only [star_trivial] at ha hb
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h; push Not at h; exact hx (funext h)
  have hpos : 0 < a ⬝ᵥ (Y *ᵥ a) + b ⬝ᵥ (Y *ᵥ b) := by
    by_cases hai : a = 0
    · have hbi : b ≠ 0 := by
        intro hbi
        apply hi
        apply Complex.ext
        · simpa using congrFun hai i
        · simpa using congrFun hbi i
      have := hY.dotProduct_mulVec_pos hbi
      simp only [star_trivial] at this
      linarith
    · have := hY.dotProduct_mulVec_pos hai
      simp only [star_trivial] at this
      linarith
  exact_mod_cast hpos
end GroundTheory.Heights₂.Heights.MCPsh
