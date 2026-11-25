-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.fderiv_eq_zero_of_vanish
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:06:05.509868+00:00
-- url     : https://prove2.me/submissions/98eadb0b-7f72-454f-9118-1cda63f6176f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_HasFDerivAtInt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_Imports
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarDir
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_FderivEqZeroOfVanish
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_two_le_infty
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_det_ne_zero_of_inG
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_HolB_fderiv_line
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_HolB_herm_real_smul
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_HolB_inG_lower
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_HolB_inG_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_HolB_inG_scalar
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_HolB_inG_upper
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_HolB_lower_line
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_HolB_upper_line
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_HolC_span_top
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_HolD_line2
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_HolD_scalar_dir


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set Metric Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs.HolB PositivityTheory.Rg.Sw.LVs.HolC
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    {Ω : Set (M2 n)} (hΩ : IsOpen Ω) (hG : GSet n ⊆ Ω) {H : M2 n → V} (hH : ContDiffOn ℂ ∞ H Ω)
    (h0 : ∀ g, InG g → H g = 0) {y : M2 n} (hy : InG y) : fderiv ℂ H y = 0 := by
  have hdiff : ∀ g, InG g → DifferentiableAt ℂ H g := fun g hg =>
    (hH.contDiffAt (hΩ.mem_nhds (hG hg))).differentiableAt (by simp)
  have hlow : ∀ g, InG g → ∀ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c →
      fderiv ℂ H g (g * fromBlocks 0 0 c 0) = 0 := by
    intro g hg c hc
    refine fderiv_line (hdiff g hg) (fun t => ?_)
    rw [lower_line, h0 _ (inG_mul hg (inG_lower (herm_real_smul hc t))), h0 g hg]
  have hup : ∀ g, InG g → ∀ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b →
      fderiv ℂ H g (g * fromBlocks 0 b 0 0) = 0 := by
    intro g hg b hb
    refine fderiv_line (hdiff g hg) (fun t => ?_)
    rw [upper_line, h0 _ (inG_mul hg (inG_upper (herm_real_smul hb t))), h0 g hg]
  have hone : fderiv ℂ H y (y * 1) = 0 := by
    rw [mul_one]
    refine HolD.scalar_dir (hdiff y hy) (fun t => h0 _ ?_)
    have e : Complex.exp (↑t * Complex.I) • y = y * (Complex.exp (↑t * Complex.I) • (1 : M2 n)) := by
      rw [mul_smul_comm, mul_one]
    rw [e]
    refine inG_mul hy (inG_scalar ?_)
    rw [Complex.star_def, Complex.conj_mul', Complex.norm_exp_ofReal_mul_I]
    simp
  have hCy : ContDiffAt ℂ ∞ H y := hH.contDiffAt (hΩ.mem_nhds (hG hy))
  have hsymm : IsSymmSndFDerivAt ℂ H y :=
    hCy.isSymmSndFDerivAt (by simpa [minSmoothness_of_isRCLikeNormedField] using two_le_infty)
  have hD : DifferentiableAt ℂ (fderiv ℂ H) y :=
    (hCy.fderiv_right (m := 1) (by simpa [one_add_one_eq_two] using two_le_infty)).differentiableAt one_ne_zero
  have hcomm : ∀ b c : Matrix (Fin n) (Fin n) ℂ, bᴴ = b → cᴴ = c →
      fderiv ℂ H y (y * fromBlocks (-(b * c)) 0 0 (c * b)) = 0 := by
    intro b c hb hc
    set U : M2 n := fromBlocks 0 b 0 0 with hU
    set L : M2 n := fromBlocks 0 0 c 0 with hL
    let mL : M2 n →L[ℂ] M2 n := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℂ L)
    let mU : M2 n →L[ℂ] M2 n := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℂ U)
    have e1 := HolD.line2 (H := H) (y := y) (w := y * U) (m := mL) hD (fun t => by
      have hg := inG_mul hy (inG_upper (herm_real_smul hb t))
      show fderiv ℂ H _ ((y + (t : ℂ) • (y * U)) * L) = 0
      rw [upper_line]
      exact hlow _ hg c hc)
    have e2 := HolD.line2 (H := H) (y := y) (w := y * L) (m := mU) hD (fun t => by
      have hg := inG_mul hy (inG_lower (herm_real_smul hc t))
      show fderiv ℂ H _ ((y + (t : ℂ) • (y * L)) * U) = 0
      rw [lower_line]
      exact hup _ hg b hb)
    change fderiv ℂ (fderiv ℂ H) y (y * U) (y * L) + fderiv ℂ H y (y * U * L) = 0 at e1
    change fderiv ℂ (fderiv ℂ H) y (y * L) (y * U) + fderiv ℂ H y (y * L * U) = 0 at e2
    have key : fromBlocks (-(b * c)) 0 0 (c * b) = L * U - U * L := by
      simp only [hU, hL, Matrix.fromBlocks_multiply]
      rw [sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
      simp
    rw [key, mul_sub, ← mul_assoc, ← mul_assoc, map_sub]
    have a1 := eq_neg_of_add_eq_zero_right e1
    have a2 := eq_neg_of_add_eq_zero_right e2
    have hs : fderiv ℂ (fderiv ℂ H) y (y * L) (y * U) = fderiv ℂ (fderiv ℂ H) y (y * U) (y * L) :=
      hsymm _ _
    rw [sub_eq_zero]
    exact a2.trans ((congrArg Neg.neg hs).trans a1.symm)
  let W : Submodule ℂ (M2 n) :=
    LinearMap.ker ((fderiv ℂ H y : M2 n →ₗ[ℂ] V) ∘ₗ LinearMap.mulLeft ℂ y)
  have hW : W = ⊤ :=
    span_top W (fun b hb => LinearMap.mem_ker.mpr (hup y hy b hb))
      (fun c hc => LinearMap.mem_ker.mpr (hlow y hy c hc))
      (fun b c hb hc => LinearMap.mem_ker.mpr (hcomm b c hb hc))
      (LinearMap.mem_ker.mpr hone)
  have hdet : IsUnit y.det := isUnit_iff_ne_zero.mpr (det_ne_zero_of_inG hy)
  ext u
  have hu : y⁻¹ * u ∈ W := hW ▸ Submodule.mem_top
  have e := LinearMap.mem_ker.mp hu
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
    ContinuousLinearMap.coe_coe, Matrix.mul_nonsing_inv_cancel_left _ _ hdet] at e
  simpa using e
end PositivityTheory.Rg.Sw.LVs
