-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogDetGramDeriv_proof_744363b5faa9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:57:24.249713+00:00
-- url     : https://prove2.me/submissions/36d4bbe4-bfdd-4afb-8c7c-9d76dffbe33f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PLogDetGramDeriv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCLogDetGramDeriv_constK_pos_9ffca9a7baa6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCLogDetGramDeriv_key_bound_462b1424da6d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
noncomputable section
open MCLogDetGramDeriv
namespace GroundTheory.Heights₂.Heights
namespace LogDetGramDeriv
theorem _root_.solution (h₁ : InvEntryBound.Statement) (h₂ : InvEntryDeriv.Statement)
    (h₃ : MatrixDetDeriv.Statement) (h₄ : GramEntryDeriv.Statement) :
    LogDetGramDeriv.Statement := by
  intro g k
  refine ⟨constK g k, constK_pos g k, ?_⟩
  intro E _ _ F Y p a b c μ hc hμ ha hb hF hY hYc hdet
  have hZ : ∀ j l, DifferentiableAt ℝ (fun q => (Y q)⁻¹ j l) p ∧ |(Y p)⁻¹ j l| ≤ c⁻¹ ∧
      ‖fderiv ℝ (fun q => (Y q)⁻¹ j l) p‖ ≤ (g : ℝ) ^ 2 * c⁻¹ ^ 2 * b := fun j l =>
    ⟨(h₂ g Y p c b hc hYc hY j l).1, h₁ g (Y p) c hc hYc j l, (h₂ g Y p c b hc hYc hY j l).2⟩
  have hG := h₄ g k F (fun q => (Y q)⁻¹) p a c⁻¹ ((g : ℝ) ^ 2 * c⁻¹ ^ 2 * b) hF hZ
  have hD := h₃ k (fun q => (F q)ᴴ * (Y q)⁻¹.map (fun x : ℝ => (x : ℂ)) * F q) p
    ((g : ℝ) ^ 2 * a ^ 2 * c⁻¹)
    ((g : ℝ) ^ 2 * (2 * a ^ 2 * c⁻¹ + a ^ 2 * ((g : ℝ) ^ 2 * c⁻¹ ^ 2 * b))) hG
  set d : E → ℂ := fun q => ((F q)ᴴ * (Y q)⁻¹.map (fun x : ℝ => (x : ℂ)) * F q).det with hd_def
  have hpos : 0 < (d p).re := lt_of_lt_of_le hμ hdet
  have hre : HasFDerivAt (fun q => (d q).re) (Complex.reCLM.comp (fderiv ℝ d p)) p := by
    have := Complex.reCLM.hasFDerivAt.comp p hD.1.hasFDerivAt
    simpa [Function.comp_def] using this
  have hL := hre.log hpos.ne'
  have hfun : (fun q => logDetGram (Y q) (F q)) = fun q => Real.log (d q).re := by
    funext q; rfl
  rw [hfun]
  refine ⟨hL.differentiableAt, ?_⟩
  rw [hL.fderiv]
  have hnorm : ‖Complex.reCLM.comp (fderiv ℝ d p)‖ ≤ ‖fderiv ℝ d p‖ := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [Complex.reCLM_norm, one_mul]
  have hkey := key_bound g k a b c⁻¹ ha hb (inv_nonneg.mpr hc.le)
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos]
  calc (d p).re⁻¹ * ‖Complex.reCLM.comp (fderiv ℝ d p)‖
      ≤ (d p).re⁻¹ * ‖fderiv ℝ d p‖ := by gcongr
    _ = ‖fderiv ℝ d p‖ / (d p).re := by ring
    _ ≤ ‖fderiv ℝ d p‖ / μ := by gcongr
    _ ≤ constK g k * (1 + a) ^ (2 * k) * (1 + c⁻¹) ^ (k + 1) * (1 + b) / μ := by
      gcongr
      exact hD.2.trans hkey
end LogDetGramDeriv
end GroundTheory.Heights₂.Heights
