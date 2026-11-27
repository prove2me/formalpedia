-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KFock.gsSch
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:20:42.316356+00:00
-- url     : https://prove2.me/submissions/f9d42624-3f2c-4944-92b2-1e8e9a221969

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_FockSpaces_EvXTemperate
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFock_eucl_norm_sq
import Theorems.Thm_GroundTheory_Global_gaussianSchwartz_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.gaussianSchwartz_apply



set_option autoImplicit false
noncomputable section
open scoped SchwartzMap
open PositivityTheory.Rg.Sw
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KFock
namespace PositivityTheory.SiegelWeilFormula.KFock
theorem _root_.solution (m n : ℕ) {c : ℝ} (hc : 0 < c) : ∃ G : 𝓢(Fin m → Fin n → ℂ, ℂ), ∀ x, G x = gs c x := by
  have hpi : 0 < Real.pi := Real.pi_pos
  set s := Real.sqrt (c / Real.pi) with hsdef
  have hs : s ≠ 0 := (Real.sqrt_pos.mpr (div_pos hc hpi)).ne'
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (eucl m n s hs)
    (GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℂ (Fin m × Fin n))), fun x => ?_⟩
  have hs2 : s ^ 2 = c / Real.pi := Real.sq_sqrt (div_pos hc hpi).le
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    GroundTheory.Global.gaussianSchwartz_apply, eucl_norm_sq, gs]
  rw [hs2, Complex.ofReal_exp]
  congr 1
  push_cast
  field_simp
end PositivityTheory.SiegelWeilFormula.KFock
