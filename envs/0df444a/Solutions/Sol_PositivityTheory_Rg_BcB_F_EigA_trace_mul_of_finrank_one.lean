-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.F.EigA.trace_mul_of_finrank_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:21:18.026677+00:00
-- url     : https://prove2.me/submissions/a75c4ff8-f841-452d-87aa-48bfb971af92

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_FixedSpaceRankOne_FinrankFixedEqOne
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_FixedSpaceRankOne_TraceMulOfFinrankOne
import Theorems.Thm_PositivityTheory_Rg_BcB_F_EigA_end_eq_trace_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Pointwise
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.EigA
variable {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.BcB.F.EigA
theorem _root_.solution (h : Module.finrank ℂ M = 1) (f g : Module.End ℂ M) :
    LinearMap.trace ℂ M (f * g) = LinearMap.trace ℂ M f * LinearMap.trace ℂ M g := by
  haveI : FiniteDimensional ℂ M := Module.finite_of_finrank_eq_succ h
  have hf := end_eq_trace_smul h f
  have hg := end_eq_trace_smul h g
  calc LinearMap.trace ℂ M (f * g)
      = LinearMap.trace ℂ M ((LinearMap.trace ℂ M f • 1) * (LinearMap.trace ℂ M g • 1)) := by
        rw [← hf, ← hg]
    _ = LinearMap.trace ℂ M f * LinearMap.trace ℂ M g := by
        rw [smul_mul_smul_comm, one_mul, map_smul, LinearMap.trace_one, h, smul_eq_mul, Nat.cast_one, mul_one]
end PositivityTheory.Rg.BcB.F.EigA
