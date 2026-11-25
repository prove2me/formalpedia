-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.F.EigA.end_eq_trace_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:33:22.016143+00:00
-- url     : https://prove2.me/submissions/f28e7e0f-ddbe-4275-8940-72dea1fa1af2

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_FixedSpaceRankOne_FinrankFixedEqOne
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_FixedSpaceRankOne_TraceMulOfFinrankOne

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
theorem _root_.solution (h : Module.finrank ℂ M = 1) (f : Module.End ℂ M) : f = LinearMap.trace ℂ M f • 1 := by
  haveI : FiniteDimensional ℂ M := Module.finite_of_finrank_eq_succ h
  let b : Module.Basis (Fin 1) ℂ M := Module.finBasisOfFinrankEq ℂ M h
  apply b.ext
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  rw [LinearMap.trace_eq_matrix_trace ℂ b f, Matrix.trace_fin_one, LinearMap.toMatrix_apply,
    LinearMap.smul_apply, Module.End.one_apply]
  conv_lhs => rw [← b.sum_repr (f (b 0))]
  rw [Fin.sum_univ_one]
end PositivityTheory.Rg.BcB.F.EigA
