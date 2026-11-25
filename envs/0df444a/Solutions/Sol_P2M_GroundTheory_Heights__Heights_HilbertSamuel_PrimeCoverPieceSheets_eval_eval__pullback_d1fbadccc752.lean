-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_PrimeCoverPieceSheets_eval_eval__pullback_d1fbadccc752
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:16.596166+00:00
-- url     : https://prove2.me/submissions/93990f75-4270-4997-b959-56ea5dc30c7b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StPrimeCoverPieceSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StPieceRootProductPolynomial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDiscrAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFunctionFieldDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDiscriminantCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveElementFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_PPrimeCoverPieceSheets
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_eval_pullback_d784c0eada3b


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial Matrix
open GroundTheory.Heights₂.Heights.HilbertSamuel.PrimeCoverPieceSheets
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.PrimeCoverPieceSheets
theorem _root_.solution {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) (x : Fin n → ℂ)
    (p : MvPolynomial (Fin n) ℂ) (G : Polynomial (MvPolynomial (Fin d) ℂ)) :
    eval x (Polynomial.eval₂ (ComplexSets.pullback A).toRingHom p G) =
      (G.map (eval (A *ᵥ x))).eval (eval x p) := by
  rw [Polynomial.hom_eval₂, Polynomial.eval_map]
  congr 1
  apply RingHom.ext
  intro P
  exact ComplexSets.FibreBound.eval_pullback A x P
end GroundTheory.Heights₂.Heights.HilbertSamuel.PrimeCoverPieceSheets
