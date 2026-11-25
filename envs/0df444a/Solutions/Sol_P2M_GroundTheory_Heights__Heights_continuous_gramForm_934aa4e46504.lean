-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_continuous_gramForm_934aa4e46504
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:26:30.768251+00:00
-- url     : https://prove2.me/submissions/86ee2958-2ef2-4a82-a2c5-f821247ac1a6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetAreaLintegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetParam
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMapArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetAreaLintegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix Filter Topology Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre segre)
open scoped ENNReal
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {e n : ℕ} :
    Continuous (gramForm : (Fin n → ℂ) × ((Fin e → ℂ) →L[ℂ] (Fin n → ℂ)) → ℝ) := by
  have hw : Continuous fun p : (Fin n → ℂ) × ((Fin e → ℂ) →L[ℂ] (Fin n → ℂ)) =>
      (Fin.cons p.1 fun j => p.2 (Pi.single j 1) : Fin (e + 1) → Fin n → ℂ) := by
    refine continuous_pi fun a => ?_
    refine Fin.cases ?_ (fun j => ?_) a
    · simpa using continuous_fst
    · simpa using continuous_snd.clm_apply continuous_const
  refine Complex.continuous_re.comp (Continuous.matrix_det ?_)
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [Matrix.of_apply]
  refine continuous_finsetSum _ fun i _ => ?_
  exact ((continuous_apply i).comp ((continuous_apply a).comp hw)).star.mul
    ((continuous_apply i).comp ((continuous_apply b).comp hw))
end GroundTheory.Heights₂.Heights
