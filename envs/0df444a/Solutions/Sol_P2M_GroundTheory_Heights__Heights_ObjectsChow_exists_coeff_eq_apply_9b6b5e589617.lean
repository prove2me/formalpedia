-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_exists_coeff_eq_apply_9b6b5e589617
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:45:35.039043+00:00
-- url     : https://prove2.me/submissions/1878fd51-d066-433a-a33a-ce0489654d99

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LinFormOneZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsGenericFibreDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PAffineChartTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PIntChowFormExists

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
open GroundTheory.Heights₂.Heights.ObjectsChow
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)
namespace GroundTheory.Heights₂.Heights.ObjectsChow
theorem _root_.solution {σ R S : Type*} [CommSemiring R] [CommSemiring S] (F : R → S) (hF : F 0 = 0)
    (p : MvPolynomial σ R) : ∃ q : MvPolynomial σ S, ∀ m, coeff m q = F (coeff m p) := by
  classical
  refine ⟨∑ m ∈ p.support, monomial m (F (coeff m p)), fun m' => ?_⟩
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, hF]
end GroundTheory.Heights₂.Heights.ObjectsChow
