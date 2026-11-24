-- Prove2me | solution 1 for PositivityTheory.KReal.pd_pd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:20.787044+00:00
-- url     : https://prove2.me/submissions/e72ae415-eed9-4de3-b7cc-12da12660c77

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_JointShape
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_FockAct1FockAct2Commute

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial FockH1Action
open PositivityTheory PositivityTheory.KReal
variable {σ : Type*} [DecidableEq σ]
namespace PositivityTheory.KReal
theorem _root_.solution (a b : σ) :
    ((pderiv a).toLinearMap * (pderiv b).toLinearMap : Module.End ℂ (MvPolynomial σ ℂ)) =
      (pderiv b).toLinearMap * (pderiv a).toLinearMap := by
  refine LinearMap.ext fun P => ?_
  change pderiv a (pderiv b P) = pderiv b (pderiv a P)
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P n hP =>
    simp only [Derivation.leibniz, smul_eq_mul, map_add, hP, pderiv_X, Pi.single_apply]
    split_ifs <;> simp <;> ring
end PositivityTheory.KReal
