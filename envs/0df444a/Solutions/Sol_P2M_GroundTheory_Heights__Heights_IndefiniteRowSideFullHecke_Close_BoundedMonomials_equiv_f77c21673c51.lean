-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_BoundedMonomials_equiv_f77c21673c51
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:05:41.529197+00:00
-- url     : https://prove2.me/submissions/5365c48b-8e1d-40c6-93d2-bc0faa45e425

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_ChartFormEvalAgree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_chartForm_eval_agree_0082e1f960fa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
namespace BoundedMonomials
theorem _root_.solution :
    GroundTheory.Heights₂.Heights.BoundedMonomials.Statement ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.BoundedMonomials.Statement := by
  constructor
  · intro hA ι _ _ n P M k e
    exact hA ι n P (powDivStd M k) e
  · intro hB ι _ _ n P A s
    have hdeg : (powDivStd (twistPow A 1 1 0) 1).deg = A.deg := by
      funext b
      simp [powDivStd, twistPow]
    have hmet : ∀ z ∈ P.points ℂ, (powDivStd (twistPow A 1 1 0) 1).metric z = A.metric z := by
      intro z hz
      have hS := ((HermLine.standard n).metric_pos z hz.1).ne'
      simp only [powDivStd, twistPow, Nat.cast_one, one_mul, mul_zero, neg_zero, Real.exp_zero,
        pow_one]
      field_simp
    exact chartForm_eval_agree P A _ hdeg hmet (hB ι n P (twistPow A 1 1 0) 1) s
end BoundedMonomials
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
