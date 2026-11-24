-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_norm_lt_of_isRoot_map_eval_c7fa46924b2e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:32.267233+00:00
-- url     : https://prove2.me/submissions/5eed0b67-d59e-4562-b808-25254370c6b5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelProper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelProper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {n : ℕ} {P : Polynomial (MvPolynomial (Fin n) ℂ)} (hPm : P.Monic)
    (x : Fin n → ℂ) {a : ℂ} (ha : (P.map (eval x)).IsRoot a) :
    ‖a‖ < 1 + ∑ j ∈ Finset.range P.natDegree, ‖eval x (P.coeff j)‖ := by
  have hQm : (P.map (eval x)).Monic := hPm.map _
  have hlt := Polynomial.IsRoot.norm_lt_cauchyBound hQm.ne_zero ha
  have hcb : Polynomial.cauchyBound (P.map (eval x)) ≤
      (∑ j ∈ Finset.range P.natDegree, ‖eval x (P.coeff j)‖₊) + 1 := by
    rw [Polynomial.cauchyBound, hQm.leadingCoeff, nnnorm_one, div_one, hPm.natDegree_map]
    gcongr
    refine Finset.sup_le fun j hj => ?_
    rw [Polynomial.coeff_map]
    exact Finset.single_le_sum (f := fun j => ‖eval x (P.coeff j)‖₊) (fun _ _ => zero_le) hj
  have h := hlt.trans_le hcb
  rw [← NNReal.coe_lt_coe, NNReal.coe_add, NNReal.coe_sum, coe_nnnorm, NNReal.coe_one] at h
  simp only [coe_nnnorm] at h
  linarith
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
