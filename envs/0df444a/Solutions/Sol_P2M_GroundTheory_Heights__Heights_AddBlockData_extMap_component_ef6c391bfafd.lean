-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AddBlockData_extMap_component_ef6c391bfafd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:43:42.117845+00:00
-- url     : https://prove2.me/submissions/07fbb2b0-ae6a-434f-9a38-4c6c7326e242

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_WeightEqMapDomain
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockData_weight_eq_mapDomain_90c6d62f9171
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockData_extMap_monomial_20d7db73113e

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
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.AddBlockData
variable {P : ArithVariety n} (D : AddBlockData P)
namespace GroundTheory.Heights₂.Heights.AddBlockData
theorem _root_.solution (m : Option ι → ℕ) (f : MvPolynomial (Coord D.extSizes) ℤ) :
    D.extMap (weightedHomogeneousComponent (coordDeg D.extSizes) m f) =
      monomial (Finsupp.equivFunOnFinite.symm m)
        (coeff (Finsupp.equivFunOnFinite.symm m) (D.extMap f)) := by
  induction f using MvPolynomial.induction_on' with
  | monomial s a =>
    have hh := isWeightedHomogeneous_monomial (coordDeg D.extSizes) s a rfl
    rw [weightedHomogeneousComponent_of_mem (m := m) hh, extMap_monomial, coeff_monomial]
    by_cases h : m = Finsupp.weight (coordDeg D.extSizes) s
    · have h' : s.mapDomain Sigma.fst = Finsupp.equivFunOnFinite.symm m := by
        apply DFunLike.coe_injective
        rw [Finsupp.coe_equivFunOnFinite_symm, h, weight_eq_mapDomain]
      rw [if_pos h, if_pos h', extMap_monomial, h']
    · have h' : s.mapDomain Sigma.fst ≠ Finsupp.equivFunOnFinite.symm m := by
        intro e
        apply h
        rw [← weight_eq_mapDomain, e]
        rfl
      rw [if_neg h, if_neg h', map_zero, monomial_zero]
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq, map_add, coeff_add, map_add]
end GroundTheory.Heights₂.Heights.AddBlockData
