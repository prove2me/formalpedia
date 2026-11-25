-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_coneAff_X_4498be14a2db
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:30:47.032568+00:00
-- url     : https://prove2.me/submissions/4423994b-52f6-49b1-8bda-4b9f472973aa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PointHeightDegreeHypotheses
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_homExp_single_zero_f61967745276
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_homExp_single_succ_a639e0d92aa5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_homMap_monomial_be73811eb40e

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
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (mConeMap mCoordIdeal mcPts)
noncomputable section
variable (K : Type) [Field K] (r : ℕ)
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
theorem _root_.solution (j : Fin (r + 1)) : coneAff K r (X j) = C (affGen K r j) * X () := by
  have hX : ∀ s : Unit ⊕ Fin r, (X s : MvPolynomial (Unit ⊕ Fin r) K) = monomial (Finsupp.single s 1) 1 :=
    fun _ ↦ rfl
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · have h : homMap K r (X 0) = X (Sum.inl ()) := by
      rw [show (X 0 : MvPolynomial (Fin (r + 1)) K) = monomial (Finsupp.single 0 1) 1 from rfl,
        homMap_monomial, homExp_single_zero, hX]
    simp only [coneAff, RingHom.comp_apply, h, fieldMap, RingEquiv.toRingHom_eq_coe,
      AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_coe, sumAlgEquiv_X_inl, map_X, affGen,
      Fin.cons_zero, map_one, one_mul]
  · have h : homMap K r (X k.succ) = X (Sum.inl ()) * X (Sum.inr k) := by
      rw [show (X k.succ : MvPolynomial (Fin (r + 1)) K) = monomial (Finsupp.single k.succ 1) 1 from rfl,
        homMap_monomial, homExp_single_succ, hX, hX, monomial_mul, one_mul]
    simp only [coneAff, RingHom.comp_apply, h, fieldMap, RingEquiv.toRingHom_eq_coe,
      AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_coe, map_mul, sumAlgEquiv_X_inl,
      sumAlgEquiv_X_inr, map_X, map_C, affGen, Fin.cons_succ]
    ring
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
