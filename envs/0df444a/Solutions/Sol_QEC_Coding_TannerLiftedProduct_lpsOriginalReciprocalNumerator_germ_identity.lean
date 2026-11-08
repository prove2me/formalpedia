-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalNumerator_germ_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:37:36.195272+00:00
-- url     : https://prove2.me/submissions/4a784b7d-7219-4b6b-b812-98723a574824

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspNormalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalE4Equation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalNumerator
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalHolomorphic_delta_j_power
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalReciprocalClearedRepresentative_restriction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizedFilledFunction_restriction


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
local notation "R" => LPSOriginalHolomorphicRing
local notation "M" => LPSOriginalMeromorphicGermRing UpperHalfPlane.upperHalfPlaneSet
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F)
    (hc : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      ∀ c, 0 ≤ meromorphicOrderAt
        (F ∘ (chartAt ℂ (Sum.inr c : LPSOriginalFilledCurve N)).symm)
        (chartAt ℂ (Sum.inr c : LPSOriginalFilledCurve N) (Sum.inr c)))
    (k : ℕ)
    (hi : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      ∀ x : MulAction.orbitRel.Quotient
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ,
        0 ≤ meromorphicOrderAt
          ((lpsOriginalReciprocalClearedRepresentative N hN F hF k).val ∘
            (chartAt ℂ (Sum.inl x : LPSOriginalFilledCurve N)).symm)
          (chartAt ℂ (Sum.inl x : LPSOriginalFilledCurve N) (Sum.inl x))) :
    let A := lpsOriginalReciprocalNumeratorModularForm N hN F hF hc k hi
    lpsOriginalHolomorphicToMeromorphicGerm
      (lpsOriginalLevelFormHolomorphic N k A) =
      lpsOriginalHolomorphicToMeromorphicGerm (lpsOriginalE4PowerHolomorphic k) *
        (lpsOriginalFilledMeromorphicRestriction N hN F hF).val := by
  let G := lpsOriginalReciprocalClearedRepresentative N hN F hF k
  let Gn := lpsOriginalNormalizedFilledFunction N hN G.val
  let hGn := lpsOriginalNormalizedFilledFunction_meromorphic N hN G.val G.property
  let A := lpsOriginalReciprocalNumeratorModularForm N hN F hF hc k hi
  have ha : lpsOriginalHolomorphicToMeromorphicGerm
      (lpsOriginalLevelFormHolomorphic N k A) =
      (lpsOriginalHolomorphicToMeromorphicGerm lpsOriginalDeltaHolomorphic)^k *
        (lpsOriginalFilledMeromorphicRestriction N hN Gn hGn).val := by
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall (fun z => rfl)
  rw [lpsOriginalNormalizedFilledFunction_restriction N hN G.val G.property,
    lpsOriginalReciprocalClearedRepresentative_restriction] at ha
  calc
    _ = (lpsOriginalHolomorphicToMeromorphicGerm lpsOriginalDeltaHolomorphic)^k *
      ((lpsOriginalHolomorphicToMeromorphicGerm lpsOriginalJHolomorphic)^k *
        (lpsOriginalFilledMeromorphicRestriction N hN F hF).val) := ha
    _ = lpsOriginalHolomorphicToMeromorphicGerm
        (lpsOriginalDeltaHolomorphic^k * lpsOriginalJHolomorphic^k) *
        (lpsOriginalFilledMeromorphicRestriction N hN F hF).val := by
      rw [map_mul, map_pow, map_pow, mul_assoc]
    _ = _ := by rw [lpsOriginalHolomorphic_delta_j_power]
end QEC.Coding.TannerLiftedProduct
