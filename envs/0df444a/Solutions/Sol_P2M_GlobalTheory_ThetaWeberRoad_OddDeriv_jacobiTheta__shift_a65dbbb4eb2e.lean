-- Prove2me | solution 1 for P2M_GlobalTheory_ThetaWeberRoad_OddDeriv_jacobiTheta__shift_a65dbbb4eb2e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:38:15.21079+00:00
-- url     : https://prove2.me/submissions/cdd793eb-2045-4b9f-b6cf-cdc725e42971

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HasDerivAtOddJacobiThetaZeroEtaCube
import Theorems.Thm_GlobalTheory_ThetaWeberRoad_OddDeriv_hasProd_tailProd
import Theorems.Thm_GlobalTheory_ThetaWeberRoad_OddDeriv_tpFactor_shift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open UpperHalfPlane hiding I
open scoped Real
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.ThetaWeberRoad GlobalTheory.ThetaWeberRoad.OddDeriv
namespace GlobalTheory.ThetaWeberRoad.OddDeriv
theorem _root_.solution (hT : TripleProduct) (τ : ℍ) (z : ℂ) :
    jacobiTheta₂ (z + ((τ : ℂ) + 1) / 2) τ =
      tailProd τ 1 * tailProd τ (cexp (2 * π * I * z)) *
        ((1 - cexp (-(2 * π * I * z))) * tailProd τ (cexp (-(2 * π * I * z)))) := by
  have hA := hasProd_tailProd τ 1
  have hB := hasProd_tailProd τ (cexp (2 * π * I * z))
  have h0 := hasProd_tailProd τ (cexp (-(2 * π * I * z)))
  have h1 : HasProd (fun n : ℕ => 1 - cexp (2 * π * I * ((n + 1 : ℕ) : ℂ) * (τ : ℂ)) *
      cexp (-(2 * π * I * z))) (tailProd τ (cexp (-(2 * π * I * z)))) := by
    convert h0 using 2 with n
    rw [ModularForm.eta_q_eq_cexp]; push_cast; ring_nf
  have hC := HasProd.zero_mul
    (f := fun n : ℕ => 1 - cexp (2 * π * I * (n : ℂ) * (τ : ℂ)) * cexp (-(2 * π * I * z))) h1
  have e0 : (1 - cexp (2 * π * I * ((0 : ℕ) : ℂ) * (τ : ℂ)) * cexp (-(2 * π * I * z))) =
      1 - cexp (-(2 * π * I * z)) := by simp
  rw [e0] at hC
  have hAll := (hA.mul hB).mul hC
  refine (hT τ (z + ((τ : ℂ) + 1) / 2)).unique ?_
  convert hAll using 1
  funext n
  rw [tpFactor_shift]
end GlobalTheory.ThetaWeberRoad.OddDeriv
