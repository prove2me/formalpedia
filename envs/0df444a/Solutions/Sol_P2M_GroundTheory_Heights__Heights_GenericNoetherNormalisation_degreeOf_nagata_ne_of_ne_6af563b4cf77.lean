-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_degreeOf_nagata_ne_of_ne_6af563b4cf77
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:11:35.8123+00:00
-- url     : https://prove2.me/submissions/61e0ee29-3f24-4042-8db7-902154606ae6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericNoetherNormalisation
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SumRMulNe
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ProofSimp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericNoetherNormalisation
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_sum_r_mul_ne_98623272d7f8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_degreeOf_zero_nagata_af52885d2172

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
open Polynomial MvPolynomial Ideal Nat RingHom List
open GroundTheory.Heights₂.Heights.GenericNoetherNormalisation
variable {A : Type*} [CommRing A] [IsDomain A] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) A)
variable (v w : Fin (n + 1) →₀ ℕ)
local notation3 "up" => 2 + f.totalDegree
local notation3 "r" => fun (i : Fin (n + 1)) ↦ up ^ i.1
namespace GroundTheory.Heights₂.Heights.GenericNoetherNormalisation
theorem _root_.solution (hv : v ∈ f.support) (hw : w ∈ f.support) (ne : v ≠ w) :
    (nagataEquiv f <| monomial v <| coeff v f).degreeOf 0 ≠
    (nagataEquiv f <| monomial w <| coeff w f).degreeOf 0 := by
  rw [degreeOf_zero_nagata _ _ <| mem_support_iff.mp hv,
    degreeOf_zero_nagata _ _ <| mem_support_iff.mp hw]
  refine sum_r_mul_ne f v w (fun i ↦ ?_) (fun i ↦ ?_) ne <;>
  exact lt_of_le_of_lt ((monomial_le_degreeOf i ‹_›).trans (degreeOf_le_totalDegree f i))
    (by lia)
end GroundTheory.Heights₂.Heights.GenericNoetherNormalisation
