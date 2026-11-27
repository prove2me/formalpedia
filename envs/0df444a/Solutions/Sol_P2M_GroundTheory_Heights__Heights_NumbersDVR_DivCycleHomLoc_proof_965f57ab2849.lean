-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_DivCycleHomLoc_proof_965f57ab2849
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:05:52.732312+00:00
-- url     : https://prove2.me/submissions/a5cadd01-88fa-41ba-9686-b1db10fb6b64

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpFibreDegreeCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleHomLocLaurent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PCutByForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPolynomialLocalizedLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleHomLoc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_multAt_eq_length_locC_ec2a4d76e286
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_CutByForm_proof_b44260dcf444
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_length_quotient_incAC_b70758caeff4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MinimalPrimeMultiHomog_proof_00f169244e2b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MultAtPrimeAtMinimal_proof_af70a5a37a53
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomogIdeal_sup_span_of_form_8aa08999bb53


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial HomLocLaurent
noncomputable section
universe u
set_option linter.style.haveILetI false
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace DivCycleHomLoc
theorem _root_.solution (h : HomLocRingLocal.Statement.{u}) : DivCycleHomLoc.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ P hP c x hx hxP W hW hWrel g hg hgW hz
  haveI := hP.isPrime
  haveI : W.IsPrime := hW.1.1
  have hPW : P ≤ W := le_trans le_sup_left hW.1.2
  have hWh : IsMultiHomogIdeal W := MinimalPrimeMultiHomog.proof O K ι _ W
    (isMultiHomogIdeal_sup_span_of_form hP.multiHomog hx) hW
  haveI : IsLocalRing (homLocRing P W) := (h O K ι P hP c x hx hxP W hW hWrel).1
  choose T hT using hWrel
  rw [← length_quotient_incAC T hPW hT hP.multiHomog hWh, multAt_eq_length_locC hPW x]
  letI := (algQC hPW).toAlgebra
  haveI := wbar_isPrime hPW
  haveI := locC_isLocalization hPW
  have hgu : IsUnit (algQC hPW (Ideal.Quotient.mk P g)) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff (locC hPW) (W.map (Ideal.Quotient.mk P)) _).mpr
      fun h => hgW ((Ideal.mem_quotient_iff_mem hPW).mp h)
  have hxz : algQC hPW (Ideal.Quotient.mk P x) =
      incAC hPW ⟨_, hz⟩ * algQC hPW (Ideal.Quotient.mk P g) := by
    apply Subtype.ext
    change fr P x = fr P x / fr P g * fr P g
    rw [div_mul_cancel₀ _ (fr_ne_zero fun h => hgW (hPW h))]
  rw [hxz, Ideal.span_singleton_mul_right_unit hgu]
end DivCycleHomLoc
end GroundTheory.Heights₂.Heights.NumbersDVR
