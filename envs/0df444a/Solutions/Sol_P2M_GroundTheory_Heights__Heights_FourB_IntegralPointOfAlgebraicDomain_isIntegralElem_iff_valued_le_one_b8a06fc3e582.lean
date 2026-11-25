-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_IntegralPointOfAlgebraicDomain_isIntegralElem_iff_valued_le_one_b8a06fc3e582
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:52:00.352622+00:00
-- url     : https://prove2.me/submissions/20903492-2646-4ba3-854a-c7175f15f942

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsIntegralPointAlgebraic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_NormLeOneIffIsIntegralElemOfEquiv
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PIntegralPointOfAlgebraicDomain
import Theorems.Thm_GroundTheory_Global_mem_valuationInteger_iff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_isIntegralElem_comp_ringEquiv_6375cdd6f877


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
noncomputable section
open GroundTheory.Heights₂.Heights.FourB.IntegralPointOfAlgebraicDomain
open GroundTheory.Global GroundTheory.Global.AdicLiesOver
variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)) [w.asIdeal.LiesOver v.asIdeal]
namespace GroundTheory.Heights₂.Heights.FourB.IntegralPointOfAlgebraicDomain
theorem _root_.solution (z : w.adicCompletion K) :
    (completionIntegersTo F v (w.adicCompletion K)).IsIntegralElem z ↔ Valued.v z ≤ 1 := by
  let φ : v.adicCompletionIntegers F ≃+* 𝒪[v.adicCompletion F] :=
    RingEquiv.subringCongr (Subring.ext fun x ↦ (mem_valuationInteger_iff v x).symm)
  have h : completionIntegersTo F v (w.adicCompletion K) =
      (algebraMap 𝒪[v.adicCompletion F] (w.adicCompletion K)).comp (φ : _ →+* _) := rfl
  rw [h, GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB.isIntegralElem_comp_ringEquiv]
  change IsIntegral 𝒪[v.adicCompletion F] z ↔ _
  rw [← mem_adicCompletionIntegers, ← mem_valuationInteger_iff]
  exact ⟨mem_integer_of_isIntegral v w, isIntegral_of_mem_integer v w⟩
end GroundTheory.Heights₂.Heights.FourB.IntegralPointOfAlgebraicDomain
