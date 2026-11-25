-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_multAt_map_relabel_58c8783fc9c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:55:53.2438+00:00
-- url     : https://prove2.me/submissions/ab9a7500-f1fd-4415-91d5-4bc948554cbd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsNefRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isPrime_map_ringEquiv_iff_9444e6a7af2b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_length_localizedModule_quotient_map_06587b043cc3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
set_option linter.unusedSectionVars false
variable {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
  [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] (ε : K ≃ K') (h : ∀ k, ι k = ι' (ε k))
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (J V : Ideal (MRing ι)) :
    multAt (J.map (relabelRingEquiv ε h)) (V.map (relabelRingEquiv ε h)) = multAt J V := by
  unfold multAt
  by_cases hV : V.IsPrime
  · have hV' : (V.map (relabelRingEquiv ε h)).IsPrime :=
      (isPrime_map_ringEquiv_iff (relabelRingEquiv ε h) V).2 hV
    rw [dif_pos hV, dif_pos hV']
    exact congrArg ENat.toNat (length_localizedModule_quotient_map (relabelRingEquiv ε h) J V)
  · have hV' : ¬ (V.map (relabelRingEquiv ε h)).IsPrime :=
      fun h' => hV ((isPrime_map_ringEquiv_iff (relabelRingEquiv ε h) V).1 h')
    rw [dif_neg hV, dif_neg hV']
end GroundTheory.Heights₂.Heights
