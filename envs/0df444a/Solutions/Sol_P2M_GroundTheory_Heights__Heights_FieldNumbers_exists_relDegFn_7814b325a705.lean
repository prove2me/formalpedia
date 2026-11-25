-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_relDegFn_7814b325a705
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:09:21.245605+00:00
-- url     : https://prove2.me/submissions/eb400863-9a94-43d0-8826-0ba72feaf927

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalLengthSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {K K' : Type} [DecidableEq K] [DecidableEq K'] {F : Type*} [Field F]
  (j : K ↪ K') {ι' : K' → Type}
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution :
    ∃ d : Ideal (MRing ι' F) → ℕ, ∀ W' (hW' : IsMultiProjPrime W'),
      haveI := hW'.isPrime
      d W' = relDeg j W' := by
  classical
  exact ⟨fun W' => if hp : W'.IsPrime then haveI := hp; relDeg j W' else 0,
    fun W' hW' => dif_pos hW'.isPrime⟩
end GroundTheory.Heights₂.Heights.FieldNumbers
