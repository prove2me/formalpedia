-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__spaces_signature_eq_b068484ac5cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:23:24.993833+00:00
-- url     : https://prove2.me/submissions/47bd92ff-4cd6-4500-be8c-6469ed2ab431

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Spaces
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_BaseFormAnisotropicOrthogonalSingle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
open NumberField IsDedekindDomain
open scoped TensorProduct
variable (R : Ranks) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E]
  (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x))
  (cm : CMData F E) (T : ℕ) (hT : T.Prime) (pz : E) (hpz : star pz * pz = T)
  (hy : ∃ y : E ⊗[F] FiniteAdeleRing (𝓞 F) F,
    Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) y * y = -1)
namespace Formalism.BasicNotions.Examples₂
theorem _root_.solution : ∀ j, j ≤ R.m → ∀ τ : E →+* ℂ,
    ((spacesOfRanks R hstar cm T hT pz hpz hy).Y j).sig τ = sigYD R j := fun _ _ _ => rfl
end Formalism.BasicNotions.Examples₂
