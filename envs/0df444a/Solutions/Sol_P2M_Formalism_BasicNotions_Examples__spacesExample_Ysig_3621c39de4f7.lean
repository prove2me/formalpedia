-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__spacesExample_Ysig_3621c39de4f7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:32:14.906805+00:00
-- url     : https://prove2.me/submissions/d040bda2-c3c4-41c1-8a2d-627a03b76535

import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExampleRanksRankComplement
import Definitions.Def_Formalism_FockGram_SymGramPosSemidef
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stdform
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Spaces

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
open NumberField
open scoped TensorProduct
open IsDedekindDomain
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x))
  (cm : CMData F E) (T : ℕ) (hT : T.Prime) (pz : E) (hpz : star pz * pz = T)
  (hy : ∃ y : E ⊗[F] FiniteAdeleRing (𝓞 F) F,
    Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) y * y = -1)
namespace Formalism.BasicNotions.Examples₂
theorem _root_.solution : ∀ j, j ≤ R0.m → ∀ τ : E →+* ℂ,
    ((spacesExample hstar cm T hT pz hpz hy).Y j).sig τ = sigYD R0 j := by
  intro j hj τ
  have : R0.m = 2 := rfl
  obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  · rfl
  · rfl
  · rfl
end Formalism.BasicNotions.Examples₂
