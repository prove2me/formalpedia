-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_stdH_span_4803d385f5ba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:32:42.208886+00:00
-- url     : https://prove2.me/submissions/8f18f544-db48-4424-b6c6-afa9338b4030

import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_LocalRingCardinality_DataForms
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZRowA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open NumberField IsDedekindDomain Formalism.BasicNotions
variable (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ)
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution : Submodule.span K ((stdH K n).L : Set (stdH K n).V) = ⊤ := by
  show Submodule.span K ((Submodule.span (𝓞 K) (Set.range (Pi.basisFun K (Fin n))) :
    Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K)) = ⊤
  rw [Submodule.span_span_of_tower]
  exact (Pi.basisFun K (Fin n)).span_eq
end Formalism.BasicNotions.Examples₂.NZ
