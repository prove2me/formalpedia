-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_tens_coeff_b71da958868c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:46:17.805806+00:00
-- url     : https://prove2.me/submissions/b3147a82-0862-4eb2-8c10-3ea09ce6979d

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeD

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
open MonoidAlgebra
variable {k : Type} [Field k] {I : Type} [Fintype I] {G : I → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution (x : ∀ i, MonoidAlgebra k (G i)) (g : ∀ i, G i) :
    (tens x).coeff g = ∏ i, (x i).coeff (g i) := rfl
end Formalism.BasicNotions.Examples₂.NZ
