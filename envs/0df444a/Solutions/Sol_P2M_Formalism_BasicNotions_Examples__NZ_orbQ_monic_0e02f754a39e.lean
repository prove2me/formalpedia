-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_orbQ_monic_0e02f754a39e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:48:00.371746+00:00
-- url     : https://prove2.me/submissions/00708d41-3ac5-4479-949f-aa9eefc27a09

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeA
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeB

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
open Polynomial Formalism.CyclotomicNorms Formalism.CyclotomicNorms.CycleTypeFiniteOrder
variable {g : ℕ} [hg : Fact g.Prime]
variable {d : ℕ} (hd : 1 ≤ d) (u : (Fbar g)ˣ) (hu : orderOf u = g ^ d - 1)
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution : (orbQ d u).Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
end Formalism.BasicNotions.Examples₂.NZ
