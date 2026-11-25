-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_mem_rootsBar_P_9cb9ba47d11d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:39:55.542967+00:00
-- url     : https://prove2.me/submissions/287b6a24-140c-4d4b-a183-70437c7c8670

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeA
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeB
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_mem_roots_orbQ_fb5a8218368f

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
variable {P : (ZMod g)[X]} (hP : P.map (algebraMap (ZMod g) (Fbar g)) = orbQ d u)
include hP
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution {y : Fbar g} : y ∈ rootsBar P ↔ ∃ i < d, y = (u : Fbar g) ^ (g ^ i) := by
  rw [rootsBar, hP]
  exact mem_roots_orbQ u
end Formalism.BasicNotions.Examples₂.NZ
