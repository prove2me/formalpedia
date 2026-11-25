-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_pow_g_add_980569a93c39
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:32:36.510219+00:00
-- url     : https://prove2.me/submissions/e7eb2203-41b9-4ba3-912c-ba356f9ae980

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeA
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeB
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_pow_gd_5940a6f3a10f

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
include hd hu
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution (j : ℕ) : u ^ (g ^ (j + d)) = u ^ (g ^ j) := by
  rw [pow_add, mul_comm, pow_mul, pow_gd hd u hu]
end Formalism.BasicNotions.Examples₂.NZ
