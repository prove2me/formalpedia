-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_pow_gd_5940a6f3a10f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:23.457828+00:00
-- url     : https://prove2.me/submissions/5f98b5c4-14fb-41b9-b123-81e1334da14d

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeA
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeB
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_one_lt_pow_g_0b14e5602731

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
theorem _root_.solution : u ^ (g ^ d) = u := by
  have := one_lt_pow_g (g := g) hd
  rw [show g ^ d = g ^ d - 1 + 1 by omega, pow_succ, ← hu, pow_orderOf_eq_one, one_mul]
end Formalism.BasicNotions.Examples₂.NZ
