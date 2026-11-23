-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_one_lt_pow_g_0b14e5602731
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:54:33.343725+00:00
-- url     : https://prove2.me/submissions/99fdc405-36d5-46bc-844e-2e6eac2b3aa8

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
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution {d : ℕ} (hd : 1 ≤ d) : 2 ≤ g ^ d := by
  calc 2 ≤ g := hg.out.two_le
    _ ≤ g ^ d := Nat.le_self_pow (by omega) g
end Formalism.BasicNotions.Examples₂.NZ
