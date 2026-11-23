-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_coprime_n_8914bd4d6568
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:57:43.574638+00:00
-- url     : https://prove2.me/submissions/b5186a5b-f58e-45a8-8271-96bb4f43fe9f

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
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution (d : ℕ) (hd : 1 ≤ d) : Nat.Coprime (g ^ d - 1) g := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hg.out]
  intro h
  have h2 : g ∣ g ^ d := dvd_pow_self g (by omega)
  have h3 := Nat.dvd_sub h2 h
  have h4 : g ^ d - (g ^ d - 1) = 1 := by
    have := one_lt_pow_g (g := g) hd
    omega
  rw [h4] at h3
  exact hg.out.one_lt.ne' (Nat.dvd_one.1 h3)
end Formalism.BasicNotions.Examples₂.NZ
