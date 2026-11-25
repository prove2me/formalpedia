-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LevelValuationRings_frob_iter_a51111b6d48b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:31:01.980904+00:00
-- url     : https://prove2.me/submissions/f433a029-8672-4f85-b967-98ea1e22229a

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatRing
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatSetting

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LevelValuationRings
open Formalism.MainNotions.G QuadraticAlgebra
variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ)
namespace Formalism.BasicNotions.Examples₂.LevelValuationRings
theorem _root_.solution (hn : n ≠ 0) (x : Wn p n) : (WittVector.frobenius^[n]) x = x := by
  ext i
  rw [WittVector.iterate_frobenius_coeff]
  have : Fintype (GaloisField p n) := Fintype.ofFinite _
  have h := FiniteField.pow_card (x.coeff i)
  rwa [← Nat.card_eq_fintype_card, GaloisField.card p n hn] at h
end Formalism.BasicNotions.Examples₂.LevelValuationRings
