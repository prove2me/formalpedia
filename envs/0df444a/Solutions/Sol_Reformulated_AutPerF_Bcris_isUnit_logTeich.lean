-- Prove2me | solution 1 for Reformulated.AutPerF.Bcris.isUnit_logTeich
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:28:26.707709+00:00
-- url     : https://prove2.me/submissions/c210ff1c-3759-4919-b8e1-7d0d50ed1f31

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_EqZeroOfPMulEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal
open scoped Nat
open Reformulated Reformulated.AutPerF
universe u v w
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
open Reformulated.AutPerF.Bcris
namespace Reformulated.AutPerF.Bcris
theorem _root_.solution {ε : tateModule p R} (h : IsPrimitive ε) : IsUnit (logTeich ε) :=
  IsLocalization.map_units (M := BcrisPlus.periods p R) (Bcris p R)
    ⟨_, Submonoid.subset_closure ⟨ε, h, rfl⟩⟩
end Reformulated.AutPerF.Bcris
