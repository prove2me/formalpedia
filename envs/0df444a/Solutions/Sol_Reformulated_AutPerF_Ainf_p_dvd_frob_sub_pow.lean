-- Prove2me | solution 1 for Reformulated.AutPerF.Ainf.p_dvd_frob_sub_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:29:53.359237+00:00
-- url     : https://prove2.me/submissions/46f0c10a-e7aa-4fa0-9b58-b1a030ae9426

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap

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
open Reformulated Reformulated.AutPerF
universe u v w
variable (p : ℕ) [Fact p.Prime]
variable (R : Type u) [CommRing R] [Fact ¬IsUnit (p : R)]
variable (S : Type v) [CommRing S] [Fact ¬IsUnit (p : S)]
variable (U : Type w) [CommRing U] [Fact ¬IsUnit (p : U)]
variable {R S U}
open Reformulated.AutPerF.Ainf
variable {p}
namespace Reformulated.AutPerF.Ainf
theorem _root_.solution (x : Ainf p R) : (p : Ainf p R) ∣ frob p R x - x ^ p := by
  rw [← Ideal.mem_span_singleton, ← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, map_pow,
    frob_eq_map]
  simp [frobenius_def]
end Reformulated.AutPerF.Ainf
