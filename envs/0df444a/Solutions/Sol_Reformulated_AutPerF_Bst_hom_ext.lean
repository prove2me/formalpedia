-- Prove2me | solution 1 for Reformulated.AutPerF.Bst.hom_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T16:59:14.029144+00:00
-- url     : https://prove2.me/submissions/196f10a0-e33d-4e50-b3ea-2b1be93368df

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero

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
variable (p : ℕ) [Fact p.Prime]
variable (R : Type u) [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
open Reformulated.AutPerF.Bst
variable {p R}
namespace Reformulated.AutPerF.Bst
theorem _root_.solution {B : Type*} [CommRing B] {f g : Bst p R →+* B}
    (h₁ : ∀ x : Bcris p R, f (algebraMap _ _ x) = g (algebraMap _ _ x))
    (h₂ : ∀ ϖ, f (logFlat ϖ) = g (logFlat ϖ)) : f = g :=
  Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext h₁ h₂)
end Reformulated.AutPerF.Bst
