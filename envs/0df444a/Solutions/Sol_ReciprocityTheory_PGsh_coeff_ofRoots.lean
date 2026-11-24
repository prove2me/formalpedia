-- Prove2me | solution 1 for ReciprocityTheory.PGsh.coeff_ofRoots
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:27:45.653084+00:00
-- url     : https://prove2.me/submissions/4e36631f-b448-43f3-85e1-9033aa271d4a

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursionStatement
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsPrimitiveRoot

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
open ReciprocityTheory ReciprocityTheory.PGsh
variable {p : ℕ} [hp : Fact p.Prime]
variable {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
namespace ReciprocityTheory.PGsh
theorem _root_.solution (f : ℕ → O) (hf : ∀ n, f (n + 1) ^ p = f n) (n : ℕ) :
    Perfection.coeff (ModP O p) p n (ofRoots f hf) = Ideal.Quotient.mk (span {(p : O)}) (f n) :=
  rfl
end ReciprocityTheory.PGsh
