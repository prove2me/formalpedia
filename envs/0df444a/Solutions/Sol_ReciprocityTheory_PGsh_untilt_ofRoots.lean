-- Prove2me | solution 1 for ReciprocityTheory.PGsh.untilt_ofRoots
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:43:47.098142+00:00
-- url     : https://prove2.me/submissions/0e9b46f4-b9dc-41b4-8443-917ae375cb2b

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursionStatement
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsPrimitiveRoot
import Theorems.Thm_ReciprocityTheory_PGsh_untilt_eq_of_coeff
import Theorems.Thm_ReciprocityTheory_PGsh_coeff_ofRoots

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
theorem _root_.solution (f : ℕ → O) (hf : ∀ n, f (n + 1) ^ p = f n) :
    (ofRoots f hf).untilt = f 0 :=
  untilt_eq_of_coeff _ f hf (coeff_ofRoots f hf)
end ReciprocityTheory.PGsh
