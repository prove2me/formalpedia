-- Prove2me | solution 1 for ReciprocityTheory.PGsh.untilt_symm_ofRoots
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:52:14.297719+00:00
-- url     : https://prove2.me/submissions/fc29a874-cf44-42ef-9747-f78ecf0d241a

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursionStatement
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsPrimitiveRoot
import Theorems.Thm_ReciprocityTheory_PGsh_untilt_eq_of_coeff

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
    ((_root_.frobeniusEquiv (PreTilt O p) p).symm (ofRoots f hf)).untilt = f 1 := by
  apply untilt_eq_of_coeff _ (fun n => f (n + 1)) (fun n => hf (n + 1))
  intro n
  rw [← PreTilt.coeff_def, PreTilt.coeff_frobeniusEquiv_symm, PreTilt.coeff_def]
  rfl
end ReciprocityTheory.PGsh
