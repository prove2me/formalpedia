-- Prove2me | solution 1 for ReciprocityTheory.PGsh.exists_eps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:03:31.724688+00:00
-- url     : https://prove2.me/submissions/0e965ffc-0f5f-4348-b766-304adab16f31

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursionStatement
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsPrimitiveRoot
import Theorems.Thm_ReciprocityTheory_PGsh_untilt_symm_ofRoots
import Theorems.Thm_ReciprocityTheory_PGsh_exists_root
import Theorems.Thm_ReciprocityTheory_PGsh_exists_primitiveRoot

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
variable (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal)
  (O : Type) [CommRing O] [Algebra O C]
variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
namespace ReciprocityTheory.PGsh
theorem _root_.solution [CharZero C] (hv : v.Integers O) :
    ∃ ε : PreTilt O p,
      IsPrimitiveRoot (((_root_.frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p := by
  choose r hr using exists_root (p := p) C v O hv
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot (p := p) C v O hv
  let f : ℕ → O := fun n => Nat.casesOn n 1 (fun m => rootSeq O r ζ m)
  have hf : ∀ n, f (n + 1) ^ p = f n := by
    intro n
    cases n with
    | zero => exact hζ.pow_eq_one
    | succ m => exact hr _
  refine ⟨ofRoots f hf, ?_⟩
  rw [untilt_symm_ofRoots]
  exact hζ
end ReciprocityTheory.PGsh
