-- Prove2me | solution 1 for ReciprocityTheory.PGsh.exists_pflat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:00:01.173687+00:00
-- url     : https://prove2.me/submissions/982508c5-0add-424d-968f-58bbc323fba7

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursionStatement
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsPrimitiveRoot
import Theorems.Thm_ReciprocityTheory_PGsh_untilt_ofRoots
import Theorems.Thm_ReciprocityTheory_PGsh_exists_root

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
theorem _root_.solution (hv : v.Integers O) : ∃ pflat : PreTilt O p, pflat.untilt = (p : O) := by
  choose r hr using exists_root (p := p) C v O hv
  exact ⟨ofRoots (rootSeq O r p) (fun n => hr _), untilt_ofRoots _ _⟩
end ReciprocityTheory.PGsh
