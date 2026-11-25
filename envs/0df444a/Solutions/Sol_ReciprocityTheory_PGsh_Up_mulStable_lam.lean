-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.mulStable_lam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:20:22.041709+00:00
-- url     : https://prove2.me/submissions/1fdd8cf8-a1a2-4d86-a8ad-c44c6cef4f32

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_ProdEraseUpdate
import Theorems.Thm_ReciprocityTheory_PGsh_Up_key_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
variable {p : ℕ} [hp : Fact p.Prime] {k : Type} [Field k] [CharP k p] {ι : Type} [Fintype ι]
  [DecidableEq ι]
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (Cm Cinv : Matrix ι ι k) (h : Cinv * Cm = 1) (l : ι) :
    MulStable (Submodule.span k (Set.range (monF (p := p) Cm))) (lam Cm l) := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨α, rfl⟩ := hg
    exact key_step Cm Cinv h _ α rfl l
  | zero => simpa using Submodule.zero_mem _
  | add f g _ _ hf hg => rw [mul_add]; exact Submodule.add_mem _ hf hg
  | smul a f _ hf => rw [mul_smul_comm]; exact Submodule.smul_mem _ a hf
end ReciprocityTheory.PGsh.Up
