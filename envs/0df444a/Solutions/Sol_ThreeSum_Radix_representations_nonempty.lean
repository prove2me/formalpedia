-- Prove2me | solution 1 for ThreeSum.Radix.representations_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:04:29.79721+00:00
-- url     : https://prove2.me/submissions/0fc46ecb-7283-4944-a867-a87b5eb07ec2

import Mathlib.Data.Int.ModEq
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega
import Aesop
import Definitions.Def_Submission_ThreeSum_Radix

set_option autoImplicit false
open ThreeSum ThreeSum.Radix
open Finset
open scoped BigOperators
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
namespace ThreeSum.Radix
theorem _root_.solution (p : ℤ) (left right : Ω → ℤ)
    (hcover : ∀ a b, (localFiber p left right a b).Nonempty)
    (j : ℕ) (a b : ℤ) : (representations p left right j a b).Nonempty := by
  induction j generalizing a b with
  | zero => exact singleton_nonempty _
  | succ j ih =>
    obtain ⟨ω, hω⟩ := hcover a b
    obtain ⟨xs, hxs⟩ := ih ((a - left ω) / p) ((b - right ω) / p)
    refine ⟨ω :: xs, ?_⟩
    exact mem_biUnion.mpr ⟨ω, hω, mem_image.mpr ⟨xs, hxs, rfl⟩⟩
end ThreeSum.Radix
