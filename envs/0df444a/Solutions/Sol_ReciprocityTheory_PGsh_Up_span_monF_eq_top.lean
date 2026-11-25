-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.span_monF_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:29:01.430587+00:00
-- url     : https://prove2.me/submissions/4c1d5c4f-a47d-4e0b-8d58-b81788a25197

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_ProdEraseUpdate
import Theorems.Thm_ReciprocityTheory_PGsh_Up_xc_eq
import Theorems.Thm_ReciprocityTheory_PGsh_Up_monF_zero
import Theorems.Thm_ReciprocityTheory_PGsh_Up_mulStable_lam
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_add
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_mul
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_const
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_sum
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_prod
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_pow
import Theorems.Thm_ReciprocityTheory_PGsh_Up_delta_apply

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
theorem _root_.solution (Cm Cinv : Matrix ι ι k) (h : Cinv * Cm = 1) :
    Submodule.span k (Set.range (monF (p := p) Cm)) = ⊤ := by
  have hxc : ∀ i, MulStable (Submodule.span k (Set.range (monF (p := p) Cm))) (fun x => xc k i x) := by
    intro i
    have e : (fun x => xc k i x) = ∑ m, (fun _ => Cinv i m) * lam Cm m := by
      funext x
      rw [xc_eq Cm Cinv h i x]
      simp [Finset.sum_apply]
    rw [e]
    exact MulStable.sum (fun m _ => (MulStable.const _ _).mul (mulStable_lam Cm Cinv h m))
  have hdelta : ∀ y, MulStable (Submodule.span k (Set.range (monF (p := p) Cm))) (delta k y) := by
    intro y
    unfold delta
    exact MulStable.prod (fun i _ => (MulStable.const _ 1).add
      ((MulStable.const _ (-1)).mul (((hxc i).add (MulStable.const _ _)).pow _)))
  have h1 : (1 : (ι → ZMod p) → k) ∈ Submodule.span k (Set.range (monF (p := p) Cm)) := by
    rw [← monF_zero Cm]
    exact Submodule.subset_span ⟨0, rfl⟩
  have hmem : ∀ y, delta k y ∈ Submodule.span k (Set.range (monF (p := p) Cm)) := fun y => by
    simpa using hdelta y 1 h1
  rw [eq_top_iff]
  intro f _
  have e : f = ∑ y, f y • delta k y := by
    funext x
    simp [Finset.sum_apply, delta_apply]
  rw [e]
  exact Submodule.sum_mem _ (fun y _ => Submodule.smul_mem _ _ (hmem y))
end ReciprocityTheory.PGsh.Up
