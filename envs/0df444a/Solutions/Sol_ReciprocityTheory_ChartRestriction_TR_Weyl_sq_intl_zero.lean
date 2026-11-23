-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.TR.Weyl.sq_intl_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:29:39.812801+00:00
-- url     : https://prove2.me/submissions/52f1d175-2c5b-48bb-b4bb-54cc6d9ebb9a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_AltBranchStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_SqCharA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.TR ReciprocityTheory.ChartRestriction.TR.Weyl
namespace ReciprocityTheory.ChartRestriction.TR.Weyl
theorem _root_.solution {k : ℕ} (f : Fin k → Fin k → ℕ) (hf : sq_Intl f) :
    ∀ (tv : ℕ) (t : Fin k), t.val = tv → ∀ a : Fin k, a.val < tv → f a t = 0 := by
  intro tv
  induction tv with
  | zero => intro t _ a ha; omega
  | succ tv ih =>
    intro t ht a ha
    have hl : tv < k := by have := t.isLt; omega
    have h1 := hf ⟨tv, hl⟩ t (by simp [ht]) a
    have h2 : (∑ b : Fin k with b < a, f b ⟨tv, hl⟩) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      rw [Finset.mem_filter] at hb
      exact ih ⟨tv, hl⟩ rfl b (by have : b.val < a.val := hb.2; omega)
    rw [h2] at h1
    have h3 : f a t ≤ ∑ b : Fin k with b ≤ a, f b t :=
      Finset.single_le_sum (f := fun b => f b t) (fun _ _ => Nat.zero_le _) (by simp)
    omega
end ReciprocityTheory.ChartRestriction.TR.Weyl
