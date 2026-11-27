-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.char_ind
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:57:05.347958+00:00
-- url     : https://prove2.me/submissions/d52e781e-b8bf-4cf2-b30b-3048d24398ad

import Definitions.Def_ReciprocityTheory_DualLattices_DetIntegralNonneg
import Definitions.Def_ReciprocityTheory_DualLattices_UpBrChar
import Theorems.Thm_ReciprocityTheory_PGsh_Up_char_step
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt



set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
variable {R : Type} [CommRing R] [IsDomain R]
variable {C : Type} [Field C] {v : Valuation C NNReal} [Algebra R C]
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (hv : v.Integers R) {g N : ℕ} (M : Matrix (Fin g) (Fin N) R) (c : R) (hc : c ≠ 0)
    (hspan : ∀ s (hs : s ≤ g), ∀ w : Fin s → R, c • w ∈ omTr M s hs) :
    ∀ s (hs : s ≤ g), ∃ ι : Fin s → Fin N, Function.Injective ι ∧ ∀ s' (hs' : s' ≤ s),
      Submodule.span R (Set.range fun b : Fin s' => fun a : Fin s' =>
        M (Fin.castLE (hs'.trans hs) a) (ι (Fin.castLE hs' b))) = omTr M s' (hs'.trans hs) := by
  intro s
  induction s with
  | zero =>
    intro _
    refine ⟨fun a => a.elim0, fun a _ _ => a.elim0, fun s' hs' => ?_⟩
    obtain rfl : s' = 0 := Nat.le_zero.mp hs'
    ext w
    have hw : w = 0 := Subsingleton.elim _ _
    subst hw
    exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩
  | succ s ih =>
    intro hs
    obtain ⟨ι, hinj, hι⟩ := ih (Nat.le_of_succ_le hs)
    obtain ⟨b, hb, hb2⟩ := char_step hv M c hc hspan s hs ι (hι s le_rfl)
    refine ⟨Fin.snoc (α := fun _ => Fin N) ι b, ?_, fun s' hs' => ?_⟩
    · intro i j hij
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => rfl
        | cast j =>
          simp only [Fin.snoc_last, Fin.snoc_castSucc] at hij
          exact (hb ⟨j, hij.symm⟩).elim
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          simp only [Fin.snoc_last, Fin.snoc_castSucc] at hij
          exact (hb ⟨i, hij⟩).elim
        | cast j =>
          simp only [Fin.snoc_castSucc] at hij
          rw [hinj hij]
    · rcases Nat.lt_or_ge s' (s + 1) with hlt | hge
      · have hle : s' ≤ s := Nat.lt_succ_iff.mp hlt
        refine Eq.trans ?_ (hι s' hle)
        congr 2
        funext b' a
        have e : (Fin.castLE hs' b' : Fin (s + 1)) = Fin.castSucc (Fin.castLE hle b') := Fin.ext rfl
        rw [e, Fin.snoc_castSucc]
      · obtain rfl : s' = s + 1 := le_antisymm hs' hge
        exact hb2
end ReciprocityTheory.PGsh.Up
