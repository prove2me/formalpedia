-- Prove2me | solution 1 for QuarterSumLadder.exists_char_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:01:22.891617+00:00
-- url     : https://prove2.me/submissions/a5c07481-4519-4344-bd64-71ec73222826

module
public import Definitions.Def_QuarterSumLadder_Prelim
public import Definitions.Def_QuarterSumLadder_Classes
public import Theorems.Thm_QuarterSumLadder_exists_generator
public import Theorems.Thm_QuarterSumLadder_gi_im
public import Theorems.Thm_QuarterSumLadder_gi_re
public import Theorems.Thm_QuarterSumLadder_gi_sq
public import Theorems.Thm_QuarterSumLadder_quartic_apply_generator
attribute [local simp] QuarterSumLadder.gi_im
attribute [local simp] QuarterSumLadder.gi_re



set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ
omit hp8
namespace QuarterSumLadder
theorem _root_.solution {z : GaussianInt} (hz : FourVal z) : ∃ c : ZMod p, c ≠ 0 ∧ χ c = z := by
  obtain ⟨g, -, hg⟩ := exists_generator (p := p)
  have hu := quartic_apply_generator χ hχ hg
  have hg0 : (g : ZMod p) ≠ 0 := g.ne_zero
  have hpow : ∀ k : ℕ, χ ((g : ZMod p) ^ k) = (χ g) ^ k := fun k => map_pow χ _ k
  have key : ∀ k : ℕ, k < 4 → z = (χ g) ^ k → ∃ c : ZMod p, c ≠ 0 ∧ χ c = z :=
    fun k _ h => ⟨(g : ZMod p) ^ k, pow_ne_zero _ hg0, by rw [hpow, h]⟩
  rcases hu with hu | hu <;> rcases hz with rfl | rfl | rfl | rfl
  · exact key 0 (by norm_num) (by simp)
  · exact key 1 (by norm_num) (by rw [hu, pow_one])
  · exact key 2 (by norm_num) (by rw [hu, gi_sq])
  · exact key 3 (by norm_num) (by rw [hu, pow_succ, gi_sq]; ring)
  · exact key 0 (by norm_num) (by simp)
  · exact key 3 (by norm_num) (by rw [hu, pow_succ, neg_sq, gi_sq]; ring)
  · exact key 2 (by norm_num) (by rw [hu, neg_sq, gi_sq])
  · exact key 1 (by norm_num) (by rw [hu, pow_one])
end QuarterSumLadder
