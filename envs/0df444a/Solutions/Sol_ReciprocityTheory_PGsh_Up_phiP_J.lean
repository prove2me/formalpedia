-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.phiP_J
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:37:59.647455+00:00
-- url     : https://prove2.me/submissions/f4b2d266-45ba-4acc-8e16-62c04f71c6fd

import Definitions.Def_ReciprocityTheory_DualLattices_InvolutionPermApplyZero
import Definitions.Def_ReciprocityTheory_DualLattices_StdJForm4
import Theorems.Thm_ReciprocityTheory_PGsh_Up_btP_facts
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


section
noncomputable section
open Matrix
namespace ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}
private lemma stdJ_form4 {D : Type} [CommRing D] {g : ℕ}
    (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) D) (i j : Fin g ⊕ Fin g) :
    (Mᵀ * stdJ D g * M) i j =
      ∑ a, (M (Sum.inr a) i * M (Sum.inl a) j - M (Sum.inl a) i * M (Sum.inr a) j) := by
  rw [Matrix.mul_assoc, Matrix.mul_apply, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Matrix.mul_apply, stdJ, Fintype.sum_sum_type, Matrix.one_apply] <;> ring
end ReciprocityTheory.PGsh.Up
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (hS : HodgeTateSetting p v R O σ cp) (H : HodgeTateDatum p g v R O σ cp) {m : ℕ} (e : Fin m → O)
    (π : Equiv.Perm (Fin m)) (horth : ∀ i j, e i * e j = if i = j then e i else 0)
    (hσ : ∀ i, σ (e i) = e (π i)) (hsT : (∑ i, H.ρ (e i)) + H.P = 1)
    (hPT : ∀ i, H.ρ (e i) * H.P = 0) (hsL : (∑ i, H.ρL (e i)) + H.PL = 1)
    (hPL : ∀ i, H.ρL (e i) * H.PL = 0) :
    (phiP H e)ᵀ * stdJ R g * phiP H e = cp • H.E.map (algebraMap ℤ_[p] R) := by
  obtain ⟨h1, -, -⟩ := btP_facts hS H e π horth hσ hsT hPT hsL hPL
  ext i j
  rw [stdJ_form4, ← h1, Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply,
    ← Finset.sum_sub_distrib]
  rfl
end ReciprocityTheory.PGsh.Up
