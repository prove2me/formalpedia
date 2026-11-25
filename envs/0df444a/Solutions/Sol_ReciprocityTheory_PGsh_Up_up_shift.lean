-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.up_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:43:25.614597+00:00
-- url     : https://prove2.me/submissions/24ca4e92-4c96-4076-9cd5-564099e47f16

import Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqMulLeProd
import Definitions.Def_ReciprocityTheory_DualLattices_CokernelsAgreeEquivariantly
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeOfFrobenius
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeOfWdetFrobenius
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Theorems.Thm_ReciprocityTheory_PGsh_Up_up_full
import Theorems.Thm_ReciprocityTheory_PGsh_Up_tsum_geom_p
import Theorems.Thm_ReciprocityTheory_PGsh_Up_summable_geom_p
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2
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
private lemma prime_rpow_neg_succ_eq_inv_mul_inv_pow {p : ℕ} [Fact p.Prime] (n : ℕ) :
    (p : ℝ) ^ (-((n : ℝ) + 1)) = (p : ℝ)⁻¹ * ((p : ℝ)⁻¹) ^ n := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hn : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [Real.rpow_neg hp0.le, hn, Real.rpow_natCast, ← inv_pow, pow_succ]
  ring
private lemma prime_inv_lt_one {p : ℕ} [Fact p.Prime] : (p : ℝ)⁻¹ < 1 := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have h1 := one_div_lt_one_div_of_lt one_pos hp
  simpa using h1
private lemma summable_prime_rpow_neg_succ {p : ℕ} [Fact p.Prime] :
    Summable fun n : ℕ => (p : ℝ) ^ (-((n : ℝ) + 1)) := by
  have e : (fun n : ℕ => (p : ℝ) ^ (-((n : ℝ) + 1))) =
      fun n : ℕ => (p : ℝ)⁻¹ * ((p : ℝ)⁻¹) ^ n := funext fun n => prime_rpow_neg_succ_eq_inv_mul_inv_pow n
  rw [e]
  exact (summable_geometric_of_lt_one (inv_nonneg.mpr (Nat.cast_nonneg p)) prime_inv_lt_one).mul_left _
end ReciprocityTheory.PGsh.Up
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (hU7 : UnramifiedCokernelLengthStatement) (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C]
    [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C]
    [Algebra ℤ_[p] R] (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R)
    (hp2 : p ≠ 2) (hS : HodgeTateSetting p v R O σ cp) (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (i : Fin U.m) (ρ r : ℕ) (rG : Fin U.m → ℕ)
    (hrB : ∀ j, U.r j + ρ = rG j) (hrc : (rG (U.cj i) : ℝ) = r - rG i)
    (N : Type) [AddCommGroup N] [Module R N] (E : cokE H.Ht U.εT U.εL i (U.cj i) ≃ₗ[R] N)
    (V1 : NNReal) (hN : HasLen v R N V1) :
    (v (algebraMap R C (p : R)) : ℝ) ^ ((rG i : ℝ) / (p - 1) -
      ∑' n : ℕ, (p : ℝ) ^ (-((n : ℝ) + 1)) * rG ((U.φ ^ (n + 1)) i) +
      ((r : ℝ) - rG i - ρ) / (p - 1)) ≤ V1 := by
  have hsplit : ∀ n : ℕ, (p : ℝ) ^ (-((n : ℝ) + 1)) * (rG ((U.φ ^ (n + 1)) i) : ℝ) =
      (p : ℝ) ^ (-((n : ℝ) + 1)) * (U.r ((U.φ ^ (n + 1)) i) : ℝ) +
        (p : ℝ) ^ (-((n : ℝ) + 1)) * (ρ : ℝ) := by
    intro n
    rw [← hrB]
    push_cast
    ring
  have hs1 : Summable fun n : ℕ => (p : ℝ) ^ (-((n : ℝ) + 1)) * (U.r ((U.φ ^ (n + 1)) i) : ℝ) :=
    summable_geom_p (fun n : ℕ => (U.r ((U.φ ^ (n + 1)) i) : ℝ)) (fun n => Nat.cast_nonneg _)
      (∑ j, (U.r j : ℝ))
      (fun n => Finset.single_le_sum (f := fun j => (U.r j : ℝ)) (fun j _ => Nat.cast_nonneg _)
        (Finset.mem_univ _))
  have hsum : ∑' n : ℕ, (p : ℝ) ^ (-((n : ℝ) + 1)) * (rG ((U.φ ^ (n + 1)) i) : ℝ) =
      frobSum U i + (ρ : ℝ) / ((p : ℝ) - 1) := by
    rw [tsum_congr hsplit, hs1.tsum_add ((summable_prime_rpow_neg_succ (p := p)).mul_right _), tsum_mul_right,
      tsum_geom_p]
    unfold frobSum
    ring
  have h1 : (rG i : ℝ) = U.r i + ρ := by
    rw [← hrB i]
    push_cast
    ring
  have h2 : (r : ℝ) - rG i - ρ = U.r (U.cj i) := by
    rw [← hrc, ← hrB (U.cj i)]
    push_cast
    ring
  have hexp : (rG i : ℝ) / (p - 1) -
      ∑' n : ℕ, (p : ℝ) ^ (-((n : ℝ) + 1)) * rG ((U.φ ^ (n + 1)) i) +
      ((r : ℝ) - rG i - ρ) / (p - 1) =
      ((U.r i : ℝ) + U.r (U.cj i)) / (p - 1) - frobSum U i := by
    rw [hsum, h2, h1]
    ring
  rw [hexp]
  exact up_full hU7 p g C v R O σ cp hp2 hS H U i N E V1 hN
end ReciprocityTheory.PGsh.Up
