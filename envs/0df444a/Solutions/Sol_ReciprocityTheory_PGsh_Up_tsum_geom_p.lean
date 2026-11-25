-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.tsum_geom_p
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:24:08.277704+00:00
-- url     : https://prove2.me/submissions/615b9847-d3f3-4766-afff-9285a58f8b69

import Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqMulLeProd
import Definitions.Def_ReciprocityTheory_DualLattices_CokernelsAgreeEquivariantly
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeOfFrobenius
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeOfWdetFrobenius
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
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
end ReciprocityTheory.PGsh.Up
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {p : ℕ} [Fact p.Prime] :
    ∑' n : ℕ, (p : ℝ) ^ (-((n : ℝ) + 1)) = 1 / ((p : ℝ) - 1) := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hp.ne'
  rw [tsum_congr (fun n : ℕ => prime_rpow_neg_succ_eq_inv_mul_inv_pow (p := p) n), tsum_mul_left,
    tsum_geometric_of_lt_one (inv_nonneg.mpr (Nat.cast_nonneg p)) prime_inv_lt_one]
  field_simp
end ReciprocityTheory.PGsh.Up
