-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.ED.dot_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:59:49.891611+00:00
-- url     : https://prove2.me/submissions/d3e235b7-3dda-4891-a166-07afc6dc9afe

import Definitions.Def_ReciprocityTheory_DualLattices_BlockOneMulMulBlockOne
import Definitions.Def_ReciprocityTheory_DualLattices_ProdDvdOfIso
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsSmulMemOfMemSpan
import Definitions.Def_ReciprocityTheory_DualLattices_DotSingle
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
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.ED
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.Up.ED
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → R) →ₗ[R] R) (x : ι → R) :
    (fun k => f (Pi.single k 1)) ⬝ᵥ x = f x := by
  conv_rhs => rw [← Finset.univ_sum_single x]
  rw [map_sum, dotProduct]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : (Pi.single k (x k) : ι → R) = x k • (Pi.single k (1 : R) : ι → R) := by
    ext i
    by_cases hi : i = k
    · subst hi; simp
    · simp [Pi.single_apply, hi]
  rw [hk, map_smul, smul_eq_mul, mul_comm]
end ReciprocityTheory.PGsh.Up.ED
