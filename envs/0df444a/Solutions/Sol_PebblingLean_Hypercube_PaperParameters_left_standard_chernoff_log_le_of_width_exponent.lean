-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.left_standard_chernoff_log_le_of_width_exponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:14:55.511362+00:00
-- url     : https://prove2.me/submissions/5fa2155a-e25a-4347-a86d-e4bae90dbfe3

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_rIn_real_le_third_sub_width
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_bernoulli_third_left_log_le_quadratic
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_annulusChernoffLambda_nonneg
public import Theorems.Thm_PebblingLean_Graph_Walk_length_append
public import Theorems.Thm_PebblingLean_Graph_Walk_length_reverse
public import Theorems.Thm_PebblingLean_Hypercube_fromDiffSet_empty
public import Theorems.Thm_PebblingLean_Hypercube_mem_annulus
public import Theorems.Thm_PebblingLean_Pebbling_fibersDistribution_apply
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_from
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_of_ne
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_to
public import Theorems.Thm_PebblingLean_Pebbling_single_apply_ne
public import Theorems.Thm_PebblingLean_Pebbling_single_apply_self
public import Theorems.Thm_PebblingLean_Pebbling_size_single
public import Theorems.Thm_PebblingLean_Pebbling_size_zero
public import Theorems.Thm_PebblingLean_Pebbling_sliceDistribution_apply_off
public import Theorems.Thm_PebblingLean_Pebbling_sliceDistribution_apply_on
public import Theorems.Thm_PebblingLean_Pebbling_twoPoint_apply_left
public import Theorems.Thm_PebblingLean_Pebbling_twoPoint_apply_ne
public import Theorems.Thm_PebblingLean_Pebbling_twoPoint_apply_right
public import Theorems.Thm_PebblingLean_Pebbling_weight_zero
attribute [local simp] PebblingLean.Graph.Walk.length_append
attribute [local simp] PebblingLean.Graph.Walk.length_reverse
attribute [local simp] PebblingLean.Hypercube.fromDiffSet_empty
attribute [local simp] PebblingLean.Hypercube.mem_annulus
attribute [local simp] PebblingLean.Pebbling.fibersDistribution_apply
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_from
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_of_ne
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_to
attribute [local simp] PebblingLean.Pebbling.single_apply_ne
attribute [local simp] PebblingLean.Pebbling.single_apply_self
attribute [local simp] PebblingLean.Pebbling.size_single
attribute [local simp] PebblingLean.Pebbling.size_zero
attribute [local simp] PebblingLean.Pebbling.sliceDistribution_apply_off
attribute [local simp] PebblingLean.Pebbling.sliceDistribution_apply_on
attribute [local simp] PebblingLean.Pebbling.twoPoint_apply_left
attribute [local simp] PebblingLean.Pebbling.twoPoint_apply_ne
attribute [local simp] PebblingLean.Pebbling.twoPoint_apply_right
attribute [local simp] PebblingLean.Pebbling.weight_zero


section
@[expose] public section
namespace PebblingLean
namespace Hypercube
namespace PaperParameters
private theorem chernoff_left_quadratic_le {a w : ℝ} (ha : 0 ≤ a) :
    let lam := 3 * w / (a + 1);
    lam * (a / 3 - w) + a * (-lam / 3 + (13 / 54) * lam ^ 2) ≤
      -((5 / 6) * (w ^ 2 / (a + 1))) := by
  have hden : 0 < a + 1 := by positivity
  dsimp
  field_simp [hden.ne']
  ring_nf
  nlinarith only [sq_nonneg w, mul_nonneg ha (sq_nonneg w)]
end PaperParameters
end Hypercube
end PebblingLean
end
end

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution
    {A K : ℝ} {n : ℕ} {E : ℝ}
    (hcenter : annulusWidth A K n ≤ splitA K n / 3)
    (hlam_le_one : annulusChernoffLambda A K n ≤ 1)
    (hE :
      E ≤ (5 / 6) *
        ((annulusWidth A K n : ℝ) ^ 2 / ((splitA K n : ℝ) + 1))) :
    annulusChernoffLambda A K n * (rIn A K n : ℝ) +
        (splitA K n : ℝ) *
          Real.log (((1 : ℝ) / 3) *
              Real.exp (-(annulusChernoffLambda A K n)) +
            ((2 : ℝ) / 3)) ≤ -E := by
  let lam := annulusChernoffLambda A K n
  let a : ℝ := splitA K n
  let w : ℝ := annulusWidth A K n
  have hlam0 : 0 ≤ lam := annulusChernoffLambda_nonneg A K n
  have ha : 0 ≤ a := Nat.cast_nonneg _
  have hrIn : (rIn A K n : ℝ) ≤ a / 3 - w :=
    rIn_real_le_third_sub_width hcenter
  have hlog := bernoulli_third_left_log_le_quadratic hlam0 hlam_le_one
  calc
    _ ≤ lam * (a / 3 - w) + a * (-lam / 3 + (13 / 54) * lam ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hrIn hlam0)
        (mul_le_mul_of_nonneg_left hlog ha)
    _ ≤ -((5 / 6) * (w ^ 2 / (a + 1))) := chernoff_left_quadratic_le ha
    _ ≤ -E := neg_le_neg hE
end PebblingLean.Hypercube.PaperParameters
