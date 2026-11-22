-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.loss_decay_of_four_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:56:21.367159+00:00
-- url     : https://prove2.me/submissions/327dad1f-f6f7-4926-90b2-2cb0db711d4b

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution {m n : ℕ}
    (hm : 0 < m) (hmn : 4 * m ≤ n) :
    loss n ≤ ((1 : ℝ) / 2) * loss m := by
  unfold loss
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hn_pos_nat : 0 < n := lt_of_lt_of_le (by omega : 0 < 4 * m) hmn
  have h4m_le_n : (4 : ℝ) * m ≤ n := by exact_mod_cast hmn
  have hden : (16 : ℝ) * (m : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
    nlinarith [h4m_le_n, sq_nonneg ((n : ℝ) - (4 : ℝ) * m)]
  have hinv : ((n : ℝ) ^ 2)⁻¹ ≤ ((16 : ℝ) * (m : ℝ) ^ 2)⁻¹ := by
    exact (inv_le_inv₀ (by positivity) (by positivity)).mpr hden
  calc
    ((n : ℝ) ^ 2)⁻¹ ≤ ((16 : ℝ) * (m : ℝ) ^ 2)⁻¹ := hinv
    _ ≤ ((1 : ℝ) / 2) * (((m : ℝ) ^ 2)⁻¹) := by
      field_simp [hm_pos.ne']
      nlinarith [sq_pos_of_pos hm_pos]
end PebblingLean.Hypercube.PaperParameters
