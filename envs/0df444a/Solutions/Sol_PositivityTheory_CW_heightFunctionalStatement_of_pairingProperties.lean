-- Prove2me | solution 1 for PositivityTheory.CW.heightFunctionalStatement_of_pairingProperties
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:41:59.331169+00:00
-- url     : https://prove2.me/submissions/72c085d7-3994-465b-a2c7-24fa1510a9ab

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_SecondDerivativeHolds
import Theorems.Thm_PositivityTheory_CW_HilbertSchmidtNorm_hilbert_schmidt_nonneg_alt
import Theorems.Thm_PositivityTheory_CW_HilbertSchmidtNorm_hilbert_schmidt_mul_le
import Theorems.Thm_PositivityTheory_CW_HilbertSchmidtNorm_abs_two_inner_le
import Theorems.Thm_PositivityTheory_CW_HilbertSchmidtNorm_hd1
import Theorems.Thm_PositivityTheory_CW_HilbertSchmidtNorm_hd2
import Theorems.Thm_PositivityTheory_CW_HilbertSchmidtNorm_L1
import Theorems.Thm_PositivityTheory_CW_HilbertSchmidtNorm_L2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open HilbertSchmidtNorm
namespace PositivityTheory.CW
theorem _root_.solution : B2 := by
  intro n X r
  set A : ℝ := 1 + hs2 X with hA
  set Bc : ℝ := 1 + hs2 (X * X) + 2 * hs2 X with hBc
  have hXn := hilbert_schmidt_nonneg_alt X
  have hXXn := hilbert_schmidt_nonneg_alt (X * X)
  refine ⟨r * r * A ^ 2 + r * Bc, by positivity, fun g => ?_⟩
  set h : ℝ → ℝ := fun s => hs2 (g * NormedSpace.exp (s • X)) with hh
  set h' : ℝ → ℝ := fun t => ∑ i, ∑ j, 2 * inner ℝ ((g * NormedSpace.exp (t • X)) i j)
    ((g * NormedSpace.exp (t • X) * X) i j) with hh'
  set H2 : ℝ := ∑ i, ∑ j, 2 * (inner ℝ ((g * NormedSpace.exp ((0:ℝ) • X)) i j)
    ((g * NormedSpace.exp ((0:ℝ) • X) * X * X) i j) + inner ℝ ((g * NormedSpace.exp ((0:ℝ) • X) * X) i j)
      ((g * NormedSpace.exp ((0:ℝ) • X) * X) i j)) with hH2
  have d1 : ∀ t, HasDerivAt h (h' t) t := fun t => hd1 g X t
  have d2 : HasDerivAt h' H2 0 := hd2 g X 0
  refine ⟨fun t => r * (1 + h t) ^ (r - 1) * h' t,
    r * (((r - 1 : ℕ) : ℝ) * (1 + h 0) ^ (r - 1 - 1) * h' 0) * h' 0 + r * (1 + h 0) ^ (r - 1) * H2,
    fun t => ((d1 t).const_add 1).pow r, (((d1 0).const_add 1).pow (r - 1)).const_mul (r : ℝ) |>.mul d2, ?_⟩
  have e0 : NormedSpace.exp ((0:ℝ) • X) = 1 := by simp
  have hg := hilbert_schmidt_nonneg_alt g
  have h0 : h 0 = hs2 g := by simp [hh]
  have hp : |h' 0| ≤ A * hs2 g := by
    have := abs_two_inner_le g (g * X)
    have := hilbert_schmidt_mul_le g X
    simp only [hh', e0, mul_one]
    nlinarith
  have hpp : |H2| ≤ Bc * hs2 g := by
    have k1 := abs_two_inner_le g (g * (X * X))
    have k2 := abs_two_inner_le (g * X) (g * X)
    have k3 := hilbert_schmidt_mul_le g X
    have k4 := hilbert_schmidt_mul_le g (X * X)
    have : H2 = (∑ i, ∑ j, 2 * inner ℝ (g i j) ((g * (X * X)) i j)) +
        ∑ i, ∑ j, 2 * inner ℝ ((g * X) i j) ((g * X) i j) := by
      simp only [hH2, e0, mul_one, mul_add, Finset.sum_add_distrib, mul_assoc]
    rw [this]
    refine (abs_add_le _ _).trans ?_
    nlinarith
  rw [h0]
  set u : ℝ := 1 + hs2 g with hu
  have hu1 : 1 ≤ u := by linarith
  have hP : 0 ≤ ((r - 1 : ℕ) : ℝ) * u ^ (r - 1 - 1) := by positivity
  have hQ : 0 ≤ u ^ (r - 1) := by positivity
  have hr : (0 : ℝ) ≤ r := by positivity
  have hA0 : 0 ≤ A := by positivity
  have hsq : h' 0 ^ 2 ≤ (A * u) ^ 2 := by
    have : |h' 0| ≤ A * u := hp.trans (by nlinarith)
    exact sq_le_sq' (by linarith [neg_abs_le (h' 0)]) (le_trans (le_abs_self _) this)
  have t1 : r * (((r - 1 : ℕ) : ℝ) * u ^ (r - 1 - 1) * h' 0) * h' 0 ≤ r * A ^ 2 * (r * u ^ r) := by
    calc r * (((r - 1 : ℕ) : ℝ) * u ^ (r - 1 - 1) * h' 0) * h' 0
        = r * (((r - 1 : ℕ) : ℝ) * u ^ (r - 1 - 1)) * h' 0 ^ 2 := by ring
      _ ≤ r * (((r - 1 : ℕ) : ℝ) * u ^ (r - 1 - 1)) * (A * u) ^ 2 := by gcongr
      _ = r * A ^ 2 * (((r - 1 : ℕ) : ℝ) * u ^ (r - 1 - 1) * u ^ 2) := by ring
      _ ≤ r * A ^ 2 * (r * u ^ r) := mul_le_mul_of_nonneg_left (L1 r u hu1) (by positivity)
  have t2 : r * u ^ (r - 1) * H2 ≤ Bc * (r * u ^ r) := by
    have hH : H2 ≤ Bc * u := (le_abs_self _).trans (hpp.trans (by nlinarith))
    calc r * u ^ (r - 1) * H2 ≤ r * u ^ (r - 1) * (Bc * u) := by gcongr
      _ = Bc * (r * u ^ (r - 1) * u) := by ring
      _ ≤ Bc * (r * u ^ r) := mul_le_mul_of_nonneg_left (L2 r u) (by rw [hBc]; positivity)
  nlinarith
end PositivityTheory.CW
