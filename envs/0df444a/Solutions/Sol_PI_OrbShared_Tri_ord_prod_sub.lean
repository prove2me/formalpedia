-- Prove2me | solution 1 for PI.OrbShared.Tri.ord_prod_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:08:42.330096+00:00
-- url     : https://prove2.me/submissions/32a7e474-a669-4c16-aad5-65fbcb0ac46f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OrbitPowerSeriesCoefficients_SolvableEquivalenceOfBaseChange
import Theorems.Thm_PI_OrbShared_Tri_ord_mul
import Theorems.Thm_PI_OrbShared_Tri_ord_add
import Theorems.Thm_PI_OrbShared_Tri_ord_pow
import Theorems.Thm_PI_OrbShared_Tri_ord_pow_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.OrbShared PI.OrbShared.Tri
open MvPowerSeries Finsupp
variable {K : Type*} [Field K] {σ : Type*} [Finite σ]
variable {c : K} {a : σ → MvPowerSeries σ K}
namespace PI.OrbShared.Tri
theorem _root_.solution {ι : Type*} (S : Finset ι) (x y : ι → MvPowerSeries σ K) (d : ι → ℕ)
    (hx : ∀ i, 1 ≤ (x i).order) (hy : ∀ i, 1 ≤ (y i).order)
    (hxy : ∀ i, ((2 : ℕ) : ℕ∞) ≤ (y i - x i).order) :
    ((∑ i ∈ S, d i : ℕ) : ℕ∞) ≤ (∏ i ∈ S, x i ^ d i).order ∧
      ((∑ i ∈ S, d i + 1 : ℕ) : ℕ∞) ≤ (∏ i ∈ S, y i ^ d i - ∏ i ∈ S, x i ^ d i).order := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert j S hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
    refine ⟨ord_mul (ord_pow (hx j) _) ih.1, ?_⟩
    rw [show y j ^ d j * ∏ i ∈ S, y i ^ d i - x j ^ d j * ∏ i ∈ S, x i ^ d i =
      y j ^ d j * (∏ i ∈ S, y i ^ d i - ∏ i ∈ S, x i ^ d i) +
        (y j ^ d j - x j ^ d j) * ∏ i ∈ S, x i ^ d i by ring]
    apply ord_add
    · have := ord_mul (ord_pow (hy j) (d j)) ih.2
      exact le_trans (by norm_cast) this
    · have := ord_mul (ord_pow_sub (hx j) (hy j) (hxy j) (d j)) ih.1
      exact le_trans (by norm_cast <;> omega) this
end PI.OrbShared.Tri
