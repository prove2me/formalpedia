-- Prove2me | solution 1 for SNumbers.half_le_entropyNumber_id
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:03:28.789428+00:00
-- url     : https://prove2.me/submissions/540ed3cf-ae81-430c-9d45-d1a57e263f0b

module
public import Definitions.Def_SNumbers_Entropy
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_MaxDifference
public import Definitions.Def_BasicResults_SVD
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Definitions.Def_SNumbers_EntropyBounds
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_John_rankOneSA_apply
public import Theorems.Thm_SNumbers_Complexification_adjoint_complexify
public import Theorems.Thm_SNumbers_Complexification_complexify_conj
public import Theorems.Thm_SNumbers_Complexification_complexify_fst
public import Theorems.Thm_SNumbers_Complexification_complexify_ofReal
public import Theorems.Thm_SNumbers_Complexification_complexify_snd
public import Theorems.Thm_SNumbers_Complexification_norm_complexify
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_bernsteinNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_entropyNumber_def
public import Theorems.Thm_SNumbers_entropyNumber_zero_op
public import Theorems.Thm_SNumbers_entropySet_nonempty
public import Theorems.Thm_SNumbers_padFin_apply
public import Theorems.Thm_Submodule_liftQL_mkQL
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] John.rankOneSA_apply
attribute [local simp] SNumbers.Complexification.adjoint_complexify
attribute [local simp] SNumbers.Complexification.complexify_conj
attribute [local simp] SNumbers.Complexification.complexify_fst
attribute [local simp] SNumbers.Complexification.complexify_ofReal
attribute [local simp] SNumbers.Complexification.complexify_snd
attribute [local simp] SNumbers.Complexification.norm_complexify
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm
attribute [local simp] SNumbers.bernsteinNumber_zero_eq_norm
attribute [local simp] SNumbers.entropyNumber_zero_op
attribute [local simp] SNumbers.padFin_apply
attribute [local simp] Submodule.liftQL_mkQL



set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open scoped Cardinal ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
open MeasureTheory
namespace SNumbers
theorem _root_.solution (X : Type u) [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [FiniteDimensional 𝕜 X] {n : ℕ}
    (hn : n < Module.finrank 𝕜 X) :
    1 / 2 ≤ entropyNumber (ContinuousLinearMap.id 𝕜 X) n := by
  have : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
  have : FiniteDimensional ℝ X := FiniteDimensional.trans ℝ 𝕜 X
  -- The real dimension is at least the `𝕜`-dimension.
  have hD : n < Module.finrank ℝ X := by
    have hmul := Module.finrank_mul_finrank ℝ 𝕜 X
    have hpos : 0 < Module.finrank ℝ 𝕜 := Module.finrank_pos
    calc n < Module.finrank 𝕜 X := hn
      _ ≤ Module.finrank ℝ 𝕜 * Module.finrank 𝕜 X := Nat.le_mul_of_pos_left _ hpos
      _ = Module.finrank ℝ X := hmul
  borelize X
  set D := Module.finrank ℝ X with hDdef
  set μ : Measure X := (Module.finBasis ℝ X).addHaar with hμ
  have hμ0 : μ (Metric.closedBall (0 : X) 1) ≠ 0 :=
    (Metric.measure_closedBall_pos μ 0 one_pos).ne'
  have hμtop : μ (Metric.closedBall (0 : X) 1) ≠ ⊤ := measure_closedBall_lt_top.ne
  rw [entropyNumber_def]
  refine le_csInf (entropySet_nonempty _ n) fun ε hε => ?_
  by_contra hcon
  have hεhalf : ε < 1 / 2 := not_le.mp hcon
  obtain ⟨hε0, N, hNcard, hcov⟩ := hε
  rw [show ⇑(ContinuousLinearMap.id 𝕜 X) '' Metric.closedBall 0 1
      = Metric.closedBall (0 : X) 1 by simp] at hcov
  -- Volume comparison.
  have h1 : μ (Metric.closedBall (0 : X) 1)
      ≤ ∑ _y ∈ N, ENNReal.ofReal (ε ^ D) * μ (Metric.closedBall (0 : X) 1) := by
    refine (measure_mono hcov).trans ?_
    refine (measure_biUnion_finset_le N _).trans ?_
    exact Finset.sum_le_sum fun y _ =>
      le_of_eq (Measure.addHaar_closedBall' μ y hε0.le)
  rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc] at h1
  -- Pass to real numbers, where the common factor `vol B` can be cancelled.
  have hfin : (N.card : ℝ≥0∞) * ENNReal.ofReal (ε ^ D)
      * μ (Metric.closedBall (0 : X) 1) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) hμtop
  have hBpos : 0 < μ.real (Metric.closedBall (0 : X) 1) :=
    ENNReal.toReal_pos hμ0 hμtop
  have h2 : μ.real (Metric.closedBall (0 : X) 1)
      ≤ (N.card : ℝ) * ε ^ D * μ.real (Metric.closedBall (0 : X) 1) := by
    have h := ENNReal.toReal_mono hfin h1
    simpa [Measure.real, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ ε ^ D)] using h
  have h3 : (1 : ℝ) ≤ (N.card : ℝ) * ε ^ D := by nlinarith [h2, hBpos]
  -- But `N.card ≤ 2 ^ n` and `ε < 1/2` make the right-hand side at most `1/2`.
  have h4 : (N.card : ℝ) * ε ^ D ≤ 2 ^ n * ε ^ D := by
    have hcard : (N.card : ℝ) ≤ 2 ^ n := by exact_mod_cast hNcard
    have hpow : (0 : ℝ) ≤ ε ^ D := by positivity
    nlinarith
  have h5 : ε ^ D ≤ (1 / 2 : ℝ) ^ (n + 1) := by
    obtain ⟨d, hd⟩ : ∃ d, D = (n + 1) + d := ⟨D - (n + 1), by omega⟩
    have hεle1 : ε ≤ 1 := by linarith
    rw [hd, pow_add]
    calc ε ^ (n + 1) * ε ^ d ≤ ε ^ (n + 1) * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ hε0.le hεle1) (by positivity)
      _ = ε ^ (n + 1) := mul_one _
      _ ≤ (1 / 2 : ℝ) ^ (n + 1) := pow_le_pow_left₀ hε0.le hεhalf.le _
  have h6 : (2 : ℝ) ^ n * ((1 : ℝ) / 2) ^ (n + 1) = 1 / 2 := by
    rw [pow_succ, ← mul_assoc, ← mul_pow]
    norm_num
  nlinarith [h3, h4, h5, h6, pow_pos hε0 D]
end SNumbers
