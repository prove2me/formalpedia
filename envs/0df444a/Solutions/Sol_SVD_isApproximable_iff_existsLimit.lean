-- Prove2me | solution 1 for SVD.isApproximable_iff_existsLimit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:32:11.565319+00:00
-- url     : https://prove2.me/submissions/b3c09ed7-5442-47b6-958f-965c7414181e

module
public import Definitions.Def_SNumbers_Approximation
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_AddOns_Approximable
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_SNumbers_approximationNumber_le_norm_sub
public import Theorems.Thm_SNumbers_approximationNumber_nonneg
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_approximationSet_nonempty
public import Theorems.Thm_SNumbers_bddBelow_approximationSet
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm



set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open Filter Topology
open SVD
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace SVD
theorem _root_.solution (S : X →L[𝕜] Y) :
    IsApproximable S ↔
      ∃ L : ℕ → X →L[𝕜] Y, (∀ n, (L n).rank ≤ (n : Cardinal)) ∧
        Tendsto (fun n => ‖S - L n‖) atTop (𝓝 0) := by
  constructor
  · -- Forward: pick a near-inf approximant for each `n`.
    intro hS
    have h_choose : ∀ n : ℕ, ∃ L : X →L[𝕜] Y,
        L.rank ≤ (n : Cardinal) ∧
          ‖S - L‖ < SNumbers.approximationNumber S n + 1 / (n + 1) := by
      intro n
      have hε : (0 : ℝ) < 1 / (n + 1) := by positivity
      have h_lt : SNumbers.approximationNumber S n <
                    SNumbers.approximationNumber S n + 1 / (n + 1) := by linarith
      obtain ⟨r, hr_mem, hr_lt⟩ :=
        (csInf_lt_iff (SNumbers.bddBelow_approximationSet S n)
          (SNumbers.approximationSet_nonempty S n)).mp h_lt
      obtain ⟨L, hL_rank, rfl⟩ := hr_mem
      exact ⟨L, hL_rank, hr_lt⟩
    choose L hL_rank hL_lt using h_choose
    refine ⟨L, hL_rank, ?_⟩
    -- Squeeze: 0 ≤ ‖S - Lₙ‖ ≤ aₙ(S) + 1/(n+1) → 0.
    have h_nonneg : ∀ n, (0 : ℝ) ≤ ‖S - L n‖ := fun n => norm_nonneg _
    have h_bd : ∀ n, ‖S - L n‖ ≤
                  SNumbers.approximationNumber S n + 1 / (n + 1) :=
      fun n => (hL_lt n).le
    have h_one_div : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h_lim :
        Tendsto (fun n : ℕ => SNumbers.approximationNumber S n + 1 / (n + 1))
          atTop (𝓝 0) := by simpa using hS.add h_one_div
    exact squeeze_zero h_nonneg h_bd h_lim
  · -- Converse: aₙ(S) ≤ ‖S - Lₙ‖ → 0.
    rintro ⟨L, hL_rank, hL_lim⟩
    have h_nonneg : ∀ n, 0 ≤ SNumbers.approximationNumber S n :=
      fun n => SNumbers.approximationNumber_nonneg _ n
    have h_bd : ∀ n, SNumbers.approximationNumber S n ≤ ‖S - L n‖ :=
      fun n => SNumbers.approximationNumber_le_norm_sub (hL_rank n)
    exact squeeze_zero h_nonneg h_bd hL_lim
end SVD
