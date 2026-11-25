-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures.trace_contra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:58:10.301627+00:00
-- url     : https://prove2.me/submissions/36719438-0b43-41bd-9152-595c152bbed6

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_PeakTraceBound
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RegularizedExponentialSum
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RegularizedExponentialSumStatement
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_PeakTraceBoundHolds
import Theorems.Thm_PositivityTheory_Rg_BcB_F_ExponentialIntegralMeasures_trace_pow_eq
import Theorems.Thm_GlobalTheory_T_regularized_exponential_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.style.haveILetI false
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures
namespace PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : Module.End ℂ V) (v : V) (hv : v ≠ 0) (μ : ℂ) (hTv : T v = μ • v) (r C : ℝ) (N j : ℕ)
    (hr : 0 ≤ r) (hrμ : r < ‖μ‖)
    (h : ∀ᶠ k : ℕ in Filter.atTop, ‖LinearMap.trace ℂ V (T ^ k)‖ ≤ C * (1 + k) ^ N * r ^ (k - j)) :
    False := by
  classical
  have hfin : {μ | T.maxGenEigenspace μ ≠ ⊥}.Finite :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep T.independent_maxGenEigenspace
  set r' : ℝ := (r + ‖μ‖) / 2 with hr'
  have hr'0 : 0 < r' := by
    have : 0 < ‖μ‖ := lt_of_le_of_lt hr hrμ
    rw [hr']; linarith
  have hrr' : r ≤ r' := by rw [hr']; linarith
  have hr'μ : r' < ‖μ‖ := by rw [hr']; linarith
  let ι := (hfin.toFinset : Set ℂ)
  have key := GlobalTheory.T.regularized_exponential_sum ι (fun i => (Module.finrank ℂ (T.maxGenEigenspace i.1) : ℂ))
    (fun i => i.1) r' (max C 0 * (r' ^ j)⁻¹) N hr'0.le ?_ μ hr'μ
  ·
    have hmem : μ ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset]
      intro hbot
      have hvm : v ∈ T.maxGenEigenspace μ :=
        Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hTv)
      rw [hbot] at hvm
      exact hv ((Submodule.mem_bot ℂ).mp hvm)
    rw [Finset.sum_eq_single_of_mem (⟨μ, Finset.mem_coe.mpr hmem⟩ : ι) (by simp)
      (fun b _ hb => by
        exfalso
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
        exact hb (Subtype.ext (by assumption)))] at key
    simp only [Nat.cast_eq_zero] at key
    have hpos : Module.finrank ℂ (T.maxGenEigenspace μ) ≠ 0 := by
      rw [Set.Finite.mem_toFinset] at hmem
      exact Submodule.finrank_eq_zero.not.mpr hmem
    exact hpos key
  · filter_upwards [h, Filter.eventually_ge_atTop j] with k hk hkj
    have hsum : ∑ i : ι, (Module.finrank ℂ (T.maxGenEigenspace i.1) : ℂ) * i.1 ^ k =
        LinearMap.trace ℂ V (T ^ k) := by
      rw [trace_pow_eq T hfin k]
      exact Finset.sum_coe_sort hfin.toFinset (fun i => (Module.finrank ℂ (T.maxGenEigenspace i) : ℂ) * i ^ k)
    rw [hsum]
    refine hk.trans ?_
    have h1 : r ^ (k - j) ≤ r' ^ (k - j) := pow_le_pow_left₀ hr hrr' _
    have h2 : r' ^ (k - j) = (r' ^ j)⁻¹ * r' ^ k := by
      rw [pow_sub₀ _ hr'0.ne' hkj]; ring
    have h3 : (0 : ℝ) ≤ (1 + k) ^ N := by positivity
    calc C * (1 + k) ^ N * r ^ (k - j) ≤ max C 0 * (1 + k) ^ N * r ^ (k - j) := by
          gcongr; exact le_max_left _ _
      _ ≤ max C 0 * (1 + k) ^ N * r' ^ (k - j) := by gcongr
      _ = max C 0 * (r' ^ j)⁻¹ * (1 + k) ^ N * r' ^ k := by rw [h2]; ring
end PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures
