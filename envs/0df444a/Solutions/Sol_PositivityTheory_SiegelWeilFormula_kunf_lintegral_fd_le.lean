-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.kunf.lintegral_fd_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:54.180312+00:00
-- url     : https://prove2.me/submissions/549975f6-ee1e-4bc8-b04c-00a3d1a4fd6b

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_UnfoldingCompactness_AbsUnfA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Pointwise
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.kunf
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V] {lam : Measure V} [lam.IsAddHaarMeasure] {Λ : AddSubgroup V} [Countable Λ]
  {𝓖 : Set V}
omit [SecondCountableTopology V]
namespace PositivityTheory.SiegelWeilFormula.kunf
theorem _root_.solution (h𝓖 : IsAddFundamentalDomain Λ 𝓖 lam) (S : V → ℝ≥0∞)
    (hS : ∀ (ν : Λ) β, S (β + ν) = S β) {C : Set V} (hcov : ∀ β, ∃ ν : Λ, β + (ν : V) ∈ C) :
    ∫⁻ β in 𝓖, S β ∂lam ≤ ∫⁻ β in C, S β ∂lam := by
  rw [h𝓖.setLIntegral_eq_tsum' S C]
  have hsub : 𝓖 ⊆ ⋃ ν : Λ, (ν +ᵥ C) ∩ 𝓖 := by
    intro β hβ
    obtain ⟨ν, hν⟩ := hcov β
    refine Set.mem_iUnion.2 ⟨-ν, ?_, hβ⟩
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg, AddSubgroup.vadd_def, vadd_eq_add, add_comm]
    exact hν
  calc ∫⁻ β in 𝓖, S β ∂lam ≤ ∫⁻ β in ⋃ ν : Λ, (ν +ᵥ C) ∩ 𝓖, S β ∂lam := lintegral_mono_set hsub
    _ ≤ ∑' ν : Λ, ∫⁻ β in (ν +ᵥ C) ∩ 𝓖, S β ∂lam := lintegral_iUnion_le _ _
    _ = ∑' ν : Λ, ∫⁻ x in (ν +ᵥ C) ∩ 𝓖, S (-ν +ᵥ x) ∂lam := by
      refine tsum_congr fun ν => lintegral_congr fun x => ?_
      rw [AddSubgroup.vadd_def, vadd_eq_add, add_comm]
      exact (hS (-ν) x).symm
end PositivityTheory.SiegelWeilFormula.kunf
