-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HolomorphicZeroSetDimH_dimH_image_le_of_analyticOnNhd_2f93c902b017
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:32:34.085134+00:00
-- url     : https://prove2.me/submissions/6bd16490-6e6a-432f-825e-63bd84d9a545

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicZeroSetDimH
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticImplicitChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProperHolomorphicSurjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHolomorphicZeroSetDimH

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Metric Filter
open scoped ENNReal NNReal
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.HolomorphicZeroSetDimH
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.HolomorphicZeroSetDimH
theorem _root_.solution {d : ℕ} {σ : Type*} [Fintype σ] {O : Set (Fin d → ℂ)}
    {g : (Fin d → ℂ) → σ → ℂ} (hg : AnalyticOnNhd ℂ g O) : dimH (g '' O) ≤ 2 * (d : ℝ≥0∞) := by
  refine (dimH_image_le_of_locally_lipschitzOn fun y hy => ?_).trans ?_
  · obtain ⟨K, t, ht, hK⟩ := ((hg y hy).contDiffAt (n := 1)).exists_lipschitzOnWith
    exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hK⟩
  · have hfin : Module.finrank ℝ (Fin d → ℂ) = 2 * d := by
      rw [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]
    calc dimH O ≤ dimH (Set.univ : Set (Fin d → ℂ)) := dimH_mono (Set.subset_univ _)
      _ = Module.finrank ℝ (Fin d → ℂ) := Real.dimH_univ_eq_finrank _
      _ = 2 * (d : ℝ≥0∞) := by rw [hfin]; push_cast; ring
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.HolomorphicZeroSetDimH
