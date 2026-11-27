-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HolomorphicZeroSetDimH_proof_97339d5c9def
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:58:12.990016+00:00
-- url     : https://prove2.me/submissions/ab602d8d-7b0a-4a54-8f19-cd8028002eea

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicZeroSetDimH
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticImplicitChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProperHolomorphicSurjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHolomorphicZeroSetDimH
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HolomorphicZeroSetDimH_dimH_regular_zeros_le_092cf97b9ce1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HolomorphicZeroSetDimH_exists_partialDeriv_8b619a5c94d6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ProperHolomorphicSurjective_analyticOnNhd_of_differentiableOn_860e95b7c849


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
theorem _root_.solution : HolomorphicZeroSetDimH.Statement := by
  intro k U h hU hh hW
  have ha : AnalyticOnNhd ℂ h U :=
    analyticOnNhd_pi_iff.1 (ProperHolomorphicSurjective.analyticOnNhd_of_differentiableOn (m := 1)
      (f := fun v _ => h v) hU (differentiableOn_pi.2 fun _ => hh)) 0
  have hpd : ∀ n m, AnalyticOnNhd ℂ (partialDeriv h n m) U := fun n m x hx =>
    ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => Fin k → ℂ) ℂ
      (fun j => Pi.basisFun ℂ (Fin k) (m j))).analyticAt _).comp (ha.iteratedFDeriv n x hx)
  calc dimH {v | v ∈ U ∧ h v = 0}
      ≤ dimH (⋃ nm : (Σ n, Fin n → Fin k),
          {v | v ∈ U ∧ partialDeriv h nm.1 nm.2 v = 0 ∧ fderiv ℂ (partialDeriv h nm.1 nm.2) v ≠ 0}) := by
        refine dimH_mono fun v hv => ?_
        obtain ⟨n, m, h1, h2⟩ := exists_partialDeriv hU ha hW hv.1 hv.2
        exact Set.mem_iUnion.2 ⟨⟨n, m⟩, hv.1, h1, h2⟩
    _ ≤ 2 * ((k - 1 : ℕ) : ℝ≥0∞) := by
        rw [dimH_iUnion]
        exact iSup_le fun nm => dimH_regular_zeros_le (hpd nm.1 nm.2)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.HolomorphicZeroSetDimH
