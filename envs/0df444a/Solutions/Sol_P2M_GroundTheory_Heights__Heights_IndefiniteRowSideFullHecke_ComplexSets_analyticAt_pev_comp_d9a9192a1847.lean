-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticAt_pev_comp_d9a9192a1847
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:43.168864+00:00
-- url     : https://prove2.me/submissions/74b4abea-16de-428d-a967-67740182456e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitivePresentationCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PevEqZeroOfPresentation
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_pev_eq_sum_range_6018055aec67

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
open Topology Filter Polynomial
noncomputable section
variable {d : ℕ} {y₀ : Fin d → ℂ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {σ : Type} [Fintype σ] (w : σ → ℂ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (ℓ : (σ → ℂ) →L[ℂ] ℂ) (H : (analyticSubring (A w))[X]) :
    AnalyticAt ℂ (fun z => pev (A z) (ℓ z) H) w := by
  have e : (fun z => pev (A z) (ℓ z) H) =
      fun z => ∑ i ∈ Finset.range (H.natDegree + 1), (H.coeff i : (Fin d → ℂ) → ℂ) (A z) * ℓ z ^ i :=
    funext fun z => pev_eq_sum_range H (Nat.lt_succ_self _) _ _
  rw [e]
  refine Finset.analyticAt_fun_sum _ fun i _ => ?_
  exact (AnalyticAt.comp (g := ((H.coeff i : analyticSubring (A w)) : (Fin d → ℂ) → ℂ))
    (H.coeff i).2 (A.analyticAt w)).mul ((ℓ.analyticAt w).pow i)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
