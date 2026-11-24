-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HolomorphicFibreInfinite_kernel_eq_of_maximal_c99173e4ddf6
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:27.314863+00:00
-- url     : https://prove2.me/submissions/f432de10-59ab-4128-abb8-086c4967e3bb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicFibreInfinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PImplicitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHolomorphicFibreInfinite

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
open Topology Metric
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.HolomorphicFibreInfinite
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.HolomorphicFibreInfinite
theorem _root_.solution {k d r : ℕ} (A : (Fin k → ℂ) →L[ℂ] (Fin d → ℂ)) (v : Fin r → Fin k → ℂ)
    (Λ : (Fin d → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (hmax : ∀ u : Fin (r + 1) → Fin k → ℂ, ¬ LinearIndependent ℂ (fun j => A (u j)))
    (hind : LinearIndependent ℂ (fun j => Λ (A (v j)))) {x : Fin k → ℂ} (hx : Λ (A x) = 0) :
    A x = 0 := by
  have hv : LinearIndependent ℂ (fun j => A (v j)) := LinearIndependent.of_comp Λ hind
  by_cases hs : A x ∈ Submodule.span ℂ (Set.range fun j => A (v j))
  · obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hs
    have h0 : ∑ j, c j • Λ (A (v j)) = 0 := by
      rw [← hx, ← hc, map_sum]
      simp only [map_smul]
    have hc0 := Fintype.linearIndependent_iff.1 hind c h0
    rw [← hc]
    simp [hc0]
  · exfalso
    apply hmax (Fin.cons x v)
    have hfun : (fun j => A ((Fin.cons x v : Fin (r + 1) → Fin k → ℂ) j)) =
        (Fin.cons (A x) (fun j => A (v j)) : Fin (r + 1) → Fin d → ℂ) := by
      funext j
      refine Fin.cases ?_ (fun i => ?_) j <;> simp
    rw [hfun]
    exact hv.finCons hs
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.HolomorphicFibreInfinite
