-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IsolatedFibreOpenOfGeneric_finiteProjection_near_4900b9fa8b95
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:28:02.68086+00:00
-- url     : https://prove2.me/submissions/81193fa4-0aec-41e8-8d55-1f8c0f2392f2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_IsClosedComplexSubmanifoldIn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIsolatedFibreOpenFixed

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
open MvPolynomial Filter Topology Matrix Metric
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsolatedFibreOpenOfGeneric
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsolatedFibreOpenOfGeneric
theorem _root_.solution (hGen : GenericProjectionFinite.Statement) {n k : ℕ}
    {J : Ideal (MvPolynomial (Fin n) ℂ)} (hJ : IsAffVariety J k) (A : Matrix (Fin k) (Fin n) ℂ) :
    ∃ M : Matrix (Fin k) (Fin n) ℂ,
      ∀ᶠ t in 𝓝[≠] (0 : ℂ), IsFiniteProjection J (A + t • (M - A)).mulVecLin := by
  obtain ⟨⟨S, ⟨M, f, hfS, hf⟩, hS⟩, -⟩ := hGen n k J hJ.isPrime hJ.dim
  refine ⟨M, ?_⟩
  set a : Fin k × Fin n → ℂ := fun p => A p.1 p.2
  set b : Fin k × Fin n → ℂ := fun p => (M - A) p.1 p.2
  have hg : ∀ t : ℂ, eval (fun p : Fin k × Fin n => (A + t • (M - A)) p.1 p.2) f = eval (a + t • b) f :=
    fun t => rfl
  have han : ∀ t : ℂ, AnalyticAt ℂ (fun t : ℂ => eval (a + t • b) f) t := fun t =>
    (AnalyticOnNhd.eval_mvPolynomial f _ trivial).comp
      (analyticAt_const.add (analyticAt_id.smul analyticAt_const))
  rcases (han 0).eventually_eq_zero_or_eventually_ne_zero with h0 | hne
  · exfalso
    have hz := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero (fun t _ => han t)
      isPreconnected_univ (Set.mem_univ 0) h0 (Set.mem_univ 1)
    apply hf
    have h1 : (fun p : Fin k × Fin n => M p.1 p.2) = a + (1 : ℂ) • b := by
      funext p
      simp [a, b]
    rw [h1]
    exact hz
  · filter_upwards [hne] with t ht
    exact hS _ ⟨f, hfS, by rw [hg]; exact ht⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsolatedFibreOpenOfGeneric
