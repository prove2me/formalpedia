-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_ker_genMap_le_7f717af17469
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:03:15.479728+00:00
-- url     : https://prove2.me/submissions/46a57fd9-b707-48c6-a5e5-6f62c1f35379

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ProjLineRankTwoPushforwardHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleMultiHomogGrad
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleMultiHomogSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution (P : Ideal (MRing ι)) {N1 : ℕ} {S S' : Type} [Fintype S] [Fintype S']
    (v : S → Fin N1 → FnField P) (v' : S' → Fin N1 → FnField P)
    (h : ∀ s', v' s' ∈ Submodule.span (FnField P) (Set.range v)) :
    RingHom.ker (genMap P v) ≤ RingHom.ker (genMap P v') := by
  choose G hG using fun s' => (Submodule.mem_span_range_iff_exists_fun (FnField P)).mp (h s')
  let σ : MvPolynomial S (FnField P) →+* MvPolynomial S' (FnField P) :=
    (aeval fun s => ∑ s', C (G s' s) * X s' : MvPolynomial S (FnField P) →ₐ[FnField P] _).toRingHom
  have key : genMap P v' = σ.comp (genMap P v) := by
    refine MvPolynomial.ringHom_ext (fun z => by simp) ?_
    rintro ⟨k | u, i⟩
    · simp [genMap, σ]
    · change Fin N1 at i
      simp only [genMap, RingHom.coe_comp, Function.comp_apply, eval₂Hom_X', map_sum, map_mul, σ,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, aeval_X, algebraMap_eq]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s' _ => ?_
      have hGi := congrFun (hG s') i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hGi
      rw [← hGi, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [map_mul]
      ring
  intro f hf
  rw [RingHom.mem_ker] at hf ⊢
  rw [key, RingHom.comp_apply, hf, map_zero]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
