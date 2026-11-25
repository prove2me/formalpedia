-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RelAlgClosureFinite_linearIndependent_adjoin_bb5beed916b1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:28:08.969858+00:00
-- url     : https://prove2.me/submissions/8f5cc543-1939-4eff-8727-73b6cd1e99e6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StRelAlgClosureFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRelAlgClosureFinite

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial IntermediateField.algebraAdjoinAdjoin
namespace GroundTheory.Heights₂.Heights.Inter
namespace RelAlgClosureFinite
theorem _root_.solution {K L : Type*} [Field K] [Field L] [Algebra K L]
    (M : IntermediateField K L) {σ : Type*} {x : σ → L} (hx : AlgebraicIndependent M x)
    {ι : Type*} {m : ι → M} (hm : LinearIndependent K m) :
    LinearIndependent (Algebra.adjoin K (Set.range x)) (fun i => (m i : L)) := by
  rw [linearIndependent_iff'] at hm ⊢
  intro s g hg i hi
  have hp : ∀ j, ∃ p : MvPolynomial σ K, aeval x p = (g j : L) := fun j => by
    have h : (g j : L) ∈ (aeval x : MvPolynomial σ K →ₐ[K] L).range := by
      rw [← Algebra.adjoin_range_eq_range_aeval]
      exact (g j).2
    exact (AlgHom.mem_range _).1 h
  choose p hp using hp
  have hP : (∑ j ∈ s, C (m j) * map (algebraMap K M) (p j) : MvPolynomial σ M) = 0 := by
    apply hx.eq_zero_of_aeval_eq_zero
    rw [← hg]
    simp only [map_sum, map_mul, aeval_C, aeval_map_algebraMap, hp]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Subalgebra.smul_def, smul_eq_mul, mul_comm]
    rfl
  have hcoeff : ∀ d, ∀ j ∈ s, coeff d (p j) = 0 := fun d => by
    apply hm s (fun j => coeff d (p j))
    have := congrArg (coeff d) hP
    simp only [coeff_sum, coeff_C_mul, coeff_map, coeff_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, mul_comm]
  have hpi : p i = 0 := MvPolynomial.ext _ _ fun d => by rw [hcoeff d i hi, coeff_zero]
  apply Subtype.ext
  rw [← hp i, hpi, map_zero]
  rfl
end RelAlgClosureFinite
end GroundTheory.Heights₂.Heights.Inter
