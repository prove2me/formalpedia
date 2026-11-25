-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_HilbertIncrement_isMultigrading_quotPiece_4a2432f4cf83
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:30:40.176707+00:00
-- url     : https://prove2.me/submissions/4a7f8f85-acce-4867-99bb-7c10173b2612

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ColonSpanSingletonEqOfNotMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertIncrement
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_HilbertIncrement_component_intWeight_mem_b9cf5cbc71b8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_isMultigrading_ring_97b61877372f


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertIncrement
variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertIncrement
theorem _root_.solution [Fintype K] {J : Ideal (MRing ι F)} (hJ : IsMultiHomogIdeal J) :
    IsMultigrading ι (MRing ι F ⧸ J) (quotPiece J) where
  internal := by
    classical
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    constructor
    · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
      intro s v hv hsum m hm
      have hex : ∀ i ∈ s, ∃ y ∈ ringPiece (F := F) (ι := ι) i,
          (Ideal.Quotient.mkₐ F J).toLinearMap y = v i := fun i hi => Submodule.mem_map.mp (hv i hi)
      choose! x hx hxv using hex
      have hy : (∑ i ∈ s, x i) ∈ J := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
        rw [← hsum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [← hxv i hi]
        rfl
      have hc := component_intWeight_mem hJ hy m
      rw [map_sum] at hc
      have hcs : (∑ i ∈ s, weightedHomogeneousComponent (intWeight (ι := ι)) m (x i)) = x m := by
        rw [Finset.sum_eq_single m]
        · rw [weightedHomogeneousComponent_of_mem (hx m hm), if_pos rfl]
        · intro j hj hjm
          rw [weightedHomogeneousComponent_of_mem (hx j hj), if_neg (Ne.symm hjm)]
        · intro h
          exact absurd hm h
      rw [hcs] at hc
      rw [← hxv m hm]
      simpa [Ideal.Quotient.eq_zero_iff_mem] using hc
    · show (⨆ m, (ringPiece (F := F) (ι := ι) m).map (Ideal.Quotient.mkₐ F J).toLinearMap) = ⊤
      rw [← Submodule.map_iSup]
      show Submodule.map _ (⨆ i, weightedHomogeneousSubmodule F (intWeight (ι := ι)) i) = ⊤
      rw [(weightedDecomposition F (intWeight (ι := ι))).isInternal.submodule_iSup_eq_top,
        Submodule.map_top, LinearMap.range_eq_top]
      exact Ideal.Quotient.mkₐ_surjective F J
  smul_mem := by
    intro v m x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    refine Submodule.mem_map.mpr ⟨(X v : MRing ι F) • y, isMultigrading_ring.smul_mem v m y hy, ?_⟩
    simp only [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, smul_eq_mul, map_mul]
    rfl
end GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertIncrement
