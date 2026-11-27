-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OneBlockPointDeg_proof_1e1e307e1416
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:21:39.731672+00:00
-- url     : https://prove2.me/submissions/ee68b8f6-0c0d-46e6-b71e-a83a03987e9a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartRankAdjoin
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_POneBlockPointDeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OneBlockPointDeg_isMultiHomog_of_isHomogeneous_03061861cacf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OneBlockPointDeg_aeval_homog_cb7eebaf88c6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OneBlockPointDeg_ringKrullDim_adjoin_eq_one_3d5c92006526
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartRankAdjoin_proof_6c9e7d5dfa01
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_proof_19b16af12153


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
noncomputable section
open OneBlockPointDeg
namespace GroundTheory.Heights₂.Heights
namespace OneBlockPointDeg
theorem _root_.solution : OneBlockPointDeg.Statement := by
  classical
  intro Φ Φ' _ _ _ K _ ι _ k₀ hK w c hc hfin htr
  set r : (Σ k, ι k) → Φ' := fun p => w p / w ⟨k₀, c k₀⟩ with hr
  set L := Algebra.adjoin Φ (Set.range r) with hL
  have hz : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => by obtain rfl := hK k; exact hc
  have hcard : Fintype.card K = 1 := Fintype.card_eq_one_iff.mpr ⟨k₀, hK⟩
  have hrL : ∀ p, r p ∈ L := fun p => Algebra.subset_adjoin ⟨p, rfl⟩

  have hcomp : ∀ f ∈ RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ'), ∀ n,
      homogeneousComponent n f ∈ RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ') := by
    intro f hf n
    have hmem : ∀ g : MRingOver Φ ι, aeval r g ∈ L := fun g => by
      rw [hL, ← aeval_range]; exact AlgHom.mem_range_self _ g
    let P : Polynomial L := ∑ i ∈ Finset.range (f.totalDegree + 1),
      Polynomial.monomial i ⟨aeval r (homogeneousComponent i f), hmem _⟩
    have hP : Polynomial.aeval (w ⟨k₀, c k₀⟩) P = 0 := by
      have h0 := RingHom.mem_ker.mp hf
      rw [← sum_homogeneousComponent f, map_sum] at h0
      rw [← h0, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Polynomial.aeval_monomial, ← aeval_homog hK hc (homogeneousComponent_isHomogeneous i f)]
      rfl
    have hP0 := (transcendental_iff.mp htr) P hP
    rw [RingHom.mem_ker, ← aeval_homog hK hc (homogeneousComponent_isHomogeneous n f)]
    by_cases hn : n < f.totalDegree + 1
    · have h1 := congrArg (fun q : Polynomial L => q.coeff n) hP0
      simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finset.sum_ite_eq',
        Finset.mem_range, hn, if_true, Polynomial.coeff_zero] at h1
      rw [show aeval r (homogeneousComponent n f) = ((⟨_, hmem _⟩ : L) : Φ') from rfl, h1]
      simp
    · rw [homogeneousComponent_eq_zero (φ := f) (n := n) (by omega)]; simp
  have hchart : IsChart (RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ')) c := fun k => by
    rw [RingHom.mem_ker, aeval_X]; exact hz k

  have hhom : IsMultiHomogIdeal (RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ')) := by
    refine ⟨{g | g ∈ RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ') ∧ ∃ a, IsMultiHomog g a}, fun g hg => hg.2,
      le_antisymm (fun f hf => ?_)
      (Ideal.span_le.mpr fun g hg => hg.1)⟩
    rw [← sum_homogeneousComponent f]
    exact Ideal.sum_mem _ fun i _ => Ideal.subset_span
      ⟨hcomp f hf i, _, isMultiHomog_of_isHomogeneous hK (homogeneousComponent_isHomogeneous i f)⟩
  refine ⟨⟨⟨RingHom.ker_isPrime _, hhom, fun k => ⟨c k, hchart k⟩⟩, ?_⟩, hchart, ?_⟩
  ·
    have hs : Set.range w ⊆ Algebra.adjoin Φ (Set.range r ∪ {w ⟨k₀, c k₀⟩}) := by
      rintro _ ⟨p, rfl⟩
      rw [show w p = r p * w ⟨k₀, c k₀⟩ from (div_mul_cancel₀ _ hc).symm]
      exact Subalgebra.mul_mem _ (Algebra.subset_adjoin (Or.inl ⟨p, rfl⟩))
        (Algebra.subset_adjoin (Or.inr rfl))
    rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerEquivRange (aeval w : MRingOver Φ ι →ₐ[Φ] Φ')).toRingEquiv,
      aeval_range, ringKrullDim_adjoin_eq_one w (Set.range r) _ htr (Algebra.subset_adjoin ⟨_, rfl⟩) hs, hcard]
    rfl
  ·
    have halg : ∀ x ∈ Set.range r, IsAlgebraic Φ x := by
      rintro _ ⟨p, rfl⟩
      exact (IsAlgebraic.of_finite Φ (⟨r p, hrL p⟩ : L)).algHom L.val
    have e : (fun q : Σ k, ι k => w q / w ⟨q.1, c q.1⟩) = r := by
      funext ⟨k, i⟩; obtain rfl := hK k; rfl
    rw [Inter.ChartRankAdjoin.proof K ι Φ Φ' w c hz hhom, e,
      ← IntermediateField.finrank_eq_finrank_subalgebra,
      IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg]
end OneBlockPointDeg
end GroundTheory.Heights₂.Heights
