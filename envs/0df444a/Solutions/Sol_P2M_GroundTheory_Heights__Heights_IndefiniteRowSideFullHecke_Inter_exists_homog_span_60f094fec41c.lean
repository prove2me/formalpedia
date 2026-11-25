-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_exists_homog_span_60f094fec41c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:40:21.558007+00:00
-- url     : https://prove2.me/submissions/f9e9a812-b44e-4e6a-8200-fc146318699c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ProjLineRankTwoPushforwardHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleMultiHomogGrad
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleMultiHomogSpan
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_ker_toFn_0318e751caee
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_evalAt_genPt_cfdf05393d79
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_weightedHomogeneousComponent_mul_of_left_31978d42d8fa


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
omit [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution [DecidableEq K] (P : Ideal (MRing ι)) [P.IsPrime]
    (hP : ∀ f ∈ P, ∀ b, weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f ∈ P)
    {t N1 n : ℕ} (c : Fin t → Fin N1 → MRing ι) (m : K → ℕ)
    (hc : ∀ r j, IsWeightedHomogeneous (NumbersDVR.blockWeight ι) (c r j) m)
    (B : Fin n → Fin N1 → FnField P)
    (hB : ∀ a, B a ∈ LinearMap.ker (Matrix.mulVecLin (Matrix.of fun r j => evalAt (genPt P) (c r j)))) :
    ∃ (S : Type) (_ : Fintype S) (V : S → Fin N1 → MRing ι) (γ : S → K → ℕ),
      (∀ s j, IsWeightedHomogeneous (NumbersDVR.blockWeight ι) (V s j) (γ s)) ∧
      (∀ s, (fun j => toFn P (V s j)) ∈
        LinearMap.ker (Matrix.mulVecLin (Matrix.of fun r j => evalAt (genPt P) (c r j)))) ∧
      ∀ a, B a ∈ Submodule.span (FnField P) (Set.range fun s j => toFn P (V s j)) := by
  classical
  set w := NumbersDVR.blockWeight ι
  choose δ hδ using fun a => IsLocalization.exist_integer_multiples (nonZeroDivisors (MRing ι ⧸ P))
    (Finset.univ : Finset (Fin N1)) (B a)
  have hlift : ∀ a j, ∃ L : MRing ι, toFn P L = (δ a : MRing ι ⧸ P) • B a j := by
    intro a j
    obtain ⟨r, hr⟩ := hδ a j (Finset.mem_univ j)
    obtain ⟨L, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact ⟨L, hr⟩
  choose L hL using hlift
  have hL' : ∀ a j, toFn P (L a j) = algebraMap (MRing ι ⧸ P) (FnField P) (δ a) * B a j :=
    fun a j => by rw [hL a j]; exact Algebra.smul_def (δ a : MRing ι ⧸ P) (B a j)
  have hrow : ∀ a r, ∑ j, c r j * L a j ∈ P := by
    intro a r
    have h0 : ∑ j, evalAt (genPt P) (c r j) * B a j = 0 := by
      have := congrFun (LinearMap.mem_ker.mp (hB a)) r
      simpa [Matrix.mulVec, dotProduct] using this
    rw [← ker_toFn P, RingHom.mem_ker, map_sum]
    simp only [map_mul, hL', ← evalAt_genPt]
    rw [show ∑ j, evalAt (genPt P) (c r j) * (algebraMap (MRing ι ⧸ P) (FnField P) (δ a) * B a j) =
        algebraMap (MRing ι ⧸ P) (FnField P) (δ a) * ∑ j, evalAt (genPt P) (c r j) * B a j by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring]
    rw [h0, mul_zero]
  let D : Finset (K → ℕ) := Finset.univ.biUnion fun aj : Fin n × Fin N1 =>
    (L aj.1 aj.2).support.image (Finsupp.weight w)
  have hsum : ∀ a j, ∑ γ ∈ D, weightedHomogeneousComponent w γ (L a j) = L a j := by
    intro a j
    conv_rhs => rw [← sum_weightedHomogeneousComponent w (L a j)]
    refine (finsum_eq_sum_of_support_subset _ fun γ hγ => ?_).symm
    rw [Function.mem_support] at hγ
    by_contra hD
    refine hγ (weightedHomogeneousComponent_eq_zero' γ (L a j) fun d hd hdγ => hD ?_)
    exact Finset.mem_biUnion.mpr ⟨(a, j), Finset.mem_univ _, Finset.mem_image.mpr ⟨d, hd, hdγ⟩⟩
  refine ⟨Fin n × D, inferInstance, fun s j => weightedHomogeneousComponent w s.2 (L s.1 j), fun s => s.2,
    fun s j => weightedHomogeneousComponent_isWeightedHomogeneous _ _, ?_, ?_⟩
  · intro s
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    funext r
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply, evalAt_genPt, ← map_mul,
      ← map_sum]
    rw [← RingHom.mem_ker, ker_toFn]
    rw [show ∑ j, c r j * weightedHomogeneousComponent w s.2 (L s.1 j) =
        weightedHomogeneousComponent w (s.2 + m) (∑ j, c r j * L s.1 j) by
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => (weightedHomogeneousComponent_mul_of_left (hc r j) _ _).symm]
    exact hP _ (hrow s.1 r) _
  · intro a
    have hδ0 : algebraMap (MRing ι ⧸ P) (FnField P) (δ a) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (δ a).2
    have hBa : B a = (algebraMap (MRing ι ⧸ P) (FnField P) (δ a))⁻¹ •
        ∑ γ : D, fun j => toFn P (weightedHomogeneousComponent w γ (L a j)) := by
      funext j
      simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, ← map_sum]
      rw [Finset.sum_coe_sort D (fun γ => weightedHomogeneousComponent w γ (L a j)), hsum, hL',
        ← mul_assoc, inv_mul_cancel₀ hδ0, one_mul]
    rw [hBa]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun γ _ => Submodule.subset_span ⟨(a, γ), rfl⟩)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
