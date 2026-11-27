-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IsolatedFibreOpenOfGeneric_proof_12cd564f4925
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:58:55.548193+00:00
-- url     : https://prove2.me/submissions/d495a3c4-dd5b-4f29-b07b-c1ddf71b1420

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_IsClosedComplexSubmanifoldIn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIsolatedFibreOpenFixed
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IsolatedFibreOpenOfGeneric_isClosed_zeroLocus_0d7acafb1441
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IsolatedFibreOpenOfGeneric_eval_linPoly_2c3dac8bdfd6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IsolatedFibreOpenOfGeneric_finiteProjection_near_4900b9fa8b95

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
theorem _root_.solution (hGen : GenericProjectionFinite.Statement) (hFin : FiniteMapOpen.Statement) :
    IsolatedFibreOpen.Statement := by
  intro n k J A x hJ hx ⟨W, hW, hiso⟩ W' hW'
  have hZc : IsClosed (zeroLocus J) := isClosed_zeroLocus J
  have hAc : ∀ B : Matrix (Fin k) (Fin n) ℂ, Continuous fun z : Fin n → ℂ => B *ᵥ z :=
    fun B => continuous_const.matrix_mulVec continuous_id

  obtain ⟨r0, hr0, hr0W⟩ := Metric.mem_nhds_iff.1 (inter_mem hW hW')
  have hr : 0 < r0 / 2 := half_pos hr0
  have hcb : closedBall x (r0 / 2) ⊆ W ∩ W' :=
    (closedBall_subset_ball (half_lt_self hr0)).trans hr0W
  have hSc : IsCompact (zeroLocus J ∩ closedBall x (r0 / 2)) :=
    (isCompact_closedBall x _).inter_left hZc
  have hKc : IsCompact (zeroLocus J ∩ sphere x (r0 / 2)) := (isCompact_sphere x _).inter_left hZc

  have hAK : A *ᵥ x ∉ (fun z => A *ᵥ z) '' (zeroLocus J ∩ sphere x (r0 / 2)) := by
    rintro ⟨z, ⟨hzZ, hzs⟩, hzA⟩
    have hzx : z = x := hiso z (hcb (sphere_subset_closedBall hzs)).1 hzZ hzA
    rw [hzx, mem_sphere, dist_self] at hzs
    exact hr.ne hzs
  obtain ⟨ε, hε, hεK⟩ := Metric.isOpen_iff.1 ((hKc.image (hAc A)).isClosed.isOpen_compl) _ hAK
  obtain ⟨M, hM⟩ := finiteProjection_near hGen hJ A
  obtain ⟨C, hC⟩ := hSc.exists_bound_of_continuousOn (hAc (M - A)).continuousOn
  have hAt : ∀ (t : ℂ) (z : Fin n → ℂ), (A + t • (M - A)) *ᵥ z = A *ᵥ z + t • ((M - A) *ᵥ z) :=
    fun t z => by rw [add_mulVec, smul_mulVec]
  have hclose : ∀ t : ℂ, ‖t‖ * C < ε / 4 → ∀ z ∈ zeroLocus J ∩ closedBall x (r0 / 2),
      dist ((A + t • (M - A)) *ᵥ z) (A *ᵥ z) < ε / 4 := by
    intro t ht z hz
    rw [dist_eq_norm, hAt, add_sub_cancel_left, norm_smul]
    exact (mul_le_mul_of_nonneg_left (hC z hz) (norm_nonneg t)).trans_lt ht

  have hstep : ∀ t : ℂ, IsFiniteProjection J (A + t • (M - A)).mulVecLin → ‖t‖ * C < ε / 4 →
      ball (A *ᵥ x) (ε / 4) ⊆
        (fun z => (A + t • (M - A)) *ᵥ z) '' (zeroLocus J ∩ closedBall x (r0 / 2)) := by
    intro t hfin ht
    set B := A + t • (M - A) with hB
    have hcomp : (Ideal.Quotient.mkₐ ℂ J).comp (aeval fun i => linPoly B.mulVecLin i) =
        projAlgHom J B.mulVecLin := by
      rw [MvPolynomial.comp_aeval]
      rfl
    have hTo : IsOpen ((fun z => B *ᵥ z) '' (zeroLocus J ∩ ball x (r0 / 2))) := by
      rw [isOpen_iff_mem_nhds]
      rintro _ ⟨z, ⟨hzZ, hzb⟩, rfl⟩
      have h := hFin n k J (fun i => linPoly B.mulVecLin i) hJ.isPrime (by rw [hcomp]; exact hfin.1)
        (by rw [hcomp]; exact hfin.2) z hzZ (ball x (r0 / 2)) (isOpen_ball.mem_nhds hzb)
      simpa only [eval_linPoly] using h
    have hTS : (fun z => B *ᵥ z) '' (zeroLocus J ∩ ball x (r0 / 2)) ⊆
        (fun z => B *ᵥ z) '' (zeroLocus J ∩ closedBall x (r0 / 2)) :=
      Set.image_mono (Set.inter_subset_inter_right _ ball_subset_closedBall)
    have hSim : IsClosed ((fun z => B *ᵥ z) '' (zeroLocus J ∩ closedBall x (r0 / 2))) :=
      (hSc.image (hAc B)).isClosed
    have hxS : x ∈ zeroLocus J ∩ closedBall x (r0 / 2) := ⟨hx, mem_closedBall_self hr.le⟩
    have hsub : ball (A *ᵥ x) (ε / 2) ⊆ (fun z => B *ᵥ z) '' (zeroLocus J ∩ ball x (r0 / 2)) := by
      refine (convex_ball _ _).isPreconnected.subset_of_closure_inter_subset hTo ?_ ?_
      · refine ⟨B *ᵥ x, ?_, x, ⟨hx, mem_ball_self hr⟩, rfl⟩
        rw [mem_ball]
        linarith [hclose t ht x hxS]
      · rintro _ ⟨hcl, hball⟩
        obtain ⟨z, hzS, rfl⟩ := closure_minimal hTS hSim hcl
        refine ⟨z, ⟨hzS.1, ?_⟩, rfl⟩
        by_contra hzb
        have hzs : z ∈ sphere x (r0 / 2) :=
          mem_sphere.2 (le_antisymm (mem_closedBall.1 hzS.2) (not_lt.1 (by simpa [mem_ball] using hzb)))
        apply hεK (show A *ᵥ z ∈ ball (A *ᵥ x) ε from ?_) ⟨z, ⟨hzS.1, hzs⟩, rfl⟩
        rw [mem_ball] at hball ⊢
        have h1 := hclose t ht z hzS
        rw [dist_comm] at h1
        linarith [dist_triangle (A *ᵥ z) (B *ᵥ z) (A *ᵥ x)]
    exact (ball_subset_ball (by linarith)).trans (hsub.trans hTS)

  have h0 : Tendsto (fun t : ℂ => ‖t‖ * C) (𝓝[≠] 0) (𝓝 0) := by
    have hc : Continuous fun t : ℂ => ‖t‖ * C := continuous_norm.mul continuous_const
    have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 0)
    simpa using h
  have hsmall : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ‖t‖ * C < ε / 4 := h0.eventually (gt_mem_nhds (by positivity))
  refine mem_of_superset (ball_mem_nhds (A *ᵥ x) (by positivity : (0 : ℝ) < ε / 4)) ?_
  intro y hy
  have hz : ∀ t : ℂ, ∃ z : Fin n → ℂ,
      (∃ w ∈ zeroLocus J ∩ closedBall x (r0 / 2), (A + t • (M - A)) *ᵥ w = y) →
        z ∈ zeroLocus J ∩ closedBall x (r0 / 2) ∧ (A + t • (M - A)) *ᵥ z = y := by
    intro t
    by_cases h : ∃ w ∈ zeroLocus J ∩ closedBall x (r0 / 2), (A + t • (M - A)) *ᵥ w = y
    · exact ⟨h.choose, fun _ => h.choose_spec⟩
    · exact ⟨x, fun h' => absurd h' h⟩
  choose zf hzf using hz
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ),
      zf t ∈ zeroLocus J ∩ closedBall x (r0 / 2) ∧ (A + t • (M - A)) *ᵥ zf t = y := by
    filter_upwards [hM, hsmall] with t h1 h2
    exact hzf t (hstep t h1 h2 hy)
  obtain ⟨a, haS, hacl⟩ := hSc (f := map zf (𝓝[≠] (0 : ℂ)))
    (le_principal_iff.2 (hev.mono fun t ht => ht.1))
  have hlim : Tendsto (fun t => A *ᵥ zf t) (𝓝[≠] (0 : ℂ)) (𝓝 y) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
    filter_upwards [hev] with t ht
    rw [← ht.2, hAt, sub_add_cancel_left, norm_neg, norm_smul]
    exact mul_le_mul_of_nonneg_left (hC _ ht.1) (norm_nonneg _)
  have hay : A *ᵥ a = y :=
    eq_of_nhds_neBot (hacl.map (hAc A).continuousAt (tendsto_map'_iff.2 hlim))
  exact ⟨a, ⟨haS.1, (hcb haS.2).2⟩, hay⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsolatedFibreOpenOfGeneric
