-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IrreducibleGermPointsOffDiscriminant_proof_d09f4d6f8b46
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:58:17.473051+00:00
-- url     : https://prove2.me/submissions/c9b87d49-12b6-4bea-8aac-ef475117a21c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermPointsOffDiscriminant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermPrimitiveForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormSheetedOffDiscriminant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormSheetedPointsNear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StManifoldZerosComplementConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIrreducibleGermPointsOffDiscriminant
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isRegularPointOf_ball_b673d809f104

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
open Topology Metric Filter Set
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace IrreducibleGermPointsOffDiscriminant
theorem _root_.solution (hPF : IrreducibleGermPrimitiveForm.Statement)
    (hSh : PrimitiveFormSheetedOffDiscriminant.Statement) (hNear : PrimitiveFormSheetedPointsNear.Statement)
    (hConn : ManifoldZerosComplementConnected.Statement) :
    IrreducibleGermPointsOffDiscriminant.Statement := by
  intro σ _ X x d A hX hirr hiso hinj
  obtain ⟨ℓ, N, a, δ, q, ha, hδ, hq, hδ0, hp, hsep, hqz⟩ := hPF σ X x d A hX hirr hiso hinj
  obtain ⟨M, hM, hMsh⟩ := hSh σ X x d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδ0 hp hsep hqz
  have hnear := hNear σ X x d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδ0 hp hsep hqz
  refine ⟨δ, hδ, hδ0, fun W hW => ?_⟩
  obtain ⟨W₀, hW₀, hiso'⟩ := hiso
  obtain ⟨Nn, k, f, hNo, hxN, hf, hXN⟩ := hX
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (inter_mem hW hM) (inter_mem hW₀ (hNo.mem_nhds hxN)))
  have hr2 : 0 < r / 2 := half_pos hr
  have hcb : closedBall x (r / 2) ⊆ (W ∩ M) ∩ (W₀ ∩ Nn) := (closedBall_subset_ball (half_lt_self hr)).trans hrsub

  set K : Set (σ → ℂ) := closedBall x (r / 2) ∩ ⋂ i, (closedBall x (r / 2) ∩ f i ⁻¹' {0}) with hK
  have hKc : IsCompact K := by
    refine (isCompact_closedBall x (r / 2)).of_isClosed_subset ?_ inter_subset_left
    refine isClosed_closedBall.inter (isClosed_iInter fun i => ?_)
    exact ((hf i).continuousOn.mono fun z hz => (hcb hz).2.2).preimage_isClosed_of_isClosed
      isClosed_closedBall isClosed_singleton
  have hKmem : ∀ z, z ∈ K ↔ z ∈ closedBall x (r / 2) ∧ z ∈ X := by
    intro z
    simp only [hK, mem_inter_iff, mem_iInter, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨hz, h0⟩
      have : z ∈ {z | z ∈ Nn ∧ ∀ i, f i z = 0} := ⟨(hcb hz).2.2, fun i => (h0 i).2⟩
      rw [← hXN] at this
      exact ⟨hz, this.1⟩
    · rintro ⟨hz, hzX⟩
      have : z ∈ X ∩ Nn := ⟨hzX, (hcb hz).2.2⟩
      rw [hXN] at this
      exact ⟨hz, fun i => ⟨hz, this.2 i⟩⟩
  have hSc : IsCompact (K ∩ sphere x (r / 2)) := hKc.inter_right isClosed_sphere
  have hAS : A x ∉ A '' (K ∩ sphere x (r / 2)) := by
    rintro ⟨z, ⟨hzK, hzs⟩, hAz⟩
    have hzx : z = x := hiso' z ⟨((hKmem z).mp hzK).2, (hcb ((hKmem z).mp hzK).1).2.1⟩ hAz
    rw [hzx, mem_sphere, dist_self] at hzs
    exact hr2.ne hzs
  obtain ⟨ε₁, hε₁, hε₁S⟩ := Metric.isOpen_iff.mp (hSc.image A.continuous).isClosed.isOpen_compl (A x) hAS
  obtain ⟨ε₂, hε₂, hε₂a⟩ := hδ.exists_ball_analyticOnNhd
  set D := ball (A x) (min ε₁ ε₂) with hD
  have hε : 0 < min ε₁ ε₂ := lt_min hε₁ hε₂
  have hDa : AnalyticOnNhd ℂ δ D := hε₂a.mono (ball_subset_ball (min_le_right _ _))

  set T := D \ {y | δ y = 0} with hT
  have hTo : IsOpen T := hDa.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton
  have hTc : IsPreconnected T := by
    refine hConn (Fin d) D δ (convex_ball _ _).isPreconnected (isRegularPointOf_ball _ _) hDa ?_
    obtain ⟨y, hy0, hyD⟩ := ((Filter.not_eventually.mp hδ0).and_eventually (ball_mem_nhds _ hε)).exists
    exact ⟨y, hyD, hy0⟩

  set u : Set (Fin d → ℂ) := T ∩ A '' (X ∩ ball x (r / 2)) with hu
  have huo : IsOpen u := by
    refine isOpen_iff_mem_nhds.mpr ?_
    rintro y ⟨hyT, z, ⟨hzX, hzb⟩, rfl⟩
    obtain ⟨O, V, g, hO, hV, hzV, hg, hAg, hXV⟩ := hMsh z ⟨hzX, (hcb (ball_subset_closedBall hzb)).1.2⟩ hyT.2
    obtain ⟨t₀, ht₀, hgt₀⟩ : z ∈ g '' O := hXV ▸ ⟨hzX, hzV⟩
    have hAz : A z = t₀ := by rw [← hgt₀]; exact hAg t₀ ht₀
    rw [hAz] at hyT ⊢
    have hpre : g ⁻¹' (V ∩ ball x (r / 2)) ∈ 𝓝 t₀ :=
      (hg t₀ ht₀).continuousAt.preimage_mem_nhds ((hV.inter isOpen_ball).mem_nhds (hgt₀ ▸ ⟨hzV, hzb⟩))
    filter_upwards [hTo.mem_nhds hyT, hO.mem_nhds ht₀, hpre] with t ht htO htg
    have hgX : g t ∈ X ∩ V := hXV ▸ ⟨t, htO, rfl⟩
    exact ⟨ht, g t, ⟨hgX.1, htg.2⟩, hAg t htO⟩
  have hune : (T ∩ u).Nonempty := by
    have hU : ball x (r / 2) ∩ A ⁻¹' D ∈ 𝓝 x :=
      inter_mem (ball_mem_nhds x hr2) (A.continuous.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hε))
    obtain ⟨z, ⟨hzX, hzb, hzD⟩, hδz, -⟩ := hnear _ hU
    exact ⟨A z, ⟨hzD, hδz⟩, ⟨hzD, hδz⟩, z, ⟨hzX, hzb⟩, rfl⟩
  have hucl : closure u ∩ T ⊆ u := by
    rintro y ⟨hycl, hyT⟩
    have hsubK : u ⊆ A '' K := by
      rintro _ ⟨-, z, ⟨hzX, hzb⟩, rfl⟩
      exact ⟨z, (hKmem z).mpr ⟨ball_subset_closedBall hzb, hzX⟩, rfl⟩
    obtain ⟨z, hzK, rfl⟩ := (hKc.image A.continuous).isClosed.closure_subset_iff.mpr hsubK hycl
    obtain ⟨hzcb, hzX⟩ := (hKmem z).mp hzK
    have hzb : z ∈ ball x (r / 2) := by
      refine mem_ball.mpr (lt_of_le_of_ne (mem_closedBall.mp hzcb) fun hzs => ?_)
      exact hε₁S (ball_subset_ball (min_le_left _ _) hyT.1) ⟨z, ⟨hzK, mem_sphere.mpr hzs⟩, rfl⟩
    exact ⟨hyT, z, ⟨hzX, hzb⟩, rfl⟩
  have hTu : T ⊆ u := hTc.subset_of_closure_inter_subset huo hune hucl
  filter_upwards [ball_mem_nhds (A x) hε] with y hy hδy
  obtain ⟨-, z, ⟨hzX, hzb⟩, hzy⟩ := hTu ⟨hy, hδy⟩
  exact ⟨z, ⟨hzX, (hcb (ball_subset_closedBall hzb)).1.1⟩, hzy⟩
end IrreducibleGermPointsOffDiscriminant
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
