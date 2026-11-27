-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceBranches_proof_9c27a3cfa563
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:08:14.541577+00:00
-- url     : https://prove2.me/submissions/5f9f75bd-2b99-4248-9eea-c4a5a4f083ef

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceBranches
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceImmersiveGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchProperAtPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceMatricesOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StImplicitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceBranches
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_zeroSet_sliceIdeal_81bd9c1d3ddc


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
open MvPolynomial Matrix ComplexSets Filter Topology
namespace GroundTheory.Heights₂.Heights
namespace SliceBranches
theorem _root_.solution (hI : IndefiniteRowSideFullHecke.ComplexSets.SliceImmersiveGeneral.Statement)
    (hB : IndefiniteRowSideFullHecke.ComplexSets.BranchProperAtPoint.Statement) (hM : SliceMatricesOpen.Statement)
    (hC : ImplicitCurve.Statement) : SliceBranches.Statement := by
  intro n d J W u p m γ ord hJ hdim hu hW hp hcov hsl hdisj hord U Λ hUo hUd hΛ
  obtain ⟨N₁, hN₁, hcov₁⟩ := hcov
  obtain ⟨V, hV, hVd⟩ := hI n d J W u p m γ hJ hdim hu hW hp hsl
  have hOp : interior (N₁ ∩ V) ∈ 𝓝 p := interior_mem_nhds.2 (inter_mem hN₁ hV)
  obtain ⟨y, hyO, hyW, hyU⟩ := mem_closure_iff_nhds.1 (hUd hp) _ hOp
  obtain ⟨q, ⟨hqO, hqU⟩, hqW, hqs⟩ := mem_closure_iff_nhds.1 (hVd ⟨hyW, (interior_subset hyO).2⟩)
    (interior (N₁ ∩ V) ∩ U) (inter_mem (isOpen_interior.mem_nhds hyO) (hUo.mem_nhds hyU))
  have hqN : N₁ ∈ 𝓝 q := mem_of_superset (mem_interior_iff_mem_nhds.1 hqO) fun x hx => hx.1
  choose s hs hs0 hsq hsinj using hqs
  obtain ⟨hGo, hGne⟩ := hM n d m (fun b => (γ b).toFun) s
    (fun b => (γ b).differentiableOn.differentiableAt (Metric.isOpen_ball.mem_nhds (hs b))) hsinj
  obtain ⟨L, hLG, hLΛ⟩ := (hΛ q ⟨hqW, hqU⟩).inter_open_nonempty _ hGo hGne
  choose r hr φ hφd hφ0 hφ P hP hPφ using fun b =>
    hC n d (γ b).toFun (γ b).radius L (s b) (γ b).differentiableOn (hs b) (hLG b)
  choose ε hεpos hεP using fun b =>
    hB n (d + 1) J u p q m γ hJ hdim hu ⟨N₁, hqN, hcov₁⟩ hdisj b (s b) (hs b) (hsq b) (P b) (hP b)
  have hφ0' : ∀ b, ∀ τ ∈ Metric.ball (0 : Fin 1 → ℂ) (r b), φ b τ 0 = τ 0 := fun b τ hτ => by
    rw [(hφ b τ hτ).2.1, hs0 b, zero_add]
  let c : Fin m → VarBranch (sliceIdeal J L q) 1 q := fun b =>
    { radius := r b
      radius_pos := hr b
      toFun := fun τ => (γ b).toFun (φ b τ)
      differentiableOn := (γ b).differentiableOn.comp (hφd b) fun τ hτ => (hφ b τ hτ).1
      injOn := fun τ hτ τ' hτ' h => by
        have h0 := congrArg (fun t => t 0) ((γ b).injOn (hφ b τ hτ).1 (hφ b τ' hτ').1 h)
        simp only [hφ0' b τ hτ, hφ0' b τ' hτ'] at h0
        funext i
        rwa [Subsingleton.elim i 0]
      map_zero := by simp only [hφ0 b, hsq b]
      mapsTo := fun τ hτ => by
        rw [zeroSet_sliceIdeal]
        exact ⟨(γ b).mapsTo (hφ b τ hτ).1, by rw [Set.mem_ofPred_eq, (hφ b τ hτ).2.2, hsq b]⟩ }
  have himg : ∀ b, (c b).image ⊆ (γ b).image := by
    rintro b _ ⟨τ, hτ, rfl⟩
    exact ⟨φ b τ, (hφ b τ hτ).1, rfl⟩
  refine ⟨q, ⟨hqW, hqU⟩, L, hLΛ, c, ⟨N₁ ∩ ⋂ b, Metric.ball q (ε b),
    inter_mem hqN (iInter_mem.2 fun b => Metric.ball_mem_nhds q (hεpos b)), ?_⟩,
    fun b b' hbb' x hx => hdisj b b' hbb' ⟨himg b hx.1, himg b' hx.2⟩, fun b => ?_⟩
  · rintro x ⟨hxs, hxN, hxε⟩
    rw [zeroSet_sliceIdeal] at hxs
    obtain ⟨b, t, ht, rfl⟩ : ∃ b, ∃ t ∈ Metric.ball 0 (γ b).radius, (γ b).toFun t = x := by
      simpa [VarBranch.image] using hcov₁ ⟨hxs.1, hxN⟩
    obtain ⟨τ, hτ, rfl⟩ := hPφ b t (hεP b t ht (Set.mem_iInter.1 hxε b))
      (by rw [hxs.2, hsq b])
    exact Set.mem_iUnion.2 ⟨b, τ, hτ, rfl⟩
  · obtain ⟨H, hHd, hH0, hHe⟩ := hord b
    refine ⟨fun τ => H (φ b τ), hHd.comp (hφd b) (fun τ hτ => (hφ b τ hτ).1),
      fun τ hτ => hH0 _ (hφ b τ hτ).1, fun τ hτ => ?_⟩
    show linEval u ((γ b).toFun (φ b τ)) = τ 0 ^ ord b * H (φ b τ)
    have h := hHe _ (hφ b τ hτ).1
    rw [hφ0' b τ hτ] at h
    exact h
end SliceBranches
end GroundTheory.Heights₂.Heights
