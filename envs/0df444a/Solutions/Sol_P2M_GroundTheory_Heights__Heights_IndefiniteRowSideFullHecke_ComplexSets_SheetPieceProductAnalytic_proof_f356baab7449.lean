-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_SheetPieceProductAnalytic_proof_f356baab7449
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:59:27.133212+00:00
-- url     : https://prove2.me/submissions/d03792db-3c10-4188-8d63-a3418391ca17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetPieceProductAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnbranchedFibreSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetPieceProductAnalytic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_SheetPieceProductAnalytic_tailL_cons_a65dbe17d6c8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_SheetPieceProductAnalytic_exists_ne_zero_of_open_fbf002cb46b2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_SheetPieceProductAnalytic_differentiableAt_prodFn_c88dec3fd0bb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_SheetPieceProductAnalytic_isBounded_prodFn_db45f8a99bed
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RiemannExtensionAnalytic_analyticOnNhd_of_differentiableOn_c966cce3f6fd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RiemannExtensionAnalytic_proof_9f4f3171a0d7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_proof_5560ddb795d4


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
open Topology Metric Filter
noncomputable section
open SheetPieceProductAnalytic
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace SheetPieceProductAnalytic
theorem _root_.solution (hsec : UnbranchedFibreSections.Statement) :
    SheetPieceProductAnalytic.Statement := by
  intro σ _ X w B d A D δ N U V ℓ hP hU hV hcov hdisj
  have hP' := hP
  obtain ⟨-, -, hD, hDc, -, -, -, hδ, hne, -, -, -⟩ := hP'
  have hW : IsOpen (tailL d ⁻¹' D) := hD.preimage (tailL d).continuous
  have hgd : DifferentiableOn ℂ (fun p => δ (tailL d p)) (tailL d ⁻¹' D) := fun p hp =>
    ((hδ _ hp).differentiableAt.comp p (tailL d).differentiableAt).differentiableWithinAt
  obtain ⟨F, hF, hFG⟩ := RiemannExtensionAnalytic.proof (d + 1) (tailL d ⁻¹' D) (fun p => δ (tailL d p))
    (prodFn X B U A ℓ) hW hgd (fun V' hV' hsub hne' => exists_ne_zero_of_open hδ hDc hne V' hV' hsub hne')
    (fun p hp => (differentiableAt_prodFn hsec ℓ hP hU hV hcov hdisj hp.1 hp.2).differentiableWithinAt)
    (fun p hp => isBounded_prodFn U ℓ hP hp)
  have hFa : AnalyticOnNhd ℂ F (tailL d ⁻¹' D) := RiemannExtensionAnalytic.analyticOnNhd_of_differentiableOn hW hF
  have hcons : ∀ z, tailL d (Fin.cons (ℓ z) (A z) : Fin (d + 1) → ℂ) = A z := fun z => tailL_cons _ _
  refine ⟨fun z => F (Fin.cons (ℓ z) (A z)), fun z hz => ?_, fun z hz hδz => ?_⟩
  · have hm : (Fin.cons (ℓ z) (A z) : Fin (d + 1) → ℂ) ∈ tailL d ⁻¹' D := by
      rw [Set.mem_preimage, hcons]
      exact hz
    have hlin : AnalyticAt ℂ (fun z => (Fin.cons (ℓ z) (A z) : Fin (d + 1) → ℂ)) z := by
      rw [analyticAt_pi_iff]
      intro i
      cases i using Fin.cases
      · simpa using ℓ.analyticAt z
      · rename_i j
        simp only [Fin.cons_succ]
        exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d => ℂ) j).comp A).analyticAt z
    exact AnalyticAt.comp (g := F) (f := fun z => (Fin.cons (ℓ z) (A z) : Fin (d + 1) → ℂ)) (hFa _ hm) hlin
  · have hm : (Fin.cons (ℓ z) (A z) : Fin (d + 1) → ℂ) ∈
        tailL d ⁻¹' D ∩ {p | δ (tailL d p) ≠ 0} := by
      refine ⟨?_, ?_⟩
      · rw [Set.mem_preimage, hcons]
        exact hz
      · show δ (tailL d _) ≠ 0
        rw [hcons]
        exact hδz
    show F _ = _
    rw [hFG hm]
    simp only [prodFn, hcons, Fin.cons_zero]
end SheetPieceProductAnalytic
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
