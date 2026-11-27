-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_LocalQuotFinsum_proof_91cbdf3541a5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:07:07.061128+00:00
-- url     : https://prove2.me/submissions/8ec0530b-d020-49ed-ae9d-a14e3a483dc0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsLocalCoeffRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PLocalQuotFinsum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace LocalQuotFinsum
theorem _root_.solution (h : LocalQuotPrimes.Statement.{u}) : LocalQuotFinsum.Statement.{u} := by
  intro R _ P U _ hPU F F' hF hF' hFF'
  have hP := h R P U hPU
  set S : Set (Ideal R) := {G | G.IsPrime ∧ P ≤ G ∧ G ≤ U} with hS
  set T : Set (Ideal (localQuot P U)) := {p | p.IsPrime} with hT
  have h1 : ∑ᶠ G, F G = ∑ᶠ G ∈ S, F G := by
    rw [← finsum_mem_univ]
    apply finsum_mem_inter_support_eq'
    intro G hG
    exact ⟨fun _ => hF G hG, fun _ => Set.mem_univ G⟩
  have h2 : ∑ᶠ p, F' p = ∑ᶠ p ∈ T, F' p := by
    rw [← finsum_mem_univ]
    apply finsum_mem_inter_support_eq'
    intro p hp
    exact ⟨fun _ => hF' p hp, fun _ => Set.mem_univ p⟩
  have hbij : S.BijOn (fun G => G.map (localQuotMap P U)) T := by
    refine ⟨fun G hG => (hP.1 G hG.1 hG.2.1 hG.2.2).1, ?_, ?_⟩
    · intro G₁ hG₁ G₂ hG₂ he
      have e₁ := (hP.1 G₁ hG₁.1 hG₁.2.1 hG₁.2.2).2
      have e₂ := (hP.1 G₂ hG₂.1 hG₂.2.1 hG₂.2.2).2
      simp only at he
      rw [← e₁, ← e₂, he]
    · intro p hp
      obtain ⟨hle, hleU, hmap⟩ := hP.2 p hp
      exact ⟨p.comap (localQuotMap P U), ⟨by have : p.IsPrime := hp; exact Ideal.comap_isPrime _ p, hle, hleU⟩, hmap⟩
  rw [h1, h2]
  exact finsum_mem_eq_of_bijOn _ hbij fun G hG => hFF' G hG.1 hG.2.1 hG.2.2
end LocalQuotFinsum
end GroundTheory.Heights₂.Heights.NumbersDVR
