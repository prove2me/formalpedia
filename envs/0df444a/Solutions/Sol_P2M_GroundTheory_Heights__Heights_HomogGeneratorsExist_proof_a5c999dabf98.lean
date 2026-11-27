-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HomogGeneratorsExist_proof_a5c999dabf98
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:57:27.146015+00:00
-- url     : https://prove2.me/submissions/0b4b41f2-1945-4daa-b23d-ce94b9236266

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PHomogGeneratorsExist
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_sum_weightedHomogeneousComponent_image_27a7ee41f296

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
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights
namespace HomogGeneratorsExist
theorem _root_.solution : HomogGeneratorsExist.Statement := by
  classical
  intro ι _ _ n P
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian P.ideal : P.ideal.FG)

  let S : Finset (MvPolynomial (Coord n) ℤ) := s.biUnion fun f ↦
    (f.support.image (Finsupp.weight (coordDeg n))).image fun m ↦ weightedHomogeneousComponent (coordDeg n) m f
  have hShom : ∀ g ∈ S, ∃ m : ι → ℕ, IsWeightedHomogeneous (coordDeg n) g m := by
    intro g hg
    simp only [S, Finset.mem_biUnion, Finset.mem_image] at hg
    obtain ⟨f, -, m, -, rfl⟩ := hg
    exact ⟨m, weightedHomogeneousComponent_isWeightedHomogeneous m f⟩
  have hSP : ∀ g ∈ S, g ∈ P.ideal := by
    intro g hg
    simp only [S, Finset.mem_biUnion, Finset.mem_image] at hg
    obtain ⟨f, hf, m, -, rfl⟩ := hg
    exact P.homogeneous f (hs ▸ Ideal.subset_span hf) m
  let e := S.equivFin
  refine ⟨S.card, fun i ↦ (e.symm i : MvPolynomial (Coord n) ℤ),
    fun i ↦ Classical.choose (hShom _ (e.symm i).2), ⟨fun i ↦ Classical.choose_spec (hShom _ (e.symm i).2), ?_⟩⟩
  have hrange : Set.range (fun i ↦ (e.symm i : MvPolynomial (Coord n) ℤ)) = (S : Set _) := by
    ext g
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).2
    · intro hg
      exact ⟨e ⟨g, hg⟩, by simp⟩
  rw [hrange]
  apply le_antisymm
  · rw [Ideal.span_le]
    intro g hg
    exact hSP g hg
  · rw [← hs, Ideal.span_le]
    intro f hf
    rw [← sum_weightedHomogeneousComponent_image f]
    refine Ideal.sum_mem _ fun m hm ↦ Ideal.subset_span ?_
    simp only [S, Finset.coe_biUnion, Finset.coe_image, Set.mem_iUnion, Set.mem_image]
    exact ⟨f, hf, m, by simpa using hm, rfl⟩
end HomogGeneratorsExist
end GroundTheory.Heights₂.Heights
