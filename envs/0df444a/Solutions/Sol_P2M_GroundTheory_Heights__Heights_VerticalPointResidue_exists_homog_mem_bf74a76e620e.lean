-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VerticalPointResidue_exists_homog_mem_bf74a76e620e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:23:09.894367+00:00
-- url     : https://prove2.me/submissions/52af099b-f0e9-4115-870f-7654fd64d7a0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsVertRIndexSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveDivVertical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PVertPointResidue
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPointResidue_isMultiHomog_iff_fb8717c574c6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPointResidue_isWH_X_pow_6ddc2bcf94e6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPointResidue_exists_homog_2fc2a6e46147
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CurveDivVertical_isWeightedHomogeneous_of_isMultiHomog_225c0c57b72c
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isWeightedHomogeneous_of_isMultiHomog


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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.VerticalPointResidue
variable {T : Type} [Fintype T]
namespace GroundTheory.Heights₂.Heights.VerticalPointResidue
theorem _root_.solution {S : Type*} [CommRing S] (χ : MRing (fun _ : Unit => T) →+* S) (c : T)
    (hχ : χ (X ⟨(), c⟩) = 1) {W : Ideal (MRing (fun _ : Unit => T))} (hW : IsMultiHomogIdeal W)
    {f : MRing (fun _ : Unit => T)} (hf : f ∈ W) :
    ∃ (n : ℕ) (G : MRing (fun _ : Unit => T)), G ∈ W ∧ IsMultiHomog G (fun _ => n) ∧ χ G = χ f := by
  obtain ⟨Sg, hSg, rfl⟩ := hW
  simp_rw [isMultiHomog_iff]
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha⟩ := hSg x hx
    exact ⟨a (), x, Ideal.subset_span hx, isWeightedHomogeneous_of_isMultiHomog ha (), rfl⟩
  | zero => exact ⟨0, 0, zero_mem _, fun d hd => absurd rfl hd, rfl⟩
  | add x z _ _ hx hz =>
    obtain ⟨n₁, G₁, hG₁, h₁, e₁⟩ := hx
    obtain ⟨n₂, G₂, hG₂, h₂, e₂⟩ := hz
    refine ⟨n₁ + n₂, G₁ * X ⟨(), c⟩ ^ n₂ + G₂ * X ⟨(), c⟩ ^ n₁,
      add_mem (Ideal.mul_mem_right _ _ hG₁) (Ideal.mul_mem_right _ _ hG₂), ?_, ?_⟩
    · refine (h₁.mul (isWH_X_pow c n₂)).add ?_
      rw [add_comm n₁]
      exact h₂.mul (isWH_X_pow c n₁)
    · simp only [map_add, map_mul, map_pow, hχ, one_pow, mul_one, e₁, e₂]
  | smul a x _ hx =>
    obtain ⟨n, G, hG, h, e⟩ := hx
    obtain ⟨m, A, hA, eA⟩ := exists_homog χ c hχ a
    refine ⟨m + n, A * G, Ideal.mul_mem_left _ _ hG, (isMultiHomog_iff.mp hA).mul h, ?_⟩
    rw [smul_eq_mul, map_mul, map_mul, eA, e]
end GroundTheory.Heights₂.Heights.VerticalPointResidue
