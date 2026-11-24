-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VerticalPointResidue_exists_homog_2fc2a6e46147
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:27.903796+00:00
-- url     : https://prove2.me/submissions/a7c1e2eb-a685-4b28-85ec-e6ce2d83e93b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsVertRIndexSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveDivVertical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PVertPointResidue
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPointResidue_isMultiHomog_iff_fb8717c574c6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPointResidue_isWH_X__785d066adc9d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VerticalPointResidue_isWH_X_pow_6ddc2bcf94e6

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
    (hχ : χ (X ⟨(), c⟩) = 1) (f : MRing (fun _ : Unit => T)) :
    ∃ (n : ℕ) (G : MRing (fun _ : Unit => T)), IsMultiHomog G (fun _ => n) ∧ χ G = χ f := by
  simp_rw [isMultiHomog_iff]
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨0, C a, isWeightedHomogeneous_C _ _, rfl⟩
  | add p q hp hq =>
    obtain ⟨n₁, G₁, h₁, e₁⟩ := hp
    obtain ⟨n₂, G₂, h₂, e₂⟩ := hq
    refine ⟨n₁ + n₂, G₁ * X ⟨(), c⟩ ^ n₂ + G₂ * X ⟨(), c⟩ ^ n₁, ?_, ?_⟩
    · refine (h₁.mul (isWH_X_pow c n₂)).add ?_
      rw [add_comm n₁]
      exact h₂.mul (isWH_X_pow c n₁)
    · simp only [map_add, map_mul, map_pow, hχ, one_pow, mul_one, e₁, e₂]
  | mul_X p i hp =>
    obtain ⟨n, G, h, e⟩ := hp
    refine ⟨n + 1, G * X i, h.mul (isWH_X' i), ?_⟩
    rw [map_mul, map_mul, e]
end GroundTheory.Heights₂.Heights.VerticalPointResidue
