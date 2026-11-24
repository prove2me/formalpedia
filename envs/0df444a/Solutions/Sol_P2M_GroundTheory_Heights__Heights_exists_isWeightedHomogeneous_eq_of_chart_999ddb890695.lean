-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_exists_isWeightedHomogeneous_eq_of_chart_999ddb890695
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:49.533664+00:00
-- url     : https://prove2.me/submissions/10753dda-5ce4-4be4-9ed0-882ac200058d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenter
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PHeightRecR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenterMemIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCenterDivSuppLemmas

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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {R : Type*} [CommRing R]
    (χ : MvPolynomial (Coord n) ℤ →+* R) (c : (k : ι) → Fin (n k + 1))
    (hχ : ∀ k, χ (X ⟨k, c k⟩) = 1) (g : MvPolynomial (Coord n) ℤ) :
    ∃ (D : ι → ℕ) (G : MvPolynomial (Coord n) ℤ),
      IsWeightedHomogeneous (coordDeg n) G D ∧ χ G = χ g := by
  have hmon : ∀ e, χ (chartMonomial c e) = 1 := fun e ↦ by
    simp [chartMonomial, map_prod, hχ]
  induction g using MvPolynomial.induction_on with
  | C a => exact ⟨0, C a, isWeightedHomogeneous_C _ _, rfl⟩
  | add p q hp hq =>
    obtain ⟨D₁, G₁, h₁, e₁⟩ := hp
    obtain ⟨D₂, G₂, h₂, e₂⟩ := hq
    refine ⟨D₁ + D₂, G₁ * chartMonomial c D₂ + G₂ * chartMonomial c D₁, ?_, ?_⟩
    · refine IsWeightedHomogeneous.add (h₁.mul (isWeightedHomogeneous_chartMonomial c D₂)) ?_
      rw [add_comm D₁]
      exact h₂.mul (isWeightedHomogeneous_chartMonomial c D₁)
    · rw [map_add, map_mul, map_mul, hmon, hmon, mul_one, mul_one, e₁, e₂, map_add]
  | mul_X p i hp =>
    obtain ⟨D, G, h, e⟩ := hp
    exact ⟨D + coordDeg n i, G * X i, h.mul (isWeightedHomogeneous_X ℤ _ i),
      by rw [map_mul, map_mul, e]⟩
end GroundTheory.Heights₂.Heights
