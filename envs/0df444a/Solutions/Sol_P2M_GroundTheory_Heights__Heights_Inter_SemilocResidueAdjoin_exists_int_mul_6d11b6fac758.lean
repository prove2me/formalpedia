-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueAdjoin_exists_int_mul_6d11b6fac758
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:17:04.032359+00:00
-- url     : https://prove2.me/submissions/3c17bd75-302d-498f-9a86-c2bc4b22218c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocResidueFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocRankAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocResidueAdjoin

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
namespace GroundTheory.Heights₂.Heights.Inter
namespace SemilocResidueAdjoin
theorem _root_.solution {σ F : Type} [Field F]
    (hF : ∀ c : F, ∃ a b : ℤ, (b : F) ≠ 0 ∧ c = a / b) (f : MvPolynomial σ F) :
    ∃ (g : MvPolynomial σ ℤ) (d : ℤ), (d : F) ≠ 0 ∧ C (d : F) * f = MvPolynomial.map (Int.castRingHom F) g := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    obtain ⟨a, b, hb, rfl⟩ := hF c
    refine ⟨C a, b, hb, ?_⟩
    rw [map_C, ← C_mul, mul_div_cancel₀ _ hb, eq_intCast]
  | add f g hf hg =>
    obtain ⟨g₁, d₁, h₁, e₁⟩ := hf
    obtain ⟨g₂, d₂, h₂, e₂⟩ := hg
    refine ⟨C d₂ * g₁ + C d₁ * g₂, d₁ * d₂, by push_cast; exact mul_ne_zero h₁ h₂, ?_⟩
    rw [map_add, map_mul, map_mul, map_C, map_C, ← e₁, ← e₂, eq_intCast, eq_intCast]
    push_cast
    rw [C_mul]
    ring
  | mul_X f q hf =>
    obtain ⟨g, d, h, e⟩ := hf
    exact ⟨g * X q, d, h, by rw [map_mul, map_X, ← e, mul_assoc]⟩
end SemilocResidueAdjoin
end GroundTheory.Heights₂.Heights.Inter
