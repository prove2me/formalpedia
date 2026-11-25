-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.im_Hf_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:10:20.979062+00:00
-- url     : https://prove2.me/submissions/19881212-72a0-44b8-9e6c-e7b5b7bc2623

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitVM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitVA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitVB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex Module
noncomputable section
variable {E : Type} [Field E] [NumberField E]
variable {dim : (E →+* ℂ) → ℕ}
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (x ξ : Vsp dim) (β : 𝓞 E) :
    ((Hf x (act β ξ)).im : ℂ) =
      ∑ σ, σ (β : E) * ((hA x ξ (ComplexEmbedding.conjugate σ) - (starRingEnd ℂ) (hA x ξ σ)) / (2 * I)) := by
  have hZ : Hf x (act β ξ) = ∑ σ, (starRingEnd ℂ) (σ (β : E)) * hA x ξ σ := by
    simp only [Hf, act, hA, Fintype.sum_sigma, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun a _ => ?_
    simp only [PiLp.toLp_apply, map_mul]
    ring
  have hre : ∑ σ, σ (β : E) * hA x ξ (ComplexEmbedding.conjugate σ) =
      ∑ σ, (starRingEnd ℂ) (σ (β : E)) * hA x ξ σ := by
    refine Fintype.sum_equiv (ComplexEmbedding.involutive_conjugate (K := E)).toPerm _ _ (fun σ => ?_)
    simp only [Function.Involutive.coe_toPerm, ComplexEmbedding.involutive_conjugate (K := E) σ,
      ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
  rw [hZ, Complex.im_eq_sub_conj, map_sum]
  simp only [map_mul, Complex.conj_conj, mul_sub, mul_div_assoc', Finset.sum_div, Finset.sum_sub_distrib]
  rw [← hre]
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_div]
end ReciprocityTheory.ChartRestriction.G.I2
