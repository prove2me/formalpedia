-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionHorizontal_isHorizontal_imageZ_419052dac111
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:13:19.140125+00:00
-- url     : https://prove2.me/submissions/9bbc5dd8-8ff2-4680-a08e-c10545c8f578

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsHorizontalSpanXb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsHorizontalImageZ

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionHorizontal
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)]
namespace GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionHorizontal
theorem _root_.solution {v : (Σ k, ι k) → (Σ k', ι' k')} {W' : Ideal (MRing ι')} (h : IsHorizontal W') :
    IsHorizontal (imageZ v W') := by
  have h' : W'.comap (C : ℤ →+* MRing ι') = ⊥ := h
  show (imageZ v W').comap (C : ℤ →+* MRing ι) = ⊥
  rw [← h']
  ext c
  simp [imageZ, Ideal.mem_comap]
end GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionHorizontal
