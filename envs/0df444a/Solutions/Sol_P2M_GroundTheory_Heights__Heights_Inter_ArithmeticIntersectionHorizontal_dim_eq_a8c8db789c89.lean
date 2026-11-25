-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionHorizontal_dim_eq_a8c8db789c89
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:13:16.364874+00:00
-- url     : https://prove2.me/submissions/9dfc1a54-fd01-45f8-9b9a-bbf40b91b704

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
namespace GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionHorizontal
theorem _root_.solution {P : Ideal (MRing ι)} {d d' : ℕ} (h : IsArithVar P d) (h' : IsArithVar P d') : d = d' := by
  have e := h.2.2.2.symm.trans h'.2.2.2
  have e2 : d + Fintype.card K = d' + Fintype.card K := by exact_mod_cast e
  omega
end GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionHorizontal
