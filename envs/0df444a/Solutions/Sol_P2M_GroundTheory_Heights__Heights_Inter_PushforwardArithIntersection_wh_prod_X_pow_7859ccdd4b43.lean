-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_wh_prod_X_pow_7859ccdd4b43
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:46.982862+00:00
-- url     : https://prove2.me/submissions/5c467625-f51b-4086-a57d-863140c4a454

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsFieldIntersectionNoBlockFam
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogRenameCoordPow

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
open GroundTheory.Heights₂.Heights.Inter.PushforwardArithIntersection
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.PushforwardArithIntersection
theorem _root_.solution {K₀ : Type} [Fintype K₀] (q : K₀ → Σ k, ι k) (α : K₀ → ℕ) :
    IsWeightedHomogeneous (blkW (ι := ι)) (∏ k, (X (q k) : MRing ι) ^ α k) (∑ k, α k • blkW (q k)) :=
  IsWeightedHomogeneous.prod _ _ _ fun k _ => (isWeightedHomogeneous_X ℤ _ (q k)).pow (α k)
end GroundTheory.Heights₂.Heights.Inter.PushforwardArithIntersection
