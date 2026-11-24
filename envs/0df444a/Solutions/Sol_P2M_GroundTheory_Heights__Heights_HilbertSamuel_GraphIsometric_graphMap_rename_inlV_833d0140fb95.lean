-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_graphMap_rename_inlV_833d0140fb95
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:24.813809+00:00
-- url     : https://prove2.me/submissions/779d03c5-22b2-42e3-abac-8b296973c508

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PChangeOfModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometric
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphIsometric_graphMap_X_inlV_57139c30c413

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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometric
variable {K : Type} [Fintype K] {ι ι₂ : K → Type} [∀ k, Fintype (ι k)] [∀ k, Fintype (ι₂ k)]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometric
theorem _root_.solution (P : Ideal (MRing ι)) (g : (Σ k, ι₂ k) → MRing ι) (p : MRing ι) :
    graphMap P g (rename inlV p) = C (Ideal.Quotient.mk P p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have e : ((graphMap P g).comp (rename (inlV (ι₂ := ι₂))).toRingHom).comp C =
        ((C : (MRing ι ⧸ P) →+* MvPolynomial K (MRing ι ⧸ P)).comp (Ideal.Quotient.mk P)).comp C :=
      RingHom.ext_int _ _
    exact RingHom.congr_fun e a
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp => simp [hp, graphMap_X_inlV]
end GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometric
