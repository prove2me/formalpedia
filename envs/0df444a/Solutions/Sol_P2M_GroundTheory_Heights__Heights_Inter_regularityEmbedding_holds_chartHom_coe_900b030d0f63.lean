-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_chartHom_coe_900b030d0f63
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:38.345797+00:00
-- url     : https://prove2.me/submissions/75db726d-1292-4302-aa7d-3b6f8d2a38a6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsFunFieldMulEq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalOfDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotMemOfNonZeroDivisor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.regularityEmbedding_holds
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.regularityEmbedding_holds
theorem _root_.solution {P : Ideal (MRing ι)} (r : (Σ k, ι k) → funField P) (f : MRing ι) :
    (chartHom r f : FractionRing (MRing ι ⧸ P)) =
      eval₂Hom (Int.castRingHom _) (fun p => (r p : FractionRing (MRing ι ⧸ P))) f := by
  have : (funField P).subtype.comp (chartHom r) =
      eval₂Hom (Int.castRingHom _) (fun p => (r p : FractionRing (MRing ι ⧸ P))) :=
    MvPolynomial.ringHom_ext (fun n => by simp [chartHom]) (fun p => by simp [chartHom])
  exact congrArg (fun φ => φ f) this
end GroundTheory.Heights₂.Heights.Inter.regularityEmbedding_holds
