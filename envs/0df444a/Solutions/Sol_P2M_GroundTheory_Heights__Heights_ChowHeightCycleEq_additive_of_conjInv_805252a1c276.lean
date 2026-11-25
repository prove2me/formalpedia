-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_additive_of_conjInv_805252a1c276
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:32:10.458702+00:00
-- url     : https://prove2.me/submissions/599b5f5c-5c2f-45a4-aad2-a68c9b426c3c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ArchOfPlacesEmbedding
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_archOfPlaces_embedding_2ed4d34525ea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_chowHt_eq_chowHt_places_1244538cd039
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_ofPointMatrix_norm_fe0404d8d94b


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
open MvPolynomial MeasureTheory NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.ChowHeightCycleEq
variable {n e : ℕ}
namespace GroundTheory.Heights₂.Heights.ChowHeightCycleEq
theorem _root_.solution (hA : ChowHeightMul.Statement) {K : Type} [Field K] [NumberField K]
    (T : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hT : ∀ w, IsUnit (T w))
    (hreal : ∀ w : InfinitePlace K, w.IsReal → ∀ u,
      IndefiniteRowSideFullHecke.ArithBezout.formNorm (T w) (star u) = IndefiniteRowSideFullHecke.ArithBezout.formNorm (T w) u)
    (f g : MvPolynomial (Fin (e + 1) × Fin n) K) (δ₁ δ₂ : ℕ) (hf : f ≠ 0) (hg : g ≠ 0) :
    ReciprocityTheory.ChartRestriction.G.Geo.chowHt (fun w => IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (T w) (e + 1)) (f * g)
        (δ₁ + δ₂) =
      ReciprocityTheory.ChartRestriction.G.Geo.chowHt (fun w => IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (T w) (e + 1)) f δ₁ +
        ReciprocityTheory.ChartRestriction.G.Geo.chowHt (fun w => IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (T w) (e + 1)) g δ₂ := by
  let H := archOfPlaces (fun w => ObjectsHeight.ofPointMatrix (T w) (hT w)) (fun w hw u => by
    rw [ObjectsHeight.ofPointMatrix_norm, ObjectsHeight.ofPointMatrix_norm]
    exact hreal w hw u)
  have hH : ∀ w u, (H.normAt w.embedding).norm u = IndefiniteRowSideFullHecke.ArithBezout.formNorm (T w) u :=
    fun w u => by rw [archOfPlaces_embedding, ObjectsHeight.ofPointMatrix_norm]
  rw [← ObjectsHeight.chowHt_eq_chowHt_places H T hT hH,
    ← ObjectsHeight.chowHt_eq_chowHt_places H T hT hH,
    ← ObjectsHeight.chowHt_eq_chowHt_places H T hT hH]
  exact hA K n H (e + 1) δ₁ δ₂ f g hf hg
end GroundTheory.Heights₂.Heights.ChowHeightCycleEq
