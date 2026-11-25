-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.exists_pullAl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:50:13.715148+00:00
-- url     : https://prove2.me/submissions/81d5a97a-e765-4854-8b77-8fd5046f1d46

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CartesianLiftThreeCompProjection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBCorr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_smul_star_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_secRel_pullSecs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (hL : D.toPre.P.L.IsLB) (oa : D.toPre.OAct O) (w0 : O)
    (uΨ : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 4)
      ![(padd D.toPre.P.A (𝟙 _) (oa.onB.act w0)).left, 𝟙 D.toPre.P.A.left, (oa.onB.act w0).left,
        (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]).left] ![1, -2, -1, 2]))
    (huΨ : uΨ.IsGen) (a : O) (N : ℕ) (hN : a * star a = (N : O)) (hN1 : 1 ≤ N) (k : ℕ)
    (s : Fam D.toPre F k)
    (hfe : DegPre.FamFE D.toPre F (k * N) (pullSecs D F hL oa w0 uΨ huΨ a N hN hN1 k s)) :
    ∃ s' : Fam D.toPre F (k * N), PullAl D F oa a k N s s' := by
  refine ⟨⟨pullSecs D F hL oa w0 uΨ huΨ a N hN hN1 k s, hfe⟩, fun χ => ?_, fun β hβ j => ?_⟩
  · refine ⟨uPull D F hL oa w0 uΨ huΨ a N hN hN1 k χ, (uPull_spec D F hL oa w0 uΨ huΨ a N hN hN1 k χ).1,
      (uPull_spec D F hL oa w0 uΨ huΨ a N hN hN1 k χ).2, ?_⟩
    have hex : ∃ χ₀, star a • χ₀ = star a • χ := ⟨χ, rfl⟩
    show GeneratorPullback.SecRel _ _ _ (pullSecs D F hL oa w0 uΨ huΨ a N hN hN1 k s (star a • χ)) _ _ _ _ _ _ _
    simp only [pullSecs, dif_pos hex]
    exact secRel_pullSecs hL oa w0 uΨ huΨ a N hN hN1 k s χ hex.choose hex.choose_spec
      (smul_star_inj a N hN hN1 hex.choose_spec)
  · have : ¬ ∃ χ, star a • χ = β := fun ⟨χ, h⟩ => hβ χ h.symm
    show (pullSecs D F hL oa w0 uΨ huΨ a N hN hN1 k s β).f j = 0
    simp only [pullSecs, dif_neg this]
    rfl
end ReciprocityTheory.ChartRestriction.G.DVR
