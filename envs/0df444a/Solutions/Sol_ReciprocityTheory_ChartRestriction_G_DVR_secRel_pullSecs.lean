-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.secRel_pullSecs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:31:57.001612+00:00
-- url     : https://prove2.me/submissions/7a89c6c7-1de7-44f9-a512-736ccb7d58ba

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CartesianLiftThreeCompProjection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBCorr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_shape_secRel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_sec_transport


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
variable {D F}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (hL : D.toPre.P.L.IsLB) (oa : D.toPre.OAct O) (w0 : O)
    (uΨ : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 4)
      ![(padd D.toPre.P.A (𝟙 _) (oa.onB.act w0)).left, 𝟙 D.toPre.P.A.left, (oa.onB.act w0).left,
        (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]).left] ![1, -2, -1, 2]))
    (huΨ : uΨ.IsGen) (a : O) (N : ℕ) (hN : a * star a = (N : O)) (hN1 : 1 ≤ N) (k : ℕ)
    (s : Fam D.toPre F k) (χ : D.toPre.X) :
    ∀ (χ₀ : D.toPre.X) (hβ : star a • χ₀ = star a • χ), χ₀ = χ →
      GeneratorPullback.SecRel D.toPre.P.L (DegPre.famφ D.toPre F (star a • χ)) (DegPre.famε (k * N))
        (Classical.choose (sec_transport hL (pullProd_sameSum D F oa a N k χ₀ (star a • χ) hβ)
          (pullProd D F hL oa w0 uΨ huΨ a N hN hN1 k s χ₀)))
        (DegPre.famφ D.toPre F χ) (DegPre.famε k) (s.s χ) (aF D F oa a).left
        (pullφ D F oa a χ) (pullε k N) (uPull D F hL oa w0 uΨ huΨ a N hN hN1 k χ) := by
  intro χ₀ hβ e
  subst χ₀
  intro j₁ j₂ j₃ hcoh
  have spec := Classical.choose_spec (sec_transport hL (pullProd_sameSum D F oa a N k χ (star a • χ) hβ)
    (pullProd D F hL oa w0 uΨ huΨ a N hN hN1 k s χ))
  have e := spec (Sum.elim j₃ j₂) j₁
    (by
      rintro (k₁ | k₁) (k₂ | k₂) h
      · exact hcoh (Sum.inr (Sum.inr k₁)) (Sum.inr (Sum.inr k₂)) h
      · exact hcoh (Sum.inr (Sum.inr k₁)) (Sum.inr (Sum.inl k₂)) h
      · exact hcoh (Sum.inr (Sum.inl k₁)) (Sum.inr (Sum.inr k₂)) h
      · exact hcoh (Sum.inr (Sum.inl k₁)) (Sum.inr (Sum.inl k₂)) h)
    (fun k₁ k₂ h => hcoh (Sum.inl k₁) (Sum.inl k₂) h)
    (by
      rintro (k | k) k' h
      · exact (hcoh (Sum.inl k') (Sum.inr (Sum.inr k)) h.symm).symm
      · exact (hcoh (Sum.inl k') (Sum.inr (Sum.inl k)) h.symm).symm)
  have ho : LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F (star a • χ)) j₁ ⊓
      LB.wchart D.toPre.P.L (fun k => (aF D F oa a).left ≫ DegPre.famφ D.toPre F χ k) j₂ ⊓
      LB.wchart D.toPre.P.L (pullφ D F oa a χ) j₃ ≤
      LB.wchart D.toPre.P.L (Sum.elim (pullφ D F oa a χ) (fun k => (aF D F oa a).left ≫ DegPre.famφ D.toPre F χ k))
        (Sum.elim j₃ j₂) ⊓ LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F (star a • χ)) j₁ :=
    fun _ hy => ⟨Set.mem_iInter.2 fun k => by
        rcases k with k | k
        · exact Set.mem_iInter.1 hy.2 k
        · exact Set.mem_iInter.1 hy.1.2 k, hy.1.1⟩
  exact shape_secRel _ _ (wchart_comp_le _ _ j₂) ho _ _ _ _ _ _ e
end ReciprocityTheory.ChartRestriction.G.DVR
