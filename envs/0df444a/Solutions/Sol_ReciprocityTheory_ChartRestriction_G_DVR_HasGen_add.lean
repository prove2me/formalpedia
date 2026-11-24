-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.HasGen.add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:00.19106+00:00
-- url     : https://prove2.me/submissions/4aa6f61c-6c3e-4cff-9b7b-4037ccd4eee2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen

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
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}} (L : LB X)
variable {L}
namespace ReciprocityTheory.ChartRestriction.G.DVR
namespace HasGen
theorem _root_.solution {F G : (Y ⟶ X) →₀ ℤ} (hF : HasGen L F) (hG : HasGen L G) : HasGen L (F + G) := by
  have res_res : ∀ {Z : Scheme.{0}} {U V W : Z.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(Z, U)ˣ),
      res h2 (res h1 x) = res (h2.trans h1) x := by
    intro Z U V W h1 h2 x
    ext
    first
      | (simp only [res, Units.coe_map, MonoidHom.coe_coe]
         rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
         rfl)
      | (simp [res, ← Functor.map_comp_apply])
      | (simp [res]; rfl)
  obtain ⟨K, _, φ, ε, rfl, g, hg⟩ := hF
  obtain ⟨K', _, φ', ε', rfl, g', hg'⟩ := hG
  have hl : ∀ i : K ⊕ K' → L.ι, LB.wchart L (Sum.elim φ φ') i ≤ LB.wchart L φ (i ∘ Sum.inl) := by
    intro i x hx
    exact Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx (Sum.inl k)
  have hr : ∀ i : K ⊕ K' → L.ι, LB.wchart L (Sum.elim φ φ') i ≤ LB.wchart L φ' (i ∘ Sum.inr) := by
    intro i x hx
    exact Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx (Sum.inr k)
  refine ⟨K ⊕ K', inferInstance, Sum.elim φ φ', Sum.elim ε ε', ?_,
    ⟨fun i => res (hl i) (g.s (i ∘ Sum.inl)) * res (hr i) (g'.s (i ∘ Sum.inr))⟩, ?_⟩
  · simp [fsum, Fintype.sum_sum_type]
  · intro i j
    have hW : LB.wchart L (Sum.elim φ φ') i ⊓ LB.wchart L (Sum.elim φ φ') j ≤
        LB.wchart L φ (i ∘ Sum.inl) ⊓ LB.wchart L φ (j ∘ Sum.inl) := inf_le_inf (hl i) (hl j)
    have hW' : LB.wchart L (Sum.elim φ φ') i ⊓ LB.wchart L (Sum.elim φ φ') j ≤
        LB.wchart L φ' (i ∘ Sum.inr) ⊓ LB.wchart L φ' (j ∘ Sum.inr) := inf_le_inf (hr i) (hr j)
    have hGs : (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).g i j =
        res hW ((LB.LinComb L φ ε).g (i ∘ Sum.inl) (j ∘ Sum.inl)) *
          res hW' ((LB.LinComb L φ' ε').g (i ∘ Sum.inr) (j ∘ Sum.inr)) := by
      first
        | (simp only [LB.LinComb, Fintype.prod_sum_type, map_prod, map_zpow, res_res]; rfl)
        | (simp [LB.LinComb, Fintype.prod_sum_type, map_prod, map_zpow]
           congr 1 <;> refine Finset.prod_congr rfl fun k _ => ?_ <;> erw [res_res] <;> try rfl)
        | (simp [LB.LinComb, Fintype.prod_sum_type, map_prod, map_zpow]
           congr 1 <;> refine Finset.prod_congr rfl fun k _ => ?_ <;> rw [res_res])
    have e1 := congrArg (res hW) (hg (i ∘ Sum.inl) (j ∘ Sum.inl))
    have e2 := congrArg (res hW') (hg' (i ∘ Sum.inr) (j ∘ Sum.inr))
    erw [map_mul, res_res, res_res] at e1 e2
    dsimp only
    rw [hGs]
    erw [map_mul, map_mul, res_res, res_res, res_res, res_res, e1, e2]
    exact mul_mul_mul_comm _ _ _ _
end HasGen
end ReciprocityTheory.ChartRestriction.G.DVR
