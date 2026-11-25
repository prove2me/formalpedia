-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.product_generator_isGenerator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:48:22.393237+00:00
-- url     : https://prove2.me/submissions/7863b052-133d-4a0d-b17b-c63158e18224

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_res_res__b0a8af1c3378


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
set_option maxHeartbeats 1000000
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) (ht : t.IsGen) (ht' : t'.IsGen)
    (i j : K ⊕ K' → L.ι) :
    res (inf_le_left : (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).U i ⊓
        (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).U j ≤ (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).U i)
        ((LB.mulGen L φ ε φ' ε' t t').s i) =
      (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).g i j *
        res (inf_le_right : (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).U i ⊓
          (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).U j ≤ (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).U j)
          ((LB.mulGen L φ ε φ' ε' t t').s j) := by
  have hA : (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).U i ⊓ (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).U j ≤
      (LB.LinComb L φ ε).U (i ∘ Sum.inl) ⊓ (LB.LinComb L φ ε).U (j ∘ Sum.inl) := fun z hz =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hz.1 (Sum.inl k),
      Set.mem_iInter.2 fun k => Set.mem_iInter.1 hz.2 (Sum.inl k)⟩
  have hB : (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).U i ⊓ (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).U j ≤
      (LB.LinComb L φ' ε').U (i ∘ Sum.inr) ⊓ (LB.LinComb L φ' ε').U (j ∘ Sum.inr) := fun z hz =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hz.1 (Sum.inr k),
      Set.mem_iInter.2 fun k => Set.mem_iInter.1 hz.2 (Sum.inr k)⟩
  have hg : (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).g i j =
      res hA ((LB.LinComb L φ ε).g (i ∘ Sum.inl) (j ∘ Sum.inl)) *
        res hB ((LB.LinComb L φ' ε').g (i ∘ Sum.inr) (j ∘ Sum.inr)) := by
    have e0 : (LB.LinComb L φ ε).g (i ∘ Sum.inl) (j ∘ Sum.inl) = ∏ k, (res (le_inf (inf_le_left.trans (LB.wchart_le L φ (i ∘ Sum.inl) k))
      (inf_le_right.trans (LB.wchart_le L φ (j ∘ Sum.inl) k)) :
        (LB.LinComb L φ ε).U (i ∘ Sum.inl) ⊓ (LB.LinComb L φ ε).U (j ∘ Sum.inl) ≤ φ k ⁻¹ᵁ (L.U (i (Sum.inl k)) ⊓ L.U (j (Sum.inl k))))
      (pullU (φ k) _ (L.g (i (Sum.inl k)) (j (Sum.inl k))))) ^ (ε k) := rfl
    have e0' : (LB.LinComb L φ' ε').g (i ∘ Sum.inr) (j ∘ Sum.inr) = ∏ k, (res (le_inf (inf_le_left.trans (LB.wchart_le L φ' (i ∘ Sum.inr) k))
      (inf_le_right.trans (LB.wchart_le L φ' (j ∘ Sum.inr) k)) :
        (LB.LinComb L φ' ε').U (i ∘ Sum.inr) ⊓ (LB.LinComb L φ' ε').U (j ∘ Sum.inr) ≤ φ' k ⁻¹ᵁ (L.U (i (Sum.inr k)) ⊓ L.U (j (Sum.inr k))))
      (pullU (φ' k) _ (L.g (i (Sum.inr k)) (j (Sum.inr k))))) ^ (ε' k) := rfl
    have e1 : (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).g i j =
        (∏ k, (res hA (res (le_inf (inf_le_left.trans (LB.wchart_le L φ (i ∘ Sum.inl) k))
      (inf_le_right.trans (LB.wchart_le L φ (j ∘ Sum.inl) k)) :
        (LB.LinComb L φ ε).U (i ∘ Sum.inl) ⊓ (LB.LinComb L φ ε).U (j ∘ Sum.inl) ≤ φ k ⁻¹ᵁ (L.U (i (Sum.inl k)) ⊓ L.U (j (Sum.inl k))))
      (pullU (φ k) _ (L.g (i (Sum.inl k)) (j (Sum.inl k)))))) ^ (ε k)) *
          ∏ k, (res hB (res (le_inf (inf_le_left.trans (LB.wchart_le L φ' (i ∘ Sum.inr) k))
      (inf_le_right.trans (LB.wchart_le L φ' (j ∘ Sum.inr) k)) :
        (LB.LinComb L φ' ε').U (i ∘ Sum.inr) ⊓ (LB.LinComb L φ' ε').U (j ∘ Sum.inr) ≤ φ' k ⁻¹ᵁ (L.U (i (Sum.inr k)) ⊓ L.U (j (Sum.inr k))))
      (pullU (φ' k) _ (L.g (i (Sum.inr k)) (j (Sum.inr k)))))) ^ (ε' k) := by
      refine (Fintype.prod_sum_type _).trans ?_
      congr 1 <;> refine Finset.prod_congr rfl fun k _ => ?_ <;> congr 1 <;> erw [res_res'] <;> rfl
    obtain ⟨a, a', ha, ha', hb⟩ : ∃ (a : K → Γ(Y, ((LB.LinComb L φ ε).U (i ∘ Sum.inl) ⊓ (LB.LinComb L φ ε).U (j ∘ Sum.inl)))ˣ) (a' : K' → Γ(Y, ((LB.LinComb L φ' ε').U (i ∘ Sum.inr) ⊓ (LB.LinComb L φ' ε').U (j ∘ Sum.inr)))ˣ),
        (LB.LinComb L φ ε).g (i ∘ Sum.inl) (j ∘ Sum.inl) = ∏ k, a k ^ ε k ∧
        (LB.LinComb L φ' ε').g (i ∘ Sum.inr) (j ∘ Sum.inr) = ∏ k, a' k ^ ε' k ∧
        (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).g i j =
          (∏ k, (res hA (a k)) ^ ε k) * ∏ k, (res hB (a' k)) ^ ε' k := ⟨_, _, e0, e0', e1⟩
    rw [hb, ha, ha']
    first
      | (rw [map_prod, map_prod]
         congr 1 <;> exact Finset.prod_congr rfl fun k _ => by rw [map_zpow])
      | simp only [map_prod, map_zpow]
  have h1 := congrArg (fun z : Γ(Y, (LB.LinComb L φ ε).U (i ∘ Sum.inl) ⊓ (LB.LinComb L φ ε).U (j ∘ Sum.inl))ˣ =>
    res hA z) (ht (i ∘ Sum.inl) (j ∘ Sum.inl))
  have h2 := congrArg (fun z : Γ(Y, (LB.LinComb L φ' ε').U (i ∘ Sum.inr) ⊓ (LB.LinComb L φ' ε').U (j ∘ Sum.inr))ˣ =>
    res hB z) (ht' (i ∘ Sum.inr) (j ∘ Sum.inr))
  simp only [map_mul, res_res'] at h1 h2
  rw [hg]
  erw [map_mul, map_mul]
  erw [res_res', res_res', res_res', res_res']
  rw [mul_mul_mul_comm (res hA _) (res hB _)]
  erw [h1, h2]
  try rfl
end ReciprocityTheory.ChartRestriction.G.DVR
