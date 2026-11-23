-- Prove2me | solution 1 for SumProduct.boxMult_card_le_two_mul_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:04:34.21378+00:00
-- url     : https://prove2.me/submissions/a2581f85-ec3d-4e04-8f3d-29315304530d

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_Blichfeldt
import Definitions.Def_SumProduct_UnitSeparation
import Definitions.Def_SumProduct_GoldenRatio
import Definitions.Def_SumProduct_CubeSectionHensley
import Definitions.Def_SumProduct_MultiplicativeCount
import Theorems.Thm_SumProduct_torsionOrder_eq_two_of_totallyReal
import Theorems.Thm_SumProduct_mem_boxMult
import Theorems.Thm_SumProduct_mem_cubeSection
attribute [local simp] SumProduct.mem_boxMult
attribute [local simp] SumProduct.mem_cubeSection



set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open scoped Classical
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem
namespace SumProduct
theorem _root_.solution {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] {Y : ℝ} :
    (boxMult K Y).card
      ≤ 2 * ((boxMult K Y).image (fun u => logEmbedding K (Additive.ofMul u))).card := by
  letI : Fintype (torsion K) := Fintype.ofFinite (torsion K)
  refine Finset.card_le_mul_card_image _ 2 (fun p _ => ?_)
  rw [← torsionOrder_eq_two_of_totallyReal (K := K), torsionOrder]
  rcases (((boxMult K Y).filter
      (fun u => logEmbedding K (Additive.ofMul u) = p))).eq_empty_or_nonempty
    with he | ⟨u₀, hu₀⟩
  · rw [he]; simp
  · rw [Finset.mem_filter] at hu₀
    obtain ⟨-, hu₀p⟩ := hu₀
    have key : ∀ u ∈ (boxMult K Y).filter (fun u => logEmbedding K (Additive.ofMul u) = p),
        u * u₀⁻¹ ∈ torsion K := by
      intro u hu
      rw [Finset.mem_filter] at hu
      rw [← logEmbedding_eq_zero_iff]
      have he2 : Additive.ofMul (u * u₀⁻¹) = Additive.ofMul u - Additive.ofMul u₀ := rfl
      rw [he2, map_sub, hu.2, hu₀p, sub_self]
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
    refine Finset.card_le_card_of_injOn
      (fun u => if h : u * u₀⁻¹ ∈ torsion K then (⟨u * u₀⁻¹, h⟩ : torsion K) else 1)
      (fun u _ => Finset.mem_univ _) ?_
    intro u hu u' hu' heq
    rw [Finset.mem_coe] at hu hu'
    simp only [dif_pos (key u hu), dif_pos (key u' hu')] at heq
    exact mul_right_cancel (Subtype.ext_iff.mp heq)
end SumProduct
