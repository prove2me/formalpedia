-- Prove2me | solution 1 for SumProduct.unitLattice_multiplicity_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:56:33.778799+00:00
-- url     : https://prove2.me/submissions/8bf5b7d6-e9d9-4553-abf2-bbdf4a157fa7

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_Blichfeldt
import Definitions.Def_SumProduct_UnitSeparation
import Definitions.Def_SumProduct_GoldenRatio
import Definitions.Def_SumProduct_CubeSectionHensley
import Definitions.Def_SumProduct_MultiplicativeCount
import Theorems.Thm_SumProduct_mem_boxMult
import Theorems.Thm_SumProduct_mem_cubeSection
import Theorems.Thm_SumProduct_sub_mem_unitBox
attribute [local simp] SumProduct.mem_boxMult
attribute [local simp] SumProduct.mem_cubeSection



set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open scoped Classical
open MeasureTheory NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem
namespace SumProduct
theorem _root_.solution {K : Type*} [Field K] [NumberField K] {Y : ℝ}
    (y : logSpace K) :
    ∑' l : ↥(unitLattice K), (unitBox K (Y / 2)).indicator (fun _ => (1 : ENNReal)) (l +ᵥ y)
      ≤ (↑(unitLattice K) ∩ unitBox K Y).encard := by
  have hfun : (fun l : ↥(unitLattice K) =>
        (unitBox K (Y / 2)).indicator (fun _ => (1 : ENNReal)) (l +ᵥ y))
      = {l : ↥(unitLattice K) | l +ᵥ y ∈ unitBox K (Y / 2)}.indicator (fun _ => 1) := by
    funext l
    by_cases h : l +ᵥ y ∈ unitBox K (Y / 2)
    · have h' : l ∈ {l : ↥(unitLattice K) | l +ᵥ y ∈ unitBox K (Y / 2)} := h
      rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
    · have h' : l ∉ {l : ↥(unitLattice K) | l +ᵥ y ∈ unitBox K (Y / 2)} := h
      rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']
  rw [hfun, ← tsum_subtype, ENNReal.tsum_set_one]
  have hle : {l : ↥(unitLattice K) | l +ᵥ y ∈ unitBox K (Y / 2)}.encard
      ≤ (↑(unitLattice K) ∩ unitBox K Y).encard := by
    rcases Set.eq_empty_or_nonempty {l : ↥(unitLattice K) | l +ᵥ y ∈ unitBox K (Y / 2)}
      with he | ⟨l₀, hl₀⟩
    · rw [he]; simp
    · have hl₀mem : (l₀ : logSpace K) + y ∈ unitBox K (Y / 2) := hl₀
      calc {l : ↥(unitLattice K) | l +ᵥ y ∈ unitBox K (Y / 2)}.encard
          = ((fun l : ↥(unitLattice K) => ((l - l₀ : ↥(unitLattice K)) : logSpace K)) ''
              {l : ↥(unitLattice K) | l +ᵥ y ∈ unitBox K (Y / 2)}).encard := by
            refine (Set.InjOn.encard_image ?_).symm
            intro a _ b _ hab
            simp only [] at hab
            exact sub_left_inj.mp (Subtype.coe_injective hab)
        _ ≤ (↑(unitLattice K) ∩ unitBox K Y).encard := by
            refine Set.encard_le_encard ?_
            rintro _ ⟨l, hl, rfl⟩
            have hlmem : (l : logSpace K) + y ∈ unitBox K (Y / 2) := hl
            have hcoe : ((l - l₀ : ↥(unitLattice K)) : logSpace K)
                = ((l : logSpace K) + y) - ((l₀ : logSpace K) + y) := by
              rw [AddSubgroupClass.coe_sub]; abel
            refine ⟨SetLike.coe_mem _, ?_⟩
            change ((l - l₀ : ↥(unitLattice K)) : logSpace K) ∈ unitBox K Y
            rw [hcoe, show Y = Y / 2 + Y / 2 by ring]
            exact sub_mem_unitBox hlmem hl₀mem
  exact_mod_cast hle
end SumProduct
