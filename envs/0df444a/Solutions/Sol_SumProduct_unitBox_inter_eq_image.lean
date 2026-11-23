-- Prove2me | solution 1 for SumProduct.unitBox_inter_eq_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:59:48.314465+00:00
-- url     : https://prove2.me/submissions/a6d0abed-d2e3-4c44-9bab-e903a4498a3b

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_Blichfeldt
import Definitions.Def_SumProduct_UnitSeparation
import Definitions.Def_SumProduct_GoldenRatio
import Definitions.Def_SumProduct_CubeSectionHensley
import Definitions.Def_SumProduct_MultiplicativeCount
import Theorems.Thm_SumProduct_logEmbedding_mem_unitBox_iff


set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open scoped Classical
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem
namespace SumProduct
theorem _root_.solution {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] {Y : ℝ} :
    ↑(unitLattice K) ∩ unitBox K Y
      = ↑((boxMult K Y).image (fun u => logEmbedding K (Additive.ofMul u))) := by
  ext p
  rw [Finset.coe_image, Set.mem_image]
  constructor
  · rintro ⟨hp1, hp2⟩
    rw [SetLike.mem_coe, unitLattice, Submodule.mem_map] at hp1
    obtain ⟨x, -, hx⟩ := hp1
    have hx' : logEmbedding K x = p := hx
    refine ⟨Additive.toMul x, ?_, ?_⟩
    · rw [Finset.mem_coe, ← logEmbedding_mem_unitBox_iff]
      change logEmbedding K x ∈ unitBox K Y
      rw [hx']; exact hp2
    · change logEmbedding K x = p
      exact hx'
  · rintro ⟨u, hu, rfl⟩
    rw [Finset.mem_coe] at hu
    refine ⟨?_, ?_⟩
    · rw [SetLike.mem_coe, unitLattice, Submodule.mem_map]
      exact ⟨Additive.ofMul u, Submodule.mem_top, rfl⟩
    · rw [logEmbedding_mem_unitBox_iff]; exact hu
end SumProduct
