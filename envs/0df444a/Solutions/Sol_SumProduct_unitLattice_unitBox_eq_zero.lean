-- Prove2me | solution 1 for SumProduct.unitLattice_unitBox_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:59:16.82604+00:00
-- url     : https://prove2.me/submissions/ccab5365-b57a-4fd2-aefd-98b45e713ad5

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_Blichfeldt
import Definitions.Def_SumProduct_UnitSeparation
import Definitions.Def_SumProduct_GoldenRatio
import Definitions.Def_SumProduct_CubeSectionHensley
import Definitions.Def_SumProduct_MultiplicativeCount
import Theorems.Thm_SumProduct_logEmbedding_mem_unitBox_iff
import Theorems.Thm_SumProduct_mem_boxMult
import Theorems.Thm_SumProduct_two_fifths_lt_log_goldenRatio
import Theorems.Thm_SumProduct_unit_separation
attribute [local simp] SumProduct.mem_boxMult



set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open scoped Classical
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem
  NumberField.InfinitePlace Real
namespace SumProduct
theorem _root_.solution {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] {p : logSpace K}
    (hp : p ∈ unitLattice K) (hp2 : p ∈ unitBox K (2 / 5)) : p = 0 := by
  rw [unitLattice, Submodule.mem_map] at hp
  obtain ⟨x, -, hx⟩ := hp
  have hx' : logEmbedding K x = p := hx
  set v : (𝓞 K)ˣ := Additive.toMul x with hv
  have hvx : Additive.ofMul v = x := rfl
  have hvbox : v ∈ boxMult K (2 / 5) := by
    rw [← logEmbedding_mem_unitBox_iff, hvx, hx']; exact hp2
  rw [mem_boxMult] at hvbox
  have hsep : ∀ w : InfinitePlace K,
      goldenRatio⁻¹ < w ((v : 𝓞 K) : K) ∧ w ((v : 𝓞 K) : K) < goldenRatio := by
    intro w
    have hwpos : 0 < w ((v : 𝓞 K) : K) :=
      NumberField.InfinitePlace.pos_iff.mpr (NumberField.Units.coe_ne_zero _)
    have hlog : |Real.log (w ((v : 𝓞 K) : K))| < Real.log goldenRatio :=
      lt_of_le_of_lt (hvbox w) two_fifths_lt_log_goldenRatio
    rw [abs_lt] at hlog
    obtain ⟨hl1, hl2⟩ := hlog
    refine ⟨?_, ?_⟩
    · have h := Real.exp_lt_exp.mpr hl1
      rwa [Real.exp_log hwpos, Real.exp_neg, Real.exp_log goldenRatio_pos] at h
    · have h := Real.exp_lt_exp.mpr hl2
      rwa [Real.exp_log hwpos, Real.exp_log goldenRatio_pos] at h
  rw [← hx', ← hvx, logEmbedding_eq_zero_iff]
  rcases unit_separation K v hsep with h | h
  · rw [h]; exact one_mem _
  · rw [h]; exact neg_one_mem_torsion
end SumProduct
