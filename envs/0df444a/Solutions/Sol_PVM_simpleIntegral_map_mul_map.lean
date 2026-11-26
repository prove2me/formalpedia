-- Prove2me | solution 1 for PVM.simpleIntegral_map_mul_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:56:39.772384+00:00
-- url     : https://prove2.me/submissions/a55a0d8b-bf3e-4dc9-a6b0-29edd364e9c7

import Definitions.Def_Spectral_PVM_Basic
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.UniformSpace.Dini
import Definitions.Def_Spectral_PVM_Integral
import Theorems.Thm_PVM_simpleIntegral_map

set_option autoImplicit false
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace PVM
theorem _root_.solution (E_pvm : PVM E) {β : Type*}
    (f : SimpleFunc ℝ β) (a b : β → ℂ) :
    E_pvm.simpleIntegral (f.map a) * E_pvm.simpleIntegral (f.map b) =
      E_pvm.simpleIntegral (f.map fun z => a z * b z) := by
  classical
  rw [E_pvm.simpleIntegral_map, E_pvm.simpleIntegral_map, E_pvm.simpleIntegral_map,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Finset.mul_sum, Finset.sum_eq_single z]
  · rw [smul_mul_smul, (E_pvm.isOrthogonalProjection (f ⁻¹' {z})
      (f.measurableSet_fiber z)).2.eq]
  · intro w hw hwz
    have hzw : z ≠ w := Ne.symm hwz
    have hzero : E_pvm.proj (f ⁻¹' {z}) * E_pvm.proj (f ⁻¹' {w}) = 0 := by
      rw [← E_pvm.inter _ _ (f.measurableSet_fiber z) (f.measurableSet_fiber w)]
      have hinter : (f ⁻¹' {z}) ∩ (f ⁻¹' {w}) = ∅ := by
        ext t
        constructor
        · intro ht
          exact hzw ((Set.mem_singleton_iff.mp ht.1).symm.trans
            (Set.mem_singleton_iff.mp ht.2))
        · intro ht
          exact False.elim ht
      rw [hinter, E_pvm.empty]
    rw [smul_mul_smul, hzero, smul_zero]
  · intro hznot
    exact (hznot hz).elim
end PVM
