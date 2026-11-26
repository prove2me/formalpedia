-- Prove2me | solution 1 for PVM.simpleIntegral_piecewise_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:56:59.036104+00:00
-- url     : https://prove2.me/submissions/c3ed579c-0408-4a10-93cc-162c225b2fb2

import Definitions.Def_Spectral_PVM_Basic
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.UniformSpace.Dini
import Definitions.Def_Spectral_PVM_Integral
import Theorems.Thm_PVM_simpleIntegral_const
import Theorems.Thm_PVM_simpleIntegral_zero
import Theorems.Thm_PVM_simpleIntegral_one
attribute [local simp] PVM.simpleIntegral_zero
attribute [local simp] PVM.simpleIntegral_one

set_option autoImplicit false
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
namespace PVM
theorem _root_.solution (E_pvm : PVM E)
    (S : Set ℝ) (hS : MeasurableSet S) (z : ℂ) :
    E_pvm.simpleIntegral
        (SimpleFunc.piecewise S hS (SimpleFunc.const ℝ z) (SimpleFunc.const ℝ 0)) =
      z • E_pvm.proj S := by
  classical
  by_cases hS_empty : S = ∅
  · subst S
    rw [SimpleFunc.piecewise_empty, E_pvm.simpleIntegral_const, zero_smul,
      E_pvm.empty, smul_zero]
  · by_cases hS_univ : S = Set.univ
    · subst S
      rw [SimpleFunc.piecewise_univ, E_pvm.simpleIntegral_const, E_pvm.univ]
    · by_cases hz : z = 0
      · subst z
        have hzero :
            SimpleFunc.piecewise S hS (SimpleFunc.const ℝ (0 : ℂ))
              (SimpleFunc.const ℝ 0) = 0 := by
          rw [show (0 : SimpleFunc ℝ ℂ) = SimpleFunc.const ℝ 0 by ext t; rfl]
          exact SimpleFunc.piecewise_same _ hS
        rw [hzero, E_pvm.simpleIntegral_zero, zero_smul]
      · rw [PVM.simpleIntegral,
          SimpleFunc.range_indicator hS (Set.nonempty_iff_ne_empty.mpr hS_empty) hS_univ z 0]
        rw [Finset.sum_insert (by
          intro hzmem
          exact hz (Finset.mem_singleton.mp hzmem)), Finset.sum_singleton]
        have hpre :
            (SimpleFunc.piecewise S hS (SimpleFunc.const ℝ z) (SimpleFunc.const ℝ 0) ⁻¹'
              {z}) = S := by
          ext t
          simp only [SimpleFunc.piecewise_apply, SimpleFunc.const_apply, Set.mem_preimage,
            Set.mem_singleton_iff]
          by_cases ht : t ∈ S
          · rw [if_pos ht]
            exact iff_of_true rfl ht
          · rw [if_neg ht]
            exact iff_of_false (Ne.symm hz) ht
        rw [hpre, zero_smul, add_zero]
end PVM
