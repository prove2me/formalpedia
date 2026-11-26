-- Prove2me | solution 1 for PVM.simpleIntegral_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:56:38.599687+00:00
-- url     : https://prove2.me/submissions/35d78bdf-c5a3-4833-96cd-6ba6c4e2bd3d

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
theorem _root_.solution (E_pvm : PVM E) (f g : SimpleFunc ℝ ℂ) :
    E_pvm.simpleIntegral (f + g) = E_pvm.simpleIntegral f + E_pvm.simpleIntegral g := by
  calc
    E_pvm.simpleIntegral (f + g) =
        ∑ p ∈ (f.pair g).range,
          (p.1 + p.2) • E_pvm.proj (f.pair g ⁻¹' {p}) := by
      rw [SimpleFunc.add_eq_map₂, E_pvm.simpleIntegral_map]
    _ = (∑ p ∈ (f.pair g).range,
          p.1 • E_pvm.proj (f.pair g ⁻¹' {p})) +
        ∑ p ∈ (f.pair g).range,
          p.2 • E_pvm.proj (f.pair g ⁻¹' {p}) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      rw [add_smul]
    _ = E_pvm.simpleIntegral ((f.pair g).map Prod.fst) +
        E_pvm.simpleIntegral ((f.pair g).map Prod.snd) := by
      rw [E_pvm.simpleIntegral_map, E_pvm.simpleIntegral_map]
    _ = E_pvm.simpleIntegral f + E_pvm.simpleIntegral g := by
      rw [SimpleFunc.map_fst_pair, SimpleFunc.map_snd_pair]
end PVM
