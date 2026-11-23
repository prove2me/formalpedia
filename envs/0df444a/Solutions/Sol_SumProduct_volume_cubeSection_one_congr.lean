-- Prove2me | solution 1 for SumProduct.volume_cubeSection_one_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:54:53.334818+00:00
-- url     : https://prove2.me/submissions/edaf632c-71c8-4088-b799-4210822c0534

import Definitions.Def_SumProduct_Boxes
import Definitions.Def_SumProduct_CubeSection
import Theorems.Thm_SumProduct_mem_cubeSection
import Theorems.Thm_SumProduct_measurableSet_cubeSection
import Theorems.Thm_SumProduct_mem_boxMult
attribute [local simp] SumProduct.mem_boxMult


attribute [local simp] SumProduct.mem_cubeSection

set_option autoImplicit true
open MeasureTheory
open scoped Pointwise
open SumProduct
variable {ι : Type*} [Fintype ι]
open scoped Classical
namespace SumProduct
theorem _root_.solution (ι : Type*) [Fintype ι] :
    volume (cubeSection ι 1) = volume (cubeSection (Fin (Fintype.card ι)) 1) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let T := MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e
  have happ : ∀ (x : Fin (Fintype.card ι) → ℝ) (a), T x (e a) = x a :=
    fun x a => MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : ι => ℝ) e x a
  have hmp : MeasurePreserving T volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : ι => ℝ) e
  have hpre : T ⁻¹' (cubeSection ι 1) = cubeSection (Fin (Fintype.card ι)) 1 := by
    ext x
    simp only [Set.mem_preimage, mem_cubeSection]
    have hsum : ∑ i, T x i = ∑ a, x a :=
      (Fintype.sum_equiv e (fun a => x a) (fun i => T x i) (fun a => (happ x a).symm)).symm
    refine ⟨fun h => ⟨fun a => ?_, ?_⟩, fun h => ⟨fun i => ?_, ?_⟩⟩
    · have hi := h.1 (e a); rwa [happ] at hi
    · rw [← hsum]; exact h.2
    · have hi := h.1 (e.symm i); rwa [← happ x (e.symm i), e.apply_symm_apply] at hi
    · rw [hsum]; exact h.2
  rw [← hmp.measure_preimage (measurableSet_cubeSection (ι := ι) 1).nullMeasurableSet, hpre]
end SumProduct
