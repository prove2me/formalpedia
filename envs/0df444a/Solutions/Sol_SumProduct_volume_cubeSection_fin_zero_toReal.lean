-- Prove2me | solution 1 for SumProduct.volume_cubeSection_fin_zero_toReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:56:22.538344+00:00
-- url     : https://prove2.me/submissions/760b8d02-192d-4607-a089-8578c6ce318a

import Definitions.Def_SumProduct_CubeSectionCore
import Definitions.Def_SumProduct_CubeSectionHensley
import Theorems.Thm_SumProduct_mem_boxMult
import Theorems.Thm_SumProduct_mem_cubeSection
attribute [local simp] SumProduct.mem_boxMult
attribute [local simp] SumProduct.mem_cubeSection



set_option autoImplicit true
open MeasureTheory
open scoped Pointwise
open SumProduct
namespace SumProduct
theorem _root_.solution :
    (volume (cubeSection (Fin 0) 1)).toReal = 1 := by
  have huniv : cubeSection (Fin 0) 1 = Set.univ := by
    ext x; simp [mem_cubeSection]
  rw [huniv, show (Set.univ : Set (Fin 0 → ℝ)) = Set.univ.pi fun _ => Set.univ by
      ext x; simp, volume_pi_pi]
  simp
end SumProduct
