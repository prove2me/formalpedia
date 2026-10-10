-- Prove2me | solution 1 for WeilDefect.MarkerStability.submodule_dimension_difference_le_analysis_card
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T20:04:14.726002+00:00
-- url     : https://prove2.me/submissions/e5ba8afd-0122-41e7-b74f-4053ee00b987

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false
open scoped Classical
noncomputable section
theorem solution
    {V J : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Fintype J]
    (U W : Submodule ℂ V) (hWU : W ≤ U) (L : V →ₗ[ℂ] (J → ℂ))
    (hker : ∀ v ∈ U, L v = 0 ↔ v ∈ W) :
    Module.finrank ℂ U - Module.finrank ℂ W ≤ Fintype.card J := by
  let f := L.comp U.subtype
  have he : LinearMap.ker f = W.comap U.subtype := by
    ext v
    exact hker v.1 v.2
  have hd : Module.finrank ℂ (LinearMap.ker f) = Module.finrank ℂ W := by
    rw [he]
    exact (Submodule.comapSubtypeEquivOfLe hWU).finrank_eq
  have hn := f.finrank_range_add_finrank_ker
  rw [hd] at hn
  rw [← Nat.eq_sub_of_add_eq hn]
  simpa only [Module.finrank_pi] using (Submodule.finrank_le (LinearMap.range f))
