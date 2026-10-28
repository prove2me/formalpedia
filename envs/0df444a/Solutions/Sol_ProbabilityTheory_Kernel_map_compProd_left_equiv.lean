-- Prove2me | solution 1 for ProbabilityTheory.Kernel.map_compProd_left_equiv
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T22:02:14.94373+00:00
-- url     : https://prove2.me/submissions/c258aaea-2443-44b5-a595-da1f85604390

import Mathlib.Probability.Kernel.Composition.CompProd
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
open ProbabilityTheory.Kernel

theorem solution
    {X A B C : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C]
    (κ : Kernel X A) [IsSFiniteKernel κ]
    (η : Kernel (X × A) B) [IsSFiniteKernel η]
    (e : A ≃ᵐ C) :
    (κ ⊗ₖ η).map (Prod.map e id) =
      κ.map e ⊗ₖ η.comap
        (fun z : X × C ↦ (z.1, e.symm z.2))
        (measurable_fst.prodMk (e.symm.measurable.comp measurable_snd)) := by
  have hm : Measurable (Prod.map e (id : B → B)) := e.measurable.prodMap measurable_id
  ext x s hs
  rw [Kernel.map_apply' _ hm _ hs, Kernel.compProd_apply (hm hs), Kernel.compProd_apply hs,
    Kernel.map_apply _ e.measurable, MeasureTheory.lintegral_map _ e.measurable]
  · congr 1
    ext a
    simp [Kernel.comap_apply]
    rfl
  · have := Kernel.measurable_kernel_prodMk_left' hs x
      (η := η.comap (fun z : X × C ↦ (z.1, e.symm z.2))
        (measurable_fst.prodMk (e.symm.measurable.comp measurable_snd)))
    exact this
