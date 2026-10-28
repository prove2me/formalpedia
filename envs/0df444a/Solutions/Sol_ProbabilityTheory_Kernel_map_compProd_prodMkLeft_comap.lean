-- Prove2me | solution 1 for ProbabilityTheory.Kernel.map_compProd_prodMkLeft_comap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T17:44:19.237464+00:00
-- url     : https://prove2.me/submissions/a38bff82-c418-4d05-9a6c-3eb9be50384c

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Probability.Kernel.Composition.CompProd
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
open ProbabilityTheory.Kernel

theorem solution
    {X A B C D T : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D] [MeasurableSpace T]
    (κ : Kernel X A) [IsSFiniteKernel κ]
    (η : Kernel T B) [IsSFiniteKernel η]
    (terminal : A → T)
    (terminal' : C → T) (hterminal' : Measurable terminal')
    (f : A → C) (hf : Measurable f) (g : B → D) (hg : Measurable g)
    (hcompat : terminal' ∘ f = terminal) :
    (κ ⊗ₖ Kernel.prodMkLeft X
      (η.comap terminal (hcompat ▸ hterminal'.comp hf))).map (Prod.map f g) =
      κ.map f ⊗ₖ
        Kernel.prodMkLeft X ((η.map g).comap terminal' hterminal') := by
  have hpair : Measurable (Prod.map f g) := hf.prodMap hg
  ext x s hs
  rw [Kernel.map_apply' _ hpair x hs,
    Kernel.compProd_apply (hs.preimage hpair), Kernel.compProd_apply hs]
  rw [Kernel.map_apply κ hf x]
  rw [MeasureTheory.lintegral_map]
  · congr with a
    rw [Kernel.prodMkLeft_apply', Kernel.prodMkLeft_apply',
      Kernel.comap_apply, Kernel.comap_apply,
      Kernel.map_apply' _ hg _ (measurable_prodMk_left hs)]
    rw [← congrFun hcompat a]
    rfl
  · exact Kernel.measurable_kernel_prodMk_left' hs x
  · exact hf
