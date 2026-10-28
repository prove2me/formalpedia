-- Prove2me | solution 1 for ProbabilityTheory.Kernel.map_compProd_prodMkLeft_right
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T17:44:13.893727+00:00
-- url     : https://prove2.me/submissions/5e073f51-28fc-45b0-8f1e-0a3a127d8f1f

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
    {X A B C : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C]
    (κ : Kernel X A) [IsSFiniteKernel κ]
    (η : Kernel A B) [IsSFiniteKernel η]
    (f : B → C) (hf : Measurable f) :
    (κ ⊗ₖ Kernel.prodMkLeft X η).map (fun z ↦ (z.1, f z.2)) =
      κ ⊗ₖ Kernel.prodMkLeft X (η.map f) := by
  have hpair : Measurable (fun z : A × B ↦ (z.1, f z.2)) :=
    measurable_fst.prodMk (hf.comp measurable_snd)
  ext x s hs
  rw [Kernel.map_apply' _ hpair x hs,
    Kernel.compProd_apply (hs.preimage hpair), Kernel.compProd_apply hs]
  congr with a
  rw [Kernel.prodMkLeft_apply', Kernel.prodMkLeft_apply',
    Kernel.map_apply' _ hf _ (measurable_prodMk_left hs)]
  rfl
