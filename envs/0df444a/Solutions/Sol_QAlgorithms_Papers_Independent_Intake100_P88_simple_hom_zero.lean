-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P88.simple_hom_zero
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T18:23:00.246598+00:00
-- url     : https://prove2.me/submissions/67045eb4-2d6b-4326-abe3-a0f0a6de9298

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P88

theorem solution (F A M N : Type*) [Field F] [IsAlgClosed F]
    [Ring A] [Algebra F A] [FiniteDimensional F A]
    [AddCommGroup M] [AddCommGroup N] [Module F M] [Module F N]
    [Module A M] [Module A N] [IsScalarTower F A M] [IsScalarTower F A N]
    [IsSimpleModule A M] [IsSimpleModule A N] (_hne : ¬ Nonempty (M ≃ₗ[A] N)) :
    ∀ f : M →ₗ[A] N, f = 0 := by
  intro f
  by_contra h
  exact _hne ⟨LinearEquiv.ofBijective f (LinearMap.bijective_of_ne_zero h)⟩
