-- Prove2me | solution 1 for TrDegJac.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-22T04:01:18.000112+00:00
-- url     : https://prove2.me/submissions/6ab15f90-acfb-4e98-9877-af1467ed90f2

import Mathlib

set_option autoImplicit false

theorem solution {F E K : Type*} [Field F] [Field E] [Field K] [Algebra F E] [Algebra E K]
    [Algebra F K] [IsScalarTower F E K] (γ : K) (hγ : IsAlgebraic F γ) :
    Module.rank E (IntermediateField.adjoin E {γ}) ≤
      Module.rank F (IntermediateField.adjoin F {γ}) := by
  have hIntF : IsIntegral F γ := hγ.isIntegral
  have hIntE : IsIntegral E γ := hIntF.tower_top
  haveI : FiniteDimensional E (IntermediateField.adjoin E {γ}) :=
    IntermediateField.adjoin.finiteDimensional hIntE
  haveI : FiniteDimensional F (IntermediateField.adjoin F {γ}) :=
    IntermediateField.adjoin.finiteDimensional hIntF
  have hdvd : minpoly E γ ∣ (minpoly F γ).map (algebraMap F E) :=
    minpoly.dvd_map_of_isScalarTower F E γ
  have hne : (minpoly F γ).map (algebraMap F E) ≠ 0 :=
    ((minpoly.monic hIntF).map (algebraMap F E)).ne_zero
  have hdeg : (minpoly E γ).natDegree ≤ (minpoly F γ).natDegree :=
    calc (minpoly E γ).natDegree
        ≤ ((minpoly F γ).map (algebraMap F E)).natDegree :=
          Polynomial.natDegree_le_of_dvd hdvd hne
      _ ≤ (minpoly F γ).natDegree := Polynomial.natDegree_map_le
  have hrankE : Module.rank E (IntermediateField.adjoin E {γ})
      = (Module.finrank E (IntermediateField.adjoin E {γ}) : Cardinal) :=
    (Module.finrank_eq_rank' E _).symm
  have hrankF : Module.rank F (IntermediateField.adjoin F {γ})
      = (Module.finrank F (IntermediateField.adjoin F {γ}) : Cardinal) :=
    (Module.finrank_eq_rank' F _).symm
  rw [hrankE, hrankF, IntermediateField.adjoin.finrank hIntE,
    IntermediateField.adjoin.finrank hIntF]
  exact Nat.cast_le.mpr hdeg
