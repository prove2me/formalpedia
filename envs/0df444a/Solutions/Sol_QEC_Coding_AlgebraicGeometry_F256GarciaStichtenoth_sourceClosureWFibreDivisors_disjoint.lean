-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureWFibreDivisors_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:26:04.498373+00:00
-- url     : https://prove2.me/submissions/67774cf5-4542-4cec-8d3e-2c6924dbc28d

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureFibreDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureRegularDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_CanonicalDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureDifferentialDivisor
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWInfinityFibreDivisor_support
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWInfinityPlaceOfPrime_order_generator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWInfinityRamificationIndex_pos
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWZeroFibreDivisor_support
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWZeroPlaceOfPrime_order_generator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWZeroRamificationIndex_pos


set_option autoImplicit false
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ) :
    Disjoint (sourceGaloisWZeroFibreDivisor m).support
      (sourceGaloisWInfinityFibreDivisor m).support := by
  classical
  apply Finset.disjoint_left.mpr
  intro Q hA hB
  have hA' : Q ∈ Set.range (sourceGaloisWZeroPlaceOfPrime m) := by
    rw [← sourceGaloisWZeroFibreDivisor_support]
    exact hA
  have hB' : Q ∈ Set.range (sourceGaloisWInfinityPlaceOfPrime m) := by
    rw [← sourceGaloisWInfinityFibreDivisor_support]
    exact hB
  obtain ⟨P, rfl⟩ := hA'
  obtain ⟨S, hS⟩ := hB'
  have h := congrArg (fun R : GlobalPlace F256 (SourceGaloisClosureField m) =>
    R.order (sourceGaloisWClosureGenerator m : SourceGaloisClosureField m)) hS
  rw [sourceGaloisWInfinityPlaceOfPrime_order_generator,
    sourceGaloisWZeroPlaceOfPrime_order_generator] at h
  have hα : (0 : ℤ) < sourceGaloisWZeroRamificationIndex m := by
    exact_mod_cast sourceGaloisWZeroRamificationIndex_pos m
  have hβ : (0 : ℤ) < sourceGaloisWInfinityRamificationIndex m := by
    exact_mod_cast sourceGaloisWInfinityRamificationIndex_pos m
  omega
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
