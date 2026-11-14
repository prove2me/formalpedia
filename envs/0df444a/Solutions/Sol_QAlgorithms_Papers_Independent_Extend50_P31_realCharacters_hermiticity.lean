-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P31.realCharacters_hermiticity
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T05:34:09.225784+00:00
-- url     : https://prove2.me/submissions/d988bc73-5011-464e-95c8-aab461bba7a4

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
noncomputable section
open scoped Matrix ComplexConjugate
open QAlgorithms.Papers.Independent.Extend50.P31
open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)
open QAlgorithms.Papers.Independent.Information100.P34 (choi)
open QAlgorithms.Papers.Independent.Dependency50.P16
set_option backward.isDefEq.respectTransparency false
variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}

set_option autoImplicit false

set_option autoImplicit false
open QAlgorithms.Papers.Independent.Extend50.P31
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq



open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Bridge50.P37 (hsAdjoint)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)

open QAlgorithms.Papers.Independent.Information100.P75 (phase)

variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}

/-- PDF p.17, consequence of Eqs.(85),(86); coefficient reality is not asserted. -/
theorem solution (D : Data G A n) (P : Pivots D)
    (hreal : ∀ a : A, ∀ g : G, (character (D.F.irrep a) g).im = 0) :
    (∀ a : OccurringIrrep D, (choi (centralMap D.U D.F a.val)).IsHermitian) ∧
    ∀ a : OccurringIrrep D, ∀ r, (spectralMatrix D P r a).im = 0 := by
  have hc (a : A) (g : G) : conj (character (D.F.irrep a) g) = character (D.F.irrep a) g :=
    Complex.conj_eq_iff_im.mpr (hreal a g)
  constructor
  · intro a
    apply Matrix.ext
    intro p q
    change conj (centralMap D.U D.F a.val (matrixUnit q.1 p.1) q.2 p.2) =
      centralMap D.U D.F a.val (matrixUnit p.1 q.1) p.2 q.2
    simp [centralMap,conjugationMap,sandwich,LinearMap.sum_apply,Matrix.sum_apply,
      Matrix.mul_apply,matrixUnit,Matrix.single_apply,ite_and,
      Matrix.conjTranspose_apply,map_sum,map_mul,map_smul,hc, mul_comm,mul_left_comm,mul_assoc]
  · intro a r
    change (muAt D a.val r (P.pivot r)).im = 0
    apply Complex.conj_eq_iff_im.mp
    simp [muAt,map_sum,map_mul,hc]
