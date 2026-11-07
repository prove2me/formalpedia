-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.specialLinear_fixed_projective_is_homothety
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:44:33.298094+00:00
-- url     : https://prove2.me/submissions/a63ffb45-f11c-4f45-908a-6c6011eede00

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
import Mathlib.GroupTheory.GroupAction.Iwasawa
import Mathlib.GroupTheory.IsPerfect
import Mathlib.LinearAlgebra.Center
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Independence
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_SpecialLinear

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Matrix
open scoped commutatorElement
open scoped Pointwise
open scoped LinearAlgebra.Projectivization
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Free K V]
    (a : SpecialLinearGroup K V)
    (hfix : ∀ x : ℙ K V, a • x = x) :
    ∃ c : K, (a : V ≃ₗ[K] V).toLinearMap = c • 1 := by
  apply LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
  intro v
  by_cases hv : v = 0
  · subst v
    intro hli
    exact (hli.ne_zero 0) rfl
  have hav : a v ≠ 0 :=
    (a : V ≃ₗ[K] V).map_ne_zero_iff.mpr hv
  intro hli
  have hind : Projectivization.Independent
      ![Projectivization.mk K v hv, Projectivization.mk K (a v) hav] :=
    (Projectivization.independent_mk_iff_LinearIndependent hv hav).2 hli
  have hne := (Projectivization.independent_pair_iff_ne _ _).1 hind
  apply hne
  have hs := hfix (Projectivization.mk K v hv)
  rw [Projectivization.specialLinearGroup_smul_def,
    Projectivization.smul_mk] at hs
  exact hs.symm
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
