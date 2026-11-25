-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_finite_integralClosure_mvPolynomial_a1f9e8023895
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:42:17.335563+00:00
-- url     : https://prove2.me/submissions/0dfe3d56-ac98-4b57-8e81-ea8c410f979a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_FiniteIntegralClosureCharP
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_module_finite_of_semilinear_0775f0fbfa71
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_mvPolynomial_finite_frobenius_range_091c722b10a9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open scoped nonZeroDivisors
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution (p : ℕ) [Fact p.Prime] (s : ℕ)
    (F : Type*) [Field F] [Algebra (MvPolynomial (Fin s) (ZMod p)) F]
    [IsFractionRing (MvPolynomial (Fin s) (ZMod p)) F]
    (L : Type*) [Field L] [Algebra F L] [FiniteDimensional F L]
    [Algebra (MvPolynomial (Fin s) (ZMod p)) L]
    [IsScalarTower (MvPolynomial (Fin s) (ZMod p)) F L] :
    Module.Finite (MvPolynomial (Fin s) (ZMod p))
      (integralClosure (MvPolynomial (Fin s) (ZMod p)) L) := by
  set B := MvPolynomial (Fin s) (ZMod p)
  have hp : p.Prime := Fact.out
  have hinjBL : Function.Injective (algebraMap B L) := by
    rw [IsScalarTower.algebraMap_eq B F L]
    exact (algebraMap F L).injective.comp (IsFractionRing.injective B F)
  have : CharP L p :=
    charP_of_injective_ringHom (f := (algebraMap B L).comp MvPolynomial.C)
      (hinjBL.comp (MvPolynomial.C_injective (Fin s) (ZMod p))) p
  set Ls := separableClosure F L
  have : ExpChar Ls p := ExpChar.prime hp
  have : IsScalarTower B Ls L := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply B F L, IsScalarTower.algebraMap_apply B F Ls,
      IsScalarTower.algebraMap_apply F Ls L]
  have : IsPurelyInseparable Ls L := separableClosure.isPurelyInseparable F L
  set e := IsPurelyInseparable.exponent Ls L
  let fr : L →+* Ls := IsPurelyInseparable.iterateFrobenius Ls L p (le_refl e)
  have hfr : ∀ y, algebraMap Ls L (fr y) = y ^ p ^ e := fun y =>
    IsPurelyInseparable.algebraMap_iterateFrobenius Ls p (le_refl e) y
  have hinjLs : Function.Injective (algebraMap Ls L) := (algebraMap Ls L).injective
  have : Algebra.IsSeparable F Ls := separableClosure.isSeparable F L
  have : Module.Finite B (integralClosure B Ls) :=
    IsIntegralClosure.finite B F Ls (integralClosure B Ls)
  have := mvPolynomial_finite_frobenius_range p s e
  have hint : ∀ y : integralClosure B L, IsIntegral B (fr y) := fun y =>
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom B Ls L) hinjLs).mp (by
      rw [IsScalarTower.toAlgHom_apply, hfr]
      exact y.2.pow _)
  let φ : integralClosure B L →+ integralClosure B Ls :=
    { toFun := fun y => ⟨fr y, hint y⟩
      map_zero' := by ext; simp
      map_add' := fun y z => by ext; simp }
  refine module_finite_of_semilinear (iterateFrobenius B p e).rangeRestrict
    (iterateFrobenius B p e).rangeRestrict_surjective φ ?_ ?_
  · intro y z h
    have h' : fr y = fr z := congrArg Subtype.val h
    exact Subtype.ext (fr.injective h')
  · intro b y
    apply Subtype.ext
    apply hinjLs
    change algebraMap Ls L (fr (b • (y : L))) =
      algebraMap Ls L (((iterateFrobenius B p e b : B) • fr y))
    rw [hfr, Algebra.smul_def, Algebra.smul_def, map_mul, hfr, iterateFrobenius_def, mul_pow,
      ← map_pow, ← IsScalarTower.algebraMap_apply]
end GroundTheory.Heights₂.Heights.Model
