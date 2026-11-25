-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_finite_integralClosure_of_charP_65f7d60edb2f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:10:22.896235+00:00
-- url     : https://prove2.me/submissions/e1f27dc6-0da8-4072-8392-ff54cd117506

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_FiniteIntegralClosureCharP
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_finite_integralClosure_mvPolynomial_a1f9e8023895

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
theorem _root_.solution (p : ℕ) [Fact p.Prime]
    (A : Type*) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A] [CharP A p]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A K L] :
    Module.Finite A (integralClosure A L) := by
  let : Algebra (ZMod p) A := ZMod.algebra A p
  have : Algebra.FiniteType (ZMod p) A :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ZMod p) A
  obtain ⟨s, g, hginj, hgfin⟩ := exists_finite_inj_algHom_of_fg (ZMod p) A
  set B := MvPolynomial (Fin s) (ZMod p)
  let : Algebra B A := g.toRingHom.toAlgebra
  have : Module.Finite B A := hgfin
  let : Algebra B K := ((algebraMap A K).comp (algebraMap B A)).toAlgebra
  let : Algebra B L := ((algebraMap A L).comp (algebraMap B A)).toAlgebra
  have : IsScalarTower B A K := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B A L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B K L := IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap A L (algebraMap B A x) = algebraMap K L (algebraMap A K (algebraMap B A x))
    exact IsScalarTower.algebraMap_apply A K L _
  have hinjBK : Function.Injective (algebraMap B K) :=
    (IsFractionRing.injective A K).comp hginj
  have : FaithfulSMul B K := (faithfulSMul_iff_algebraMap_injective B K).mpr hinjBK
  let : Algebra (FractionRing B) K := FractionRing.liftAlgebra B K
  let : Algebra (FractionRing B) L :=
    ((algebraMap K L).comp (algebraMap (FractionRing B) K)).toAlgebra
  have : IsScalarTower (FractionRing B) K L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B (FractionRing B) L := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply (FractionRing B) K L,
      ← IsScalarTower.algebraMap_apply B (FractionRing B) K,
      ← IsScalarTower.algebraMap_apply B K L]
  have : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  have : FiniteDimensional (FractionRing B) K := by
    obtain ⟨t, ht⟩ := (Module.Finite.fg_top : (⊤ : Submodule B A).FG)
    let T : Set K := algebraMap A K '' t
    have hTint : ∀ x ∈ T, IsIntegral (FractionRing B) x := by
      rintro _ ⟨a, -, rfl⟩
      have : IsIntegral B (algebraMap A K a) :=
        (Algebra.IsIntegral.isIntegral a).map (IsScalarTower.toAlgHom B A K)
      exact this.tower_top
    have : Finite T := (t.finite_toSet.image _).to_subtype
    have hfd := IntermediateField.finiteDimensional_adjoin hTint
    have htop : IntermediateField.adjoin (FractionRing B) T = ⊤ := by
      rw [eq_top_iff]
      rintro x -
      have hA : ∀ a : A, algebraMap A K a ∈ IntermediateField.adjoin (FractionRing B) T := by
        intro a
        have ha : a ∈ Submodule.span B (t : Set A) := ht ▸ Submodule.mem_top
        induction ha using Submodule.span_induction with
        | mem y hy => exact IntermediateField.subset_adjoin (FractionRing B) T ⟨y, hy, rfl⟩
        | zero => simp
        | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
        | smul b y _ hy =>
          rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
            IsScalarTower.algebraMap_apply B (FractionRing B) K]
          exact mul_mem (IntermediateField.algebraMap_mem _ _) hy
      obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := A) x
      exact div_mem (hA a) (hA b)
    rw [htop] at hfd
    exact (IntermediateField.topEquiv (F := FractionRing B) (E := K)).toLinearEquiv.finiteDimensional
  have : FiniteDimensional (FractionRing B) L := Module.Finite.trans K L
  have hB := finite_integralClosure_mvPolynomial p s (FractionRing B) L
  have hle : (integralClosure A L).toSubmodule.restrictScalars B ≤
      (integralClosure B L).toSubmodule := fun y hy => isIntegral_trans (R := B) (A := A) y hy
  have : IsNoetherian B (integralClosure B L).toSubmodule :=
    isNoetherian_of_isNoetherianRing_of_finite B (integralClosure B L)
  have : IsNoetherian B ((integralClosure A L).toSubmodule.restrictScalars B) :=
    isNoetherian_of_le hle
  have : Module.Finite B (integralClosure A L) :=
    Module.IsNoetherian.finite B ((integralClosure A L).toSubmodule.restrictScalars B)
  exact Module.Finite.of_restrictScalars_finite B A (integralClosure A L)
end GroundTheory.Heights₂.Heights.Model
