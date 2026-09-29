-- Prove2me | solution 1 for TwistedUnipotentTerm.isLocallyConstant_integral_setIntegral_integral_semiLocalCharacter_mul_twist_and_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/8370f1b1-8e60-5580-99f6-bc26dfb7e0bb

import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Theorems.Thm_IsLocallyConstant_exists_isOpen_one_mem_forall_mul_eq_of_hasCompactSupport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TwistedUnipotentTerm_isLocallyConstant_integral_setIntegral_integral_semiLocalCharacter_mul_twist_and_hasCompactSupport

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Pointwise

attribute [local instance] AutomorphicForm.glBorelOf

noncomputable section

namespace K6A

open scoped TensorProduct.RightActions

section Generic

variable {B : Type*} [CommRing B]

theorem diagonal_eq (a : B) : Matrix.diagonal ![a, 1] = !![a, 0; 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem scalar_eq (c : B) : Matrix.scalar (Fin 2) c = !![c, 0; 0, c] := by
  ext i j
  · fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, Matrix.diagonal]

theorem upper_mul (x : B) (a c : B) :
    !![(1 : B), x; 0, 1] * Matrix.diagonal ![a, 1] * (Matrix.scalar (Fin 2) c) = !![a * c, x * c; 0, c] := by
  rw [diagonal_eq, scalar_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem lower_mul (x : B) (a c : B) :
    (Matrix.scalar (Fin 2) c) * Matrix.diagonal ![a, 1] * !![(1 : B), x; 0, 1] = !![c * a, c * a * x; 0, c] := by
  rw [diagonal_eq, scalar_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem unipotent_add (x y : B) : !![(1 : B), x + y; 0, 1] = !![(1 : B), x; 0, 1] * !![(1 : B), y; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem unipotent_conj_matrix (a : Bˣ) (y : B) :
    Matrix.diagonal ![((a⁻¹ : Bˣ) : B), 1] * !![1, y; 0, 1] * Matrix.diagonal ![(a : B), 1] =
      !![1, y * ((a⁻¹ : Bˣ) : B); 0, 1] := by
  rw [diagonal_eq, diagonal_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

end Generic

section SemiLocal

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)

abbrev sU : (L ⊗[K] v.adicCompletion K)ˣ ≃* (L ⊗[K] v.adicCompletion K)ˣ :=
  Units.mapEquiv (Algebra.TensorProduct.congr σ
    (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toMulEquiv

abbrev sG : GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (L ⊗[K] v.adicCompletion K) :=
  Matrix.GeneralLinearGroup.map
    ((Algebra.TensorProduct.congr σ (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toRingHom)

def arg (y : L ⊗[K] v.adicCompletion K) (t : (L ⊗[K] v.adicCompletion K)ˣ)
    (κ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (ζ : (L ⊗[K] v.adicCompletion K)ˣ) :
    GL (Fin 2) (L ⊗[K] v.adicCompletion K) :=
  κ⁻¹ * TwistedUnipotentTerm.semiLocalUnipotent K L v (y * ((t⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) :
      L ⊗[K] v.adicCompletion K)) *
    NumberField.AdelicLevel.diagOne (sU K L v σ t * t⁻¹) *
    TwistedUnipotentTerm.semiLocalCentral K L v (sU K L v σ ζ) * sG K L v σ κ

def mid (x : L ⊗[K] v.adicCompletion K) (a c : (L ⊗[K] v.adicCompletion K)ˣ) :
    GL (Fin 2) (L ⊗[K] v.adicCompletion K) :=
  TwistedUnipotentTerm.semiLocalUnipotent K L v x * NumberField.AdelicLevel.diagOne a *
    TwistedUnipotentTerm.semiLocalCentral K L v c

theorem arg_eq_mid (y : L ⊗[K] v.adicCompletion K) (t : (L ⊗[K] v.adicCompletion K)ˣ)
    (κ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (ζ : (L ⊗[K] v.adicCompletion K)ˣ) :
    arg K L v σ y t κ ζ = κ⁻¹ * mid K L v (y * ((t⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K))
      (sU K L v σ t * t⁻¹) (sU K L v σ ζ) * sG K L v σ κ := by
  simp only [arg, mid, mul_assoc]

theorem semiLocalUnipotent_coe (x : L ⊗[K] v.adicCompletion K) :
    (TwistedUnipotentTerm.semiLocalUnipotent K L v x : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
      !![1, x; 0, 1] := rfl

theorem semiLocalUnipotent_inv_coe (x : L ⊗[K] v.adicCompletion K) :
    (((TwistedUnipotentTerm.semiLocalUnipotent K L v x)⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
      Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) = !![1, -x; 0, 1] := rfl

theorem diagOne_coe (a : (L ⊗[K] v.adicCompletion K)ˣ) :
    (NumberField.AdelicLevel.diagOne a : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
      Matrix.diagonal ![(a : L ⊗[K] v.adicCompletion K), 1] := rfl

theorem diagOne_inv_coe (a : (L ⊗[K] v.adicCompletion K)ˣ) :
    (((NumberField.AdelicLevel.diagOne a)⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
      Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
      Matrix.diagonal ![((a⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K), 1] := rfl

theorem semiLocalCentral_coe (c : (L ⊗[K] v.adicCompletion K)ˣ) :
    (TwistedUnipotentTerm.semiLocalCentral K L v c : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
      Matrix.scalar (Fin 2) (c : L ⊗[K] v.adicCompletion K) := rfl

theorem semiLocalCentral_inv_coe (c : (L ⊗[K] v.adicCompletion K)ˣ) :
    (((TwistedUnipotentTerm.semiLocalCentral K L v c)⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
      Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
      Matrix.scalar (Fin 2) (((c⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ)) : L ⊗[K] v.adicCompletion K) := rfl

theorem mid_entries (x : L ⊗[K] v.adicCompletion K) (a c : (L ⊗[K] v.adicCompletion K)ˣ) :
    ((mid K L v x a c : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) _) 0 1 =
        x * (c : L ⊗[K] v.adicCompletion K) ∧
    ((mid K L v x a c : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) _) 1 1 =
        (c : L ⊗[K] v.adicCompletion K) ∧
    (((mid K L v x a c)⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) _) 1 1 =
        ((c⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mid, Units.val_mul, Units.val_mul, semiLocalUnipotent_coe, diagOne_coe, semiLocalCentral_coe, upper_mul]
    rfl
  · rw [mid, Units.val_mul, Units.val_mul, semiLocalUnipotent_coe, diagOne_coe, semiLocalCentral_coe, upper_mul]
    rfl
  · rw [mid, mul_inv_rev, mul_inv_rev, ← mul_assoc, Units.val_mul, Units.val_mul, semiLocalUnipotent_inv_coe,
      diagOne_inv_coe, semiLocalCentral_inv_coe, lower_mul]
    rfl

theorem semiLocalUnipotent_add (x y : L ⊗[K] v.adicCompletion K) :
    TwistedUnipotentTerm.semiLocalUnipotent K L v (x + y) =
      TwistedUnipotentTerm.semiLocalUnipotent K L v x * TwistedUnipotentTerm.semiLocalUnipotent K L v y := by
  apply Units.ext
  rw [Units.val_mul, semiLocalUnipotent_coe, semiLocalUnipotent_coe, semiLocalUnipotent_coe, unipotent_add]

theorem semiLocalUnipotent_mul_diagOne (x : L ⊗[K] v.adicCompletion K) (a : (L ⊗[K] v.adicCompletion K)ˣ) :
    TwistedUnipotentTerm.semiLocalUnipotent K L v x * NumberField.AdelicLevel.diagOne a =
      NumberField.AdelicLevel.diagOne a *
        TwistedUnipotentTerm.semiLocalUnipotent K L v (x * ((a⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) :
          L ⊗[K] v.adicCompletion K)) := by
  have h : TwistedUnipotentTerm.semiLocalUnipotent K L v (x * ((a⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) :
      L ⊗[K] v.adicCompletion K)) =
      (NumberField.AdelicLevel.diagOne a)⁻¹ * TwistedUnipotentTerm.semiLocalUnipotent K L v x *
        NumberField.AdelicLevel.diagOne a := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, semiLocalUnipotent_coe, semiLocalUnipotent_coe, diagOne_inv_coe, diagOne_coe,
      unipotent_conj_matrix]
  rw [h, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]

theorem semiLocalCentral_comm (ζ : (L ⊗[K] v.adicCompletion K)ˣ) (g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    TwistedUnipotentTerm.semiLocalCentral K L v ζ * g = g * TwistedUnipotentTerm.semiLocalCentral K L v ζ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact (Matrix.scalar_commute (ζ : L ⊗[K] v.adicCompletion K) (fun r' => Commute.all _ _) _).eq

theorem arg_add (y u : L ⊗[K] v.adicCompletion K) (t : (L ⊗[K] v.adicCompletion K)ˣ)
    (κ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (ζ : (L ⊗[K] v.adicCompletion K)ˣ) :
    arg K L v σ (y + u) t κ ζ = arg K L v σ y t κ ζ *
      ((sG K L v σ κ)⁻¹ * TwistedUnipotentTerm.semiLocalUnipotent K L v
        (u * (((sU K L v σ t)⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K)) * sG K L v σ κ) := by
  have hu : (y + u) * ((t⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) =
      y * ((t⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) +
      u * ((t⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) := add_mul _ _ _
  have hx : u * ((t⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) *
      (((sU K L v σ t * t⁻¹)⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) =
      u * (((sU K L v σ t)⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) := by
    rw [mul_inv_rev, inv_inv, Units.val_mul, mul_assoc, ← mul_assoc ((t⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) :
      L ⊗[K] v.adicCompletion K), ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  rw [arg, arg, hu, semiLocalUnipotent_add]
  set n₁ := TwistedUnipotentTerm.semiLocalUnipotent K L v (y * ((t⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) :
      L ⊗[K] v.adicCompletion K))
  set D := NumberField.AdelicLevel.diagOne (sU K L v σ t * t⁻¹)
  set c := TwistedUnipotentTerm.semiLocalCentral K L v (sU K L v σ ζ)
  set G := sG K L v σ κ
  have h2 : TwistedUnipotentTerm.semiLocalUnipotent K L v (u * ((t⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) :
      L ⊗[K] v.adicCompletion K)) * D = D * TwistedUnipotentTerm.semiLocalUnipotent K L v
        (u * (((sU K L v σ t)⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K)) := by
    rw [semiLocalUnipotent_mul_diagOne, hx]
  set n₃ := TwistedUnipotentTerm.semiLocalUnipotent K L v
    (u * (((sU K L v σ t)⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K))
  have hc : c * n₃ = n₃ * c := semiLocalCentral_comm K L v _ _
  calc κ⁻¹ * (n₁ * TwistedUnipotentTerm.semiLocalUnipotent K L v (u * ((t⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) :
          L ⊗[K] v.adicCompletion K))) * D * c * G
      = κ⁻¹ * n₁ * (TwistedUnipotentTerm.semiLocalUnipotent K L v (u * ((t⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) :
          L ⊗[K] v.adicCompletion K)) * D) * c * G := by simp only [mul_assoc]
    _ = κ⁻¹ * n₁ * (D * n₃) * c * G := by rw [h2]
    _ = κ⁻¹ * n₁ * D * (n₃ * c) * G := by simp only [mul_assoc]
    _ = κ⁻¹ * n₁ * D * (c * n₃) * G := by rw [hc]
    _ = κ⁻¹ * n₁ * D * c * G * (G⁻¹ * n₃ * G) := by group

end SemiLocal

end K6A

namespace K6A

section Main

open scoped TensorProduct.RightActions
open Topology Filter

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)

theorem semiLocalUnipotent_zero : TwistedUnipotentTerm.semiLocalUnipotent K L v 0 = 1 := by
  apply Units.ext
  rw [semiLocalUnipotent_coe, Units.val_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem congr_algebraMap (a : v.adicCompletion K) :
    (Algebra.TensorProduct.congr σ (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K))
      (algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) a) =
      algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) a := by
  show (Algebra.TensorProduct.congr σ (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K))
      ((1 : L) ⊗ₜ[K] a) = (1 : L) ⊗ₜ[K] a
  rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  simp

noncomputable def congrLinear : (L ⊗[K] v.adicCompletion K) →ₗ[v.adicCompletion K] (L ⊗[K] v.adicCompletion K) where
  toFun := Algebra.TensorProduct.congr σ (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)
  map_add' x y := map_add _ x y
  map_smul' a x :=
    calc (Algebra.TensorProduct.congr σ (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)) (a • x)
        = (Algebra.TensorProduct.congr σ (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K))
            (algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) a * x) :=
          congrArg _ (Algebra.smul_def a x)
      _ = algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) a *
            (Algebra.TensorProduct.congr σ (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)) x := by
          rw [map_mul, congr_algebraMap]
      _ = a • (Algebra.TensorProduct.congr σ (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)) x :=
          (Algebra.smul_def a _).symm

theorem continuous_congr :
    Continuous (Algebra.TensorProduct.congr σ (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)) :=
  IsModuleTopology.continuous_of_linearMap (congrLinear K L v σ)

theorem continuous_sU [IsTopologicalRing (L ⊗[K] v.adicCompletion K)] : Continuous (sU K L v σ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_congr K L v σ).comp Units.continuous_val
  · have : (fun u : (L ⊗[K] v.adicCompletion K)ˣ => ((sU K L v σ u)⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ).val) =
        fun u => (Algebra.TensorProduct.congr σ (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K))
          ((u⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) := by
      funext u; rw [← map_inv]; rfl
    rw [this]
    exact (continuous_congr K L v σ).comp Units.continuous_coe_inv

theorem continuous_sG [IsTopologicalRing (L ⊗[K] v.adicCompletion K)] : Continuous (sG K L v σ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun κ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
      (κ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).map
        (Algebra.TensorProduct.congr σ (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K))
    exact Units.continuous_val.matrix_map (continuous_congr K L v σ)
  · show Continuous fun κ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
      (((sG K L v σ κ)⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))
    have : (fun κ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
        (((sG K L v σ κ)⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
          Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) =
        fun κ => ((κ⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) _).map
          (Algebra.TensorProduct.congr σ (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)) := by
      funext κ; rw [← map_inv]; rfl
    rw [this]
    exact Units.continuous_coe_inv.matrix_map (continuous_congr K L v σ)

theorem continuous_semiLocalUnipotent [IsTopologicalRing (L ⊗[K] v.adicCompletion K)] :
    Continuous (TwistedUnipotentTerm.semiLocalUnipotent K L v) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun x : L ⊗[K] v.adicCompletion K => (!![1, x; 0, 1] : Matrix (Fin 2) (Fin 2) _)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · show Continuous fun x : L ⊗[K] v.adicCompletion K => (!![1, -x; 0, 1] : Matrix (Fin 2) (Fin 2) _)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

set_option maxHeartbeats 3200000 in

theorem main (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)ˣ] [BorelSpace (L ⊗[K] v.adicCompletion K)ˣ]
    (μZ : Measure (L ⊗[K] v.adicCompletion K)ˣ) [μZ.IsHaarMeasure]
    (Φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hΦ : AutomorphicForm.IsSemiLocalTestFn K L v Φ)
    (μT : Measure (L ⊗[K] v.adicCompletion K)ˣ) [IsFiniteMeasure μT]
    (C : Set (L ⊗[K] v.adicCompletion K)ˣ) (hC : IsCompact C) (hμTC : μT Cᶜ = 0) :
    IsLocallyConstant (fun y : L ⊗[K] v.adicCompletion K =>
        ∫ t : (L ⊗[K] v.adicCompletion K)ˣ, ∫ κ in AutomorphicForm.semiLocalIntegralSet K L v,
          ∫ ζ : (L ⊗[K] v.adicCompletion K)ˣ,
            TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ * Φ (arg K L v σ y t κ ζ) ∂μZ
          ∂(AutomorphicForm.semiLocalHaar K L v) ∂μT) ∧
    HasCompactSupport (fun y : L ⊗[K] v.adicCompletion K =>
        ∫ t : (L ⊗[K] v.adicCompletion K)ˣ, ∫ κ in AutomorphicForm.semiLocalIntegralSet K L v,
          ∫ ζ : (L ⊗[K] v.adicCompletion K)ˣ,
            TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ * Φ (arg K L v σ y t κ ζ) ∂μZ
          ∂(AutomorphicForm.semiLocalHaar K L v) ∂μT) := by
  classical
  haveI := AutomorphicForm.borelSpace_glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := AutomorphicForm.t2Space_tensor K L (v.adicCompletion K)
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  have hUc : IsCompact (AutomorphicForm.semiLocalIntegralSet K L v) := AutomorphicForm.isCompact_semiLocalIntegralSet K L v
  have hUm : MeasurableSet (AutomorphicForm.semiLocalIntegralSet K L v) :=
    (AutomorphicForm.isOpen_semiLocalIntegralSet K L v).measurableSet
  have haeC : ∀ᵐ t ∂μT, t ∈ C := mem_ae_iff.mpr hμTC
  set F : L ⊗[K] v.adicCompletion K → ℂ := fun y =>
    ∫ t : (L ⊗[K] v.adicCompletion K)ˣ, ∫ κ in AutomorphicForm.semiLocalIntegralSet K L v,
      ∫ ζ : (L ⊗[K] v.adicCompletion K)ˣ,
        TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ * Φ (arg K L v σ y t κ ζ) ∂μZ
      ∂(AutomorphicForm.semiLocalHaar K L v) ∂μT with hF
  constructor
  ·
    obtain ⟨W, hWo, hW1, hW⟩ :=
      IsLocallyConstant.exists_isOpen_one_mem_forall_mul_eq_of_hasCompactSupport Φ hΦ.1 hΦ.2

    set ρ : (L ⊗[K] v.adicCompletion K) × ((L ⊗[K] v.adicCompletion K)ˣ × GL (Fin 2) (L ⊗[K] v.adicCompletion K)) →
        GL (Fin 2) (L ⊗[K] v.adicCompletion K) := fun p =>
      (sG K L v σ p.2.2)⁻¹ * TwistedUnipotentTerm.semiLocalUnipotent K L v
        (p.1 * (((sU K L v σ p.2.1)⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K)) *
        sG K L v σ p.2.2 with hρ
    have hρc : Continuous ρ := by
      rw [hρ]
      refine ((((continuous_sG K L v σ).comp (continuous_snd.comp continuous_snd)).inv).mul ?_).mul
        ((continuous_sG K L v σ).comp (continuous_snd.comp continuous_snd))
      refine (continuous_semiLocalUnipotent K L v).comp (continuous_fst.mul ?_)
      exact Units.continuous_val.comp (((continuous_sU K L v σ).comp (continuous_fst.comp continuous_snd)).inv)
    have hρ0 : ∀ q : (L ⊗[K] v.adicCompletion K)ˣ × GL (Fin 2) (L ⊗[K] v.adicCompletion K), ρ (0, q) ∈ W := by
      intro q
      rw [hρ]
      dsimp only
      rw [zero_mul, semiLocalUnipotent_zero, mul_one, inv_mul_cancel]
      exact hW1
    obtain ⟨N, V, hNo, -, h0N, hCV, hNV⟩ := generalized_tube_lemma (isCompact_singleton (x := (0 : L ⊗[K] v.adicCompletion K)))
      (hC.prod hUc) (hWo.preimage hρc) (by
        rintro ⟨u, q⟩ ⟨hu, -⟩
        rw [Set.mem_singleton_iff] at hu
        subst hu
        exact hρ0 q)
    have h0 : (0 : L ⊗[K] v.adicCompletion K) ∈ N := h0N (Set.mem_singleton 0)
    have hshift : ∀ y, ∀ u ∈ N, F (y + u) = F y := by
      intro y u hu
      rw [hF]
      refine integral_congr_ae ?_
      filter_upwards [haeC] with t ht
      refine setIntegral_congr_fun hUm fun κ hκ => ?_
      refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
      have hmem : ρ (u, (t, κ)) ∈ W := hNV (Set.mk_mem_prod hu (hCV (Set.mk_mem_prod ht hκ)))
      dsimp only
      rw [arg_add, (hW _ _ hmem).1]
    intro s
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have hNy : (fun u => y + u) '' N ∈ 𝓝 y := by
      refine ((Homeomorph.addLeft y).isOpenMap N hNo).mem_nhds ?_
      exact ⟨0, h0, add_zero y⟩
    refine Filter.mem_of_superset hNy ?_
    rintro z ⟨u, hu, rfl⟩
    show F (y + u) ∈ s
    rw [hshift y u hu]
    exact hy
  ·
    set S := tsupport Φ with hS
    have hSc : IsCompact S := hΦ.2
    set S' : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
      (fun p : GL (Fin 2) (L ⊗[K] v.adicCompletion K) × (GL (Fin 2) (L ⊗[K] v.adicCompletion K) ×
          GL (Fin 2) (L ⊗[K] v.adicCompletion K)) => p.1 * p.2.1 * p.2.2⁻¹) ''
        (AutomorphicForm.semiLocalIntegralSet K L v ×ˢ (S ×ˢ (sG K L v σ '' AutomorphicForm.semiLocalIntegralSet K L v)))
      with hS'
    have hS'c : IsCompact S' :=
      (hUc.prod (hSc.prod (hUc.image (continuous_sG K L v σ)))).image (by fun_prop)
    set E01 : Set (L ⊗[K] v.adicCompletion K) :=
      (fun g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) => (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 1) '' S'
    set E11 : Set (L ⊗[K] v.adicCompletion K) :=
      (fun g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
        ((g⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1) '' S'
    set EC : Set (L ⊗[K] v.adicCompletion K) := (fun t : (L ⊗[K] v.adicCompletion K)ˣ => (t : L ⊗[K] v.adicCompletion K)) '' C
    have hE01 : IsCompact E01 := hS'c.image (Units.continuous_val.matrix_elem 0 1)
    have hE11 : IsCompact E11 := hS'c.image (Units.continuous_coe_inv.matrix_elem 1 1)
    have hEC : IsCompact EC := hC.image Units.continuous_val
    set Y₀ : Set (L ⊗[K] v.adicCompletion K) :=
      (fun p : (L ⊗[K] v.adicCompletion K) × ((L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K)) =>
        p.1 * p.2.1 * p.2.2) '' (E01 ×ˢ (E11 ×ˢ EC)) with hY₀
    have hY₀c : IsCompact Y₀ := (hE01.prod (hE11.prod hEC)).image (by fun_prop)

    have hconf : ∀ (y : L ⊗[K] v.adicCompletion K) (t : (L ⊗[K] v.adicCompletion K)ˣ)
        (κ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (ζ : (L ⊗[K] v.adicCompletion K)ˣ),
        t ∈ C → κ ∈ AutomorphicForm.semiLocalIntegralSet K L v → Φ (arg K L v σ y t κ ζ) ≠ 0 → y ∈ Y₀ := by
      intro y t κ ζ ht hκ hne
      have hargS : arg K L v σ y t κ ζ ∈ S := subset_tsupport _ (Function.mem_support.mpr hne)
      have hmid : mid K L v (y * ((t⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K))
          (sU K L v σ t * t⁻¹) (sU K L v σ ζ) ∈ S' := by
        refine ⟨(κ, (arg K L v σ y t κ ζ, sG K L v σ κ)), ⟨hκ, hargS, ⟨κ, hκ, rfl⟩⟩, ?_⟩
        dsimp only
        rw [arg_eq_mid]
        group
      obtain ⟨e01, e11, e11i⟩ := mid_entries K L v (y * ((t⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) :
        L ⊗[K] v.adicCompletion K)) (sU K L v σ t * t⁻¹) (sU K L v σ ζ)
      refine ⟨(y * ((t⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) *
          ((sU K L v σ ζ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K),
        ((((sU K L v σ ζ)⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K),
          (t : L ⊗[K] v.adicCompletion K))), ⟨⟨_, hmid, e01⟩, ⟨_, hmid, e11i⟩, ⟨t, ht, rfl⟩⟩, ?_⟩
      show y * ((t⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) *
          ((sU K L v σ ζ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) *
          ((((sU K L v σ ζ)⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K)) *
          (t : L ⊗[K] v.adicCompletion K) = y
      rw [mul_assoc (y * _), Units.mul_inv, mul_one, mul_assoc, Units.inv_mul, mul_one]
    refine HasCompactSupport.intro hY₀c fun y hy => ?_
    show F y = 0
    have hzero : ∀ t ∈ C, ∀ κ ∈ AutomorphicForm.semiLocalIntegralSet K L v, ∀ ζ, Φ (arg K L v σ y t κ ζ) = 0 := by
      intro t ht κ hκ ζ
      by_contra hne
      exact hy (hconf y t κ ζ ht hκ hne)
    rw [hF]
    dsimp only
    have h1 : (fun t => ∫ κ in AutomorphicForm.semiLocalIntegralSet K L v, ∫ ζ : (L ⊗[K] v.adicCompletion K)ˣ,
        TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ * Φ (arg K L v σ y t κ ζ) ∂μZ
        ∂(AutomorphicForm.semiLocalHaar K L v)) =ᵐ[μT] fun _ => 0 := by
      filter_upwards [haeC] with t ht
      rw [setIntegral_congr_fun hUm (fun κ hκ => by
        show (∫ ζ : (L ⊗[K] v.adicCompletion K)ˣ,
          TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ * Φ (arg K L v σ y t κ ζ) ∂μZ) = 0
        simp only [hzero t ht κ hκ, mul_zero, integral_zero])]
      simp
    rw [integral_congr_ae h1, integral_zero]

end Main

end K6A

end

open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)ˣ] [BorelSpace (L ⊗[K] v.adicCompletion K)ˣ]
    (μZ : Measure (L ⊗[K] v.adicCompletion K)ˣ) [μZ.IsHaarMeasure]
    (Φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hΦ : AutomorphicForm.IsSemiLocalTestFn K L v Φ)
    (μT : Measure (L ⊗[K] v.adicCompletion K)ˣ) [IsFiniteMeasure μT]
    (C : Set (L ⊗[K] v.adicCompletion K)ˣ) (hC : IsCompact C) (hμTC : μT Cᶜ = 0) :
    IsLocallyConstant (fun y : L ⊗[K] v.adicCompletion K =>
        ∫ t : (L ⊗[K] v.adicCompletion K)ˣ, ∫ κ in AutomorphicForm.semiLocalIntegralSet K L v,
          ∫ ζ : (L ⊗[K] v.adicCompletion K)ˣ,
            TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ *
              Φ (κ⁻¹ * TwistedUnipotentTerm.semiLocalUnipotent K L v (y * ((t⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) :
                    L ⊗[K] v.adicCompletion K)) *
                  NumberField.AdelicLevel.diagOne
                    (Units.mapEquiv (Algebra.TensorProduct.congr σ
                      (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toMulEquiv t * t⁻¹) *
                  TwistedUnipotentTerm.semiLocalCentral K L v
                    (Units.mapEquiv (Algebra.TensorProduct.congr σ
                      (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toMulEquiv ζ) *
                  Matrix.GeneralLinearGroup.map
                    ((Algebra.TensorProduct.congr σ
                      (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toRingHom) κ)
            ∂μZ ∂(AutomorphicForm.semiLocalHaar K L v) ∂μT) ∧
    HasCompactSupport (fun y : L ⊗[K] v.adicCompletion K =>
        ∫ t : (L ⊗[K] v.adicCompletion K)ˣ, ∫ κ in AutomorphicForm.semiLocalIntegralSet K L v,
          ∫ ζ : (L ⊗[K] v.adicCompletion K)ˣ,
            TwistedUnipotentTerm.semiLocalCharacter K L ξL v ζ *
              Φ (κ⁻¹ * TwistedUnipotentTerm.semiLocalUnipotent K L v (y * ((t⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) :
                    L ⊗[K] v.adicCompletion K)) *
                  NumberField.AdelicLevel.diagOne
                    (Units.mapEquiv (Algebra.TensorProduct.congr σ
                      (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toMulEquiv t * t⁻¹) *
                  TwistedUnipotentTerm.semiLocalCentral K L v
                    (Units.mapEquiv (Algebra.TensorProduct.congr σ
                      (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toMulEquiv ζ) *
                  Matrix.GeneralLinearGroup.map
                    ((Algebra.TensorProduct.congr σ
                      (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toRingHom) κ)
            ∂μZ ∂(AutomorphicForm.semiLocalHaar K L v) ∂μT) :=
  K6A.main K L v σ ξL μZ Φ hΦ μT C hC hμTC

end S_TwistedUnipotentTerm_isLocallyConstant_integral_setIntegral_integral_semiLocalCharacter_mul_twist_and_hasCompactSupport
end P2MW
export P2MW.S_TwistedUnipotentTerm_isLocallyConstant_integral_setIntegral_integral_semiLocalCharacter_mul_twist_and_hasCompactSupport (solution)
