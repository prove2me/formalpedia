-- Prove2me | solution 1 for QuadraticForm.forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/f2be4dc6-fe5e-5513-9f5e-265dc077c1ce

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

namespace Classical
p2m_export "Classical" "em by_cases choose not_not"
p2m_open "Classical"
end Classical
namespace ENNReal
p2m_export "ENNReal" "coe_zero isUnit_iff coe_natCast mul_pos coe_add coe_eq_zero coe_injective coe_ne_zero coe_sub coe_mul coe_one"
p2m_open "ENNReal"
end ENNReal
namespace FLT
namespace AdelicIwasawaHeight
end FLT.AdelicIwasawaHeight
namespace FLT
namespace AdelicLsXi
end FLT.AdelicLsXi
namespace FLT
namespace AdelicTruncation
end FLT.AdelicTruncation
namespace FLT
namespace ArchimedeanSiegel
end FLT.ArchimedeanSiegel
namespace FLT
namespace CampGenuineMk
end FLT.CampGenuineMk
namespace FLT
namespace GL1FujisakiFiniteShadow
end FLT.GL1FujisakiFiniteShadow
namespace FLT
namespace GL2FiniteAdelicMatrixIdentification
end FLT.GL2FiniteAdelicMatrixIdentification
namespace FLT
namespace JpssD4GJProp83EisensteinAdelicQuadrupleInhabit
end FLT.JpssD4GJProp83EisensteinAdelicQuadrupleInhabit
namespace FLT
namespace JpssD4GJProp83EisensteinAdelicQuadrupleLayer
end FLT.JpssD4GJProp83EisensteinAdelicQuadrupleLayer
namespace FLT
namespace JpssD4GJProp83EisensteinInputSlice
end FLT.JpssD4GJProp83EisensteinInputSlice
namespace FLT
namespace JpssD4GJProp83GenuineCarrierSkeleton
end FLT.JpssD4GJProp83GenuineCarrierSkeleton
namespace FLT
namespace JpssD4GJProp83L2EngineProofSkeleton
end FLT.JpssD4GJProp83L2EngineProofSkeleton
namespace FLT
namespace JpssD4GJProp83MetaplecticKubotaCoverCarrier
end FLT.JpssD4GJProp83MetaplecticKubotaCoverCarrier
namespace FLT
namespace JpssD4KubotaArchimedeanCocycleSlice
end FLT.JpssD4KubotaArchimedeanCocycleSlice
namespace FLT
namespace JpssD4KubotaFiniteAdelicProductObjectSlice
end FLT.JpssD4KubotaFiniteAdelicProductObjectSlice
namespace FLT
namespace JpssD4KubotaGlobalProductFormulaSlice
end FLT.JpssD4KubotaGlobalProductFormulaSlice
namespace FLT
namespace JpssD4KubotaPTwoHilbertSolvabilityIdentification
end FLT.JpssD4KubotaPTwoHilbertSolvabilityIdentification
namespace FLT
namespace JpssD4KubotaPTwoHilbertSolvabilityIdentificationGrid
end FLT.JpssD4KubotaPTwoHilbertSolvabilityIdentificationGrid
namespace FLT
namespace JpssD4KubotaPTwoHilbertTable
end FLT.JpssD4KubotaPTwoHilbertTable
namespace FLT
namespace JpssD4KubotaTameSymbolUniformWindowSlice
end FLT.JpssD4KubotaTameSymbolUniformWindowSlice
namespace FreyPackage
end FreyPackage
namespace Function
p2m_export "Function" "Injective comp support eval"
p2m_open "Function"
end Function
namespace IsDedekindDomain
p2m_export "IsDedekindDomain" "HeightOneSpectrum.instAlgebraAdicCompletion HeightOneSpectrum.adicCompletion FiniteAdeleRing HeightOneSpectrum"
p2m_open "IsDedekindDomain"
end IsDedekindDomain
namespace IsDedekindDomain
p2m_export "IsDedekindDomain" "HeightOneSpectrum.instAlgebraAdicCompletion HeightOneSpectrum.adicCompletion FiniteAdeleRing HeightOneSpectrum"
namespace HeightOneSpectrum
p2m_export "IsDedekindDomain.HeightOneSpectrum" "instAlgebraAdicCompletion adicCompletion valuation prime"
p2m_open "IsDedekindDomain.HeightOneSpectrum IsDedekindDomain"
end IsDedekindDomain.HeightOneSpectrum
namespace Matrix
p2m_export "Matrix" "J ext den_intCast algebraMap_matrix_apply norm_def num_intCast zero comp zero_apply one_apply zpow_neg num_div_den add_apply of map mul_apply"
p2m_open "Matrix"
end Matrix
namespace MeasureTheory
p2m_open "MeasureTheory"
end MeasureTheory
namespace ModularCurve
end ModularCurve
namespace NNReal
p2m_export "NNReal" "sub_div sqrt coe_one natCast_natAbs sq_sqrt coe_eq_zero coe_zero coe_ne_zero"
p2m_open "NNReal"
end NNReal
namespace NumberField
p2m_export "NumberField" "place RingOfIntegers"
p2m_open "NumberField"
end NumberField
namespace Pointwise
p2m_open "Pointwise"
end Pointwise
namespace Polynomial
p2m_export "Polynomial" "C mul_mod X support coe_one derivative_C coe_neg aeval aeval_C derivative_X_pow map derivative_X comp coe_mul coe_sub eval_X coe_injective eval_C flt coe_zero derivative_sq derivative_sub pow coe_add derivative aeval_X erase ext funext isUnit_iff ring eval"
p2m_open "Polynomial"
end Polynomial
namespace Quaternion
p2m_export "Quaternion" "coe_injective coe_zero coe_sub coe_mul finrank_eq_four coe_one coe_natCast coe_add ext coe_intCast coe_neg"
p2m_open "Quaternion"
end Quaternion
namespace QuaternionAlgebra
p2m_export "QuaternionAlgebra" "re coe_mul finrank_eq_four coe_neg coe_injective coe_one coe_algebraMap mk_mul_mk coe_sub coe_add imK coe_zero coe_intCast imJ imI Basis neg_mk coe_natCast"
p2m_open "QuaternionAlgebra"
end QuaternionAlgebra
namespace Rat
p2m_export "Rat" "num_intCast cast_natCast cast_neg cast_mul cast_nonneg pos den neg_num num cast_ofNat num_mul_num_eq_num_mul_gcd cast_intCast HeightOneSpectrum.primesEquiv neg_den neg_zero cast_id sqrt num_div_den cast_add cast_sub castHom den_intCast cast_zero mul_den_dvd cast_ne_zero cast_pow cast_one HeightOneSpectrum.adicCompletion.padicEquiv num_ne_zero ext den_nz"
namespace FiniteAdeleRing
p2m_open "Rat"
end Rat.FiniteAdeleRing
namespace Rat
p2m_export "Rat" "num_intCast cast_natCast cast_neg cast_mul cast_nonneg pos den neg_num num cast_ofNat num_mul_num_eq_num_mul_gcd cast_intCast HeightOneSpectrum.primesEquiv neg_den neg_zero cast_id sqrt num_div_den cast_add cast_sub castHom den_intCast cast_zero mul_den_dvd cast_ne_zero cast_pow cast_one HeightOneSpectrum.adicCompletion.padicEquiv num_ne_zero ext den_nz"
namespace HeightOneSpectrum
p2m_export "Rat.HeightOneSpectrum" "primesEquiv adicCompletion.padicEquiv"
p2m_open "Rat.HeightOneSpectrum Rat"
end Rat.HeightOneSpectrum
namespace TensorProduct
p2m_export "TensorProduct" "congr ext map"
p2m_open "TensorProduct"
end TensorProduct
namespace TopologicalSpace
p2m_open "TopologicalSpace"
end TopologicalSpace
namespace TotallyDefiniteQuaternionAlgebra
end TotallyDefiniteQuaternionAlgebra
namespace WithZero
p2m_export "WithZero" "coe_one coe_add map coe_mul coe_injective exists pow le coe_neg coe_ne_zero"
p2m_open "WithZero"
end WithZero

namespace PadicInt
p2m_export "PadicInt" "ker_toZMod norm_p mem_subring_iff norm_int_lt_one_iff_dvd toZMod coe_eq_zero norm_units valuation_mul coe_intCast coe_neg coe_add isUnit_iff norm_int_le_pow_iff_dvd coe_natCast maximalIdeal_eq_span_p coe_mul toZModPow padic_norm_e_of_padicInt norm_le_one valuation valuation_p le_valuation_add coe_sub ext norm_lt_one_iff_dvd mul_inv norm_le_pow_iff_mem_span_pow ker_toZModPow valuation_pow coe_one norm_def coe_zero coe_ne_zero mkUnits mkUnits_eq subring norm_eq_zpow_neg_valuation"
p2m_open "PadicInt"
theorem coe_injective_s18 {p : ℕ} [Fact p.Prime] : Function.Injective ((↑) : ℤ_[p] → ℚ_[p]) :=
  Subtype.val_injective
end PadicInt

scoped instance instCharZeroAdicCompletionRingOfIntegers_s18 {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    CharZero (v.adicCompletion K) :=
  ((algebraMap K (v.adicCompletion K)).charZero_iff (algebraMap K (v.adicCompletion K)).injective).mp inferInstance

scoped instance fact_prime_two_s18 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
scoped instance fact_prime_three_s18 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
scoped instance fact_prime_seven_s18 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

section
section

suppress_compilation

p2m_open "IsDedekindDomain P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.IsDedekindDomain NumberField P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.NumberField QuaternionAlgebra P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.QuaternionAlgebra"
p2m_open_scoped "Quaternion P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.Quaternion"

namespace FLT
namespace NumberTheory

p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.IsDedekindDomain.HeightOneSpectrum"

def kw_pureNrdRep (F : Type*) [CommRing F] (a b c : F) : Prop :=
  ∃ x y z : F, -a * x ^ 2 - b * y ^ 2 + a * b * z ^ 2 = c

def kw_HSCluster_pureNrdLocalGlobal (a b : ℚ) : Prop :=
  ∀ c : ℚ, c ≠ 0 →
    (∀ v : HeightOneSpectrum (𝓞 ℚ),
      kw_pureNrdRep (v.adicCompletion ℚ)
        (algebraMap ℚ _ a) (algebraMap ℚ _ b) (algebraMap ℚ _ c)) →
    kw_pureNrdRep ℝ (algebraMap ℚ ℝ a) (algebraMap ℚ ℝ b) (algebraMap ℚ ℝ c) →
    kw_pureNrdRep ℚ a b c

end FLT.NumberTheory

end

end

section
section

suppress_compilation

p2m_open "IsDedekindDomain P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.IsDedekindDomain NumberField P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.NumberField QuaternionAlgebra P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.QuaternionAlgebra"
p2m_open_scoped "TensorProduct P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.TensorProduct Quaternion P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.Quaternion Polynomial P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.Polynomial"
open ModularCurve

namespace FLT
namespace NumberTheory

open TotallyDefiniteQuaternionAlgebra FreyPackage
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.IsDedekindDomain.HeightOneSpectrum"

local notation "𝔸" => FiniteAdeleRing (𝓞 ℚ) ℚ

section StrengthenedCarrier

variable (a b : ℚ)

abbrev kw_isSplitAtPlace (v : HeightOneSpectrum (𝓞 ℚ)) : Prop :=
  Nonempty (QuaternionAlgebra (v.adicCompletion ℚ)
    (algebraMap ℚ _ a) 0 (algebraMap ℚ _ b)
      ≃ₐ[v.adicCompletion ℚ] Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))

variable (p : ℕ) [Fact p.Prime]

end StrengthenedCarrier

section RatStrongApprox

p2m_open "Polynomial P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.Polynomial"

variable (p : ℕ) [Fact p.Prime]

end RatStrongApprox

section LocalIrredAtoms

p2m_open "Polynomial P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.Polynomial"

variable (a b : ℚ) (p : ℕ) [Fact p.Prime]

end LocalIrredAtoms

section LocalGlobalEmbed

p2m_open "Polynomial P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.Polynomial"

variable (a b : ℚ)

end LocalGlobalEmbed

section MainWire

p2m_open "Polynomial P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.Polynomial"

variable (a b : ℚ) (p : ℕ) [Fact p.Prime]

end MainWire

end FLT.NumberTheory

end

end

section
section

suppress_compilation

p2m_open "IsDedekindDomain P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.IsDedekindDomain NumberField P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.NumberField QuaternionAlgebra P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.QuaternionAlgebra"
p2m_open_scoped "Quaternion P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.Quaternion Polynomial P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.Polynomial"

namespace FLT
namespace NumberTheory

p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.IsDedekindDomain.HeightOneSpectrum"

section RationalBridge

variable {a b : ℚ}

end RationalBridge

section QuadraticIrred

p2m_open "Polynomial P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.Polynomial"

variable {F : Type*} [Field F]

end QuadraticIrred

section SplitPlace

variable {F : Type*} [Field F] {a b : F}

def kw_isotropicPureNrdUniversal : Prop :=
  ∀ (F : Type) [Field F] [CharZero F], ∀ (a b : F), a ≠ 0 → b ≠ 0 →
    (∃ x y z : F, ¬ (x = 0 ∧ y = 0 ∧ z = 0) ∧ -a * x ^ 2 - b * y ^ 2 + a * b * z ^ 2 = 0) →
    ∀ c : F, kw_pureNrdRep F a b c

end SplitPlace

section ArchimedeanPlace

end ArchimedeanPlace

section MainWire

p2m_open "Polynomial P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.Polynomial"

variable (a b : ℚ)

end MainWire

end FLT.NumberTheory

end

end

section
section

p2m_open "IsDedekindDomain P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.IsDedekindDomain.HeightOneSpectrum NumberField P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.NumberField"
p2m_open "Rat.HeightOneSpectrum P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.Rat.HeightOneSpectrum"

p2m_open_scoped "Polynomial P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.Polynomial WithZero P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.WithZero"

namespace FLT
namespace NumberTheory

section PadicSqrt

variable {p : ℕ} [Fact p.Prime]

theorem kw_hjoint_padic_isSquare_of_close_one {u : ℚ_[p]}
    (hu : ‖u - 1‖ < ‖(2 : ℚ_[p])‖ ^ 2) :
    IsSquare u := by

  have h2le1 : ‖(2 : ℚ_[p])‖ ^ 2 ≤ 1 := by
    have : ‖(2 : ℤ_[p])‖ ≤ 1 := PadicInt.norm_le_one _
    rw [show ‖(2 : ℚ_[p])‖ = ‖(2 : ℤ_[p])‖ from rfl]
    exact pow_le_one₀ (norm_nonneg _) this
  have humem : u - 1 ∈ PadicInt.subring p :=
    (PadicInt.mem_subring_iff p).mpr (hu.le.trans h2le1)
  set u₀ : ℤ_[p] := (1 : ℤ_[p]) + ⟨u - 1, humem⟩ with hu₀
  have hu₀coe : (u₀ : ℚ_[p]) = u := by simp [hu₀]

  let f : Polynomial ℤ_[p] := Polynomial.X ^ 2 - Polynomial.C u₀
  have heval : f.aeval (1 : ℤ_[p]) = 1 - u₀ := by simp [f]
  have hderiv : f.derivative.aeval (1 : ℤ_[p]) = 2 := by
    simp only [f, map_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C, sub_zero,
      Nat.cast_ofNat, map_mul, map_ofNat, Polynomial.aeval_X, mul_one, Nat.add_one_sub_one,
      pow_one]
  have hnorm1u₀ : ‖(1 : ℤ_[p]) - u₀‖ = ‖u - 1‖ := by
    rw [show (1 : ℤ_[p]) - u₀ = -⟨u - 1, humem⟩ from by simp [hu₀], norm_neg]
    rfl
  have hlt : ‖f.aeval (1 : ℤ_[p])‖ < ‖f.derivative.aeval (1 : ℤ_[p])‖ ^ 2 := by
    rw [heval, hderiv, hnorm1u₀,
      show ‖(2 : ℤ_[p])‖ = ‖(2 : ℚ_[p])‖ from rfl]
    exact hu
  obtain ⟨s, hs, -, -, -⟩ := hensels_lemma hlt
  refine ⟨(s : ℚ_[p]), ?_⟩
  have hs2 : s ^ 2 = u₀ := by
    have : f.aeval s = 0 := hs
    simpa [f, sub_eq_zero] using this
  rw [← hu₀coe, ← hs2]
  push_cast
  ring

end PadicSqrt

section PadicOpen

variable {p : ℕ} [Fact p.Prime]

end PadicOpen

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

end FLT.NumberTheory

end

end

section
section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

namespace FLT
namespace CampGenuineMk

variable {p : ℕ} [Fact p.Prime]

noncomputable def gmk9_ser_diagForm (a b : ZMod p) : MvPolynomial (Fin 3) (ZMod p) :=
  MvPolynomial.C a * MvPolynomial.X 0 ^ 2 + MvPolynomial.C b * MvPolynomial.X 1 ^ 2
    - MvPolynomial.X 2 ^ 2

theorem gmk9_ser_diagForm_totalDegree_lt (a b : ZMod p) :
    (gmk9_ser_diagForm a b).totalDegree < Fintype.card (Fin 3) := by
  have _pin := Classical.em True
  have hsq : ∀ i : Fin 3,
      ((MvPolynomial.X i : MvPolynomial (Fin 3) (ZMod p)) ^ 2).totalDegree ≤ 2 := by
    intro i
    refine le_trans (MvPolynomial.totalDegree_pow _ 2) ?_
    rw [MvPolynomial.totalDegree_X]
  have hmul : ∀ (c : ZMod p) (i : Fin 3),
      (MvPolynomial.C c * MvPolynomial.X i ^ 2
        : MvPolynomial (Fin 3) (ZMod p)).totalDegree ≤ 2 := by
    intro c i
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    exact hsq i
  have hadd : ((MvPolynomial.C a * MvPolynomial.X 0 ^ 2 +
      MvPolynomial.C b * MvPolynomial.X 1 ^ 2
        : MvPolynomial (Fin 3) (ZMod p))).totalDegree ≤ 2 :=
    le_trans (MvPolynomial.totalDegree_add _ _) (max_le (hmul a 0) (hmul b 1))
  have hfull : (gmk9_ser_diagForm a b).totalDegree ≤ 2 := by
    unfold gmk9_ser_diagForm
    exact le_trans (MvPolynomial.totalDegree_sub _ _) (max_le hadd (hsq 2))
  rw [Fintype.card_fin]
  omega

theorem gmk9_ser_diagForm_eval (a b : ZMod p) (v : Fin 3 → ZMod p) :
    MvPolynomial.eval v (gmk9_ser_diagForm a b)
      = a * (v 0 * v 0) + b * (v 1 * v 1) - v 2 * v 2 := by
  have _pin := Classical.em True
  unfold gmk9_ser_diagForm
  simp only [map_sub, map_add, map_mul, map_pow, MvPolynomial.eval_C,
    MvPolynomial.eval_X]
  ring

theorem gmk9_ser_diagForm_eval_zero (a b : ZMod p) :
    MvPolynomial.eval (fun _ => (0 : ZMod p)) (gmk9_ser_diagForm a b) = 0 := by
  have _pin := Classical.em True
  rw [gmk9_ser_diagForm_eval]
  ring

theorem gmk9_ser_char_dvd_card_diagForm_solutions (a b : ZMod p) :
    p ∣ Fintype.card
      { v : Fin 3 → ZMod p // MvPolynomial.eval v (gmk9_ser_diagForm a b) = 0 } := by
  have _pin := Classical.em True
  exact char_dvd_card_solutions p (gmk9_ser_diagForm_totalDegree_lt a b)

theorem gmk9_ser_diagForm_nontrivial_zero (a b : ZMod p) :
    ∃ x y z : ZMod p, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
      z * z = a * (x * x) + b * (y * y) := by
  have _pin := Classical.em True
  have hzero : MvPolynomial.eval (fun _ => (0 : ZMod p)) (gmk9_ser_diagForm a b) = 0 :=
    gmk9_ser_diagForm_eval_zero a b
  have hpos : 0 < Fintype.card
      { v : Fin 3 → ZMod p // MvPolynomial.eval v (gmk9_ser_diagForm a b) = 0 } :=
    Fintype.card_pos_iff.mpr ⟨⟨fun _ => 0, hzero⟩⟩
  have hdvd := gmk9_ser_char_dvd_card_diagForm_solutions a b
  have hple := Nat.le_of_dvd hpos hdvd
  have hp2 := (Fact.out : p.Prime).two_le
  have hlt : 1 < Fintype.card
      { v : Fin 3 → ZMod p // MvPolynomial.eval v (gmk9_ser_diagForm a b) = 0 } := by
    omega
  obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card hlt ⟨fun _ => 0, hzero⟩
  refine ⟨w.1 0, w.1 1, w.1 2, ?_, ?_⟩
  · by_contra hall
    push Not at hall
    apply hw
    apply Subtype.ext
    funext i
    fin_cases i
    · exact hall.1
    · exact hall.2.1
    · exact hall.2.2
  · have hv := w.2
    rw [gmk9_ser_diagForm_eval] at hv
    exact (sub_eq_zero.mp hv).symm

theorem gmk9_ser_diagForm_zcase_nonzero {a b x y z : ZMod p} (ha : a ≠ 0) (hb : b ≠ 0)
    (hnt : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) (heq : z * z = a * (x * x) + b * (y * y))
    (hz : z = 0) : x ≠ 0 ∧ y ≠ 0 := by
  have _pin := Classical.em True
  subst hz
  have hsum : a * (x * x) + b * (y * y) = 0 := by
    rw [← heq]
    ring
  constructor
  · intro hx
    subst hx
    have hyy : b * (y * y) = 0 := by
      calc b * (y * y) = a * (0 * 0) + b * (y * y) := by ring
        _ = 0 := hsum
    have hy : y = 0 := by
      rcases mul_eq_zero.mp hyy with hc | hc
      · exact absurd hc hb
      · exact mul_self_eq_zero.mp hc
    subst hy
    rcases hnt with hc | hc | hc <;> exact hc rfl
  · intro hy
    subst hy
    have hxx : a * (x * x) = 0 := by
      calc a * (x * x) = a * (x * x) + b * (0 * 0) := by ring
        _ = 0 := hsum
    have hx : x = 0 := by
      rcases mul_eq_zero.mp hxx with hc | hc
      · exact absurd hc ha
      · exact mul_self_eq_zero.mp hc
    subst hx
    rcases hnt with hc | hc | hc <;> exact hc rfl

theorem gmk9_ser_diagForm_solution_dichotomy (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) :
    (∃ x y z : ZMod p, z ≠ 0 ∧ z * z = a * (x * x) + b * (y * y)) ∨
      (∃ x y : ZMod p, x ≠ 0 ∧ y ≠ 0 ∧ a * (x * x) + b * (y * y) = 0) := by
  have _pin := Classical.em True
  obtain ⟨x, y, z, hnt, heq⟩ := gmk9_ser_diagForm_nontrivial_zero a b
  by_cases hz : z = 0
  · obtain ⟨hx, hy⟩ := gmk9_ser_diagForm_zcase_nonzero ha hb hnt heq hz
    right
    refine ⟨x, y, hx, hy, ?_⟩
    rw [← heq, hz]
    ring
  · left
    exact ⟨x, y, z, hz, heq⟩

theorem gmk9_ser_neg_mul_isSquare_of_isotropic {a b x y : ZMod p} (hy : y ≠ 0)
    (h : a * (x * x) + b * (y * y) = 0) : IsSquare (-(a * b)) := by
  have _pin := Classical.em True
  have h1 : a * (x * x) = -(b * (y * y)) := eq_neg_of_add_eq_zero_left h
  have hyinv : y * y⁻¹ = 1 := mul_inv_cancel₀ hy
  refine ⟨a * x * y⁻¹, ?_⟩
  calc -(a * b)
      = -(a * b) * ((y * y⁻¹) * (y * y⁻¹)) := by rw [hyinv]; ring
    _ = a * (-(b * (y * y))) * (y⁻¹ * y⁻¹) := by ring
    _ = a * (a * (x * x)) * (y⁻¹ * y⁻¹) := by rw [← h1]
    _ = (a * x * y⁻¹) * (a * x * y⁻¹) := by ring

theorem gmk9_ser_isSquare_neg_of_two_nonsquares {u : ZMod p}
    (h1 : ¬IsSquare (-1 : ZMod p)) (hu : ¬IsSquare u) (hu0 : u ≠ 0) :
    IsSquare (-u) := by
  have _pin := Classical.em True
  have hχ1 : quadraticChar (ZMod p) (-1) = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr h1
  have hχu : quadraticChar (ZMod p) u = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr hu
  have hχ : quadraticChar (ZMod p) (-u) = 1 := by
    rw [← neg_one_mul u, map_mul, hχ1, hχu]
    ring
  exact (quadraticChar_one_iff_isSquare (neg_ne_zero.mpr hu0)).mp hχ

theorem gmk9_ser_not_isSquare_neg_of_square_nonsquare {u : ZMod p}
    (h1 : IsSquare (-1 : ZMod p)) (hu : ¬IsSquare u) : ¬IsSquare (-u) := by
  have _pin := Classical.em True
  intro hnu
  apply hu
  have hrw : u = (-1 : ZMod p) * (-u) := by ring
  rw [hrw]
  exact h1.mul hnu

theorem gmk9_ser_isSquare_neg_mul_self_iff {u : ZMod p} (hu : u ≠ 0) :
    IsSquare (-(u * u)) ↔ IsSquare (-1 : ZMod p) := by
  have _pin := Classical.em True
  have huinv : u * u⁻¹ = 1 := mul_inv_cancel₀ hu
  constructor
  · intro h
    have hkey : (-1 : ZMod p) = (-(u * u)) * (u⁻¹ * u⁻¹) := by
      calc (-1 : ZMod p) = -((u * u⁻¹) * (u * u⁻¹)) := by rw [huinv]; ring
        _ = (-(u * u)) * (u⁻¹ * u⁻¹) := by ring
    rw [hkey]
    exact h.mul ⟨u⁻¹, rfl⟩
  · intro h
    have hkey : -(u * u) = (-1 : ZMod p) * (u * u) := by ring
    rw [hkey]
    exact h.mul ⟨u, rfl⟩

end FLT.CampGenuineMk

end

end

section
section

p2m_open "IsDedekindDomain P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.IsDedekindDomain.HeightOneSpectrum NumberField P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.NumberField QuaternionAlgebra P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.QuaternionAlgebra"
open ModularCurve

namespace FLT
namespace NumberTheory

open TotallyDefiniteQuaternionAlgebra FreyPackage
p2m_open_scoped "Classical P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.Classical"

section WireRamFinset

variable (a b : ℚ) (p : ℕ) [Fact p.Prime]

end WireRamFinset

section SubAtoms

abbrev kw_HSCluster_A_fin (a b : ℚ) : Prop :=
  a ≠ 0 → b ≠ 0 →
  ∀ v : HeightOneSpectrum (𝓞 ℚ),
    ¬ kw_isSplitAtPlace a b v ↔
      ¬ ∃ z x y : v.adicCompletion ℚ, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
        z ^ 2 - algebraMap ℚ _ a * x ^ 2 - algebraMap ℚ _ b * y ^ 2 = 0

abbrev kw_HSCluster_C_hilbertProduct (a b : ℚ) : Prop :=
  a ≠ 0 → b ≠ 0 →
  ∃ Rf : Finset (HeightOneSpectrum (𝓞 ℚ)),
    (∀ v, v ∈ Rf ↔
      ¬ ∃ z x y : v.adicCompletion ℚ, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
        z ^ 2 - algebraMap ℚ _ a * x ^ 2 - algebraMap ℚ _ b * y ^ 2 = 0) ∧
    Even (Rf.card + (if (a : ℝ) < 0 ∧ (b : ℝ) < 0 then 1 else 0))

end SubAtoms

section SplitEngine

p2m_open "Matrix P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.Matrix"

variable {F : Type*} [Field F] [CharZero F]

noncomputable def kw_hjoint_sqBasis {a b : F} {c : F} (hac : a = c * c) :
    QuaternionAlgebra.Basis (R := F) (Matrix (Fin 2) (Fin 2) F) a 0 b where
  i := !![c, 0; 0, -c]
  j := !![0, 1; b, 0]
  k := !![0, c; -(b*c), 0]
  i_mul_i := by
    ext r s; fin_cases r <;> fin_cases s <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hac] <;> ring
  j_mul_j := by
    ext r s; fin_cases r <;> fin_cases s <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  i_mul_j := by
    ext r s; fin_cases r <;> fin_cases s <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  j_mul_i := by

    ext r s; fin_cases r <;> fin_cases s <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

noncomputable def kw_hjoint_normBasis {a b : F} {u v : F}
    (huv : b = u * u - a * (v * v)) :
    QuaternionAlgebra.Basis (R := F) (Matrix (Fin 2) (Fin 2) F) a 0 b where
  i := !![0, a; 1, 0]
  j := !![u, -(a*v); v, -u]
  k := !![a*v, -(a*u); u, -(a*v)]
  i_mul_i := by
    ext r s; fin_cases r <;> fin_cases s <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  j_mul_j := by
    ext r s; fin_cases r <;> fin_cases s <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, huv] <;> ring
  i_mul_j := by
    ext r s; fin_cases r <;> fin_cases s <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  j_mul_i := by
    ext r s; fin_cases r <;> fin_cases s <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem kw_hjoint_sqBasis_liftHom_apply {a b : F} {c : F} (hac : a = c * c)
    (z : QuaternionAlgebra F a 0 b) :
    (kw_hjoint_sqBasis (b := b) hac).liftHom z =
      !![z.re + c * z.imI, z.imJ + c * z.imK;
         b * z.imJ - b * c * z.imK, z.re - c * z.imI] := by
  have h : (kw_hjoint_sqBasis (b := b) hac).liftHom z
      = algebraMap F (Matrix (Fin 2) (Fin 2) F) z.re
        + z.imI • !![c, 0; 0, -c] + z.imJ • !![(0:F), 1; b, 0]
        + z.imK • !![(0:F), c; -(b*c), 0] := rfl
  rw [h]
  ext r s; fin_cases r <;> fin_cases s <;>
    simp [Matrix.algebraMap_matrix_apply] <;> ring

theorem kw_hjoint_normBasis_liftHom_apply {a b : F} {u v : F}
    (huv : b = u * u - a * (v * v)) (z : QuaternionAlgebra F a 0 b) :
    (kw_hjoint_normBasis huv).liftHom z =
      !![z.re + u * z.imJ + a * v * z.imK, a * z.imI - a * v * z.imJ - a * u * z.imK;
         z.imI + v * z.imJ + u * z.imK, z.re - u * z.imJ - a * v * z.imK] := by
  have h : (kw_hjoint_normBasis huv).liftHom z
      = algebraMap F (Matrix (Fin 2) (Fin 2) F) z.re
        + z.imI • !![(0:F), a; 1, 0] + z.imJ • !![u, -(a*v); v, -u]
        + z.imK • !![a*v, -(a*u); u, -(a*v)] := rfl
  rw [h]
  ext r s; fin_cases r <;> fin_cases s <;>
    simp [Matrix.algebraMap_matrix_apply] <;> ring

theorem kw_hjoint_quatSplit_of_sq {a b : F} (hb : b ≠ 0) {c : F} (hc : c ≠ 0)
    (hac : a = c * c) :
    Nonempty (QuaternionAlgebra F a 0 b ≃ₐ[F] Matrix (Fin 2) (Fin 2) F) := by
  let φ := (kw_hjoint_sqBasis (b := b) hac).liftHom
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨z0, z1, z2, z3⟩ := z
    rw [kw_hjoint_sqBasis_liftHom_apply] at hz
    have h00 : z0 + c * z1 = 0 := by simpa using congrFun (congrFun hz 0) 0
    have h01 : z2 + c * z3 = 0 := by simpa using congrFun (congrFun hz 0) 1
    have h10 : b * z2 - b * c * z3 = 0 := by simpa using congrFun (congrFun hz 1) 0
    have h11 : z0 - c * z1 = 0 := by simpa using congrFun (congrFun hz 1) 1
    have h2 : (2 : F) ≠ 0 := two_ne_zero
    have e0 : z0 = 0 := by
      have : (2 : F) * z0 = 0 := by linear_combination h00 + h11
      exact (mul_eq_zero.mp this).resolve_left h2
    have e1 : z1 = 0 := by
      have : (2 : F) * c * z1 = 0 := by linear_combination h00 - h11
      exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h2 hc)
    have e2 : z2 = 0 := by
      have : (2 : F) * b * z2 = 0 := by linear_combination b * h01 + h10
      exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h2 hb)
    have e3 : z3 = 0 := by
      have : (2 : F) * b * c * z3 = 0 := by linear_combination b * h01 - h10
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (mul_ne_zero (mul_ne_zero h2 hb) hc)
      · exact h
    exact QuaternionAlgebra.ext e0 e1 e2 e3
  have hdim : Module.finrank F (QuaternionAlgebra F a 0 b)
      = Module.finrank F (Matrix (Fin 2) (Fin 2) F) := by
    simp [QuaternionAlgebra.finrank_eq_four, Module.finrank_matrix]
  exact ⟨AlgEquiv.ofBijective φ
    (LinearMap.linearEquivOfInjective φ.toLinearMap hinj hdim).bijective⟩

theorem kw_hjoint_quatSplit_of_norm {a b : F} (ha : a ≠ 0) (hb : b ≠ 0)
    {u v : F} (huv : b = u * u - a * (v * v)) :
    Nonempty (QuaternionAlgebra F a 0 b ≃ₐ[F] Matrix (Fin 2) (Fin 2) F) := by
  let φ := (kw_hjoint_normBasis huv).liftHom
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨z0, z1, z2, z3⟩ := z
    rw [kw_hjoint_normBasis_liftHom_apply] at hz
    have h00 : z0 + u * z2 + a * v * z3 = 0 := by simpa using congrFun (congrFun hz 0) 0
    have h01 : a * z1 - a * v * z2 - a * u * z3 = 0 := by
      simpa using congrFun (congrFun hz 0) 1
    have h10 : z1 + v * z2 + u * z3 = 0 := by simpa using congrFun (congrFun hz 1) 0
    have h11 : z0 - u * z2 - a * v * z3 = 0 := by simpa using congrFun (congrFun hz 1) 1
    have h2 : (2 : F) ≠ 0 := two_ne_zero
    have e0 : z0 = 0 := by
      have : (2 : F) * z0 = 0 := by linear_combination h00 + h11
      exact (mul_eq_zero.mp this).resolve_left h2
    have e1 : z1 = 0 := by
      have : (2 : F) * a * z1 = 0 := by linear_combination h01 + a * h10
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (mul_ne_zero h2 ha)
      · exact h

    have hA : u * z2 + a * v * z3 = 0 := by linear_combination h00 - e0
    have hB : v * z2 + u * z3 = 0 := by linear_combination h10 - e1
    have e2 : z2 = 0 := by
      have : b * z2 = 0 := by linear_combination u * hA - a * v * hB + z2 * huv
      exact (mul_eq_zero.mp this).resolve_left hb
    have e3 : z3 = 0 := by
      have : b * z3 = 0 := by linear_combination (-v) * hA + u * hB + z3 * huv
      exact (mul_eq_zero.mp this).resolve_left hb
    exact QuaternionAlgebra.ext e0 e1 e2 e3
  have hdim : Module.finrank F (QuaternionAlgebra F a 0 b)
      = Module.finrank F (Matrix (Fin 2) (Fin 2) F) := by
    simp [QuaternionAlgebra.finrank_eq_four, Module.finrank_matrix]
  exact ⟨AlgEquiv.ofBijective φ
    (LinearMap.linearEquivOfInjective φ.toLinearMap hinj hdim).bijective⟩

theorem kw_hjoint_quatSplit_of_ternaryIsotropic {a b : F} (ha : a ≠ 0) (hb : b ≠ 0)
    {x y z : F} (hnt : ¬ (x = 0 ∧ y = 0 ∧ z = 0))
    (heq : z * z = a * (x * x) + b * (y * y)) :
    Nonempty (QuaternionAlgebra F a 0 b ≃ₐ[F] Matrix (Fin 2) (Fin 2) F) := by
  by_cases hy : y = 0
  ·

    subst hy
    simp only [mul_zero, add_zero] at heq
    have hx : x ≠ 0 := fun hx0 ↦ hnt ⟨hx0, rfl,
      mul_self_eq_zero.mp (by rw [heq, hx0]; ring)⟩
    have hxx : x * x ≠ 0 := mul_ne_zero hx hx
    have hz : z ≠ 0 := fun hz0 ↦ ha (by
      have : a * (x * x) = 0 := by rw [← heq, hz0]; ring
      exact (mul_eq_zero.mp this).resolve_right hxx)
    refine kw_hjoint_quatSplit_of_sq hb (c := z / x)
      (div_ne_zero hz hx) ?_
    rw [div_mul_div_comm, heq, mul_div_assoc, div_self hxx, mul_one]
  ·
    have hyy : y * y ≠ 0 := mul_ne_zero hy hy
    refine kw_hjoint_quatSplit_of_norm ha hb (u := z / y) (v := x / y) ?_
    have key : z * z - a * (x * x) = b * (y * y) := by linear_combination heq
    rw [div_mul_div_comm, div_mul_div_comm, ← mul_div_assoc, ← sub_div, key,
      mul_div_assoc, div_self hyy, mul_one]

end SplitEngine

section SplitConverse

p2m_open "Matrix P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.Matrix"

variable {F : Type*} [Field F] [CharZero F]

theorem kw_hjoint_ternaryIsotropic_of_quatSplit {a b : F} (ha : a ≠ 0) (hb : b ≠ 0)
    (hsp : Nonempty (QuaternionAlgebra F a 0 b ≃ₐ[F] Matrix (Fin 2) (Fin 2) F)) :
    ∃ x y z : F, ¬ (x = 0 ∧ y = 0 ∧ z = 0) ∧ z * z = a * (x * x) + b * (y * y) := by

  by_cases hsq : ∃ c : F, a = c * c
  · obtain ⟨c, hc⟩ := hsq
    exact ⟨1, 0, c, by simp, by rw [hc]; ring⟩

  obtain ⟨e⟩ := hsp
  let I : Matrix (Fin 2) (Fin 2) F := e ⟨0, 1, 0, 0⟩
  let J : Matrix (Fin 2) (Fin 2) F := e ⟨0, 0, 1, 0⟩

  have hI2 : I * I = a • (1 : Matrix (Fin 2) (Fin 2) F) := by
    have h : (⟨0,1,0,0⟩ * ⟨0,1,0,0⟩ : QuaternionAlgebra F a 0 b) = algebraMap F _ a := by
      rw [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.coe_algebraMap]
      congr 1 <;> ring
    rw [show I * I = e (⟨0,1,0,0⟩ * ⟨0,1,0,0⟩) from (map_mul e _ _).symm, h,
      AlgEquiv.commutes, Algebra.algebraMap_eq_smul_one]
  have hJ2 : J * J = b • (1 : Matrix (Fin 2) (Fin 2) F) := by
    have h : (⟨0,0,1,0⟩ * ⟨0,0,1,0⟩ : QuaternionAlgebra F a 0 b) = algebraMap F _ b := by
      rw [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.coe_algebraMap]
      congr 1 <;> ring
    rw [show J * J = e (⟨0,0,1,0⟩ * ⟨0,0,1,0⟩) from (map_mul e _ _).symm, h,
      AlgEquiv.commutes, Algebra.algebraMap_eq_smul_one]
  have hanti : J * I = -(I * J) := by

    have hji : (⟨0,0,1,0⟩ * ⟨0,1,0,0⟩ : QuaternionAlgebra F a 0 b)
        = (⟨0, 0, 0, -1⟩ : QuaternionAlgebra F a 0 b) := by
      rw [QuaternionAlgebra.mk_mul_mk]; congr 1 <;> ring
    have hij : (⟨0,1,0,0⟩ * ⟨0,0,1,0⟩ : QuaternionAlgebra F a 0 b)
        = (⟨0, 0, 0, 1⟩ : QuaternionAlgebra F a 0 b) := by
      rw [QuaternionAlgebra.mk_mul_mk]; congr 1 <;> ring
    have hneg : (⟨0, 0, 0, -1⟩ : QuaternionAlgebra F a 0 b)
        = -(⟨0, 0, 0, 1⟩ : QuaternionAlgebra F a 0 b) := by
      rw [QuaternionAlgebra.neg_mk]; congr 1 <;> ring
    calc J * I = e (⟨0,0,1,0⟩ * ⟨0,1,0,0⟩) := (map_mul e _ _).symm
      _ = e (-(⟨0,1,0,0⟩ * ⟨0,0,1,0⟩)) := by rw [hji, hneg, hij]
      _ = -(I * J) := by rw [_root_.map_neg, map_mul]

  set t := I 0 0 with ht_def
  set s := I 0 1 with hs_def
  set u := I 1 0 with hu_def
  set p := J 0 0 with hp_def
  set q := J 0 1 with hq_def
  set r := J 1 0 with hr_def

  have h_a : t * t + s * u = a := by
    have := congrFun (congrFun hI2 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using this
  have h_b : p * p + q * r = b := by
    have := congrFun (congrFun hJ2 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using this
  have h_anti : p * t + q * u = -(t * p + s * r) := by
    have := congrFun (congrFun hanti 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this

  have hu : u ≠ 0 := fun hu0 ↦ hsq ⟨t, by rw [← h_a, hu0, mul_zero, add_zero]⟩

  refine ⟨r, u, p * u - r * t, fun ⟨_, hy, _⟩ ↦ hu hy, ?_⟩
  linear_combination r * r * h_a + u * u * h_b - u * r * h_anti

end SplitConverse

section AInfProof

p2m_open "Matrix P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.Matrix"

end AInfProof

section BCofiniteProof

open FLT.CampGenuineMk

scoped instance kw_hjoint_instFactPrimePrimesEquiv (v : HeightOneSpectrum (𝓞 ℚ)) :
    Fact (Rat.HeightOneSpectrum.primesEquiv v : ℕ).Prime :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

theorem kw_hjoint_padic_norm_ratCast_eq_one {p : ℕ} [Fact p.Prime] {q : ℚ}
    (hnum : ¬ p ∣ q.num.natAbs) (hden : ¬ p ∣ q.den) :
    ‖(q : ℚ_[p])‖ = 1 := by
  have hint : ∀ (k : ℤ), ¬ p ∣ k.natAbs → ‖((k : ℤ) : ℚ_[p])‖ = 1 := fun k hk ↦ by
    have hk' : ¬ (p : ℤ) ∣ k :=
      fun h ↦ hk (Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr h))
    rw [← PadicInt.coe_intCast, PadicInt.padic_norm_e_of_padicInt]
    exact le_antisymm (PadicInt.norm_le_one _)
      (not_lt.mp (mt (PadicInt.norm_int_lt_one_iff_dvd k).mp hk'))
  rw [show ((q : ℚ) : ℚ_[p]) = ((q.num : ℤ) : ℚ_[p]) / ((q.den : ℤ) : ℚ_[p]) by
      push_cast; exact_mod_cast (Rat.num_div_den q).symm,
    norm_div, hint q.num hnum, hint (q.den : ℤ) (by simpa using hden), div_one]

abbrev kw_hjoint_padic_ternaryIsotropic_atom : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (a b : ℚ_[p]), ‖a‖ = 1 → ‖b‖ = 1 →
    ∃ x y z : ℚ_[p], ¬ (x = 0 ∧ y = 0 ∧ z = 0) ∧
      z * z = a * (x * x) + b * (y * y)

theorem kw_hjoint_padic_isSquare_of_residue_sq {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) {c : ℤ_[p]} {s : ZMod p} (hs : s ≠ 0)
    (hcs : PadicInt.toZMod c = s * s) :
    IsSquare (c : ℚ_[p]) := by

  obtain ⟨sl, hslred⟩ := ZMod.ringHom_surjective (PadicInt.toZMod (p := p)) s
  have hslunit : IsUnit sl := IsLocalRing.notMem_maximalIdeal.mp <| by
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, hslred]; exact hs
  have hslnorm : ‖((sl : ℤ_[p]) : ℚ_[p])‖ = 1 := by
    rw [PadicInt.padic_norm_e_of_padicInt]; exact PadicInt.isUnit_iff.mp hslunit
  have hslne : ((sl : ℤ_[p]) : ℚ_[p]) ≠ 0 := fun h ↦ by simp [h] at hslnorm

  have hdiff0 : PadicInt.toZMod (c - sl * sl) = 0 := by
    rw [map_sub, map_mul, hslred, hcs, sub_self]
  have hdiffnorm : ‖((c - sl * sl : ℤ_[p]) : ℚ_[p])‖ < 1 := by
    rw [PadicInt.padic_norm_e_of_padicInt]
    refine lt_of_le_of_ne (PadicInt.norm_le_one _) (fun heq ↦ ?_)
    refine absurd hdiff0 ?_
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod]
    exact IsLocalRing.notMem_maximalIdeal.mpr (PadicInt.isUnit_iff.mpr heq)

  have htwo : ‖((2 : ℤ) : ℚ_[p])‖ = 1 := by
    have h2dvd : ¬ (p : ℤ) ∣ (2 : ℤ) := Int.natCast_dvd_natCast.not.mpr
      (fun h ↦ hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h))
    rw [← PadicInt.coe_intCast, PadicInt.padic_norm_e_of_padicInt]
    exact le_antisymm (PadicInt.norm_le_one _)
      (not_lt.mp (mt (PadicInt.norm_int_lt_one_iff_dvd (2 : ℤ)).mp h2dvd))
  have hlt : ‖(c : ℚ_[p]) / ((sl : ℚ_[p]) * (sl : ℚ_[p])) - 1‖ < ‖(2 : ℚ_[p])‖ ^ 2 := by
    rw [show ((2 : ℤ) : ℚ_[p]) = (2 : ℚ_[p]) from by push_cast; ring] at htwo
    rw [htwo, one_pow, div_sub_one (mul_ne_zero hslne hslne), norm_div, norm_mul, hslnorm,
      one_mul, div_one,
      show (c : ℚ_[p]) - (sl : ℚ_[p]) * (sl : ℚ_[p]) = ((c - sl * sl : ℤ_[p]) : ℚ_[p]) from
        by push_cast; ring]
    exact hdiffnorm
  obtain ⟨t, ht⟩ := kw_hjoint_padic_isSquare_of_close_one hlt
  exact ⟨(sl : ℚ_[p]) * t, by
    field_simp [mul_ne_zero hslne hslne] at ht
    linear_combination ht⟩

theorem kw_hjoint_padic_ternaryIsotropic_proved :
    kw_hjoint_padic_ternaryIsotropic_atom := by
  intro p hp hp2 a b hau hbu

  let a₀ : ℤ_[p] := ⟨a, hau.le⟩
  let b₀ : ℤ_[p] := ⟨b, hbu.le⟩
  have ha0 : PadicInt.toZMod a₀ ≠ 0 := by
    rw [ne_eq, ← RingHom.mem_ker, PadicInt.ker_toZMod]
    exact IsLocalRing.notMem_maximalIdeal.mpr
      (PadicInt.isUnit_iff.mpr (show ‖a₀‖ = 1 from hau))
  have hb0 : PadicInt.toZMod b₀ ≠ 0 := by
    rw [ne_eq, ← RingHom.mem_ker, PadicInt.ker_toZMod]
    exact IsLocalRing.notMem_maximalIdeal.mpr
      (PadicInt.isUnit_iff.mpr (show ‖b₀‖ = 1 from hbu))

  rcases gmk9_ser_diagForm_solution_dichotomy
      (PadicInt.toZMod a₀) (PadicInt.toZMod b₀) ha0 hb0 with
    ⟨x₀, y₀, z₀, hz₀, heq₀⟩ | ⟨x₀, y₀, hx₀, hy₀, heq₀⟩
  ·

    obtain ⟨xl, hxl⟩ := ZMod.ringHom_surjective (PadicInt.toZMod (p := p)) x₀
    obtain ⟨yl, hyl⟩ := ZMod.ringHom_surjective (PadicInt.toZMod (p := p)) y₀
    let c : ℤ_[p] := a₀ * (xl * xl) + b₀ * (yl * yl)
    have hcred : PadicInt.toZMod c = z₀ * z₀ := by
      simp only [c, map_add, map_mul, hxl, hyl]; exact heq₀.symm
    obtain ⟨z, hz⟩ := kw_hjoint_padic_isSquare_of_residue_sq hp2 hz₀ hcred
    refine ⟨(xl : ℚ_[p]), (yl : ℚ_[p]), z, ?_, ?_⟩
    · rintro ⟨-, -, rfl⟩
      rw [mul_zero] at hz
      have hcu : IsUnit c := IsLocalRing.notMem_maximalIdeal.mp <| by
        rw [← PadicInt.ker_toZMod, RingHom.mem_ker, hcred]; exact mul_ne_zero hz₀ hz₀
      refine absurd (PadicInt.isUnit_iff.mp hcu) (fun hn ↦ ?_)
      rw [PadicInt.norm_def, hz, norm_zero] at hn
      exact one_ne_zero hn.symm
    · rw [← hz]
      show (c : ℚ_[p]) = (a₀ : ℚ_[p]) * _ + (b₀ : ℚ_[p]) * _
      push_cast [c]
      ring
  ·

    have hneg : IsSquare (-(PadicInt.toZMod a₀ * PadicInt.toZMod b₀)) :=
      gmk9_ser_neg_mul_isSquare_of_isotropic hy₀ heq₀
    obtain ⟨r, hr⟩ := hneg
    have hr0 : r ≠ 0 := fun h ↦ by
      rw [h, mul_zero, neg_eq_zero, mul_eq_zero] at hr; exact hr.elim ha0 hb0
    obtain ⟨w, hw⟩ := kw_hjoint_padic_isSquare_of_residue_sq hp2
      (c := -(a₀ * b₀)) hr0 (by rw [_root_.map_neg, map_mul]; exact hr)

    refine ⟨b, w, 0, ?_, ?_⟩
    · rintro ⟨rfl, -, -⟩; simp at hbu
    · have hb' : (b₀ : ℚ_[p]) = b := rfl
      have ha' : (a₀ : ℚ_[p]) = a := rfl
      push_cast [← hb', ← ha'] at hw
      linear_combination b * hw

theorem kw_hjoint_isSplitAtPlace_of_units
    (hCW : kw_hjoint_padic_ternaryIsotropic_atom)
    (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0)
    (v : HeightOneSpectrum (𝓞 ℚ))
    (hp2 : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) ≠ 2)
    (hau : ‖(a : ℚ_[Rat.HeightOneSpectrum.primesEquiv v])‖ = 1)
    (hbu : ‖(b : ℚ_[Rat.HeightOneSpectrum.primesEquiv v])‖ = 1) :
    kw_isSplitAtPlace a b v := by
  set p : ℕ := (Rat.HeightOneSpectrum.primesEquiv v : ℕ) with hp_def
  haveI hpfact : Fact p.Prime := ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

  obtain ⟨x', y', z', hnt', heq'⟩ := hCW p hp2 (a : ℚ_[p]) (b : ℚ_[p]) hau hbu

  haveI : CharZero (v.adicCompletion ℚ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (v.adicCompletion ℚ)).injective
  let φ : v.adicCompletion ℚ ≃+* ℚ_[p] :=
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toRingEquiv
  let x := φ.symm x'; let y := φ.symm y'; let z := φ.symm z'

  have heq : z * z = ((a : ℚ) : v.adicCompletion ℚ) * (x * x)
      + ((b : ℚ) : v.adicCompletion ℚ) * (y * y) := by
    have h := congrArg φ.symm heq'
    simp only [map_add, map_mul, map_ratCast, x, y, z] at h
    exact h
  have hnt : ¬ (x = 0 ∧ y = 0 ∧ z = 0) := fun ⟨hx, hy, hz⟩ ↦ hnt'
    ⟨φ.symm.injective (hx.trans (_root_.map_zero φ.symm).symm),
      φ.symm.injective (hy.trans (_root_.map_zero φ.symm).symm),
      φ.symm.injective (hz.trans (_root_.map_zero φ.symm).symm)⟩

  exact kw_hjoint_quatSplit_of_ternaryIsotropic
    (Rat.cast_ne_zero.mpr ha : ((a : ℚ) : v.adicCompletion ℚ) ≠ 0)
    (Rat.cast_ne_zero.mpr hb : ((b : ℚ) : v.adicCompletion ℚ) ≠ 0) hnt heq

end BCofiniteProof

section AFinProof

theorem kw_HSCluster_A_fin_proved (a b : ℚ) : kw_HSCluster_A_fin a b := by
  intro ha hb v
  haveI : CharZero (v.adicCompletion ℚ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (v.adicCompletion ℚ)).injective
  have haF : (algebraMap ℚ (v.adicCompletion ℚ)) a ≠ 0 :=
    fun h ↦ ha ((algebraMap ℚ _).injective (h.trans (_root_.map_zero _).symm))
  have hbF : (algebraMap ℚ (v.adicCompletion ℚ)) b ≠ 0 :=
    fun h ↦ hb ((algebraMap ℚ _).injective (h.trans (_root_.map_zero _).symm))
  rw [not_iff_not]
  constructor
  ·
    intro hsp
    obtain ⟨x, y, z, hnt, heq⟩ :=
      kw_hjoint_ternaryIsotropic_of_quatSplit haF hbF hsp
    exact ⟨z, x, y, fun ⟨hz, hx, hy⟩ ↦ hnt ⟨hx, hy, hz⟩, by linear_combination heq⟩
  ·
    rintro ⟨z, x, y, hnt, heq⟩
    exact kw_hjoint_quatSplit_of_ternaryIsotropic haF hbF
      (x := x) (y := y) (z := z)
      (fun ⟨hx, hy, hz⟩ ↦ hnt ⟨hz, hx, hy⟩) (by linear_combination heq)

end AFinProof

section MainWire

variable (a b : ℚ)

end MainWire

end FLT.NumberTheory

end

end

section
section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

namespace FLT
namespace CampGenuineMk

structure gmk6_hil_SquareClass : Type where

  valParity : ZMod 2

  unitSign : ℤˣ
deriving DecidableEq

@[scoped ext] theorem gmk6_hil_SquareClass_ext {x y : gmk6_hil_SquareClass}
    (h1 : x.valParity = y.valParity) (h2 : x.unitSign = y.unitSign) : x = y := by
  have _pin := Classical.em True
  cases x; cases y; cases h1; cases h2; rfl

scoped instance gmk6_hil_instOne : One gmk6_hil_SquareClass := ⟨⟨0, 1⟩⟩

scoped instance gmk6_hil_instMul : Mul gmk6_hil_SquareClass :=
  ⟨fun x y => ⟨x.valParity + y.valParity, x.unitSign * y.unitSign⟩⟩

scoped instance gmk6_hil_instInv : Inv gmk6_hil_SquareClass := ⟨fun x => x⟩

@[scoped simp] theorem gmk6_hil_mul_valParity (x y : gmk6_hil_SquareClass) :
    (x * y).valParity = x.valParity + y.valParity := rfl

@[scoped simp] theorem gmk6_hil_mul_unitSign (x y : gmk6_hil_SquareClass) :
    (x * y).unitSign = x.unitSign * y.unitSign := rfl

@[scoped simp] theorem gmk6_hil_one_valParity :
    (1 : gmk6_hil_SquareClass).valParity = 0 := rfl

@[scoped simp] theorem gmk6_hil_one_unitSign :
    (1 : gmk6_hil_SquareClass).unitSign = 1 := rfl

theorem gmk6_hil_zmod_two_add_self (c : ZMod 2) : c + c = 0 := by
  have _pin := Classical.em True
  revert c; decide

theorem gmk6_hil_units_mul_self (u : ℤˣ) : u * u = 1 := by
  have _pin := Classical.em True
  rcases Int.units_eq_one_or u with rfl | rfl <;> decide

scoped instance gmk6_hil_instCommGroup : CommGroup gmk6_hil_SquareClass where
  mul_assoc a b c := gmk6_hil_SquareClass_ext (add_assoc _ _ _) (mul_assoc _ _ _)
  one_mul a := gmk6_hil_SquareClass_ext (zero_add _) (one_mul _)
  mul_one a := gmk6_hil_SquareClass_ext (add_zero _) (mul_one _)
  inv_mul_cancel a := gmk6_hil_SquareClass_ext
    (gmk6_hil_zmod_two_add_self _) (gmk6_hil_units_mul_self _)
  mul_comm a b := gmk6_hil_SquareClass_ext (add_comm _ _) (mul_comm _ _)

def gmk6_hil_unitClass (s : ℤˣ) : gmk6_hil_SquareClass := ⟨0, s⟩

def gmk6_hil_uniformiserClass : gmk6_hil_SquareClass := ⟨1, 1⟩

theorem gmk6_hil_unitClass_one : gmk6_hil_unitClass 1 = 1 := by
  have _pin := Classical.em True
  exact rfl

theorem gmk6_hil_units_pow_val_add (u : ℤˣ) (a b : ZMod 2) :
    u ^ (a + b).val = u ^ a.val * u ^ b.val := by
  have _pin := Classical.em True
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · revert a b; decide

def gmk6_hil_pair (e : ℤˣ) (x y : gmk6_hil_SquareClass) : ℤˣ :=
  e ^ (x.valParity * y.valParity).val
    * y.unitSign ^ x.valParity.val
    * x.unitSign ^ y.valParity.val

theorem gmk6_hil_pair_symm (e : ℤˣ) (x y : gmk6_hil_SquareClass) :
    gmk6_hil_pair e x y = gmk6_hil_pair e y x := by
  have _pin := Classical.em True
  unfold gmk6_hil_pair
  rw [mul_comm x.valParity y.valParity]
  simp [mul_comm, mul_left_comm, mul_assoc]

theorem gmk6_hil_pair_one_left (e : ℤˣ) (y : gmk6_hil_SquareClass) :
    gmk6_hil_pair e 1 y = 1 := by
  have _pin := Classical.em True
  unfold gmk6_hil_pair
  simp

theorem gmk6_hil_pair_mul_left (e : ℤˣ) (x y z : gmk6_hil_SquareClass) :
    gmk6_hil_pair e (x * y) z = gmk6_hil_pair e x z * gmk6_hil_pair e y z := by
  have _pin := Classical.em True
  obtain ⟨a, s⟩ := x
  obtain ⟨b, t⟩ := y
  obtain ⟨c, u⟩ := z
  have hZ : ∀ w : ZMod 2, w = 0 ∨ w = 1 := by decide
  rcases hZ a with rfl | rfl <;> rcases hZ b with rfl | rfl <;>
    rcases hZ c with rfl | rfl <;>
    rcases Int.units_eq_one_or e with rfl | rfl <;>
    rcases Int.units_eq_one_or s with rfl | rfl <;>
    rcases Int.units_eq_one_or t with rfl | rfl <;>
    rcases Int.units_eq_one_or u with rfl | rfl <;> decide

theorem gmk6_hil_pair_mul_right (e : ℤˣ) (x y z : gmk6_hil_SquareClass) :
    gmk6_hil_pair e x (y * z) = gmk6_hil_pair e x y * gmk6_hil_pair e x z := by
  have _pin := Classical.em True
  rw [gmk6_hil_pair_symm e x (y * z), gmk6_hil_pair_mul_left,
    gmk6_hil_pair_symm e y x, gmk6_hil_pair_symm e z x]

def gmk6_hil_epsSign (p : ℕ) : ℤˣ :=
  if p % 4 = 1 then 1 else -1

def gmk6_hil_legendreSign (p : ℕ) [Fact p.Prime] (a : ℤ) : ℤˣ :=
  if legendreSym p a = 1 then 1 else -1

def gmk6_hil_unitClassOf (p : ℕ) [Fact p.Prime] (a : ℤ) : gmk6_hil_SquareClass :=
  gmk6_hil_unitClass (gmk6_hil_legendreSign p a)

theorem gmk6_hil_legendreSign_coe (p : ℕ) [Fact p.Prime] (a : ℤ)
    (ha : (a : ZMod p) ≠ 0) :
    ((gmk6_hil_legendreSign p a : ℤˣ) : ℤ) = legendreSym p a := by
  have _pin := Classical.em True
  rcases legendreSym.eq_one_or_neg_one p ha with h | h
  · unfold gmk6_hil_legendreSign
    rw [if_pos h, h, Units.val_one]
  · unfold gmk6_hil_legendreSign
    rw [if_neg (by rw [h]; norm_num), h]
    simp

theorem gmk6_hil_epsSign_eq_legendre_neg_one (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) :
    ((gmk6_hil_epsSign p : ℤˣ) : ℤ) = legendreSym p (-1) := by
  have _pin := Classical.em True
  have hodd : p % 2 = 1 :=
    Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp2)
  have h4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
  rw [legendreSym.at_neg_one hp2]
  rcases h4 with h | h
  · unfold gmk6_hil_epsSign
    rw [if_pos h, ZMod.χ₄_nat_one_mod_four h, Units.val_one]
  · unfold gmk6_hil_epsSign
    rw [if_neg (by omega), ZMod.χ₄_nat_three_mod_four h]
    simp

theorem gmk6_hil_table_unit_unit (e : ℤˣ) (s t : ℤˣ) :
    gmk6_hil_pair e (gmk6_hil_unitClass s) (gmk6_hil_unitClass t) = 1 := by
  have _pin := Classical.em True
  unfold gmk6_hil_pair gmk6_hil_unitClass
  simp

theorem gmk6_hil_table_unit_uniformiser (e : ℤˣ) (s : ℤˣ) :
    gmk6_hil_pair e (gmk6_hil_unitClass s) gmk6_hil_uniformiserClass = s := by
  have _pin := Classical.em True
  rcases Int.units_eq_one_or e with rfl | rfl <;>
    rcases Int.units_eq_one_or s with rfl | rfl <;> decide

theorem gmk6_hil_table_uniformiser_unit (e : ℤˣ) (t : ℤˣ) :
    gmk6_hil_pair e gmk6_hil_uniformiserClass (gmk6_hil_unitClass t) = t := by
  have _pin := Classical.em True
  rw [gmk6_hil_pair_symm]
  exact gmk6_hil_table_unit_uniformiser e t

theorem gmk6_hil_table_uniformiser_uniformiser (e : ℤˣ) :
    gmk6_hil_pair e gmk6_hil_uniformiserClass gmk6_hil_uniformiserClass = e := by
  have _pin := Classical.em True
  rcases Int.units_eq_one_or e with rfl | rfl <;> decide

end FLT.CampGenuineMk
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section
section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

namespace FLT
namespace CampGenuineMk

variable {p : ℕ} [Fact p.Prime]

theorem gmk7_cls_p_real_pos : (0 : ℝ) < (p : ℝ) := by
  have _pin := Classical.em True
  exact_mod_cast (Fact.out : p.Prime).pos

theorem gmk7_cls_p_real_ne_zero : (p : ℝ) ≠ 0 := by
  have _pin := Classical.em True
  exact_mod_cast (Fact.out : p.Prime).ne_zero

theorem gmk7_cls_p_real_ne_one : (p : ℝ) ≠ 1 := by
  have _pin := Classical.em True
  exact_mod_cast (Fact.out : p.Prime).ne_one

theorem gmk7_cls_p_padic_ne_zero : (p : ℚ_[p]) ≠ 0 := by
  have _pin := Classical.em True
  exact_mod_cast (Fact.out : p.Prime).ne_zero

theorem gmk7_cls_valuation_eq_zero_of_norm_one {x : ℚ_[p]} (hx : x ≠ 0)
    (h : ‖x‖ = 1) : x.valuation = 0 := by
  have _pin := Classical.em True
  have h1 : (p : ℝ) ^ (-x.valuation) = (p : ℝ) ^ (0 : ℤ) := by
    rw [← Padic.norm_eq_zpow_neg_valuation hx, h, zpow_zero]
  have h2 := (zpow_right_inj₀ gmk7_cls_p_real_pos gmk7_cls_p_real_ne_one).mp h1
  omega

theorem gmk7_cls_norm_unitScale {x : ℚ_[p]} (hx : x ≠ 0) :
    ‖x * (p : ℚ_[p]) ^ (-x.valuation)‖ = 1 := by
  have _pin := Classical.em True
  rw [norm_mul, Padic.norm_p_zpow, Padic.norm_eq_zpow_neg_valuation hx, neg_neg,
    ← zpow_add₀ gmk7_cls_p_real_ne_zero, _root_.neg_add_cancel, zpow_zero]

noncomputable def gmk7_cls_unitPart {x : ℚ_[p]} (hx : x ≠ 0) : ℤ_[p]ˣ :=
  PadicInt.mkUnits (gmk7_cls_norm_unitScale hx)

theorem gmk7_cls_unitPart_coe {x : ℚ_[p]} (hx : x ≠ 0) :
    ((gmk7_cls_unitPart hx : ℤ_[p]) : ℚ_[p]) = x * (p : ℚ_[p]) ^ (-x.valuation) := by
  have _pin := Classical.em True
  exact PadicInt.mkUnits_eq _

theorem gmk7_cls_unitPart_spec {x : ℚ_[p]} (hx : x ≠ 0) :
    x = ((gmk7_cls_unitPart hx : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ x.valuation := by
  have _pin := Classical.em True
  rw [gmk7_cls_unitPart_coe, mul_assoc, ← zpow_add₀ gmk7_cls_p_padic_ne_zero,
    _root_.neg_add_cancel, zpow_zero, mul_one]

theorem gmk7_cls_unitPart_mul {x y : ℚ_[p]} (hx : x ≠ 0) (hy : y ≠ 0) :
    gmk7_cls_unitPart (mul_ne_zero hx hy) = gmk7_cls_unitPart hx * gmk7_cls_unitPart hy := by
  have _pin := Classical.em True
  have h : ((gmk7_cls_unitPart (mul_ne_zero hx hy) : ℤ_[p]) : ℚ_[p])
      = (((gmk7_cls_unitPart hx * gmk7_cls_unitPart hy : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) := by
    rw [Units.val_mul, PadicInt.coe_mul, gmk7_cls_unitPart_coe (mul_ne_zero hx hy),
      gmk7_cls_unitPart_coe hx, gmk7_cls_unitPart_coe hy, Padic.valuation_mul hx hy,
      neg_add, zpow_add₀ gmk7_cls_p_padic_ne_zero]
    ring
  exact Units.ext (Subtype.coe_injective h)

theorem gmk7_cls_toZMod_eq_zero_iff (z : ℤ_[p]) :
    PadicInt.toZMod z = 0 ↔ ‖z‖ < 1 := by
  have _pin := Classical.em True
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]
  exact (PadicInt.norm_lt_one_iff_dvd z).symm

theorem gmk7_cls_norm_one_iff_toZMod_ne_zero (z : ℤ_[p]) :
    ‖z‖ = 1 ↔ PadicInt.toZMod z ≠ 0 := by
  have _pin := Classical.em True
  constructor
  · intro h h0
    rw [gmk7_cls_toZMod_eq_zero_iff, h] at h0
    exact lt_irrefl 1 h0
  · intro h
    rcases lt_or_eq_of_le (PadicInt.norm_le_one z) with hlt | heq
    · exact absurd ((gmk7_cls_toZMod_eq_zero_iff z).mpr hlt) h
    · exact heq

noncomputable def gmk7_cls_residue {x : ℚ_[p]} (hx : x ≠ 0) : ZMod p :=
  PadicInt.toZMod ((gmk7_cls_unitPart hx : ℤ_[p]))

theorem gmk7_cls_residue_ne_zero {x : ℚ_[p]} (hx : x ≠ 0) :
    gmk7_cls_residue hx ≠ 0 := by
  have _pin := Classical.em True
  unfold gmk7_cls_residue
  rw [← gmk7_cls_norm_one_iff_toZMod_ne_zero]
  exact PadicInt.norm_units _

theorem gmk7_cls_residue_mul {x y : ℚ_[p]} (hx : x ≠ 0) (hy : y ≠ 0) :
    gmk7_cls_residue (mul_ne_zero hx hy) = gmk7_cls_residue hx * gmk7_cls_residue hy := by
  have _pin := Classical.em True
  unfold gmk7_cls_residue
  rw [gmk7_cls_unitPart_mul hx hy, Units.val_mul, map_mul]

noncomputable def gmk7_cls_sign {x : ℚ_[p]} (hx : x ≠ 0) : ℤˣ :=
  if quadraticChar (ZMod p) (gmk7_cls_residue hx) = 1 then 1 else -1

theorem gmk7_cls_sign_eq_one_iff {x : ℚ_[p]} (hx : x ≠ 0) :
    gmk7_cls_sign hx = 1 ↔ IsSquare (gmk7_cls_residue hx) := by
  have _pin := Classical.em True
  unfold gmk7_cls_sign
  split_ifs with h
  · exact iff_of_true rfl
      ((quadraticChar_one_iff_isSquare (gmk7_cls_residue_ne_zero hx)).mp h)
  · refine iff_of_false (by decide) fun hsq =>
      h ((quadraticChar_one_iff_isSquare (gmk7_cls_residue_ne_zero hx)).mpr hsq)

theorem gmk7_cls_sign_mul {x y : ℚ_[p]} (hx : x ≠ 0) (hy : y ≠ 0) :
    gmk7_cls_sign (mul_ne_zero hx hy) = gmk7_cls_sign hx * gmk7_cls_sign hy := by
  have _pin := Classical.em True
  unfold gmk7_cls_sign
  rw [gmk7_cls_residue_mul hx hy, map_mul]
  rcases quadraticChar_dichotomy (gmk7_cls_residue_ne_zero hx) with h1 | h1 <;>
    rcases quadraticChar_dichotomy (gmk7_cls_residue_ne_zero hy) with h2 | h2 <;>
    rw [h1, h2] <;> decide

noncomputable def gmk7_cls_classOf {x : ℚ_[p]} (hx : x ≠ 0) : gmk6_hil_SquareClass :=
  ⟨(x.valuation : ZMod 2), gmk7_cls_sign hx⟩

theorem gmk7_cls_classOf_mul {x y : ℚ_[p]} (hx : x ≠ 0) (hy : y ≠ 0) :
    gmk7_cls_classOf (mul_ne_zero hx hy) = gmk7_cls_classOf hx * gmk7_cls_classOf hy := by
  have _pin := Classical.em True
  refine gmk6_hil_SquareClass_ext ?_ (gmk7_cls_sign_mul hx hy)
  rw [gmk6_hil_mul_valParity]
  show (((x * y).valuation : ℤ) : ZMod 2) = ((x.valuation : ZMod 2)) + ((y.valuation : ZMod 2))
  rw [Padic.valuation_mul hx hy, Int.cast_add]

theorem gmk7_cls_carrier_mul_self (c : gmk6_hil_SquareClass) : c * c = 1 := by
  have _pin := Classical.em True
  exact gmk6_hil_SquareClass_ext (gmk6_hil_zmod_two_add_self _) (gmk6_hil_units_mul_self _)

theorem gmk7_cls_classOf_eq_one_of_isSquare {x : ℚ_[p]} (hx : x ≠ 0)
    (h : IsSquare x) : gmk7_cls_classOf hx = 1 := by
  have _pin := Classical.em True
  obtain ⟨r, rfl⟩ := h
  have hr : r ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hx
    exact hx rfl
  calc gmk7_cls_classOf hx = gmk7_cls_classOf (mul_ne_zero hr hr) := rfl
    _ = gmk7_cls_classOf hr * gmk7_cls_classOf hr := gmk7_cls_classOf_mul hr hr
    _ = 1 := gmk7_cls_carrier_mul_self _

theorem gmk7_cls_classOf_one :
    gmk7_cls_classOf (one_ne_zero : (1 : ℚ_[p]) ≠ 0) = 1 := by
  have _pin := Classical.em True
  exact gmk7_cls_classOf_eq_one_of_isSquare one_ne_zero ⟨1, (one_mul 1).symm⟩

theorem gmk7_cls_unit_isSquare_of_residue (hp2 : p ≠ 2) {u : ℤ_[p]}
    (hu : ‖u‖ = 1) (hsq : IsSquare (PadicInt.toZMod u)) : IsSquare u := by
  have _pin := Classical.em True
  obtain ⟨t, ht⟩ := hsq
  have hu0 : PadicInt.toZMod u ≠ 0 := (gmk7_cls_norm_one_iff_toZMod_ne_zero u).mp hu
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [mul_zero] at ht
    exact hu0 ht
  set a : ℤ_[p] := ((t.val : ℕ) : ℤ_[p]) with ha_def
  have ha_res : PadicInt.toZMod a = t := by
    rw [ha_def, map_natCast, ZMod.natCast_val, ZMod.cast_id]
  have ha_norm : ‖a‖ = 1 :=
    (gmk7_cls_norm_one_iff_toZMod_ne_zero a).mpr (by rw [ha_res]; exact ht0)
  have h2norm : ‖(2 : ℤ_[p])‖ = 1 := by
    have h22 : (2 : ℤ_[p]) = ((2 : ℕ) : ℤ_[p]) := by norm_cast
    rw [h22, gmk7_cls_norm_one_iff_toZMod_ne_zero, map_natCast]
    intro h20
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h20
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hdvd)
  set F : Polynomial ℤ_[p] := Polynomial.X ^ 2 - Polynomial.C u with hF_def
  have hFa : ∀ b : ℤ_[p], Polynomial.aeval b F = b ^ 2 - u := by
    intro b
    rw [hF_def]
    simp
  have hFda : Polynomial.aeval a F.derivative = 2 * a := by
    rw [hF_def, Polynomial.derivative_sub, Polynomial.derivative_C,
      Polynomial.derivative_sq, Polynomial.derivative_X, sub_zero, mul_one,
      map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    simp
  have hnorm : ‖Polynomial.aeval a F‖ < ‖Polynomial.aeval a F.derivative‖ ^ 2 := by
    rw [hFa a, hFda, norm_mul, h2norm, ha_norm, mul_one, one_pow,
      ← gmk7_cls_toZMod_eq_zero_iff, map_sub, map_pow, ha_res, ht]
    ring
  obtain ⟨z, hz, -, -, -⟩ := hensels_lemma hnorm
  have hz2 : z ^ 2 - u = 0 := by
    rw [← hFa z]
    exact hz
  have hzu : z ^ 2 = u := sub_eq_zero.mp hz2
  exact ⟨z, by rw [← hzu, pow_two]⟩

theorem gmk7_cls_isSquare_of_classOf_eq_one (hp2 : p ≠ 2) {x : ℚ_[p]}
    (hx : x ≠ 0) (h : gmk7_cls_classOf hx = 1) : IsSquare x := by
  have _pin := Classical.em True
  have hval : ((x.valuation : ℤ) : ZMod 2) = 0 := congrArg gmk6_hil_SquareClass.valParity h
  have hsgn : gmk7_cls_sign hx = 1 := congrArg gmk6_hil_SquareClass.unitSign h
  obtain ⟨k, hk⟩ : (2 : ℤ) ∣ x.valuation := by
    have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd x.valuation 2).mp hval
    exact_mod_cast hdvd
  have hres : IsSquare (gmk7_cls_residue hx) := (gmk7_cls_sign_eq_one_iff hx).mp hsgn
  obtain ⟨s, hs⟩ : IsSquare ((gmk7_cls_unitPart hx : ℤ_[p])) :=
    gmk7_cls_unit_isSquare_of_residue hp2 (PadicInt.norm_units _) hres
  refine ⟨(s : ℚ_[p]) * (p : ℚ_[p]) ^ k, ?_⟩
  calc x = ((gmk7_cls_unitPart hx : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ x.valuation :=
        gmk7_cls_unitPart_spec hx
    _ = (((s : ℤ_[p]) : ℚ_[p]) * ((s : ℤ_[p]) : ℚ_[p])) * (p : ℚ_[p]) ^ (2 * k) := by
        rw [hk, hs, PadicInt.coe_mul]
    _ = ((s : ℚ_[p]) * (p : ℚ_[p]) ^ k) * ((s : ℚ_[p]) * (p : ℚ_[p]) ^ k) := by
        rw [two_mul, zpow_add₀ gmk7_cls_p_padic_ne_zero]
        ring

theorem gmk7_cls_classOf_eq_one_iff_isSquare (hp2 : p ≠ 2) {x : ℚ_[p]}
    (hx : x ≠ 0) : gmk7_cls_classOf hx = 1 ↔ IsSquare x := by
  have _pin := Classical.em True
  exact ⟨gmk7_cls_isSquare_of_classOf_eq_one hp2 hx, gmk7_cls_classOf_eq_one_of_isSquare hx⟩

theorem gmk7_cls_norm_natCast_eq_one {n : ℕ} (hn : (n : ZMod p) ≠ 0) :
    ‖(n : ℤ_[p])‖ = 1 := by
  have _pin := Classical.em True
  rw [gmk7_cls_norm_one_iff_toZMod_ne_zero, map_natCast]
  exact hn

theorem gmk7_cls_natCast_ne_zero {n : ℕ} (hn : (n : ZMod p) ≠ 0) :
    (n : ℚ_[p]) ≠ 0 := by
  have _pin := Classical.em True
  intro h0
  have h1 : ‖(n : ℚ_[p])‖ = 1 := by
    rw [← PadicInt.coe_natCast, PadicInt.padic_norm_e_of_padicInt]
    exact gmk7_cls_norm_natCast_eq_one hn
  rw [h0, norm_zero] at h1
  exact zero_ne_one h1

theorem gmk7_cls_valuation_natCast_eq_zero {n : ℕ} (hn : (n : ZMod p) ≠ 0) :
    (n : ℚ_[p]).valuation = 0 := by
  have _pin := Classical.em True
  apply gmk7_cls_valuation_eq_zero_of_norm_one (gmk7_cls_natCast_ne_zero hn)
  rw [← PadicInt.coe_natCast, PadicInt.padic_norm_e_of_padicInt]
  exact gmk7_cls_norm_natCast_eq_one hn

theorem gmk7_cls_unitPart_natCast {n : ℕ} (hn : (n : ZMod p) ≠ 0) :
    ((gmk7_cls_unitPart (gmk7_cls_natCast_ne_zero hn) : ℤ_[p])) = (n : ℤ_[p]) := by
  have _pin := Classical.em True
  have h : ((gmk7_cls_unitPart (gmk7_cls_natCast_ne_zero hn) : ℤ_[p]) : ℚ_[p])
      = (((n : ℤ_[p])) : ℚ_[p]) := by
    rw [gmk7_cls_unitPart_coe, gmk7_cls_valuation_natCast_eq_zero hn, _root_.neg_zero,
      zpow_zero, mul_one, PadicInt.coe_natCast]
  exact Subtype.coe_injective h

theorem gmk7_cls_residue_natCast {n : ℕ} (hn : (n : ZMod p) ≠ 0) :
    gmk7_cls_residue (gmk7_cls_natCast_ne_zero hn) = (n : ZMod p) := by
  have _pin := Classical.em True
  unfold gmk7_cls_residue
  rw [gmk7_cls_unitPart_natCast hn, map_natCast]

theorem gmk7_cls_classOf_natCast {n : ℕ} (hn : (n : ZMod p) ≠ 0) :
    gmk7_cls_classOf (gmk7_cls_natCast_ne_zero hn)
      = gmk6_hil_unitClass
          (if quadraticChar (ZMod p) ((n : ZMod p)) = 1 then 1 else -1) := by
  have _pin := Classical.em True
  refine gmk6_hil_SquareClass_ext ?_ ?_
  · show (((n : ℚ_[p]).valuation : ℤ) : ZMod 2) = (0 : ZMod 2)
    rw [gmk7_cls_valuation_natCast_eq_zero hn, Int.cast_zero]
  · show gmk7_cls_sign (gmk7_cls_natCast_ne_zero hn)
      = (if quadraticChar (ZMod p) ((n : ZMod p)) = 1 then 1 else -1)
    unfold gmk7_cls_sign
    rw [gmk7_cls_residue_natCast hn]

theorem gmk7_cls_classOf_natCast_eq_unitClassOf {n : ℕ} (hn : (n : ZMod p) ≠ 0) :
    gmk7_cls_classOf (gmk7_cls_natCast_ne_zero hn) = gmk6_hil_unitClassOf p (n : ℤ) := by
  have _pin := Classical.em True
  rw [gmk7_cls_classOf_natCast hn]
  unfold gmk6_hil_unitClassOf gmk6_hil_legendreSign legendreSym
  have hcast : (((n : ℤ) : ZMod p)) = ((n : ZMod p)) := by
    norm_cast
  rw [hcast]

theorem gmk7_cls_unitPart_p :
    gmk7_cls_unitPart (gmk7_cls_p_padic_ne_zero (p := p)) = 1 := by
  have _pin := Classical.em True
  have h : ((gmk7_cls_unitPart (gmk7_cls_p_padic_ne_zero (p := p)) : ℤ_[p]) : ℚ_[p])
      = (((1 : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) := by
    rw [Units.val_one, PadicInt.coe_one, gmk7_cls_unitPart_coe, Padic.valuation_p,
      _root_.zpow_neg, zpow_one]
    exact mul_inv_cancel₀ gmk7_cls_p_padic_ne_zero
  exact Units.ext (Subtype.coe_injective h)

theorem gmk7_cls_classOf_p :
    gmk7_cls_classOf (gmk7_cls_p_padic_ne_zero (p := p)) = gmk6_hil_uniformiserClass := by
  have _pin := Classical.em True
  refine gmk6_hil_SquareClass_ext ?_ ?_
  · show ((((p : ℚ_[p]).valuation : ℤ)) : ZMod 2) = (1 : ZMod 2)
    rw [Padic.valuation_p, Int.cast_one]
  · show gmk7_cls_sign (gmk7_cls_p_padic_ne_zero (p := p)) = 1
    unfold gmk7_cls_sign gmk7_cls_residue
    rw [gmk7_cls_unitPart_p, Units.val_one, map_one,
      if_pos (MulChar.map_one (quadraticChar (ZMod p)))]

end FLT.CampGenuineMk
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section
section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

namespace FLT
namespace CampGenuineMk

variable {p : ℕ} [Fact p.Prime]

theorem gmk7_cls_valuation_neg {x : ℚ_[p]} (hx : x ≠ 0) :
    (-x).valuation = x.valuation := by
  have _pin := Classical.em True
  have h1 : (p : ℝ) ^ (-(-x).valuation) = (p : ℝ) ^ (-x.valuation) := by
    rw [← Padic.norm_eq_zpow_neg_valuation (neg_ne_zero.mpr hx), norm_neg,
      Padic.norm_eq_zpow_neg_valuation hx]
  have h2 := (zpow_right_inj₀ gmk7_cls_p_real_pos gmk7_cls_p_real_ne_one).mp h1
  omega

theorem gmk7_cls_valuation_sub_eq_left {a b : ℚ_[p]} (ha : a ≠ 0) (hb : b ≠ 0)
    (hlt : a.valuation < b.valuation) : (a - b).valuation = a.valuation := by
  have _pin := Classical.em True
  have hab : a - b ≠ 0 := by
    intro h0
    rw [sub_eq_zero] at h0
    rw [h0] at hlt
    exact lt_irrefl _ hlt
  have h1 : min a.valuation (-b).valuation ≤ (a + -b).valuation :=
    Padic.le_valuation_add (by rw [← sub_eq_add_neg]; exact hab)
  rw [← sub_eq_add_neg, gmk7_cls_valuation_neg hb, min_eq_left hlt.le] at h1
  have hsum : a - b + b = a := by ring
  have h2 : min (a - b).valuation b.valuation ≤ (a - b + b).valuation :=
    Padic.le_valuation_add (by rw [hsum]; exact ha)
  rw [hsum] at h2
  rcases le_or_gt (a - b).valuation b.valuation with hle | hgt
  · rw [min_eq_left hle] at h2
    exact le_antisymm h2 h1
  · rw [min_eq_right hgt.le] at h2
    exact absurd h2 (not_le.mpr hlt)

theorem gmk7_cls_norm_sq_sub_nonsquare_unit {W U : ℤ_[p]}
    (hUns : ¬IsSquare (PadicInt.toZMod U)) : ‖W * W - U‖ = 1 := by
  have _pin := Classical.em True
  rw [gmk7_cls_norm_one_iff_toZMod_ne_zero]
  intro h0
  rw [map_sub, map_mul] at h0
  exact hUns ⟨PadicInt.toZMod W, (sub_eq_zero.mp h0).symm⟩

theorem gmk7_cls_sq_sub_nonsquare_unit_valuation (hp2 : p ≠ 2) {U : ℤ_[p]}
    (hU1 : ‖U‖ = 1) (hUns : ¬IsSquare (PadicInt.toZMod U)) (x z : ℚ_[p])
    (hxz : ¬(x = 0 ∧ z = 0)) :
    z * z - (U : ℚ_[p]) * (x * x) ≠ 0 ∧
      (2 : ℤ) ∣ (z * z - (U : ℚ_[p]) * (x * x)).valuation := by
  have _pin := Classical.em True
  have hU0 : U ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hU1
    exact zero_ne_one hU1
  have hUq : (U : ℚ_[p]) ≠ 0 := PadicInt.coe_ne_zero.mpr hU0
  have hUqn : ‖(U : ℚ_[p])‖ = 1 := by
    rw [PadicInt.padic_norm_e_of_padicInt]
    exact hU1
  have hUv : (U : ℚ_[p]).valuation = 0 :=
    gmk7_cls_valuation_eq_zero_of_norm_one hUq hUqn
  by_cases hx0 : x = 0
  · have hz0 : z ≠ 0 := fun h0 => hxz ⟨hx0, h0⟩
    rw [hx0, zero_mul, mul_zero, sub_zero]
    refine ⟨mul_ne_zero hz0 hz0, ⟨z.valuation, ?_⟩⟩
    rw [Padic.valuation_mul hz0 hz0]
    ring
  · by_cases hz0 : z = 0
    · have hBne : (U : ℚ_[p]) * (x * x) ≠ 0 :=
        mul_ne_zero hUq (mul_ne_zero hx0 hx0)
      rw [hz0, zero_mul, zero_sub]
      refine ⟨neg_ne_zero.mpr hBne, ?_⟩
      rw [gmk7_cls_valuation_neg hBne, Padic.valuation_mul hUq (mul_ne_zero hx0 hx0),
        hUv, Padic.valuation_mul hx0 hx0]
      exact ⟨x.valuation, by ring⟩
    · have hA : z * z ≠ 0 := mul_ne_zero hz0 hz0
      have hB : (U : ℚ_[p]) * (x * x) ≠ 0 :=
        mul_ne_zero hUq (mul_ne_zero hx0 hx0)
      have hvA : (z * z).valuation = 2 * z.valuation := by
        rw [Padic.valuation_mul hz0 hz0]
        ring
      have hvB : ((U : ℚ_[p]) * (x * x)).valuation = 2 * x.valuation := by
        rw [Padic.valuation_mul hUq (mul_ne_zero hx0 hx0), hUv,
          Padic.valuation_mul hx0 hx0]
        ring
      rcases lt_trichotomy (z * z).valuation ((U : ℚ_[p]) * (x * x)).valuation
        with hlt | heq2 | hgt
      · have hne : z * z - (U : ℚ_[p]) * (x * x) ≠ 0 := by
          intro h0
          rw [sub_eq_zero] at h0
          rw [h0] at hlt
          exact lt_irrefl _ hlt
        refine ⟨hne, ?_⟩
        rw [gmk7_cls_valuation_sub_eq_left hA hB hlt, hvA]
        exact ⟨z.valuation, rfl⟩
      · have hvzx : z.valuation = x.valuation := by
          rw [hvA, hvB] at heq2
          omega
        set w : ℚ_[p] := z * x⁻¹ with hw_def
        have hxw : x * w = z := by
          rw [hw_def, mul_comm z x⁻¹, ← mul_assoc, mul_inv_cancel₀ hx0, one_mul]
        have hw_norm : ‖w‖ = 1 := by
          rw [hw_def, norm_mul, norm_inv, Padic.norm_eq_zpow_neg_valuation hz0,
            Padic.norm_eq_zpow_neg_valuation hx0, hvzx]
          exact mul_inv_cancel₀ (zpow_ne_zero _ gmk7_cls_p_real_ne_zero)
        set W : ℤ_[p] := ⟨w, le_of_eq hw_norm⟩ with hW_def
        have hWcoe : ((W : ℤ_[p]) : ℚ_[p]) = w := rfl
        have hcore : ‖W * W - U‖ = 1 := gmk7_cls_norm_sq_sub_nonsquare_unit hUns
        have hkey : z * z - (U : ℚ_[p]) * (x * x)
            = (x * x) * (((W * W - U : ℤ_[p]) : ℚ_[p])) := by
          rw [PadicInt.coe_sub, PadicInt.coe_mul, hWcoe, ← hxw]
          ring
        have hcoeq : ‖((W * W - U : ℤ_[p]) : ℚ_[p])‖ = 1 := by
          rw [PadicInt.padic_norm_e_of_padicInt]
          exact hcore
        have hcoene : ((W * W - U : ℤ_[p]) : ℚ_[p]) ≠ 0 := by
          intro h0
          rw [h0, norm_zero] at hcoeq
          exact zero_ne_one hcoeq
        have hcoev : ((W * W - U : ℤ_[p]) : ℚ_[p]).valuation = 0 :=
          gmk7_cls_valuation_eq_zero_of_norm_one hcoene hcoeq
        refine ⟨?_, ?_⟩
        · rw [hkey]
          exact mul_ne_zero (mul_ne_zero hx0 hx0) hcoene
        · rw [hkey, Padic.valuation_mul (mul_ne_zero hx0 hx0) hcoene,
            Padic.valuation_mul hx0 hx0, hcoev]
          exact ⟨x.valuation, by ring⟩
      · have hBA : (U : ℚ_[p]) * (x * x) - z * z ≠ 0 := by
          intro h0
          rw [sub_eq_zero] at h0
          rw [h0] at hgt
          exact lt_irrefl _ hgt
        have hneg : z * z - (U : ℚ_[p]) * (x * x)
            = -((U : ℚ_[p]) * (x * x) - z * z) := by
          ring
        refine ⟨?_, ?_⟩
        · rw [hneg]
          exact neg_ne_zero.mpr hBA
        · rw [hneg, gmk7_cls_valuation_neg hBA,
            gmk7_cls_valuation_sub_eq_left hB hA hgt, hvB]
          exact ⟨x.valuation, rfl⟩

end FLT.CampGenuineMk
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section
section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

namespace FLT
namespace CampGenuineMk

variable {p : ℕ} [Fact p.Prime]

def gmk8_cls_solvable (a b : ℚ_[p]) : Prop :=
  ∃ x y z : ℚ_[p], (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
    z * z = a * (x * x) + b * (y * y)

theorem gmk8_cls_solvable_def (a b : ℚ_[p]) :
    gmk8_cls_solvable a b ↔
      ∃ x y z : ℚ_[p], (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
        z * z = a * (x * x) + b * (y * y) := by
  have _pin := Classical.em True
  exact Iff.rfl

theorem gmk8_cls_solvable_swap {a b : ℚ_[p]} (h : gmk8_cls_solvable a b) :
    gmk8_cls_solvable b a := by
  have _pin := Classical.em True
  obtain ⟨x, y, z, hnt, heq⟩ := h
  refine ⟨y, x, z, ?_, by rw [heq]; ring⟩
  rcases hnt with h1 | h1 | h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inl h1
  · exact Or.inr (Or.inr h1)

theorem gmk8_cls_solvable_comm (a b : ℚ_[p]) :
    gmk8_cls_solvable a b ↔ gmk8_cls_solvable b a := by
  have _pin := Classical.em True
  exact ⟨gmk8_cls_solvable_swap, gmk8_cls_solvable_swap⟩

theorem gmk8_cls_solvable_scale_left {a b s : ℚ_[p]} (hs : s ≠ 0)
    (h : gmk8_cls_solvable a b) : gmk8_cls_solvable (a * (s * s)) b := by
  have _pin := Classical.em True
  obtain ⟨x, y, z, hnt, heq⟩ := h
  have hkey : a * (s * s) * (x * s⁻¹ * (x * s⁻¹)) = a * (x * x) := by
    have hss : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
    calc a * (s * s) * (x * s⁻¹ * (x * s⁻¹))
        = a * (x * x) * (s * s⁻¹ * (s * s⁻¹)) := by ring
      _ = a * (x * x) := by rw [hss, one_mul, mul_one]
  refine ⟨x * s⁻¹, y, z, ?_, ?_⟩
  · rcases hnt with hx | hyz
    · exact Or.inl (mul_ne_zero hx (inv_ne_zero hs))
    · exact Or.inr hyz
  · rw [hkey]
    exact heq

theorem gmk8_cls_solvable_iff_scale_left {a b s : ℚ_[p]} (hs : s ≠ 0) :
    gmk8_cls_solvable (a * (s * s)) b ↔ gmk8_cls_solvable a b := by
  have _pin := Classical.em True
  constructor
  · intro h
    have h2 := gmk8_cls_solvable_scale_left (inv_ne_zero hs) h
    have hval : a * (s * s) * (s⁻¹ * s⁻¹) = a := by
      have hss : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
      calc a * (s * s) * (s⁻¹ * s⁻¹) = a * (s * s⁻¹ * (s * s⁻¹)) := by ring
        _ = a := by rw [hss, one_mul, mul_one]
    rwa [hval] at h2
  · exact gmk8_cls_solvable_scale_left hs

theorem gmk8_cls_solvable_iff_scale_right {a b s : ℚ_[p]} (hs : s ≠ 0) :
    gmk8_cls_solvable a (b * (s * s)) ↔ gmk8_cls_solvable a b := by
  have _pin := Classical.em True
  rw [gmk8_cls_solvable_comm, gmk8_cls_solvable_iff_scale_left hs,
    gmk8_cls_solvable_comm]

theorem gmk8_cls_classOf_congr {x y : ℚ_[p]} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x = y) : gmk7_cls_classOf hx = gmk7_cls_classOf hy := by
  have _pin := Classical.em True
  subst h
  rfl

theorem gmk8_cls_exists_sq_ratio_of_classOf_eq (hp2 : p ≠ 2) {a b : ℚ_[p]}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (h : gmk7_cls_classOf ha = gmk7_cls_classOf hb) :
    ∃ s : ℚ_[p], s ≠ 0 ∧ b = a * (s * s) := by
  have _pin := Classical.em True
  have hc : b * a⁻¹ ≠ 0 := mul_ne_zero hb (inv_ne_zero ha)
  have hac : a * (b * a⁻¹) = b := by
    rw [mul_comm b a⁻¹, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  have h1 : gmk7_cls_classOf hb = gmk7_cls_classOf (mul_ne_zero ha hc) :=
    gmk8_cls_classOf_congr hb (mul_ne_zero ha hc) hac.symm
  rw [gmk7_cls_classOf_mul ha hc] at h1
  have h2 : gmk7_cls_classOf ha * (1 : gmk6_hil_SquareClass)
      = gmk7_cls_classOf ha * gmk7_cls_classOf hc := by
    rw [mul_one]
    exact h.trans h1
  have h3 : (1 : gmk6_hil_SquareClass) = gmk7_cls_classOf hc :=
    mul_left_cancel h2
  have hsq : IsSquare (b * a⁻¹) :=
    (gmk7_cls_classOf_eq_one_iff_isSquare hp2 hc).mp h3.symm
  obtain ⟨s, hs⟩ := hsq
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hs
    exact hc hs
  refine ⟨s, hs0, ?_⟩
  rw [← hs]
  exact hac.symm

theorem gmk8_cls_solvable_congr (hp2 : p ≠ 2) {a a' b b' : ℚ_[p]}
    (ha : a ≠ 0) (ha' : a' ≠ 0) (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hca : gmk7_cls_classOf ha = gmk7_cls_classOf ha')
    (hcb : gmk7_cls_classOf hb = gmk7_cls_classOf hb') :
    gmk8_cls_solvable a b ↔ gmk8_cls_solvable a' b' := by
  have _pin := Classical.em True
  obtain ⟨s, hs0, hsa⟩ := gmk8_cls_exists_sq_ratio_of_classOf_eq hp2 ha ha' hca
  obtain ⟨t, ht0, htb⟩ := gmk8_cls_exists_sq_ratio_of_classOf_eq hp2 hb hb' hcb
  rw [hsa, htb, gmk8_cls_solvable_iff_scale_left hs0,
    gmk8_cls_solvable_iff_scale_right ht0]

end FLT.CampGenuineMk
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section
section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

namespace FLT
namespace CampGenuineMk

variable {p : ℕ} [Fact p.Prime]

theorem gmk9_ser_unit_ne_zero {A : ℤ_[p]} (hA : ‖A‖ = 1) : A ≠ 0 := by
  have _pin := Classical.em True
  intro h0
  rw [h0, norm_zero] at hA
  exact zero_ne_one hA

theorem gmk9_ser_unit_coe_ne_zero {A : ℤ_[p]} (hA : ‖A‖ = 1) : (A : ℚ_[p]) ≠ 0 := by
  have _pin := Classical.em True
  exact PadicInt.coe_ne_zero.mpr (gmk9_ser_unit_ne_zero hA)

theorem gmk9_ser_unit_coe_valuation {A : ℤ_[p]} (hA : ‖A‖ = 1) :
    (A : ℚ_[p]).valuation = 0 := by
  have _pin := Classical.em True
  refine gmk7_cls_valuation_eq_zero_of_norm_one (gmk9_ser_unit_coe_ne_zero hA) ?_
  rw [PadicInt.padic_norm_e_of_padicInt]
  exact hA

theorem gmk9_ser_solvable_unit_unit (hp2 : p ≠ 2) {A B : ℤ_[p]}
    (hA : ‖A‖ = 1) (hB : ‖B‖ = 1) :
    gmk8_cls_solvable ((A : ℚ_[p])) ((B : ℚ_[p])) := by
  have _pin := Classical.em True
  have ha0 : PadicInt.toZMod A ≠ 0 := (gmk7_cls_norm_one_iff_toZMod_ne_zero A).mp hA
  have hb0 : PadicInt.toZMod B ≠ 0 := (gmk7_cls_norm_one_iff_toZMod_ne_zero B).mp hB
  rcases gmk9_ser_diagForm_solution_dichotomy (PadicInt.toZMod A) (PadicInt.toZMod B)
    ha0 hb0 with ⟨x0, y0, z0, hz0, heq0⟩ | ⟨x0, y0, hx0, hy0, heq0⟩
  ·
    set X : ℤ_[p] := ((x0.val : ℕ) : ℤ_[p]) with hXdef
    set Y : ℤ_[p] := ((y0.val : ℕ) : ℤ_[p]) with hYdef
    set c : ℤ_[p] := A * (X * X) + B * (Y * Y) with hcdef
    have hXres : PadicInt.toZMod X = x0 := by
      rw [hXdef, map_natCast, ZMod.natCast_val, ZMod.cast_id]
    have hYres : PadicInt.toZMod Y = y0 := by
      rw [hYdef, map_natCast, ZMod.natCast_val, ZMod.cast_id]
    have hcres : PadicInt.toZMod c = z0 * z0 := by
      simp only [hcdef, map_add, map_mul, hXres, hYres]
      exact heq0.symm
    have hcres0 : PadicInt.toZMod c ≠ 0 := by
      rw [hcres]
      exact mul_ne_zero hz0 hz0
    have hcnorm : ‖c‖ = 1 := (gmk7_cls_norm_one_iff_toZMod_ne_zero c).mpr hcres0
    have hcsq : IsSquare (PadicInt.toZMod c) := ⟨z0, hcres⟩
    obtain ⟨w, hw⟩ := gmk7_cls_unit_isSquare_of_residue hp2 hcnorm hcsq
    have hwz : w ≠ 0 := by
      intro h0
      apply hcres0
      rw [hw, h0, mul_zero, _root_.map_zero]
    refine ⟨(X : ℚ_[p]), (Y : ℚ_[p]), (w : ℚ_[p]),
      Or.inr (Or.inr (PadicInt.coe_ne_zero.mpr hwz)), ?_⟩
    calc (w : ℚ_[p]) * (w : ℚ_[p])
        = ((w * w : ℤ_[p]) : ℚ_[p]) := by rw [PadicInt.coe_mul]
      _ = ((c : ℤ_[p]) : ℚ_[p]) := by rw [hw]
      _ = (A : ℚ_[p]) * ((X : ℚ_[p]) * (X : ℚ_[p]))
            + (B : ℚ_[p]) * ((Y : ℚ_[p]) * (Y : ℚ_[p])) := by
          rw [hcdef, PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_mul,
            PadicInt.coe_mul, PadicInt.coe_mul]
  ·
    have hsqres : IsSquare (PadicInt.toZMod (-(A * B))) := by
      rw [_root_.map_neg, map_mul]
      exact gmk9_ser_neg_mul_isSquare_of_isotropic hy0 heq0
    have hABnorm : ‖(-(A * B) : ℤ_[p])‖ = 1 := by
      rw [norm_neg, norm_mul, hA, hB, mul_one]
    obtain ⟨s, hs⟩ := gmk7_cls_unit_isSquare_of_residue hp2 hABnorm hsqres
    have hzero : A * (s * s) + B * (A * A) = 0 := by
      rw [← hs]
      ring
    refine ⟨(s : ℚ_[p]), (A : ℚ_[p]), 0,
      Or.inr (Or.inl (gmk9_ser_unit_coe_ne_zero hA)), ?_⟩
    calc (0 : ℚ_[p]) * 0
        = ((A * (s * s) + B * (A * A) : ℤ_[p]) : ℚ_[p]) := by
          rw [hzero, PadicInt.coe_zero]
          ring
      _ = (A : ℚ_[p]) * ((s : ℚ_[p]) * (s : ℚ_[p]))
            + (B : ℚ_[p]) * ((A : ℚ_[p]) * (A : ℚ_[p])) := by
          rw [PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_mul,
            PadicInt.coe_mul, PadicInt.coe_mul]

theorem gmk9_ser_solvable_pV_pW_of_isSquare (hp2 : p ≠ 2) {V W : ℤ_[p]}
    (hV : ‖V‖ = 1) (hW : ‖W‖ = 1)
    (hsq : IsSquare (PadicInt.toZMod (-(V * W)))) :
    gmk8_cls_solvable ((p : ℚ_[p]) * (V : ℚ_[p])) ((p : ℚ_[p]) * (W : ℚ_[p])) := by
  have _pin := Classical.em True
  have hVWnorm : ‖(-(V * W) : ℤ_[p])‖ = 1 := by
    rw [norm_neg, norm_mul, hV, hW, mul_one]
  obtain ⟨s, hs⟩ := gmk7_cls_unit_isSquare_of_residue hp2 hVWnorm hsq
  have hzero : V * (s * s) + W * (V * V) = 0 := by
    rw [← hs]
    ring
  refine ⟨(s : ℚ_[p]), (V : ℚ_[p]), 0,
    Or.inr (Or.inl (gmk9_ser_unit_coe_ne_zero hV)), ?_⟩
  calc (0 : ℚ_[p]) * 0
      = (p : ℚ_[p]) * ((V * (s * s) + W * (V * V) : ℤ_[p]) : ℚ_[p]) := by
        rw [hzero, PadicInt.coe_zero]
        ring
    _ = (p : ℚ_[p]) * (V : ℚ_[p]) * ((s : ℚ_[p]) * (s : ℚ_[p]))
          + (p : ℚ_[p]) * (W : ℚ_[p]) * ((V : ℚ_[p]) * (V : ℚ_[p])) := by
        rw [PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_mul,
          PadicInt.coe_mul, PadicInt.coe_mul]
        ring

theorem gmk9_ser_not_solvable_nonsquare_pW (hp2 : p ≠ 2) {U W : ℤ_[p]}
    (hU : ‖U‖ = 1) (hUns : ¬IsSquare (PadicInt.toZMod U)) (hW : ‖W‖ = 1) :
    ¬gmk8_cls_solvable ((U : ℚ_[p])) ((p : ℚ_[p]) * (W : ℚ_[p])) := by
  have _pin := Classical.em True
  rintro ⟨x, y, z, hnt, heq⟩
  have hWq : (W : ℚ_[p]) ≠ 0 := gmk9_ser_unit_coe_ne_zero hW
  have hpW : (p : ℚ_[p]) * (W : ℚ_[p]) ≠ 0 :=
    mul_ne_zero gmk7_cls_p_padic_ne_zero hWq
  have hxz : ¬(x = 0 ∧ z = 0) := by
    rintro ⟨rfl, rfl⟩
    simp only [mul_zero, zero_add] at heq
    have hy : y = 0 := by
      rcases mul_eq_zero.mp heq.symm with hc | hc
      · exact absurd hc hpW
      · exact mul_self_eq_zero.mp hc
    subst hy
    rcases hnt with hc | hc | hc <;> exact hc rfl
  obtain ⟨hne, hdvd⟩ := gmk7_cls_sq_sub_nonsquare_unit_valuation hp2 hU hUns x z hxz
  have hsub : z * z - (U : ℚ_[p]) * (x * x) = (p : ℚ_[p]) * (W : ℚ_[p]) * (y * y) := by
    rw [heq]
    ring
  rw [hsub] at hne hdvd
  have hy0 : y ≠ 0 := by
    intro h0
    apply hne
    rw [h0]
    ring
  have hval : ((p : ℚ_[p]) * (W : ℚ_[p]) * (y * y)).valuation
      = 1 + (y.valuation + y.valuation) := by
    rw [Padic.valuation_mul (mul_ne_zero gmk7_cls_p_padic_ne_zero hWq)
        (mul_ne_zero hy0 hy0),
      Padic.valuation_mul gmk7_cls_p_padic_ne_zero hWq, Padic.valuation_p,
      gmk9_ser_unit_coe_valuation hW, Padic.valuation_mul hy0 hy0]
    ring
  rw [hval] at hdvd
  obtain ⟨c, hc⟩ := hdvd
  omega

theorem gmk9_ser_not_solvable_pV_pW_of_nonsquare (hp2 : p ≠ 2) {V W : ℤ_[p]}
    (hV : ‖V‖ = 1) (hW : ‖W‖ = 1)
    (hns : ¬IsSquare (PadicInt.toZMod (-(V * W)))) :
    ¬gmk8_cls_solvable ((p : ℚ_[p]) * (V : ℚ_[p])) ((p : ℚ_[p]) * (W : ℚ_[p])) := by
  have _pin := Classical.em True
  rintro ⟨x, y, z, hnt, heq⟩
  have hVq : (V : ℚ_[p]) ≠ 0 := gmk9_ser_unit_coe_ne_zero hV
  have hVWnorm : ‖(-(V * W) : ℤ_[p])‖ = 1 := by
    rw [norm_neg, norm_mul, hV, hW, mul_one]
  have hxy : ¬(y = 0 ∧ (V : ℚ_[p]) * x = 0) := by
    rintro ⟨rfl, hVx⟩
    have hx0 : x = 0 := (mul_eq_zero.mp hVx).resolve_left hVq
    subst hx0
    have hz0 : z = 0 := by
      have h0 : z * z = 0 := by
        rw [heq]
        ring
      exact mul_self_eq_zero.mp h0
    subst hz0
    rcases hnt with hc | hc | hc <;> exact hc rfl
  obtain ⟨hSne, hSdvd⟩ := gmk7_cls_sq_sub_nonsquare_unit_valuation hp2 hVWnorm hns
    y ((V : ℚ_[p]) * x) hxy
  have hcoe : ((-(V * W) : ℤ_[p]) : ℚ_[p]) = -((V : ℚ_[p]) * (W : ℚ_[p])) := by
    rw [PadicInt.coe_neg, PadicInt.coe_mul]
  have hkey : (V : ℚ_[p]) * (z * z)
      = (p : ℚ_[p]) * ((V : ℚ_[p]) * x * ((V : ℚ_[p]) * x)
          - ((-(V * W) : ℤ_[p]) : ℚ_[p]) * (y * y)) := by
    rw [hcoe, heq]
    ring
  have hz0 : z ≠ 0 := by
    intro h0
    apply hSne
    have h1 : (p : ℚ_[p]) * ((V : ℚ_[p]) * x * ((V : ℚ_[p]) * x)
        - ((-(V * W) : ℤ_[p]) : ℚ_[p]) * (y * y)) = 0 := by
      rw [← hkey, h0]
      ring
    exact (mul_eq_zero.mp h1).resolve_left gmk7_cls_p_padic_ne_zero
  have h1 : ((V : ℚ_[p]) * (z * z)).valuation = z.valuation + z.valuation := by
    rw [Padic.valuation_mul hVq (mul_ne_zero hz0 hz0),
      gmk9_ser_unit_coe_valuation hV, Padic.valuation_mul hz0 hz0]
    ring
  have h2 : ((p : ℚ_[p]) * ((V : ℚ_[p]) * x * ((V : ℚ_[p]) * x)
      - ((-(V * W) : ℤ_[p]) : ℚ_[p]) * (y * y))).valuation
      = 1 + ((V : ℚ_[p]) * x * ((V : ℚ_[p]) * x)
          - ((-(V * W) : ℤ_[p]) : ℚ_[p]) * (y * y)).valuation := by
    rw [Padic.valuation_mul gmk7_cls_p_padic_ne_zero hSne, Padic.valuation_p]
  have h3 : z.valuation + z.valuation
      = 1 + ((V : ℚ_[p]) * x * ((V : ℚ_[p]) * x)
          - ((-(V * W) : ℤ_[p]) : ℚ_[p]) * (y * y)).valuation := by
    rw [← h1, hkey, h2]
  obtain ⟨c, hc⟩ := hSdvd
  omega

end FLT.CampGenuineMk
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section
section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

namespace FLT
namespace CampGenuineMk

variable {p : ℕ} [Fact p.Prime]

theorem gmk9_ser_mod_four (hp2 : p ≠ 2) : p % 4 = 1 ∨ p % 4 = 3 := by
  have _pin := Classical.em True
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  obtain ⟨k, hk⟩ := hodd
  omega

theorem gmk9_ser_epsSign_one (hp4 : p % 4 = 1) : gmk6_hil_epsSign p = 1 := by
  have _pin := Classical.em True
  unfold gmk6_hil_epsSign
  rw [if_pos hp4]

theorem gmk9_ser_epsSign_neg_one (hp4 : p % 4 = 3) : gmk6_hil_epsSign p = -1 := by
  have _pin := Classical.em True
  unfold gmk6_hil_epsSign
  rw [if_neg (by omega)]

noncomputable def gmk9_ser_rep (n : ℕ) (c : gmk6_hil_SquareClass) : ℚ_[p] :=
  if c.valParity = 0 then (if c.unitSign = 1 then 1 else (n : ℚ_[p]))
  else (if c.unitSign = 1 then (p : ℚ_[p]) else (p : ℚ_[p]) * (n : ℚ_[p]))

theorem gmk9_ser_rep_unit (n : ℕ) : gmk9_ser_rep (p := p) n ⟨0, 1⟩ = 1 := by
  have _pin := Classical.em True
  unfold gmk9_ser_rep
  rw [if_pos (show ((⟨0, 1⟩ : gmk6_hil_SquareClass).valParity = 0) from rfl),
    if_pos (show ((⟨0, 1⟩ : gmk6_hil_SquareClass).unitSign = 1) from rfl)]

theorem gmk9_ser_rep_nonres (n : ℕ) :
    gmk9_ser_rep (p := p) n ⟨0, -1⟩ = (n : ℚ_[p]) := by
  have _pin := Classical.em True
  unfold gmk9_ser_rep
  rw [if_pos (show ((⟨0, -1⟩ : gmk6_hil_SquareClass).valParity = 0) from rfl),
    if_neg (show ¬((⟨0, -1⟩ : gmk6_hil_SquareClass).unitSign = 1) by decide)]

theorem gmk9_ser_rep_unif (n : ℕ) :
    gmk9_ser_rep (p := p) n ⟨1, 1⟩ = (p : ℚ_[p]) := by
  have _pin := Classical.em True
  unfold gmk9_ser_rep
  rw [if_neg (show ¬((⟨1, 1⟩ : gmk6_hil_SquareClass).valParity = 0) by decide),
    if_pos (show ((⟨1, 1⟩ : gmk6_hil_SquareClass).unitSign = 1) from rfl)]

theorem gmk9_ser_rep_unifNonres (n : ℕ) :
    gmk9_ser_rep (p := p) n ⟨1, -1⟩ = (p : ℚ_[p]) * (n : ℚ_[p]) := by
  have _pin := Classical.em True
  unfold gmk9_ser_rep
  rw [if_neg (show ¬((⟨1, -1⟩ : gmk6_hil_SquareClass).valParity = 0) by decide),
    if_neg (show ¬((⟨1, -1⟩ : gmk6_hil_SquareClass).unitSign = 1) by decide)]

theorem gmk9_ser_rep_ne_zero {n : ℕ} (hn : (n : ZMod p) ≠ 0)
    (c : gmk6_hil_SquareClass) : gmk9_ser_rep (p := p) n c ≠ 0 := by
  have _pin := Classical.em True
  obtain ⟨av, sv⟩ := c
  have hZ2 : ∀ w : ZMod 2, w = 0 ∨ w = 1 := by decide
  rcases hZ2 av with rfl | rfl <;> rcases Int.units_eq_one_or sv with rfl | rfl
  · rw [gmk9_ser_rep_unit]
    exact one_ne_zero
  · rw [gmk9_ser_rep_nonres]
    exact gmk7_cls_natCast_ne_zero hn
  · rw [gmk9_ser_rep_unif]
    exact gmk7_cls_p_padic_ne_zero
  · rw [gmk9_ser_rep_unifNonres]
    exact mul_ne_zero gmk7_cls_p_padic_ne_zero (gmk7_cls_natCast_ne_zero hn)

theorem gmk9_ser_classOf_rep (hp2 : p ≠ 2) {n : ℕ} (hn : (n : ZMod p) ≠ 0)
    (hns : ¬IsSquare ((n : ZMod p))) (c : gmk6_hil_SquareClass) :
    gmk7_cls_classOf (gmk9_ser_rep_ne_zero hn c) = c := by
  have _pin := Classical.em True
  have hq : quadraticChar (ZMod p) ((n : ZMod p)) = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr hns
  obtain ⟨av, sv⟩ := c
  have hZ2 : ∀ w : ZMod 2, w = 0 ∨ w = 1 := by decide
  rcases hZ2 av with rfl | rfl <;> rcases Int.units_eq_one_or sv with rfl | rfl
  ·
    rw [gmk8_cls_classOf_congr (gmk9_ser_rep_ne_zero hn ⟨0, 1⟩)
        (one_ne_zero : (1 : ℚ_[p]) ≠ 0) (gmk9_ser_rep_unit n),
      gmk7_cls_classOf_one]
    exact gmk6_hil_SquareClass_ext (by decide) (by decide)
  ·
    rw [gmk8_cls_classOf_congr (gmk9_ser_rep_ne_zero hn ⟨0, -1⟩)
        (gmk7_cls_natCast_ne_zero hn) (gmk9_ser_rep_nonres n),
      gmk7_cls_classOf_natCast hn, hq,
      if_neg (by decide : ¬((-1 : ℤ) = 1))]
    exact gmk6_hil_SquareClass_ext (by decide) (by decide)
  ·
    rw [gmk8_cls_classOf_congr (gmk9_ser_rep_ne_zero hn ⟨1, 1⟩)
        (gmk7_cls_p_padic_ne_zero (p := p)) (gmk9_ser_rep_unif n),
      gmk7_cls_classOf_p]
    exact gmk6_hil_SquareClass_ext (by decide) (by decide)
  ·
    rw [gmk8_cls_classOf_congr (gmk9_ser_rep_ne_zero hn ⟨1, -1⟩)
        (mul_ne_zero (gmk7_cls_p_padic_ne_zero (p := p))
          (gmk7_cls_natCast_ne_zero hn)) (gmk9_ser_rep_unifNonres n),
      gmk7_cls_classOf_mul (gmk7_cls_p_padic_ne_zero (p := p))
        (gmk7_cls_natCast_ne_zero hn),
      gmk7_cls_classOf_p, gmk7_cls_classOf_natCast hn, hq,
      if_neg (by decide : ¬((-1 : ℤ) = 1))]
    exact gmk6_hil_SquareClass_ext (by decide) (by decide)

theorem gmk9_ser_solvability_table (hp2 : p ≠ 2) {n : ℕ}
    (hn : (n : ZMod p) ≠ 0) (hns : ¬IsSquare ((n : ZMod p)))
    (c₁ c₂ : gmk6_hil_SquareClass) :
    gmk8_cls_solvable (gmk9_ser_rep (p := p) n c₁) (gmk9_ser_rep (p := p) n c₂)
      ↔ gmk6_hil_pair (gmk6_hil_epsSign p) c₁ c₂ = 1 := by
  have _pin := Classical.em True
  have hnormn : ‖((n : ℤ_[p]))‖ = 1 := gmk7_cls_norm_natCast_eq_one hn
  have hresn : ¬IsSquare (PadicInt.toZMod ((n : ℤ_[p]))) := by
    rw [map_natCast]
    exact hns
  obtain ⟨a₁, s₁⟩ := c₁
  obtain ⟨a₂, s₂⟩ := c₂
  have hZ2 : ∀ w : ZMod 2, w = 0 ∨ w = 1 := by decide
  rcases hZ2 a₁ with rfl | rfl <;> rcases Int.units_eq_one_or s₁ with rfl | rfl <;>
    rcases hZ2 a₂ with rfl | rfl <;> rcases Int.units_eq_one_or s₂ with rfl | rfl
  ·
    rw [gmk9_ser_rep_unit]
    exact iff_of_true ⟨1, 0, 1, Or.inl one_ne_zero, by ring⟩
      (by rcases Int.units_eq_one_or (gmk6_hil_epsSign p) with he | he <;>
        rw [he] <;> decide)
  ·
    rw [gmk9_ser_rep_unit, gmk9_ser_rep_nonres]
    exact iff_of_true ⟨1, 0, 1, Or.inl one_ne_zero, by ring⟩
      (by rcases Int.units_eq_one_or (gmk6_hil_epsSign p) with he | he <;>
        rw [he] <;> decide)
  ·
    rw [gmk9_ser_rep_unit, gmk9_ser_rep_unif]
    exact iff_of_true ⟨1, 0, 1, Or.inl one_ne_zero, by ring⟩
      (by rcases Int.units_eq_one_or (gmk6_hil_epsSign p) with he | he <;>
        rw [he] <;> decide)
  ·
    rw [gmk9_ser_rep_unit, gmk9_ser_rep_unifNonres]
    exact iff_of_true ⟨1, 0, 1, Or.inl one_ne_zero, by ring⟩
      (by rcases Int.units_eq_one_or (gmk6_hil_epsSign p) with he | he <;>
        rw [he] <;> decide)
  ·
    rw [gmk9_ser_rep_nonres, gmk9_ser_rep_unit]
    exact iff_of_true ⟨0, 1, 1, Or.inr (Or.inl one_ne_zero), by ring⟩
      (by rcases Int.units_eq_one_or (gmk6_hil_epsSign p) with he | he <;>
        rw [he] <;> decide)
  ·
    rw [gmk9_ser_rep_nonres]
    refine iff_of_true ?_
      (by rcases Int.units_eq_one_or (gmk6_hil_epsSign p) with he | he <;>
        rw [he] <;> decide)
    have h := gmk9_ser_solvable_unit_unit hp2 hnormn hnormn
    rwa [PadicInt.coe_natCast] at h
  ·
    rw [gmk9_ser_rep_nonres, gmk9_ser_rep_unif]
    refine iff_of_false ?_
      (by rcases Int.units_eq_one_or (gmk6_hil_epsSign p) with he | he <;>
        rw [he] <;> decide)
    have h := gmk9_ser_not_solvable_nonsquare_pW hp2 hnormn hresn norm_one
    rwa [PadicInt.coe_natCast, PadicInt.coe_one, mul_one] at h
  ·
    rw [gmk9_ser_rep_nonres, gmk9_ser_rep_unifNonres]
    refine iff_of_false ?_
      (by rcases Int.units_eq_one_or (gmk6_hil_epsSign p) with he | he <;>
        rw [he] <;> decide)
    have h := gmk9_ser_not_solvable_nonsquare_pW hp2 hnormn hresn hnormn
    rwa [PadicInt.coe_natCast] at h
  ·
    rw [gmk9_ser_rep_unif, gmk9_ser_rep_unit]
    exact iff_of_true ⟨0, 1, 1, Or.inr (Or.inl one_ne_zero), by ring⟩
      (by rcases Int.units_eq_one_or (gmk6_hil_epsSign p) with he | he <;>
        rw [he] <;> decide)
  ·
    rw [gmk9_ser_rep_unif, gmk9_ser_rep_nonres]
    refine iff_of_false ?_
      (by rcases Int.units_eq_one_or (gmk6_hil_epsSign p) with he | he <;>
        rw [he] <;> decide)
    intro hsol
    have h := gmk9_ser_not_solvable_nonsquare_pW hp2 hnormn hresn norm_one
    rw [PadicInt.coe_natCast, PadicInt.coe_one, mul_one] at h
    exact h (gmk8_cls_solvable_swap hsol)
  ·
    rw [gmk9_ser_rep_unif]
    rcases gmk9_ser_mod_four hp2 with hp4 | hp4
    · refine iff_of_true ?_ (by rw [gmk9_ser_epsSign_one hp4]; decide)
      have hsq : IsSquare (PadicInt.toZMod (-((1 : ℤ_[p]) * 1))) := by
        rw [mul_one, _root_.map_neg, map_one]
        exact ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
      have h := gmk9_ser_solvable_pV_pW_of_isSquare hp2 norm_one norm_one hsq
      rwa [PadicInt.coe_one, mul_one] at h
    · refine iff_of_false ?_ (by rw [gmk9_ser_epsSign_neg_one hp4]; decide)
      have hnsq : ¬IsSquare (PadicInt.toZMod (-((1 : ℤ_[p]) * 1))) := by
        rw [mul_one, _root_.map_neg, map_one]
        intro hcon
        exact (ZMod.exists_sq_eq_neg_one_iff.mp hcon) hp4
      have h := gmk9_ser_not_solvable_pV_pW_of_nonsquare hp2 norm_one norm_one hnsq
      rwa [PadicInt.coe_one, mul_one] at h
  ·
    rw [gmk9_ser_rep_unif, gmk9_ser_rep_unifNonres]
    rcases gmk9_ser_mod_four hp2 with hp4 | hp4
    · refine iff_of_false ?_ (by rw [gmk9_ser_epsSign_one hp4]; decide)
      have hnsq : ¬IsSquare (PadicInt.toZMod (-((1 : ℤ_[p]) * (n : ℤ_[p])))) := by
        rw [one_mul, _root_.map_neg, map_natCast]
        exact gmk9_ser_not_isSquare_neg_of_square_nonsquare
          (ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)) hns
      have h := gmk9_ser_not_solvable_pV_pW_of_nonsquare hp2 norm_one hnormn hnsq
      rwa [PadicInt.coe_one, mul_one, PadicInt.coe_natCast] at h
    · refine iff_of_true ?_ (by rw [gmk9_ser_epsSign_neg_one hp4]; decide)
      have hsq : IsSquare (PadicInt.toZMod (-((1 : ℤ_[p]) * (n : ℤ_[p])))) := by
        rw [one_mul, _root_.map_neg, map_natCast]
        exact gmk9_ser_isSquare_neg_of_two_nonsquares
          (fun hcon => (ZMod.exists_sq_eq_neg_one_iff.mp hcon) hp4) hns hn
      have h := gmk9_ser_solvable_pV_pW_of_isSquare hp2 norm_one hnormn hsq
      rwa [PadicInt.coe_one, mul_one, PadicInt.coe_natCast] at h
  ·
    rw [gmk9_ser_rep_unifNonres, gmk9_ser_rep_unit]
    exact iff_of_true ⟨0, 1, 1, Or.inr (Or.inl one_ne_zero), by ring⟩
      (by rcases Int.units_eq_one_or (gmk6_hil_epsSign p) with he | he <;>
        rw [he] <;> decide)
  ·
    rw [gmk9_ser_rep_unifNonres, gmk9_ser_rep_nonres]
    refine iff_of_false ?_
      (by rcases Int.units_eq_one_or (gmk6_hil_epsSign p) with he | he <;>
        rw [he] <;> decide)
    intro hsol
    have h := gmk9_ser_not_solvable_nonsquare_pW hp2 hnormn hresn hnormn
    rw [PadicInt.coe_natCast] at h
    exact h (gmk8_cls_solvable_swap hsol)
  ·
    rw [gmk9_ser_rep_unifNonres, gmk9_ser_rep_unif]
    rcases gmk9_ser_mod_four hp2 with hp4 | hp4
    · refine iff_of_false ?_ (by rw [gmk9_ser_epsSign_one hp4]; decide)
      intro hsol
      have hnsq : ¬IsSquare (PadicInt.toZMod (-((1 : ℤ_[p]) * (n : ℤ_[p])))) := by
        rw [one_mul, _root_.map_neg, map_natCast]
        exact gmk9_ser_not_isSquare_neg_of_square_nonsquare
          (ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)) hns
      have h := gmk9_ser_not_solvable_pV_pW_of_nonsquare hp2 norm_one hnormn hnsq
      rw [PadicInt.coe_one, mul_one, PadicInt.coe_natCast] at h
      exact h (gmk8_cls_solvable_swap hsol)
    · refine iff_of_true ?_ (by rw [gmk9_ser_epsSign_neg_one hp4]; decide)
      have hsq : IsSquare (PadicInt.toZMod (-((1 : ℤ_[p]) * (n : ℤ_[p])))) := by
        rw [one_mul, _root_.map_neg, map_natCast]
        exact gmk9_ser_isSquare_neg_of_two_nonsquares
          (fun hcon => (ZMod.exists_sq_eq_neg_one_iff.mp hcon) hp4) hns hn
      have h := gmk9_ser_solvable_pV_pW_of_isSquare hp2 norm_one hnormn hsq
      rw [PadicInt.coe_one, mul_one, PadicInt.coe_natCast] at h
      exact gmk8_cls_solvable_swap h
  ·
    rw [gmk9_ser_rep_unifNonres]
    rcases gmk9_ser_mod_four hp2 with hp4 | hp4
    · refine iff_of_true ?_ (by rw [gmk9_ser_epsSign_one hp4]; decide)
      have hsq : IsSquare (PadicInt.toZMod (-((n : ℤ_[p]) * (n : ℤ_[p])))) := by
        rw [_root_.map_neg, map_mul, map_natCast]
        exact (gmk9_ser_isSquare_neg_mul_self_iff hn).mpr
          (ZMod.exists_sq_eq_neg_one_iff.mpr (by omega))
      have h := gmk9_ser_solvable_pV_pW_of_isSquare hp2 hnormn hnormn hsq
      rwa [PadicInt.coe_natCast] at h
    · refine iff_of_false ?_ (by rw [gmk9_ser_epsSign_neg_one hp4]; decide)
      have hnsq : ¬IsSquare (PadicInt.toZMod (-((n : ℤ_[p]) * (n : ℤ_[p])))) := by
        rw [_root_.map_neg, map_mul, map_natCast]
        intro hcon
        exact (ZMod.exists_sq_eq_neg_one_iff.mp
          ((gmk9_ser_isSquare_neg_mul_self_iff hn).mp hcon)) hp4
      have h := gmk9_ser_not_solvable_pV_pW_of_nonsquare hp2 hnormn hnormn hnsq
      rwa [PadicInt.coe_natCast] at h

theorem gmk9_ser_solvability_pair (hp2 : p ≠ 2) {a b : ℚ_[p]}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    gmk8_cls_solvable a b ↔
      gmk6_hil_pair (gmk6_hil_epsSign p) (gmk7_cls_classOf ha)
        (gmk7_cls_classOf hb) = 1 := by
  have _pin := Classical.em True
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  obtain ⟨u0, hu0⟩ := FiniteField.exists_nonsquare (F := ZMod p) hchar
  have hu00 : u0 ≠ 0 := by
    rintro rfl
    exact hu0 ⟨0, (mul_zero 0).symm⟩
  have hn : ((u0.val : ℕ) : ZMod p) ≠ 0 := by
    rw [ZMod.natCast_val, ZMod.cast_id]
    exact hu00
  have hns : ¬IsSquare (((u0.val : ℕ) : ZMod p)) := by
    rw [ZMod.natCast_val, ZMod.cast_id]
    exact hu0
  have h1 : gmk8_cls_solvable a b ↔
      gmk8_cls_solvable (gmk9_ser_rep (p := p) u0.val (gmk7_cls_classOf ha))
        (gmk9_ser_rep (p := p) u0.val (gmk7_cls_classOf hb)) :=
    gmk8_cls_solvable_congr hp2 ha
      (gmk9_ser_rep_ne_zero hn (gmk7_cls_classOf ha)) hb
      (gmk9_ser_rep_ne_zero hn (gmk7_cls_classOf hb))
      (gmk9_ser_classOf_rep hp2 hn hns (gmk7_cls_classOf ha)).symm
      (gmk9_ser_classOf_rep hp2 hn hns (gmk7_cls_classOf hb)).symm
  exact h1.trans
    (gmk9_ser_solvability_table hp2 hn hns (gmk7_cls_classOf ha)
      (gmk7_cls_classOf hb))

end FLT.CampGenuineMk
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section
section

set_option linter.dupNamespace false
set_option maxHeartbeats 1600000

noncomputable section

namespace FLT
namespace JpssD4KubotaPTwoHilbertTable

def jpd4r14t3_epsZ (u : ℤ) : ZMod 2 := (((u - 1) / 2 : ℤ) : ZMod 2)

def jpd4r14t3_omegaZ (u : ℤ) : ZMod 2 := (((u ^ 2 - 1) / 8 : ℤ) : ZMod 2)

def jpd4r14t3_pairTwoZ (alpha : ZMod 2) (u : ℤ) (beta : ZMod 2) (v : ℤ) : ℤˣ :=
  (-1) ^ (jpd4r14t3_epsZ u * jpd4r14t3_epsZ v
      + alpha * jpd4r14t3_omegaZ v + beta * jpd4r14t3_omegaZ u).val

theorem jpd4r14t3_repCoherence :
    jpd4r14t3_epsZ 9 = jpd4r14t3_epsZ 1
      ∧ jpd4r14t3_epsZ (-1) = jpd4r14t3_epsZ 7
      ∧ jpd4r14t3_epsZ (-5) = jpd4r14t3_epsZ 3
      ∧ jpd4r14t3_epsZ 11 = jpd4r14t3_epsZ 3
      ∧ jpd4r14t3_omegaZ 9 = jpd4r14t3_omegaZ 1
      ∧ jpd4r14t3_omegaZ (-1) = jpd4r14t3_omegaZ 7
      ∧ jpd4r14t3_omegaZ (-5) = jpd4r14t3_omegaZ 3
      ∧ jpd4r14t3_omegaZ 11 = jpd4r14t3_omegaZ 3
      ∧ jpd4r14t3_epsZ (-1) = 1 ∧ jpd4r14t3_omegaZ (-1) = 0 := by
  have _pin := Classical.em True
  decide +kernel

end FLT.JpssD4KubotaPTwoHilbertTable
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"
end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section
section

set_option linter.dupNamespace false
set_option maxHeartbeats 1600000

noncomputable section

namespace FLT
namespace JpssD4KubotaPTwoHilbertSolvabilityIdentification

open FLT.JpssD4KubotaPTwoHilbertTable

def jpd4r15t3_hilbertSolvable (a b : ℚ_[2]) : Prop :=
  ∃ z x y : ℚ_[2], ¬(z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0

theorem jpd4r15t3_solvableOfWitness (a b z x y : ℚ_[2])
    (h1 : z = 1 ∨ x = 1 ∨ y = 1) (heq : z ^ 2 = a * x ^ 2 + b * y ^ 2) :
    jpd4r15t3_hilbertSolvable a b := by
  have _pin := Classical.em True
  refine ⟨z, x, y, ?_, by linear_combination heq⟩
  rintro ⟨rfl, rfl, rfl⟩
  rcases h1 with h | h | h <;> exact one_ne_zero h.symm

theorem jpd4r15t3_divNormLeOne {c t : ℚ_[2]} (hc : c ≠ 0) (ht : ‖t‖ ≤ ‖c‖) :
    ‖t / c‖ ≤ 1 := by
  have _pin := Classical.em True
  rw [norm_div]
  exact (div_le_one (norm_pos_iff.mpr hc)).mpr ht

theorem jpd4r15t3_scaledEq {a b z x y : ℚ_[2]} (c : ℚ_[2])
    (heq : z ^ 2 = a * x ^ 2 + b * y ^ 2) :
    (z / c) ^ 2 = a * (x / c) ^ 2 + b * (y / c) ^ 2 := by
  have _pin := Classical.em True
  rw [div_pow, div_pow, div_pow, heq]
  ring

theorem jpd4r15t3_descent (a b : ℚ_[2]) (h : jpd4r15t3_hilbertSolvable a b) :
    ∃ z x y : ℚ_[2], (z = 1 ∨ x = 1 ∨ y = 1) ∧ ‖z‖ ≤ 1 ∧ ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1 ∧
      z ^ 2 = a * x ^ 2 + b * y ^ 2 := by
  have _pin := Classical.em True
  obtain ⟨z, x, y, hne, heq0⟩ := h
  have heq : z ^ 2 = a * x ^ 2 + b * y ^ 2 := by linear_combination heq0
  rcases le_total ‖z‖ ‖x‖ with h1 | h1
  · rcases le_total ‖x‖ ‖y‖ with h2 | h2
    · have hy : y ≠ 0 := by
        rintro rfl
        rw [norm_zero] at h2
        exact hne ⟨norm_le_zero_iff.mp (h1.trans h2), norm_le_zero_iff.mp h2, rfl⟩
      exact ⟨z / y, x / y, y / y, Or.inr (Or.inr (div_self hy)),
        jpd4r15t3_divNormLeOne hy (h1.trans h2), jpd4r15t3_divNormLeOne hy h2,
        jpd4r15t3_divNormLeOne hy le_rfl, jpd4r15t3_scaledEq y heq⟩
    · have hx : x ≠ 0 := by
        rintro rfl
        rw [norm_zero] at h1 h2
        exact hne ⟨norm_le_zero_iff.mp h1, rfl, norm_le_zero_iff.mp h2⟩
      exact ⟨z / x, x / x, y / x, Or.inr (Or.inl (div_self hx)),
        jpd4r15t3_divNormLeOne hx h1, jpd4r15t3_divNormLeOne hx le_rfl,
        jpd4r15t3_divNormLeOne hx h2, jpd4r15t3_scaledEq x heq⟩
  · rcases le_total ‖z‖ ‖y‖ with h2 | h2
    · have hy : y ≠ 0 := by
        rintro rfl
        rw [norm_zero] at h2
        exact hne ⟨norm_le_zero_iff.mp h2, norm_le_zero_iff.mp (h1.trans h2), rfl⟩
      exact ⟨z / y, x / y, y / y, Or.inr (Or.inr (div_self hy)),
        jpd4r15t3_divNormLeOne hy h2, jpd4r15t3_divNormLeOne hy (h1.trans h2),
        jpd4r15t3_divNormLeOne hy le_rfl, jpd4r15t3_scaledEq y heq⟩
    · have hz : z ≠ 0 := by
        rintro rfl
        rw [norm_zero] at h1 h2
        exact hne ⟨rfl, norm_le_zero_iff.mp h1, norm_le_zero_iff.mp h2⟩
      exact ⟨z / z, x / z, y / z, Or.inl (div_self hz),
        jpd4r15t3_divNormLeOne hz le_rfl, jpd4r15t3_divNormLeOne hz h1,
        jpd4r15t3_divNormLeOne hz h2, jpd4r15t3_scaledEq z heq⟩

def jpd4r15t3_redMod (m k : ℕ) (h : m ∣ 2 ^ k) : ℤ_[2] →+* ZMod m :=
  (ZMod.castHom h (ZMod m)).comp (PadicInt.toZModPow k)

theorem jpd4r15t3_insolvabilityEngine {M : Type} [CommRing M]
    (φ : ℤ_[2] →+* M) (a b : ℤ)
    (hone : ¬ ∃ t : M, (1 : M) = 2 * t)
    (hobs : ∀ z x y : M, z ^ 2 = (a : M) * x ^ 2 + (b : M) * y ^ 2 →
      ((∃ t, z = 2 * t) ∧ (∃ t, x = 2 * t) ∧ (∃ t, y = 2 * t))) :
    ¬ jpd4r15t3_hilbertSolvable (a : ℚ_[2]) (b : ℚ_[2]) := by
  have _pin := Classical.em True
  intro hsol
  obtain ⟨z, x, y, h1, hz1, hx1, hy1, heq⟩ := jpd4r15t3_descent _ _ hsol
  obtain ⟨Z, hZ⟩ : ∃ Z : ℤ_[2], (Z : ℚ_[2]) = z := ⟨⟨z, hz1⟩, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : ℤ_[2], (X : ℚ_[2]) = x := ⟨⟨x, hx1⟩, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℤ_[2], (Y : ℚ_[2]) = y := ⟨⟨y, hy1⟩, rfl⟩
  have hZeq : Z ^ 2 = (a : ℤ_[2]) * X ^ 2 + (b : ℤ_[2]) * Y ^ 2 := by
    apply PadicInt.ext
    push_cast
    rw [hZ, hX, hY]
    exact heq
  have hmod : (φ Z) ^ 2 = (a : M) * (φ X) ^ 2 + (b : M) * (φ Y) ^ 2 := by
    have h0 := congrArg φ hZeq
    simpa only [map_pow, map_add, map_mul, map_intCast] using h0
  obtain ⟨hdz, hdx, hdy⟩ := hobs _ _ _ hmod
  rcases h1 with h | h | h
  · obtain ⟨t, ht⟩ := hdz
    refine hone ⟨t, ?_⟩
    rw [← ht, show Z = 1 from PadicInt.ext (by rw [hZ, h]; simp), map_one]
  · obtain ⟨t, ht⟩ := hdx
    refine hone ⟨t, ?_⟩
    rw [← ht, show X = 1 from PadicInt.ext (by rw [hX, h]; simp), map_one]
  · obtain ⟨t, ht⟩ := hdy
    refine hone ⟨t, ?_⟩
    rw [← ht, show Y = 1 from PadicInt.ext (by rw [hY, h]; simp), map_one]

theorem jpd4r15t3_oneOddPack :
    (¬ ∃ t : ZMod 4, (1 : ZMod 4) = 2 * t) ∧ (¬ ∃ t : ZMod 8, (1 : ZMod 8) = 2 * t)
      ∧ (¬ ∃ t : ZMod 16, (1 : ZMod 16) = 2 * t) := by
  have _pin := Classical.em True
  decide +kernel

theorem jpd4r15t3_sqrtOfOneModEight (m : ℤ) (hm : (2 : ℤ) ^ 3 ∣ 1 - m) :
    ∃ s : ℚ_[2], s ^ 2 = (m : ℚ_[2]) := by
  have _pin := Classical.em True
  have heval1 : (Polynomial.X ^ 2 - Polynomial.C (m : ℤ_[2])).aeval (1 : ℤ_[2])
      = ((1 - m : ℤ) : ℤ_[2]) := by
    simp
  have hderiv : (Polynomial.X ^ 2
      - Polynomial.C (m : ℤ_[2])).derivative.aeval (1 : ℤ_[2]) = (2 : ℤ_[2]) := by
    simp
    norm_num
  have h8 := (PadicInt.norm_int_le_pow_iff_dvd (p := 2) (k := 1 - m) (n := 3)).mpr
    (by exact_mod_cast hm)
  have h2norm : ‖(2 : ℤ_[2])‖ = (2 : ℝ)⁻¹ := by
    simpa using PadicInt.norm_p (p := 2)
  have hlt : ‖(Polynomial.X ^ 2 - Polynomial.C (m : ℤ_[2])).aeval (1 : ℤ_[2])‖
      < ‖(Polynomial.X ^ 2
          - Polynomial.C (m : ℤ_[2])).derivative.aeval (1 : ℤ_[2])‖ ^ 2 := by
    rw [heval1, hderiv, h2norm]
    refine lt_of_le_of_lt h8 ?_
    norm_num
  obtain ⟨s, hs, -, -, -⟩ := hensels_lemma hlt
  have hs2 : s ^ 2 = (m : ℤ_[2]) := by
    have h0 := hs
    simp [sub_eq_zero] at h0
    exact h0
  refine ⟨(s : ℚ_[2]), ?_⟩
  have h3 : ((s ^ 2 : ℤ_[2]) : ℚ_[2]) = ((m : ℤ_[2]) : ℚ_[2]) := by
    rw [hs2]
  push_cast at h3
  exact h3

theorem jpd4r15t3_sqrtNeg7 : ∃ s : ℚ_[2], s ^ 2 = (-7 : ℚ_[2]) := by
  have _pin := Classical.em True
  have h := jpd4r15t3_sqrtOfOneModEight (-7) (by norm_num)
  push_cast at h
  exact h

theorem jpd4r15t3_sqrtNeg15 : ∃ s : ℚ_[2], s ^ 2 = (-15 : ℚ_[2]) := by
  have _pin := Classical.em True
  have h := jpd4r15t3_sqrtOfOneModEight (-15) (by norm_num)
  push_cast at h
  exact h

theorem jpd4r15t3_neOne_of_eqNegOne {u : ℤˣ} (h : u = -1) : ¬ u = 1 := by
  have _pin := Classical.em True
  rintro rfl
  exact absurd h (by decide)

theorem jpd4r15t3_obstructionPackMod4 :
    (∀ z x y : ZMod 4,
          z ^ 2 = ((-1 : ℤ) : ZMod 4) * x ^ 2 + ((-1 : ℤ) : ZMod 4) * y ^ 2 →
            ((∃ t, z = 2 * t) ∧ (∃ t, x = 2 * t) ∧ (∃ t, y = 2 * t)))
      ∧ (∀ z x y : ZMod 4,
          z ^ 2 = ((-1 : ℤ) : ZMod 4) * x ^ 2 + ((-5 : ℤ) : ZMod 4) * y ^ 2 →
            ((∃ t, z = 2 * t) ∧ (∃ t, x = 2 * t) ∧ (∃ t, y = 2 * t)))
      ∧ (∀ z x y : ZMod 4,
          z ^ 2 = ((-5 : ℤ) : ZMod 4) * x ^ 2 + ((-1 : ℤ) : ZMod 4) * y ^ 2 →
            ((∃ t, z = 2 * t) ∧ (∃ t, x = 2 * t) ∧ (∃ t, y = 2 * t)))
      ∧ (∀ z x y : ZMod 4,
          z ^ 2 = ((-5 : ℤ) : ZMod 4) * x ^ 2 + ((-5 : ℤ) : ZMod 4) * y ^ 2 →
            ((∃ t, z = 2 * t) ∧ (∃ t, x = 2 * t) ∧ (∃ t, y = 2 * t))) := by
  have _pin := Classical.em True
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem jpd4r15t3_obstructionPackMod8 :
    (∀ z x y : ZMod 8,
          z ^ 2 = ((-1 : ℤ) : ZMod 8) * x ^ 2 + ((-2 : ℤ) : ZMod 8) * y ^ 2 →
            ((∃ t, z = 2 * t) ∧ (∃ t, x = 2 * t) ∧ (∃ t, y = 2 * t)))
      ∧ (∀ z x y : ZMod 8,
          z ^ 2 = ((-1 : ℤ) : ZMod 8) * x ^ 2 + ((-10 : ℤ) : ZMod 8) * y ^ 2 →
            ((∃ t, z = 2 * t) ∧ (∃ t, x = 2 * t) ∧ (∃ t, y = 2 * t)))
      ∧ (∀ z x y : ZMod 8,
          z ^ 2 = ((5 : ℤ) : ZMod 8) * x ^ 2 + ((2 : ℤ) : ZMod 8) * y ^ 2 →
            ((∃ t, z = 2 * t) ∧ (∃ t, x = 2 * t) ∧ (∃ t, y = 2 * t)))
      ∧ (∀ z x y : ZMod 8,
          z ^ 2 = ((5 : ℤ) : ZMod 8) * x ^ 2 + ((-2 : ℤ) : ZMod 8) * y ^ 2 →
            ((∃ t, z = 2 * t) ∧ (∃ t, x = 2 * t) ∧ (∃ t, y = 2 * t)))
      ∧ (∀ z x y : ZMod 8,
          z ^ 2 = ((5 : ℤ) : ZMod 8) * x ^ 2 + ((10 : ℤ) : ZMod 8) * y ^ 2 →
            ((∃ t, z = 2 * t) ∧ (∃ t, x = 2 * t) ∧ (∃ t, y = 2 * t)))
      ∧ (∀ z x y : ZMod 8,
          z ^ 2 = ((5 : ℤ) : ZMod 8) * x ^ 2 + ((-10 : ℤ) : ZMod 8) * y ^ 2 →
            ((∃ t, z = 2 * t) ∧ (∃ t, x = 2 * t) ∧ (∃ t, y = 2 * t)))
      ∧ (∀ z x y : ZMod 8,
          z ^ 2 = ((-5 : ℤ) : ZMod 8) * x ^ 2 + ((2 : ℤ) : ZMod 8) * y ^ 2 →
            ((∃ t, z = 2 * t) ∧ (∃ t, x = 2 * t) ∧ (∃ t, y = 2 * t)))
      ∧ (∀ z x y : ZMod 8,
          z ^ 2 = ((-5 : ℤ) : ZMod 8) * x ^ 2 + ((10 : ℤ) : ZMod 8) * y ^ 2 →
            ((∃ t, z = 2 * t) ∧ (∃ t, x = 2 * t) ∧ (∃ t, y = 2 * t)))
      ∧ (∀ z x y : ZMod 8,
          z ^ 2 = ((2 : ℤ) : ZMod 8) * x ^ 2 + ((5 : ℤ) : ZMod 8) * y ^ 2 →
            ((∃ t, z = 2 * t) ∧ (∃ t, x = 2 * t) ∧ (∃ t, y = 2 * t)))
      ∧ (∀ z x y : ZMod 8,
          z ^ 2 = ((2 : ℤ) : ZMod 8) * x ^ 2 + ((-5 : ℤ) : ZMod 8) * y ^ 2 →
            ((∃ t, z = 2 * t) ∧ (∃ t, x = 2 * t) ∧ (∃ t, y = 2 * t)))
      ∧ (∀ z x y : ZMod 8,
          z ^ 2 = ((-2 : ℤ) : ZMod 8) * x ^ 2 + ((-1 : ℤ) : ZMod 8) * y ^ 2 →
            ((∃ t, z = 2 * t) ∧ (∃ t, x = 2 * t) ∧ (∃ t, y = 2 * t)))
      ∧ (∀ z x y : ZMod 8,
          z ^ 2 = ((-2 : ℤ) : ZMod 8) * x ^ 2 + ((5 : ℤ) : ZMod 8) * y ^ 2 →
            ((∃ t, z = 2 * t) ∧ (∃ t, x = 2 * t) ∧ (∃ t, y = 2 * t)))
      ∧ (∀ z x y : ZMod 8,
          z ^ 2 = ((10 : ℤ) : ZMod 8) * x ^ 2 + ((5 : ℤ) : ZMod 8) * y ^ 2 →
            ((∃ t, z = 2 * t) ∧ (∃ t, x = 2 * t) ∧ (∃ t, y = 2 * t)))
      ∧ (∀ z x y : ZMod 8,
          z ^ 2 = ((10 : ℤ) : ZMod 8) * x ^ 2 + ((-5 : ℤ) : ZMod 8) * y ^ 2 →
            ((∃ t, z = 2 * t) ∧ (∃ t, x = 2 * t) ∧ (∃ t, y = 2 * t)))
      ∧ (∀ z x y : ZMod 8,
          z ^ 2 = ((-10 : ℤ) : ZMod 8) * x ^ 2 + ((-1 : ℤ) : ZMod 8) * y ^ 2 →
            ((∃ t, z = 2 * t) ∧ (∃ t, x = 2 * t) ∧ (∃ t, y = 2 * t)))
      ∧ (∀ z x y : ZMod 8,
          z ^ 2 = ((-10 : ℤ) : ZMod 8) * x ^ 2 + ((5 : ℤ) : ZMod 8) * y ^ 2 →
            ((∃ t, z = 2 * t) ∧ (∃ t, x = 2 * t) ∧ (∃ t, y = 2 * t))) := by
  have _pin := Classical.em True
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem jpd4r15t3_obstructionPackMod16 :
    (∀ z x y : ZMod 16,
          z ^ 2 = ((2 : ℤ) : ZMod 16) * x ^ 2 + ((10 : ℤ) : ZMod 16) * y ^ 2 →
            ((∃ t, z = 2 * t) ∧ (∃ t, x = 2 * t) ∧ (∃ t, y = 2 * t)))
      ∧ (∀ z x y : ZMod 16,
          z ^ 2 = ((2 : ℤ) : ZMod 16) * x ^ 2 + ((-10 : ℤ) : ZMod 16) * y ^ 2 →
            ((∃ t, z = 2 * t) ∧ (∃ t, x = 2 * t) ∧ (∃ t, y = 2 * t)))
      ∧ (∀ z x y : ZMod 16,
          z ^ 2 = ((-2 : ℤ) : ZMod 16) * x ^ 2 + ((-2 : ℤ) : ZMod 16) * y ^ 2 →
            ((∃ t, z = 2 * t) ∧ (∃ t, x = 2 * t) ∧ (∃ t, y = 2 * t)))
      ∧ (∀ z x y : ZMod 16,
          z ^ 2 = ((-2 : ℤ) : ZMod 16) * x ^ 2 + ((10 : ℤ) : ZMod 16) * y ^ 2 →
            ((∃ t, z = 2 * t) ∧ (∃ t, x = 2 * t) ∧ (∃ t, y = 2 * t)))
      ∧ (∀ z x y : ZMod 16,
          z ^ 2 = ((10 : ℤ) : ZMod 16) * x ^ 2 + ((2 : ℤ) : ZMod 16) * y ^ 2 →
            ((∃ t, z = 2 * t) ∧ (∃ t, x = 2 * t) ∧ (∃ t, y = 2 * t)))
      ∧ (∀ z x y : ZMod 16,
          z ^ 2 = ((10 : ℤ) : ZMod 16) * x ^ 2 + ((-2 : ℤ) : ZMod 16) * y ^ 2 →
            ((∃ t, z = 2 * t) ∧ (∃ t, x = 2 * t) ∧ (∃ t, y = 2 * t)))
      ∧ (∀ z x y : ZMod 16,
          z ^ 2 = ((-10 : ℤ) : ZMod 16) * x ^ 2 + ((2 : ℤ) : ZMod 16) * y ^ 2 →
            ((∃ t, z = 2 * t) ∧ (∃ t, x = 2 * t) ∧ (∃ t, y = 2 * t)))
      ∧ (∀ z x y : ZMod 16,
          z ^ 2 = ((-10 : ℤ) : ZMod 16) * x ^ 2 + ((-10 : ℤ) : ZMod 16) * y ^ 2 →
            ((∃ t, z = 2 * t) ∧ (∃ t, x = 2 * t) ∧ (∃ t, y = 2 * t))) := by
  have _pin := Classical.em True
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem jpd4r15t3_tableRow_negOne :
    jpd4r14t3_pairTwoZ 0 (-1) 0 1 = 1
          ∧ jpd4r14t3_pairTwoZ 0 (-1) 0 (-1) = (-1)
          ∧ jpd4r14t3_pairTwoZ 0 (-1) 0 5 = 1
          ∧ jpd4r14t3_pairTwoZ 0 (-1) 0 (-5) = (-1)
          ∧ jpd4r14t3_pairTwoZ 0 (-1) 1 1 = 1
          ∧ jpd4r14t3_pairTwoZ 0 (-1) 1 (-1) = (-1)
          ∧ jpd4r14t3_pairTwoZ 0 (-1) 1 5 = 1
          ∧ jpd4r14t3_pairTwoZ 0 (-1) 1 (-5) = (-1) := by
  have _pin := Classical.em True
  decide +kernel

theorem jpd4r15t3_tableRow_five :
    jpd4r14t3_pairTwoZ 0 5 0 1 = 1
          ∧ jpd4r14t3_pairTwoZ 0 5 0 (-1) = 1
          ∧ jpd4r14t3_pairTwoZ 0 5 0 5 = 1
          ∧ jpd4r14t3_pairTwoZ 0 5 0 (-5) = 1
          ∧ jpd4r14t3_pairTwoZ 0 5 1 1 = (-1)
          ∧ jpd4r14t3_pairTwoZ 0 5 1 (-1) = (-1)
          ∧ jpd4r14t3_pairTwoZ 0 5 1 5 = (-1)
          ∧ jpd4r14t3_pairTwoZ 0 5 1 (-5) = (-1) := by
  have _pin := Classical.em True
  decide +kernel

theorem jpd4r15t3_tableRow_two :
    jpd4r14t3_pairTwoZ 1 1 0 1 = 1
          ∧ jpd4r14t3_pairTwoZ 1 1 0 (-1) = 1
          ∧ jpd4r14t3_pairTwoZ 1 1 0 5 = (-1)
          ∧ jpd4r14t3_pairTwoZ 1 1 0 (-5) = (-1)
          ∧ jpd4r14t3_pairTwoZ 1 1 1 1 = 1
          ∧ jpd4r14t3_pairTwoZ 1 1 1 (-1) = 1
          ∧ jpd4r14t3_pairTwoZ 1 1 1 5 = (-1)
          ∧ jpd4r14t3_pairTwoZ 1 1 1 (-5) = (-1) := by
  have _pin := Classical.em True
  decide +kernel

theorem jpd4r15t3_solvable_two_negOne :
    jpd4r15t3_hilbertSolvable (2 : ℚ_[2]) (-1 : ℚ_[2]) := by
  have _pin := Classical.em True
  exact jpd4r15t3_solvableOfWitness _ _ 1 1 1 (Or.inl rfl) (by norm_num)

theorem jpd4r15t3_notSolvable_negOne_negOne :
    ¬ jpd4r15t3_hilbertSolvable (-1 : ℚ_[2]) (-1 : ℚ_[2]) := by
  have _pin := Classical.em True
  have h := jpd4r15t3_insolvabilityEngine (jpd4r15t3_redMod 4 2 (by norm_num)) (-1) (-1)
    jpd4r15t3_oneOddPack.1 jpd4r15t3_obstructionPackMod4.1
  push_cast at h
  exact h

theorem jpd4r15t3_notSolvable_negOne_negFive :
    ¬ jpd4r15t3_hilbertSolvable (-1 : ℚ_[2]) (-5 : ℚ_[2]) := by
  have _pin := Classical.em True
  have h := jpd4r15t3_insolvabilityEngine (jpd4r15t3_redMod 4 2 (by norm_num)) (-1) (-5)
    jpd4r15t3_oneOddPack.1 jpd4r15t3_obstructionPackMod4.2.1
  push_cast at h
  exact h

theorem jpd4r15t3_notSolvable_five_two :
    ¬ jpd4r15t3_hilbertSolvable (5 : ℚ_[2]) (2 : ℚ_[2]) := by
  have _pin := Classical.em True
  have h := jpd4r15t3_insolvabilityEngine (jpd4r15t3_redMod 8 3 (by norm_num)) (5) (2)
    jpd4r15t3_oneOddPack.2.1 jpd4r15t3_obstructionPackMod8.2.2.1
  push_cast at h
  exact h

theorem jpd4r15t3_notSolvable_five_negTwo :
    ¬ jpd4r15t3_hilbertSolvable (5 : ℚ_[2]) (-2 : ℚ_[2]) := by
  have _pin := Classical.em True
  have h := jpd4r15t3_insolvabilityEngine (jpd4r15t3_redMod 8 3 (by norm_num)) (5) (-2)
    jpd4r15t3_oneOddPack.2.1 jpd4r15t3_obstructionPackMod8.2.2.2.1
  push_cast at h
  exact h

theorem jpd4r15t3_notSolvable_five_ten :
    ¬ jpd4r15t3_hilbertSolvable (5 : ℚ_[2]) (10 : ℚ_[2]) := by
  have _pin := Classical.em True
  have h := jpd4r15t3_insolvabilityEngine (jpd4r15t3_redMod 8 3 (by norm_num)) (5) (10)
    jpd4r15t3_oneOddPack.2.1 jpd4r15t3_obstructionPackMod8.2.2.2.2.1
  push_cast at h
  exact h

theorem jpd4r15t3_notSolvable_five_negTen :
    ¬ jpd4r15t3_hilbertSolvable (5 : ℚ_[2]) (-10 : ℚ_[2]) := by
  have _pin := Classical.em True
  have h := jpd4r15t3_insolvabilityEngine (jpd4r15t3_redMod 8 3 (by norm_num)) (5) (-10)
    jpd4r15t3_oneOddPack.2.1 jpd4r15t3_obstructionPackMod8.2.2.2.2.2.1
  push_cast at h
  exact h

theorem jpd4r15t3_iff_two_negOne :
    jpd4r14t3_pairTwoZ 1 1 0 (-1) = 1
      ↔ jpd4r15t3_hilbertSolvable (2 : ℚ_[2]) (-1 : ℚ_[2]) := by
  have _pin := Classical.em True
  exact iff_of_true jpd4r15t3_tableRow_two.2.1 jpd4r15t3_solvable_two_negOne

theorem jpd4r15t3_iff_negOne_negOne :
    jpd4r14t3_pairTwoZ 0 (-1) 0 (-1) = 1
      ↔ jpd4r15t3_hilbertSolvable (-1 : ℚ_[2]) (-1 : ℚ_[2]) := by
  have _pin := Classical.em True
  exact iff_of_false (jpd4r15t3_neOne_of_eqNegOne jpd4r15t3_tableRow_negOne.2.1)
    jpd4r15t3_notSolvable_negOne_negOne

theorem jpd4r15t3_iff_negOne_negFive :
    jpd4r14t3_pairTwoZ 0 (-1) 0 (-5) = 1
      ↔ jpd4r15t3_hilbertSolvable (-1 : ℚ_[2]) (-5 : ℚ_[2]) := by
  have _pin := Classical.em True
  exact iff_of_false (jpd4r15t3_neOne_of_eqNegOne jpd4r15t3_tableRow_negOne.2.2.2.1)
    jpd4r15t3_notSolvable_negOne_negFive

theorem jpd4r15t3_iff_five_two :
    jpd4r14t3_pairTwoZ 0 5 1 1 = 1
      ↔ jpd4r15t3_hilbertSolvable (5 : ℚ_[2]) (2 : ℚ_[2]) := by
  have _pin := Classical.em True
  exact iff_of_false (jpd4r15t3_neOne_of_eqNegOne jpd4r15t3_tableRow_five.2.2.2.2.1)
    jpd4r15t3_notSolvable_five_two

theorem jpd4r15t3_iff_five_negTwo :
    jpd4r14t3_pairTwoZ 0 5 1 (-1) = 1
      ↔ jpd4r15t3_hilbertSolvable (5 : ℚ_[2]) (-2 : ℚ_[2]) := by
  have _pin := Classical.em True
  exact iff_of_false (jpd4r15t3_neOne_of_eqNegOne jpd4r15t3_tableRow_five.2.2.2.2.2.1)
    jpd4r15t3_notSolvable_five_negTwo

theorem jpd4r15t3_iff_five_ten :
    jpd4r14t3_pairTwoZ 0 5 1 5 = 1
      ↔ jpd4r15t3_hilbertSolvable (5 : ℚ_[2]) (10 : ℚ_[2]) := by
  have _pin := Classical.em True
  exact iff_of_false (jpd4r15t3_neOne_of_eqNegOne jpd4r15t3_tableRow_five.2.2.2.2.2.2.1)
    jpd4r15t3_notSolvable_five_ten

theorem jpd4r15t3_iff_five_negTen :
    jpd4r14t3_pairTwoZ 0 5 1 (-5) = 1
      ↔ jpd4r15t3_hilbertSolvable (5 : ℚ_[2]) (-10 : ℚ_[2]) := by
  have _pin := Classical.em True
  exact iff_of_false (jpd4r15t3_neOne_of_eqNegOne jpd4r15t3_tableRow_five.2.2.2.2.2.2.2)
    jpd4r15t3_notSolvable_five_negTen

end FLT.JpssD4KubotaPTwoHilbertSolvabilityIdentification
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"
end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section
section

set_option linter.dupNamespace false
set_option maxHeartbeats 1600000

noncomputable section

namespace FLT
namespace JpssD4KubotaPTwoHilbertSolvabilityIdentificationGrid

open FLT.JpssD4KubotaPTwoHilbertTable
open FLT.JpssD4KubotaPTwoHilbertSolvabilityIdentification

theorem jpd4r15t3_tableRow_one :
    jpd4r14t3_pairTwoZ 0 1 0 1 = 1
          ∧ jpd4r14t3_pairTwoZ 0 1 0 (-1) = 1
          ∧ jpd4r14t3_pairTwoZ 0 1 0 5 = 1
          ∧ jpd4r14t3_pairTwoZ 0 1 0 (-5) = 1
          ∧ jpd4r14t3_pairTwoZ 0 1 1 1 = 1
          ∧ jpd4r14t3_pairTwoZ 0 1 1 (-1) = 1
          ∧ jpd4r14t3_pairTwoZ 0 1 1 5 = 1
          ∧ jpd4r14t3_pairTwoZ 0 1 1 (-5) = 1 := by
  have _pin := Classical.em True
  decide +kernel

theorem jpd4r15t3_tableRow_negFive :
    jpd4r14t3_pairTwoZ 0 (-5) 0 1 = 1
          ∧ jpd4r14t3_pairTwoZ 0 (-5) 0 (-1) = (-1)
          ∧ jpd4r14t3_pairTwoZ 0 (-5) 0 5 = 1
          ∧ jpd4r14t3_pairTwoZ 0 (-5) 0 (-5) = (-1)
          ∧ jpd4r14t3_pairTwoZ 0 (-5) 1 1 = (-1)
          ∧ jpd4r14t3_pairTwoZ 0 (-5) 1 (-1) = 1
          ∧ jpd4r14t3_pairTwoZ 0 (-5) 1 5 = (-1)
          ∧ jpd4r14t3_pairTwoZ 0 (-5) 1 (-5) = 1 := by
  have _pin := Classical.em True
  decide +kernel

theorem jpd4r15t3_tableRow_negTwo :
    jpd4r14t3_pairTwoZ 1 (-1) 0 1 = 1
          ∧ jpd4r14t3_pairTwoZ 1 (-1) 0 (-1) = (-1)
          ∧ jpd4r14t3_pairTwoZ 1 (-1) 0 5 = (-1)
          ∧ jpd4r14t3_pairTwoZ 1 (-1) 0 (-5) = 1
          ∧ jpd4r14t3_pairTwoZ 1 (-1) 1 1 = 1
          ∧ jpd4r14t3_pairTwoZ 1 (-1) 1 (-1) = (-1)
          ∧ jpd4r14t3_pairTwoZ 1 (-1) 1 5 = (-1)
          ∧ jpd4r14t3_pairTwoZ 1 (-1) 1 (-5) = 1 := by
  have _pin := Classical.em True
  decide +kernel

theorem jpd4r15t3_tableRow_ten :
    jpd4r14t3_pairTwoZ 1 5 0 1 = 1
          ∧ jpd4r14t3_pairTwoZ 1 5 0 (-1) = 1
          ∧ jpd4r14t3_pairTwoZ 1 5 0 5 = (-1)
          ∧ jpd4r14t3_pairTwoZ 1 5 0 (-5) = (-1)
          ∧ jpd4r14t3_pairTwoZ 1 5 1 1 = (-1)
          ∧ jpd4r14t3_pairTwoZ 1 5 1 (-1) = (-1)
          ∧ jpd4r14t3_pairTwoZ 1 5 1 5 = 1
          ∧ jpd4r14t3_pairTwoZ 1 5 1 (-5) = 1 := by
  have _pin := Classical.em True
  decide +kernel

theorem jpd4r15t3_tableRow_negTen :
    jpd4r14t3_pairTwoZ 1 (-5) 0 1 = 1
          ∧ jpd4r14t3_pairTwoZ 1 (-5) 0 (-1) = (-1)
          ∧ jpd4r14t3_pairTwoZ 1 (-5) 0 5 = (-1)
          ∧ jpd4r14t3_pairTwoZ 1 (-5) 0 (-5) = 1
          ∧ jpd4r14t3_pairTwoZ 1 (-5) 1 1 = (-1)
          ∧ jpd4r14t3_pairTwoZ 1 (-5) 1 (-1) = 1
          ∧ jpd4r14t3_pairTwoZ 1 (-5) 1 5 = 1
          ∧ jpd4r14t3_pairTwoZ 1 (-5) 1 (-5) = (-1) := by
  have _pin := Classical.em True
  decide +kernel

theorem jpd4r15t3_gridRow_one :
    (jpd4r14t3_pairTwoZ 0 1 0 1 = 1
        ↔ jpd4r15t3_hilbertSolvable (1 : ℚ_[2]) (1 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 0 1 0 (-1) = 1
        ↔ jpd4r15t3_hilbertSolvable (1 : ℚ_[2]) (-1 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 0 1 0 5 = 1
        ↔ jpd4r15t3_hilbertSolvable (1 : ℚ_[2]) (5 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 0 1 0 (-5) = 1
        ↔ jpd4r15t3_hilbertSolvable (1 : ℚ_[2]) (-5 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 0 1 1 1 = 1
        ↔ jpd4r15t3_hilbertSolvable (1 : ℚ_[2]) (2 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 0 1 1 (-1) = 1
        ↔ jpd4r15t3_hilbertSolvable (1 : ℚ_[2]) (-2 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 0 1 1 5 = 1
        ↔ jpd4r15t3_hilbertSolvable (1 : ℚ_[2]) (10 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 0 1 1 (-5) = 1
        ↔ jpd4r15t3_hilbertSolvable (1 : ℚ_[2]) (-10 : ℚ_[2])) := by
  have _pin := Classical.em True
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    exact iff_of_true jpd4r15t3_tableRow_one.1
      (jpd4r15t3_solvableOfWitness _ _ 1 1 0 (Or.inl rfl) (by norm_num))
  ·
    exact iff_of_true jpd4r15t3_tableRow_one.2.1
      (jpd4r15t3_solvableOfWitness _ _ 1 1 0 (Or.inl rfl) (by norm_num))
  ·
    exact iff_of_true jpd4r15t3_tableRow_one.2.2.1
      (jpd4r15t3_solvableOfWitness _ _ 1 1 0 (Or.inl rfl) (by norm_num))
  ·
    exact iff_of_true jpd4r15t3_tableRow_one.2.2.2.1
      (jpd4r15t3_solvableOfWitness _ _ 1 1 0 (Or.inl rfl) (by norm_num))
  ·
    exact iff_of_true jpd4r15t3_tableRow_one.2.2.2.2.1
      (jpd4r15t3_solvableOfWitness _ _ 1 1 0 (Or.inl rfl) (by norm_num))
  ·
    exact iff_of_true jpd4r15t3_tableRow_one.2.2.2.2.2.1
      (jpd4r15t3_solvableOfWitness _ _ 1 1 0 (Or.inl rfl) (by norm_num))
  ·
    exact iff_of_true jpd4r15t3_tableRow_one.2.2.2.2.2.2.1
      (jpd4r15t3_solvableOfWitness _ _ 1 1 0 (Or.inl rfl) (by norm_num))
  ·
    exact iff_of_true jpd4r15t3_tableRow_one.2.2.2.2.2.2.2
      (jpd4r15t3_solvableOfWitness _ _ 1 1 0 (Or.inl rfl) (by norm_num))

theorem jpd4r15t3_gridRow_negOne :
    (jpd4r14t3_pairTwoZ 0 (-1) 0 1 = 1
        ↔ jpd4r15t3_hilbertSolvable (-1 : ℚ_[2]) (1 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 0 (-1) 0 (-1) = 1
        ↔ jpd4r15t3_hilbertSolvable (-1 : ℚ_[2]) (-1 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 0 (-1) 0 5 = 1
        ↔ jpd4r15t3_hilbertSolvable (-1 : ℚ_[2]) (5 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 0 (-1) 0 (-5) = 1
        ↔ jpd4r15t3_hilbertSolvable (-1 : ℚ_[2]) (-5 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 0 (-1) 1 1 = 1
        ↔ jpd4r15t3_hilbertSolvable (-1 : ℚ_[2]) (2 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 0 (-1) 1 (-1) = 1
        ↔ jpd4r15t3_hilbertSolvable (-1 : ℚ_[2]) (-2 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 0 (-1) 1 5 = 1
        ↔ jpd4r15t3_hilbertSolvable (-1 : ℚ_[2]) (10 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 0 (-1) 1 (-5) = 1
        ↔ jpd4r15t3_hilbertSolvable (-1 : ℚ_[2]) (-10 : ℚ_[2])) := by
  have _pin := Classical.em True
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    exact iff_of_true jpd4r15t3_tableRow_negOne.1
      (jpd4r15t3_solvableOfWitness _ _ 1 0 1 (Or.inl rfl) (by norm_num))
  ·
    exact jpd4r15t3_iff_negOne_negOne
  ·
    exact iff_of_true jpd4r15t3_tableRow_negOne.2.2.1
      (jpd4r15t3_solvableOfWitness _ _ 1 2 1 (Or.inl rfl) (by norm_num))
  ·
    exact jpd4r15t3_iff_negOne_negFive
  ·
    exact iff_of_true jpd4r15t3_tableRow_negOne.2.2.2.2.1
      (jpd4r15t3_solvableOfWitness _ _ 1 1 1 (Or.inl rfl) (by norm_num))
  ·
    refine iff_of_false (jpd4r15t3_neOne_of_eqNegOne jpd4r15t3_tableRow_negOne.2.2.2.2.2.1) ?_
    have h := jpd4r15t3_insolvabilityEngine (jpd4r15t3_redMod 8 3 (by norm_num))
      (-1) (-2) jpd4r15t3_oneOddPack.2.1 jpd4r15t3_obstructionPackMod8.1
    push_cast at h
    exact h
  ·
    exact iff_of_true jpd4r15t3_tableRow_negOne.2.2.2.2.2.2.1
      (jpd4r15t3_solvableOfWitness _ _ 1 3 1 (Or.inl rfl) (by norm_num))
  ·
    refine iff_of_false (jpd4r15t3_neOne_of_eqNegOne jpd4r15t3_tableRow_negOne.2.2.2.2.2.2.2) ?_
    have h := jpd4r15t3_insolvabilityEngine (jpd4r15t3_redMod 8 3 (by norm_num))
      (-1) (-10) jpd4r15t3_oneOddPack.2.1 jpd4r15t3_obstructionPackMod8.2.1
    push_cast at h
    exact h

theorem jpd4r15t3_gridRow_five :
    (jpd4r14t3_pairTwoZ 0 5 0 1 = 1
        ↔ jpd4r15t3_hilbertSolvable (5 : ℚ_[2]) (1 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 0 5 0 (-1) = 1
        ↔ jpd4r15t3_hilbertSolvable (5 : ℚ_[2]) (-1 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 0 5 0 5 = 1
        ↔ jpd4r15t3_hilbertSolvable (5 : ℚ_[2]) (5 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 0 5 0 (-5) = 1
        ↔ jpd4r15t3_hilbertSolvable (5 : ℚ_[2]) (-5 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 0 5 1 1 = 1
        ↔ jpd4r15t3_hilbertSolvable (5 : ℚ_[2]) (2 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 0 5 1 (-1) = 1
        ↔ jpd4r15t3_hilbertSolvable (5 : ℚ_[2]) (-2 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 0 5 1 5 = 1
        ↔ jpd4r15t3_hilbertSolvable (5 : ℚ_[2]) (10 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 0 5 1 (-5) = 1
        ↔ jpd4r15t3_hilbertSolvable (5 : ℚ_[2]) (-10 : ℚ_[2])) := by
  have _pin := Classical.em True
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    exact iff_of_true jpd4r15t3_tableRow_five.1
      (jpd4r15t3_solvableOfWitness _ _ 1 0 1 (Or.inl rfl) (by norm_num))
  ·
    exact iff_of_true jpd4r15t3_tableRow_five.2.1
      (jpd4r15t3_solvableOfWitness _ _ 1 1 2 (Or.inl rfl) (by norm_num))
  ·
    exact iff_of_true jpd4r15t3_tableRow_five.2.2.1
      (jpd4r15t3_solvableOfWitness _ _ 5 1 2 (Or.inr (Or.inl rfl)) (by norm_num))
  ·
    exact iff_of_true jpd4r15t3_tableRow_five.2.2.2.1
      (jpd4r15t3_solvableOfWitness _ _ 0 1 1 (Or.inr (Or.inl rfl)) (by norm_num))
  ·
    exact jpd4r15t3_iff_five_two
  ·
    exact jpd4r15t3_iff_five_negTwo
  ·
    exact jpd4r15t3_iff_five_ten
  ·
    exact jpd4r15t3_iff_five_negTen

theorem jpd4r15t3_gridRow_negFive :
    (jpd4r14t3_pairTwoZ 0 (-5) 0 1 = 1
        ↔ jpd4r15t3_hilbertSolvable (-5 : ℚ_[2]) (1 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 0 (-5) 0 (-1) = 1
        ↔ jpd4r15t3_hilbertSolvable (-5 : ℚ_[2]) (-1 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 0 (-5) 0 5 = 1
        ↔ jpd4r15t3_hilbertSolvable (-5 : ℚ_[2]) (5 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 0 (-5) 0 (-5) = 1
        ↔ jpd4r15t3_hilbertSolvable (-5 : ℚ_[2]) (-5 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 0 (-5) 1 1 = 1
        ↔ jpd4r15t3_hilbertSolvable (-5 : ℚ_[2]) (2 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 0 (-5) 1 (-1) = 1
        ↔ jpd4r15t3_hilbertSolvable (-5 : ℚ_[2]) (-2 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 0 (-5) 1 5 = 1
        ↔ jpd4r15t3_hilbertSolvable (-5 : ℚ_[2]) (10 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 0 (-5) 1 (-5) = 1
        ↔ jpd4r15t3_hilbertSolvable (-5 : ℚ_[2]) (-10 : ℚ_[2])) := by
  have _pin := Classical.em True
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    exact iff_of_true jpd4r15t3_tableRow_negFive.1
      (jpd4r15t3_solvableOfWitness _ _ 1 0 1 (Or.inl rfl) (by norm_num))
  ·
    refine iff_of_false (jpd4r15t3_neOne_of_eqNegOne jpd4r15t3_tableRow_negFive.2.1) ?_
    have h := jpd4r15t3_insolvabilityEngine (jpd4r15t3_redMod 4 2 (by norm_num))
      (-5) (-1) jpd4r15t3_oneOddPack.1 jpd4r15t3_obstructionPackMod4.2.2.1
    push_cast at h
    exact h
  ·
    exact iff_of_true jpd4r15t3_tableRow_negFive.2.2.1
      (jpd4r15t3_solvableOfWitness _ _ 0 1 1 (Or.inr (Or.inl rfl)) (by norm_num))
  ·
    refine iff_of_false (jpd4r15t3_neOne_of_eqNegOne jpd4r15t3_tableRow_negFive.2.2.2.1) ?_
    have h := jpd4r15t3_insolvabilityEngine (jpd4r15t3_redMod 4 2 (by norm_num))
      (-5) (-5) jpd4r15t3_oneOddPack.1 jpd4r15t3_obstructionPackMod4.2.2.2
    push_cast at h
    exact h
  ·
    refine iff_of_false (jpd4r15t3_neOne_of_eqNegOne jpd4r15t3_tableRow_negFive.2.2.2.2.1) ?_
    have h := jpd4r15t3_insolvabilityEngine (jpd4r15t3_redMod 8 3 (by norm_num))
      (-5) (2) jpd4r15t3_oneOddPack.2.1 jpd4r15t3_obstructionPackMod8.2.2.2.2.2.2.1
    push_cast at h
    exact h
  ·
    refine iff_of_true jpd4r15t3_tableRow_negFive.2.2.2.2.2.1 ?_
    obtain ⟨s, hs⟩ := jpd4r15t3_sqrtNeg7
    exact jpd4r15t3_solvableOfWitness _ _ (s) 1 1 (Or.inr (Or.inl rfl))
      (by rw [hs]; norm_num)
  ·
    refine iff_of_false (jpd4r15t3_neOne_of_eqNegOne jpd4r15t3_tableRow_negFive.2.2.2.2.2.2.1) ?_
    have h := jpd4r15t3_insolvabilityEngine (jpd4r15t3_redMod 8 3 (by norm_num))
      (-5) (10) jpd4r15t3_oneOddPack.2.1 jpd4r15t3_obstructionPackMod8.2.2.2.2.2.2.2.1
    push_cast at h
    exact h
  ·
    refine iff_of_true jpd4r15t3_tableRow_negFive.2.2.2.2.2.2.2 ?_
    obtain ⟨s, hs⟩ := jpd4r15t3_sqrtNeg15
    exact jpd4r15t3_solvableOfWitness _ _ (s) 1 1 (Or.inr (Or.inl rfl))
      (by rw [hs]; norm_num)

theorem jpd4r15t3_gridRow_two :
    (jpd4r14t3_pairTwoZ 1 1 0 1 = 1
        ↔ jpd4r15t3_hilbertSolvable (2 : ℚ_[2]) (1 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 1 1 0 (-1) = 1
        ↔ jpd4r15t3_hilbertSolvable (2 : ℚ_[2]) (-1 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 1 1 0 5 = 1
        ↔ jpd4r15t3_hilbertSolvable (2 : ℚ_[2]) (5 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 1 1 0 (-5) = 1
        ↔ jpd4r15t3_hilbertSolvable (2 : ℚ_[2]) (-5 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 1 1 1 1 = 1
        ↔ jpd4r15t3_hilbertSolvable (2 : ℚ_[2]) (2 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 1 1 1 (-1) = 1
        ↔ jpd4r15t3_hilbertSolvable (2 : ℚ_[2]) (-2 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 1 1 1 5 = 1
        ↔ jpd4r15t3_hilbertSolvable (2 : ℚ_[2]) (10 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 1 1 1 (-5) = 1
        ↔ jpd4r15t3_hilbertSolvable (2 : ℚ_[2]) (-10 : ℚ_[2])) := by
  have _pin := Classical.em True
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    exact iff_of_true jpd4r15t3_tableRow_two.1
      (jpd4r15t3_solvableOfWitness _ _ 1 0 1 (Or.inl rfl) (by norm_num))
  ·
    exact jpd4r15t3_iff_two_negOne
  ·
    refine iff_of_false (jpd4r15t3_neOne_of_eqNegOne jpd4r15t3_tableRow_two.2.2.1) ?_
    have h := jpd4r15t3_insolvabilityEngine (jpd4r15t3_redMod 8 3 (by norm_num))
      (2) (5) jpd4r15t3_oneOddPack.2.1 jpd4r15t3_obstructionPackMod8.2.2.2.2.2.2.2.2.1
    push_cast at h
    exact h
  ·
    refine iff_of_false (jpd4r15t3_neOne_of_eqNegOne jpd4r15t3_tableRow_two.2.2.2.1) ?_
    have h := jpd4r15t3_insolvabilityEngine (jpd4r15t3_redMod 8 3 (by norm_num))
      (2) (-5) jpd4r15t3_oneOddPack.2.1 jpd4r15t3_obstructionPackMod8.2.2.2.2.2.2.2.2.2.1
    push_cast at h
    exact h
  ·
    exact iff_of_true jpd4r15t3_tableRow_two.2.2.2.2.1
      (jpd4r15t3_solvableOfWitness _ _ 2 1 1 (Or.inr (Or.inl rfl)) (by norm_num))
  ·
    exact iff_of_true jpd4r15t3_tableRow_two.2.2.2.2.2.1
      (jpd4r15t3_solvableOfWitness _ _ 0 1 1 (Or.inr (Or.inl rfl)) (by norm_num))
  ·
    refine iff_of_false (jpd4r15t3_neOne_of_eqNegOne jpd4r15t3_tableRow_two.2.2.2.2.2.2.1) ?_
    have h := jpd4r15t3_insolvabilityEngine (jpd4r15t3_redMod 16 4 (by norm_num))
      (2) (10) jpd4r15t3_oneOddPack.2.2 jpd4r15t3_obstructionPackMod16.1
    push_cast at h
    exact h
  ·
    refine iff_of_false (jpd4r15t3_neOne_of_eqNegOne jpd4r15t3_tableRow_two.2.2.2.2.2.2.2) ?_
    have h := jpd4r15t3_insolvabilityEngine (jpd4r15t3_redMod 16 4 (by norm_num))
      (2) (-10) jpd4r15t3_oneOddPack.2.2 jpd4r15t3_obstructionPackMod16.2.1
    push_cast at h
    exact h

theorem jpd4r15t3_gridRow_negTwo :
    (jpd4r14t3_pairTwoZ 1 (-1) 0 1 = 1
        ↔ jpd4r15t3_hilbertSolvable (-2 : ℚ_[2]) (1 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 1 (-1) 0 (-1) = 1
        ↔ jpd4r15t3_hilbertSolvable (-2 : ℚ_[2]) (-1 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 1 (-1) 0 5 = 1
        ↔ jpd4r15t3_hilbertSolvable (-2 : ℚ_[2]) (5 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 1 (-1) 0 (-5) = 1
        ↔ jpd4r15t3_hilbertSolvable (-2 : ℚ_[2]) (-5 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 1 (-1) 1 1 = 1
        ↔ jpd4r15t3_hilbertSolvable (-2 : ℚ_[2]) (2 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 1 (-1) 1 (-1) = 1
        ↔ jpd4r15t3_hilbertSolvable (-2 : ℚ_[2]) (-2 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 1 (-1) 1 5 = 1
        ↔ jpd4r15t3_hilbertSolvable (-2 : ℚ_[2]) (10 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 1 (-1) 1 (-5) = 1
        ↔ jpd4r15t3_hilbertSolvable (-2 : ℚ_[2]) (-10 : ℚ_[2])) := by
  have _pin := Classical.em True
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    exact iff_of_true jpd4r15t3_tableRow_negTwo.1
      (jpd4r15t3_solvableOfWitness _ _ 1 0 1 (Or.inl rfl) (by norm_num))
  ·
    refine iff_of_false (jpd4r15t3_neOne_of_eqNegOne jpd4r15t3_tableRow_negTwo.2.1) ?_
    have h := jpd4r15t3_insolvabilityEngine (jpd4r15t3_redMod 8 3 (by norm_num))
      (-2) (-1) jpd4r15t3_oneOddPack.2.1 jpd4r15t3_obstructionPackMod8.2.2.2.2.2.2.2.2.2.2.1
    push_cast at h
    exact h
  ·
    refine iff_of_false (jpd4r15t3_neOne_of_eqNegOne jpd4r15t3_tableRow_negTwo.2.2.1) ?_
    have h := jpd4r15t3_insolvabilityEngine (jpd4r15t3_redMod 8 3 (by norm_num))
      (-2) (5) jpd4r15t3_oneOddPack.2.1 jpd4r15t3_obstructionPackMod8.2.2.2.2.2.2.2.2.2.2.2.1
    push_cast at h
    exact h
  ·
    refine iff_of_true jpd4r15t3_tableRow_negTwo.2.2.2.1 ?_
    obtain ⟨s, hs⟩ := jpd4r15t3_sqrtNeg7
    exact jpd4r15t3_solvableOfWitness _ _ (s) 1 1 (Or.inr (Or.inl rfl))
      (by rw [hs]; norm_num)
  ·
    exact iff_of_true jpd4r15t3_tableRow_negTwo.2.2.2.2.1
      (jpd4r15t3_solvableOfWitness _ _ 0 1 1 (Or.inr (Or.inl rfl)) (by norm_num))
  ·
    refine iff_of_false (jpd4r15t3_neOne_of_eqNegOne jpd4r15t3_tableRow_negTwo.2.2.2.2.2.1) ?_
    have h := jpd4r15t3_insolvabilityEngine (jpd4r15t3_redMod 16 4 (by norm_num))
      (-2) (-2) jpd4r15t3_oneOddPack.2.2 jpd4r15t3_obstructionPackMod16.2.2.1
    push_cast at h
    exact h
  ·
    refine iff_of_false (jpd4r15t3_neOne_of_eqNegOne jpd4r15t3_tableRow_negTwo.2.2.2.2.2.2.1) ?_
    have h := jpd4r15t3_insolvabilityEngine (jpd4r15t3_redMod 16 4 (by norm_num))
      (-2) (10) jpd4r15t3_oneOddPack.2.2 jpd4r15t3_obstructionPackMod16.2.2.2.1
    push_cast at h
    exact h
  ·
    refine iff_of_true jpd4r15t3_tableRow_negTwo.2.2.2.2.2.2.2 ?_
    obtain ⟨s, hs⟩ := jpd4r15t3_sqrtNeg7
    exact jpd4r15t3_solvableOfWitness _ _ (2 * s) 3 1 (Or.inr (Or.inr rfl))
      (by rw [mul_pow, hs]; norm_num)

theorem jpd4r15t3_gridRow_ten :
    (jpd4r14t3_pairTwoZ 1 5 0 1 = 1
        ↔ jpd4r15t3_hilbertSolvable (10 : ℚ_[2]) (1 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 1 5 0 (-1) = 1
        ↔ jpd4r15t3_hilbertSolvable (10 : ℚ_[2]) (-1 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 1 5 0 5 = 1
        ↔ jpd4r15t3_hilbertSolvable (10 : ℚ_[2]) (5 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 1 5 0 (-5) = 1
        ↔ jpd4r15t3_hilbertSolvable (10 : ℚ_[2]) (-5 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 1 5 1 1 = 1
        ↔ jpd4r15t3_hilbertSolvable (10 : ℚ_[2]) (2 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 1 5 1 (-1) = 1
        ↔ jpd4r15t3_hilbertSolvable (10 : ℚ_[2]) (-2 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 1 5 1 5 = 1
        ↔ jpd4r15t3_hilbertSolvable (10 : ℚ_[2]) (10 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 1 5 1 (-5) = 1
        ↔ jpd4r15t3_hilbertSolvable (10 : ℚ_[2]) (-10 : ℚ_[2])) := by
  have _pin := Classical.em True
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    exact iff_of_true jpd4r15t3_tableRow_ten.1
      (jpd4r15t3_solvableOfWitness _ _ 1 0 1 (Or.inl rfl) (by norm_num))
  ·
    exact iff_of_true jpd4r15t3_tableRow_ten.2.1
      (jpd4r15t3_solvableOfWitness _ _ 1 1 3 (Or.inl rfl) (by norm_num))
  ·
    refine iff_of_false (jpd4r15t3_neOne_of_eqNegOne jpd4r15t3_tableRow_ten.2.2.1) ?_
    have h := jpd4r15t3_insolvabilityEngine (jpd4r15t3_redMod 8 3 (by norm_num))
      (10) (5) jpd4r15t3_oneOddPack.2.1 jpd4r15t3_obstructionPackMod8.2.2.2.2.2.2.2.2.2.2.2.2.1
    push_cast at h
    exact h
  ·
    refine iff_of_false (jpd4r15t3_neOne_of_eqNegOne jpd4r15t3_tableRow_ten.2.2.2.1) ?_
    have h := jpd4r15t3_insolvabilityEngine (jpd4r15t3_redMod 8 3 (by norm_num))
      (10) (-5) jpd4r15t3_oneOddPack.2.1 jpd4r15t3_obstructionPackMod8.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    push_cast at h
    exact h
  ·
    refine iff_of_false (jpd4r15t3_neOne_of_eqNegOne jpd4r15t3_tableRow_ten.2.2.2.2.1) ?_
    have h := jpd4r15t3_insolvabilityEngine (jpd4r15t3_redMod 16 4 (by norm_num))
      (10) (2) jpd4r15t3_oneOddPack.2.2 jpd4r15t3_obstructionPackMod16.2.2.2.2.1
    push_cast at h
    exact h
  ·
    refine iff_of_false (jpd4r15t3_neOne_of_eqNegOne jpd4r15t3_tableRow_ten.2.2.2.2.2.1) ?_
    have h := jpd4r15t3_insolvabilityEngine (jpd4r15t3_redMod 16 4 (by norm_num))
      (10) (-2) jpd4r15t3_oneOddPack.2.2 jpd4r15t3_obstructionPackMod16.2.2.2.2.2.1
    push_cast at h
    exact h
  ·
    exact iff_of_true jpd4r15t3_tableRow_ten.2.2.2.2.2.2.1
      (jpd4r15t3_solvableOfWitness _ _ 10 1 3 (Or.inr (Or.inl rfl)) (by norm_num))
  ·
    exact iff_of_true jpd4r15t3_tableRow_ten.2.2.2.2.2.2.2
      (jpd4r15t3_solvableOfWitness _ _ 0 1 1 (Or.inr (Or.inl rfl)) (by norm_num))

theorem jpd4r15t3_gridRow_negTen :
    (jpd4r14t3_pairTwoZ 1 (-5) 0 1 = 1
        ↔ jpd4r15t3_hilbertSolvable (-10 : ℚ_[2]) (1 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 1 (-5) 0 (-1) = 1
        ↔ jpd4r15t3_hilbertSolvable (-10 : ℚ_[2]) (-1 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 1 (-5) 0 5 = 1
        ↔ jpd4r15t3_hilbertSolvable (-10 : ℚ_[2]) (5 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 1 (-5) 0 (-5) = 1
        ↔ jpd4r15t3_hilbertSolvable (-10 : ℚ_[2]) (-5 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 1 (-5) 1 1 = 1
        ↔ jpd4r15t3_hilbertSolvable (-10 : ℚ_[2]) (2 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 1 (-5) 1 (-1) = 1
        ↔ jpd4r15t3_hilbertSolvable (-10 : ℚ_[2]) (-2 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 1 (-5) 1 5 = 1
        ↔ jpd4r15t3_hilbertSolvable (-10 : ℚ_[2]) (10 : ℚ_[2]))
      ∧ (jpd4r14t3_pairTwoZ 1 (-5) 1 (-5) = 1
        ↔ jpd4r15t3_hilbertSolvable (-10 : ℚ_[2]) (-10 : ℚ_[2])) := by
  have _pin := Classical.em True
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    exact iff_of_true jpd4r15t3_tableRow_negTen.1
      (jpd4r15t3_solvableOfWitness _ _ 1 0 1 (Or.inl rfl) (by norm_num))
  ·
    refine iff_of_false (jpd4r15t3_neOne_of_eqNegOne jpd4r15t3_tableRow_negTen.2.1) ?_
    have h := jpd4r15t3_insolvabilityEngine (jpd4r15t3_redMod 8 3 (by norm_num))
      (-10) (-1) jpd4r15t3_oneOddPack.2.1 jpd4r15t3_obstructionPackMod8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    push_cast at h
    exact h
  ·
    refine iff_of_false (jpd4r15t3_neOne_of_eqNegOne jpd4r15t3_tableRow_negTen.2.2.1) ?_
    have h := jpd4r15t3_insolvabilityEngine (jpd4r15t3_redMod 8 3 (by norm_num))
      (-10) (5) jpd4r15t3_oneOddPack.2.1 jpd4r15t3_obstructionPackMod8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    push_cast at h
    exact h
  ·
    refine iff_of_true jpd4r15t3_tableRow_negTen.2.2.2.1 ?_
    obtain ⟨s, hs⟩ := jpd4r15t3_sqrtNeg15
    exact jpd4r15t3_solvableOfWitness _ _ (s) 1 1 (Or.inr (Or.inl rfl))
      (by rw [hs]; norm_num)
  ·
    refine iff_of_false (jpd4r15t3_neOne_of_eqNegOne jpd4r15t3_tableRow_negTen.2.2.2.2.1) ?_
    have h := jpd4r15t3_insolvabilityEngine (jpd4r15t3_redMod 16 4 (by norm_num))
      (-10) (2) jpd4r15t3_oneOddPack.2.2 jpd4r15t3_obstructionPackMod16.2.2.2.2.2.2.1
    push_cast at h
    exact h
  ·
    refine iff_of_true jpd4r15t3_tableRow_negTen.2.2.2.2.2.1 ?_
    obtain ⟨s, hs⟩ := jpd4r15t3_sqrtNeg7
    exact jpd4r15t3_solvableOfWitness _ _ (2 * s) 1 3 (Or.inr (Or.inl rfl))
      (by rw [mul_pow, hs]; norm_num)
  ·
    exact iff_of_true jpd4r15t3_tableRow_negTen.2.2.2.2.2.2.1
      (jpd4r15t3_solvableOfWitness _ _ 0 1 1 (Or.inr (Or.inl rfl)) (by norm_num))
  ·
    refine iff_of_false (jpd4r15t3_neOne_of_eqNegOne jpd4r15t3_tableRow_negTen.2.2.2.2.2.2.2) ?_
    have h := jpd4r15t3_insolvabilityEngine (jpd4r15t3_redMod 16 4 (by norm_num))
      (-10) (-10) jpd4r15t3_oneOddPack.2.2 jpd4r15t3_obstructionPackMod16.2.2.2.2.2.2.2
    push_cast at h
    exact h

end FLT.JpssD4KubotaPTwoHilbertSolvabilityIdentificationGrid
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"
end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section
section

set_option linter.dupNamespace false
set_option maxHeartbeats 1600000

p2m_open "MeasureTheory P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.MeasureTheory NumberField P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.NumberField IsDedekindDomain P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.IsDedekindDomain Matrix P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.Matrix"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.IsDedekindDomain.HeightOneSpectrum"
open FLT.AdelicLsXi FLT.AdelicTruncation FLT.AdelicIwasawaHeight FLT.ArchimedeanSiegel
open Rat.FiniteAdeleRing

noncomputable section

namespace FLT
namespace JpssD4GJProp83MetaplecticKubotaCoverCarrier

open FLT.JpssD4GJProp83L2EngineProofSkeleton
open FLT.JpssD4GJProp83GenuineCarrierSkeleton
open FLT.JpssD4GJProp83EisensteinInputSlice
open FLT.JpssD4GJProp83EisensteinAdelicQuadrupleLayer
open FLT.JpssD4GJProp83EisensteinAdelicQuadrupleInhabit
open FLT.GL2FiniteAdelicMatrixIdentification
open FLT.CampGenuineMk

section CoverLaw

end CoverLaw
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section Splitting

end Splitting
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section TwistedQuadruple

end TwistedQuadruple
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section WitnessChain

end WitnessChain
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section ArchimedeanFactor

open scoped _root_.Classical _root_.P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.Classical in

noncomputable def jpd4r13t6_hilbR (a b : ℝ) : ℤˣ :=
  if a < 0 ∧ b < 0 then -1 else 1

theorem jpd4r13t6_hilbR_symm (a b : ℝ) :
    jpd4r13t6_hilbR a b = jpd4r13t6_hilbR b a := by
  unfold jpd4r13t6_hilbR
  by_cases h : a < 0 ∧ b < 0
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
  · rw [if_neg h, if_neg (fun hc => h ⟨hc.2, hc.1⟩)]

end ArchimedeanFactor
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section AdjoinedCarrier

end AdjoinedCarrier
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section ArchimedeanObstruction

end ArchimedeanObstruction
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section Registries

end Registries
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end FLT.JpssD4GJProp83MetaplecticKubotaCoverCarrier
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"
end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section
section

set_option maxHeartbeats 1600000

p2m_open "Matrix P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.Matrix"

noncomputable section

namespace FLT
namespace JpssD4KubotaArchimedeanCocycleSlice

open FLT.CampGenuineMk
open FLT.JpssD4GJProp83EisensteinAdelicQuadrupleInhabit
open FLT.JpssD4GJProp83MetaplecticKubotaCoverCarrier

theorem jpd4r14t4_hilbR_neg_neg (a b : ℝ) (ha : a < 0) (hb : b < 0) :
    jpd4r13t6_hilbR a b = -1 := by
  have _pin := Classical.em True
  unfold jpd4r13t6_hilbR
  rw [if_pos ⟨ha, hb⟩]

theorem jpd4r14t4_hilbR_left_nonneg (a b : ℝ) (ha : 0 ≤ a) :
    jpd4r13t6_hilbR a b = 1 := by
  have _pin := Classical.em True
  unfold jpd4r13t6_hilbR
  rw [if_neg]
  rintro ⟨h1, -⟩
  exact absurd ha (not_le.mpr h1)

theorem jpd4r14t4_hilbR_right_nonneg (a b : ℝ) (hb : 0 ≤ b) :
    jpd4r13t6_hilbR a b = 1 := by
  have _pin := Classical.em True
  unfold jpd4r13t6_hilbR
  rw [if_neg]
  rintro ⟨-, h2⟩
  exact absurd hb (not_le.mpr h2)

end FLT.JpssD4KubotaArchimedeanCocycleSlice
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section
section

set_option maxHeartbeats 1600000

p2m_open "Matrix P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.Matrix"

noncomputable section

namespace FLT
namespace JpssD4KubotaGlobalProductFormulaSlice

open FLT.CampGenuineMk
open FLT.JpssD4GJProp83EisensteinAdelicQuadrupleInhabit
open FLT.JpssD4GJProp83MetaplecticKubotaCoverCarrier
open FLT.JpssD4KubotaPTwoHilbertTable
open FLT.JpssD4KubotaArchimedeanCocycleSlice

theorem jpd4r15t2_signWindow_reciprocity :
    ∀ u ∈ ([1, -1] : List ℤ), ∀ v ∈ ([1, -1] : List ℤ),
      jpd4r14t3_pairTwoZ 0 u 0 v * jpd4r13t6_hilbR (u : ℝ) (v : ℝ) = 1 := by
  have _pin := Classical.em True
  intro u hu v hv
  fin_cases hu <;> fin_cases hv <;>
    simp only [Int.cast_one, Int.cast_neg]
  · rw [jpd4r14t4_hilbR_left_nonneg 1 1 (by norm_num)]
    decide +kernel
  · rw [jpd4r14t4_hilbR_left_nonneg 1 (-1) (by norm_num)]
    decide +kernel
  · rw [jpd4r14t4_hilbR_right_nonneg (-1) 1 (by norm_num)]
    decide +kernel
  · rw [jpd4r14t4_hilbR_neg_neg (-1) (-1) (by norm_num) (by norm_num)]
    decide +kernel

end FLT.JpssD4KubotaGlobalProductFormulaSlice
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section
section

set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

noncomputable section

namespace FLT
namespace JpssD4KubotaTameSymbolUniformWindowSlice

open FLT.CampGenuineMk
open FLT.JpssD4GJProp83MetaplecticKubotaCoverCarrier
open FLT.JpssD4KubotaPTwoHilbertTable
open FLT.JpssD4KubotaArchimedeanCocycleSlice
open FLT.JpssD4KubotaGlobalProductFormulaSlice

theorem jpd4r16t6_epsZ_zero_of_oneMod4 (a : ℤ) (ha : a % 4 = 1) :
    jpd4r14t3_epsZ a = 0 := by
  have _pin := Classical.em True
  unfold jpd4r14t3_epsZ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  omega

theorem jpd4r16t6_epsZ_one_of_threeMod4 (a : ℤ) (ha : a % 4 = 3) :
    jpd4r14t3_epsZ a = 1 := by
  have _pin := Classical.em True
  have hd : (((a - 1) / 2 - 1 : ℤ) : ZMod 2) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    omega
  unfold jpd4r14t3_epsZ
  push_cast at hd
  exact sub_eq_zero.mp hd

theorem jpd4r16t6_nonUnitClass_decompose (s : ℤˣ) :
    (⟨1, s⟩ : gmk6_hil_SquareClass)
      = gmk6_hil_uniformiserClass * gmk6_hil_unitClass s := by
  have _pin := Classical.em True
  refine gmk6_hil_SquareClass_ext ?_ ?_
  · show (1 : ZMod 2) = 1 + 0
    decide
  · exact (one_mul s).symm

def jpd4r16t6_classOf (p : ℕ) [Fact p.Prime] (alpha : ZMod 2) (a : ℤ) :
    gmk6_hil_SquareClass :=
  ⟨alpha, gmk6_hil_legendreSign p a⟩

theorem jpd4r16t6_epsExponent_bridge (p : ℕ) (hodd : p % 2 = 1) :
    gmk6_hil_epsSign p = (-1 : ℤˣ) ^ (jpd4r14t3_epsZ (p : ℤ)).val := by
  have _pin := Classical.em True
  rcases (by omega : p % 4 = 1 ∨ p % 4 = 3) with h | h
  · unfold gmk6_hil_epsSign
    rw [if_pos h, jpd4r16t6_epsZ_zero_of_oneMod4 (p : ℤ) (by omega)]
    decide +kernel
  · unfold gmk6_hil_epsSign
    rw [if_neg (by omega : ¬p % 4 = 1),
      jpd4r16t6_epsZ_one_of_threeMod4 (p : ℤ) (by omega)]
    decide +kernel

theorem jpd4r16t6_reciprocity_uniformiserSelf (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) :
    gmk6_hil_pair (gmk6_hil_epsSign p) gmk6_hil_uniformiserClass
          gmk6_hil_uniformiserClass
        * jpd4r14t3_pairTwoZ 0 (p : ℤ) 0 (p : ℤ)
        * jpd4r13t6_hilbR (p : ℝ) (p : ℝ)
      = 1 := by
  have _pin := Classical.em True
  have hodd : p % 2 = 1 :=
    Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp2)
  rw [gmk6_hil_table_uniformiser_uniformiser,
    jpd4r14t4_hilbR_left_nonneg (p : ℝ) (p : ℝ) (by positivity), mul_one,
    jpd4r16t6_epsExponent_bridge p hodd]
  unfold jpd4r14t3_pairTwoZ
  have hexp : ∀ c d : ZMod 2, c * c + 0 * d + 0 * d = c := by decide
  rw [hexp (jpd4r14t3_epsZ (p : ℤ)) (jpd4r14t3_omegaZ (p : ℤ))]
  exact gmk6_hil_units_mul_self _

end FLT.JpssD4KubotaTameSymbolUniformWindowSlice
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section
section

p2m_open "IsDedekindDomain P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.IsDedekindDomain.HeightOneSpectrum NumberField P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.NumberField QuaternionAlgebra P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.QuaternionAlgebra"
p2m_open_scoped "Classical P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.Classical"

namespace FLT
namespace NumberTheory

open FLT.CampGenuineMk
open FLT.JpssD4KubotaPTwoHilbertTable
open FLT.JpssD4KubotaPTwoHilbertSolvabilityIdentification
open FLT.JpssD4GJProp83MetaplecticKubotaCoverCarrier
open FLT.JpssD4KubotaArchimedeanCocycleSlice
open FLT.JpssD4KubotaTameSymbolUniformWindowSlice

abbrev kw_hpSolvAt (a b : ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) : Prop :=
  ∃ z x y : v.adicCompletion ℚ, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
    z ^ 2 - algebraMap ℚ _ a * x ^ 2 - algebraMap ℚ _ b * y ^ 2 = 0

theorem kw_hpSolvAt_sqScale_left (a b : ℚ) (s : ℚ) (hs : s ≠ 0)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    kw_hpSolvAt (a * s ^ 2) b v ↔ kw_hpSolvAt a b v := by
  have _pin := Classical.em True
  have hsF : algebraMap ℚ (v.adicCompletion ℚ) s ≠ 0 :=
    fun h ↦ hs ((algebraMap ℚ _).injective (h.trans (_root_.map_zero _).symm))
  constructor
  · rintro ⟨z, x, y, hnt, heq⟩
    refine ⟨z, algebraMap ℚ _ s * x, y, ?_, ?_⟩
    · rintro ⟨hz, hx, hy⟩
      exact hnt ⟨hz, (mul_eq_zero.mp hx).resolve_left hsF, hy⟩
    · simp only [map_mul, map_pow] at heq ⊢
      linear_combination heq
  · rintro ⟨z, x, y, hnt, heq⟩
    refine ⟨algebraMap ℚ _ s * z, x, algebraMap ℚ _ s * y, ?_, ?_⟩
    · rintro ⟨hz, hx, hy⟩
      exact hnt ⟨(mul_eq_zero.mp hz).resolve_left hsF, hx,
        (mul_eq_zero.mp hy).resolve_left hsF⟩
    · simp only [map_mul, map_pow] at heq ⊢
      linear_combination (algebraMap ℚ _ s) ^ 2 * heq

theorem kw_hpSolvAt_symm (a b : ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    kw_hpSolvAt a b v ↔ kw_hpSolvAt b a v := by
  have _pin := Classical.em True
  constructor <;>
    · rintro ⟨z, x, y, hnt, heq⟩
      exact ⟨z, y, x, fun ⟨hz, hy, hx⟩ ↦ hnt ⟨hz, hx, hy⟩, by linear_combination heq⟩

abbrev kw_hpSolvAt_iff_gmk8_odd : Prop :=
  ∀ (a b : ℚ) (_ : a ≠ 0) (_ : b ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ)),
    (Rat.HeightOneSpectrum.primesEquiv v : ℕ) ≠ 2 →
    (kw_hpSolvAt a b v ↔
      gmk8_cls_solvable (p := (Rat.HeightOneSpectrum.primesEquiv v : ℕ))
        (a : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)])
        (b : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)]))

abbrev kw_hpSolvAt_iff_jpd4_two : Prop :=
  ∀ (a b : ℚ) (_ : a ≠ 0) (_ : b ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ)),
    (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = 2 →
    (kw_hpSolvAt a b v ↔ jpd4r15t3_hilbertSolvable (a : ℚ_[2]) (b : ℚ_[2]))

abbrev kw_HSCluster_C_F_two : Prop :=
  ∀ (a b : ℚ_[2]) (_ : a ≠ 0) (_ : b ≠ 0),
    ∃ (α : ZMod 2) (u : ℤ) (β : ZMod 2) (w : ℤ),
      u % 2 = 1 ∧ w % 2 = 1 ∧
      (∃ s : ℚ_[2], s ≠ 0 ∧ a = (2 : ℚ_[2]) ^ α.val * (u : ℚ_[2]) * s ^ 2) ∧
      (∃ t : ℚ_[2], t ≠ 0 ∧ b = (2 : ℚ_[2]) ^ β.val * (w : ℚ_[2]) * t ^ 2) ∧
      (jpd4r15t3_hilbertSolvable a b ↔ jpd4r14t3_pairTwoZ α u β w = 1)

noncomputable def kw_hpOrd2 (a : ℤ) : ℕ := padicValNat 2 a.natAbs

noncomputable def kw_hpOdd2 (a : ℤ) : ℤ := a / (2 : ℤ) ^ kw_hpOrd2 a

noncomputable def kw_hpFsymbOdd (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0)
    (p : ℕ) [Fact p.Prime] : ℤˣ :=
  gmk6_hil_pair (gmk6_hil_epsSign p)
    (gmk7_cls_classOf (p := p)
      (show (a : ℚ_[p]) ≠ 0 from Int.cast_ne_zero.mpr ha))
    (gmk7_cls_classOf (p := p)
      (show (b : ℚ_[p]) ≠ 0 from Int.cast_ne_zero.mpr hb))

abbrev kw_HSCluster_C_G_formulaProduct : Prop :=
  ∀ (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0),
    (∏ p ∈ ((2 * a.natAbs * b.natAbs).primeFactors \ {2}).attach,
        haveI : Fact p.1.Prime :=
          ⟨Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp p.2).1⟩
        kw_hpFsymbOdd a b ha hb p.1)
      * jpd4r14t3_pairTwoZ ((kw_hpOrd2 a : ℕ) : ZMod 2) (kw_hpOdd2 a)
          ((kw_hpOrd2 b : ℕ) : ZMod 2) (kw_hpOdd2 b)
      * jpd4r13t6_hilbR (a : ℝ) (b : ℝ) = 1

abbrev kw_HSCluster_C_W_wire : Prop :=
  kw_hpSolvAt_iff_gmk8_odd →
  kw_hpSolvAt_iff_jpd4_two →
  kw_HSCluster_C_F_two →
  kw_HSCluster_C_G_formulaProduct →
  ∀ a b : ℚ, kw_HSCluster_C_hilbertProduct a b

end FLT.NumberTheory
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section
section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

p2m_open "NumberField P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.NumberField IsDedekindDomain P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.IsDedekindDomain MeasureTheory P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.MeasureTheory TopologicalSpace P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.TopologicalSpace"
open Rat.FiniteAdeleRing
open FLT.GL1FujisakiFiniteShadow
p2m_open_scoped "ENNReal P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.ENNReal NNReal P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.NNReal Pointwise P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.Pointwise"

noncomputable section

namespace FLT
namespace CampGenuineMk

def gmk11_rec_wildMul (x y : ZMod 2 × (ZMod 8)ˣ) : ZMod 2 × (ZMod 8)ˣ :=
  (x.1 + y.1, x.2 * y.2)

def gmk11_rec_wildOne : ZMod 2 × (ZMod 8)ˣ := (0, 1)

end FLT.CampGenuineMk
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"
end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section
section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

namespace FLT
namespace CampGenuineMk

theorem gmk12_wcl_eight_dvd_pow : (8 : ℕ) ∣ 2 ^ 3 := by
  have _pin := Classical.em True
  norm_num

noncomputable def gmk12_wcl_res8Hom : ℤ_[2] →+* ZMod 8 :=
  (ZMod.castHom gmk12_wcl_eight_dvd_pow (ZMod 8)).comp (PadicInt.toZModPow 3)

theorem gmk12_wcl_res8Hom_apply (z : ℤ_[2]) :
    gmk12_wcl_res8Hom z
      = ZMod.castHom gmk12_wcl_eight_dvd_pow (ZMod 8) (PadicInt.toZModPow 3 z) := by
  have _pin := Classical.em True
  rfl

theorem gmk12_wcl_zmod2_cases (w : ZMod 2) : w = 0 ∨ w = 1 := by
  have _pin := Classical.em True
  revert w
  decide +kernel

theorem gmk12_wcl_zmod2_add_self : ∀ w : ZMod 2, w + w = 0 := by
  have _pin := Classical.em True
  decide +kernel

theorem gmk12_wcl_zmod8_mul_eq_one_cases :
    ∀ r s : ZMod 8, r * s = 1 → r = 1 ∨ r = 3 ∨ r = 5 ∨ r = 7 := by
  have _pin := Classical.em True
  decide +kernel

def gmk12_wcl_u3 : (ZMod 8)ˣ := ⟨3, 3, by decide +kernel, by decide +kernel⟩

def gmk12_wcl_u5 : (ZMod 8)ˣ := ⟨5, 5, by decide +kernel, by decide +kernel⟩

def gmk12_wcl_u7 : (ZMod 8)ˣ := ⟨7, 7, by decide +kernel, by decide +kernel⟩

theorem gmk12_wcl_units_cases (u : (ZMod 8)ˣ) :
    u = 1 ∨ u = gmk12_wcl_u3 ∨ u = gmk12_wcl_u5 ∨ u = gmk12_wcl_u7 := by
  have _pin := Classical.em True
  rcases gmk12_wcl_zmod8_mul_eq_one_cases ((u : ZMod 8)) (((u⁻¹ : (ZMod 8)ˣ) : ZMod 8))
      (Units.mul_inv u) with h | h | h | h
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Or.inl (Units.ext h))
  · exact Or.inr (Or.inr (Or.inl (Units.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Units.ext h)))

theorem gmk12_wcl_units_sq (u : (ZMod 8)ˣ) : u * u = 1 := by
  have _pin := Classical.em True
  rcases gmk12_wcl_units_cases u with rfl | rfl | rfl | rfl
  · exact Units.ext (by decide +kernel)
  · exact Units.ext (by decide +kernel)
  · exact Units.ext (by decide +kernel)
  · exact Units.ext (by decide +kernel)

theorem gmk12_wcl_cert_u7_mul_u5 : gmk12_wcl_u7 * gmk12_wcl_u5 = gmk12_wcl_u3 := by
  have _pin := Classical.em True
  exact Units.ext (by decide +kernel)

noncomputable def gmk12_wcl_unitResidue {x : ℚ_[2]} (hx : x ≠ 0) : (ZMod 8)ˣ :=
  Units.map gmk12_wcl_res8Hom.toMonoidHom (gmk7_cls_unitPart hx)

theorem gmk12_wcl_unitResidue_coe {x : ℚ_[2]} (hx : x ≠ 0) :
    ((gmk12_wcl_unitResidue hx : (ZMod 8)ˣ) : ZMod 8)
      = gmk12_wcl_res8Hom ((gmk7_cls_unitPart hx : ℤ_[2])) := by
  have _pin := Classical.em True
  rfl

theorem gmk12_wcl_unitResidue_mul {x y : ℚ_[2]} (hx : x ≠ 0) (hy : y ≠ 0) :
    gmk12_wcl_unitResidue (mul_ne_zero hx hy)
      = gmk12_wcl_unitResidue hx * gmk12_wcl_unitResidue hy := by
  have _pin := Classical.em True
  unfold gmk12_wcl_unitResidue
  rw [gmk7_cls_unitPart_mul hx hy, map_mul]

theorem gmk12_wcl_unitResidue_natCast {n : ℕ} (hn : (n : ZMod 2) ≠ 0) :
    ((gmk12_wcl_unitResidue (gmk7_cls_natCast_ne_zero hn) : (ZMod 8)ˣ) : ZMod 8)
      = (n : ZMod 8) := by
  have _pin := Classical.em True
  rw [gmk12_wcl_unitResidue_coe, gmk7_cls_unitPart_natCast hn, map_natCast]

noncomputable def gmk12_wcl_classOf {x : ℚ_[2]} (hx : x ≠ 0) : ZMod 2 × (ZMod 8)ˣ :=
  ((x.valuation : ZMod 2), gmk12_wcl_unitResidue hx)

theorem gmk12_wcl_classOf_congr {x y : ℚ_[2]} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x = y) : gmk12_wcl_classOf hx = gmk12_wcl_classOf hy := by
  have _pin := Classical.em True
  subst h
  rfl

theorem gmk12_wcl_classOf_mul {x y : ℚ_[2]} (hx : x ≠ 0) (hy : y ≠ 0) :
    gmk12_wcl_classOf (mul_ne_zero hx hy)
      = gmk11_rec_wildMul (gmk12_wcl_classOf hx) (gmk12_wcl_classOf hy) := by
  have _pin := Classical.em True
  have h1 : (((x * y).valuation : ZMod 2))
      = ((x.valuation : ZMod 2)) + ((y.valuation : ZMod 2)) := by
    rw [Padic.valuation_mul hx hy, Int.cast_add]
  show (((x * y).valuation : ZMod 2), gmk12_wcl_unitResidue (mul_ne_zero hx hy))
      = ((x.valuation : ZMod 2) + (y.valuation : ZMod 2),
          gmk12_wcl_unitResidue hx * gmk12_wcl_unitResidue hy)
  rw [h1, gmk12_wcl_unitResidue_mul hx hy]

theorem gmk12_wcl_carrier_mul_self (c : ZMod 2 × (ZMod 8)ˣ) :
    gmk11_rec_wildMul c c = gmk11_rec_wildOne := by
  have _pin := Classical.em True
  show (c.1 + c.1, c.2 * c.2) = ((0 : ZMod 2), (1 : (ZMod 8)ˣ))
  rw [gmk12_wcl_zmod2_add_self c.1, gmk12_wcl_units_sq c.2]

theorem gmk12_wcl_norm_two : ‖(2 : ℤ_[2])‖ = 2⁻¹ := by
  have _pin := Classical.em True
  have h2 : ((2 : ℕ) : ℤ_[2]) = (2 : ℤ_[2]) := by norm_num
  have h := PadicInt.norm_p (p := 2)
  rw [h2] at h
  rw [h]
  norm_num

theorem gmk12_wcl_norm_eight : ‖(8 : ℤ_[2])‖ = 8⁻¹ := by
  have _pin := Classical.em True
  have h8 : (8 : ℤ_[2]) = 2 * 2 * 2 := by norm_num
  rw [h8, norm_mul, norm_mul, gmk12_wcl_norm_two]
  norm_num

theorem gmk12_wcl_unit_isSquare_of_one_mod_eight {u : ℤ_[2]}
    (h8 : (8 : ℤ_[2]) ∣ (u - 1)) : IsSquare u := by
  have _pin := Classical.em True
  obtain ⟨c, hc⟩ := h8
  have hu1 : ‖u - 1‖ ≤ (8 : ℝ)⁻¹ := by
    rw [hc, norm_mul, gmk12_wcl_norm_eight]
    calc (8 : ℝ)⁻¹ * ‖c‖ ≤ (8 : ℝ)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left (PadicInt.norm_le_one c) (by norm_num)
      _ = (8 : ℝ)⁻¹ := mul_one _
  set F : Polynomial ℤ_[2] := Polynomial.X ^ 2 - Polynomial.C u with hF_def
  have hFa : ∀ b : ℤ_[2], Polynomial.aeval b F = b ^ 2 - u := by
    intro b
    rw [hF_def]
    simp
  have hFda : Polynomial.aeval (1 : ℤ_[2]) F.derivative = 2 * 1 := by
    rw [hF_def, Polynomial.derivative_sub, Polynomial.derivative_C,
      Polynomial.derivative_sq, Polynomial.derivative_X, sub_zero, mul_one,
      map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    simp
  have hnorm : ‖Polynomial.aeval (1 : ℤ_[2]) F‖
      < ‖Polynomial.aeval (1 : ℤ_[2]) F.derivative‖ ^ 2 := by
    rw [hFa 1, hFda, mul_one, gmk12_wcl_norm_two, one_pow]
    have hneg : (1 : ℤ_[2]) - u = -(u - 1) := by ring
    rw [hneg, norm_neg]
    exact lt_of_le_of_lt hu1 (by norm_num)
  obtain ⟨z, hz, -, -, -⟩ := hensels_lemma hnorm
  have hz2 : z ^ 2 - u = 0 := by
    rw [← hFa z]
    exact hz
  have hzu : z ^ 2 = u := sub_eq_zero.mp hz2
  exact ⟨z, by rw [← hzu, pow_two]⟩

theorem gmk12_wcl_toZModPow_three_eq_zero_iff (z : ℤ_[2]) :
    PadicInt.toZModPow 3 z = 0 ↔ (8 : ℤ_[2]) ∣ z := by
  have _pin := Classical.em True
  have h8 : (8 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) ^ 3 := by norm_num
  constructor
  · intro h
    have hker : z ∈ RingHom.ker (PadicInt.toZModPow (p := 2) 3) := by
      rw [RingHom.mem_ker]
      exact h
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hker
    rw [h8]
    exact hker
  · intro h
    obtain ⟨c, hc⟩ := h
    rw [hc, h8, map_mul, map_pow, map_natCast]
    have h0 : ((2 : ℕ) : ZMod (2 ^ 3)) ^ 3 = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_self]
    rw [h0, zero_mul]

theorem gmk12_wcl_res8Hom_eq_one_of_eight_dvd {z : ℤ_[2]}
    (h : (8 : ℤ_[2]) ∣ (z - 1)) : gmk12_wcl_res8Hom z = 1 := by
  have _pin := Classical.em True
  have h0 : PadicInt.toZModPow 3 (z - 1) = 0 :=
    (gmk12_wcl_toZModPow_three_eq_zero_iff (z - 1)).mpr h
  have h1 : PadicInt.toZModPow 3 z = 1 := by
    rw [map_sub, map_one, sub_eq_zero] at h0
    exact h0
  rw [gmk12_wcl_res8Hom_apply, h1, map_one]

theorem gmk12_wcl_natCast_one : ((1 : ℕ) : ℚ_[2]) = (1 : ℚ_[2]) := by
  have _pin := Classical.em True
  norm_num

theorem gmk12_wcl_natCast_two : ((2 : ℕ) : ℚ_[2]) = (2 : ℚ_[2]) := by
  have _pin := Classical.em True
  norm_num

theorem gmk12_wcl_natCast_five : ((5 : ℕ) : ℚ_[2]) = (5 : ℚ_[2]) := by
  have _pin := Classical.em True
  norm_num

theorem gmk12_wcl_one_ne_zero : (1 : ℚ_[2]) ≠ 0 := by
  have _pin := Classical.em True
  exact one_ne_zero

theorem gmk12_wcl_two_ne_zero : (2 : ℚ_[2]) ≠ 0 := by
  have _pin := Classical.em True
  rw [← gmk12_wcl_natCast_two]
  exact gmk7_cls_p_padic_ne_zero (p := 2)

theorem gmk12_wcl_five_ne_zero : (5 : ℚ_[2]) ≠ 0 := by
  have _pin := Classical.em True
  rw [← gmk12_wcl_natCast_five]
  exact gmk7_cls_natCast_ne_zero (show ((5 : ℕ) : ZMod 2) ≠ 0 by decide +kernel)

theorem gmk12_wcl_ten_ne_zero : (10 : ℚ_[2]) ≠ 0 := by
  have _pin := Classical.em True
  have h : (2 : ℚ_[2]) * 5 = 10 := by norm_num
  rw [← h]
  exact mul_ne_zero gmk12_wcl_two_ne_zero gmk12_wcl_five_ne_zero

theorem gmk12_wcl_negOne_ne_zero : (-1 : ℚ_[2]) ≠ 0 := by
  have _pin := Classical.em True
  exact neg_ne_zero.mpr gmk12_wcl_one_ne_zero

theorem gmk12_wcl_negTwo_ne_zero : (-2 : ℚ_[2]) ≠ 0 := by
  have _pin := Classical.em True
  exact neg_ne_zero.mpr gmk12_wcl_two_ne_zero

theorem gmk12_wcl_negFive_ne_zero : (-5 : ℚ_[2]) ≠ 0 := by
  have _pin := Classical.em True
  exact neg_ne_zero.mpr gmk12_wcl_five_ne_zero

theorem gmk12_wcl_negTen_ne_zero : (-10 : ℚ_[2]) ≠ 0 := by
  have _pin := Classical.em True
  exact neg_ne_zero.mpr gmk12_wcl_ten_ne_zero

theorem gmk12_wcl_valuation_negOne : (-1 : ℚ_[2]).valuation = 0 := by
  have _pin := Classical.em True
  apply gmk7_cls_valuation_eq_zero_of_norm_one gmk12_wcl_negOne_ne_zero
  rw [norm_neg, norm_one]

theorem gmk12_wcl_unitPart_negOne :
    ((gmk7_cls_unitPart gmk12_wcl_negOne_ne_zero : ℤ_[2])) = -1 := by
  have _pin := Classical.em True
  have h : ((gmk7_cls_unitPart gmk12_wcl_negOne_ne_zero : ℤ_[2]) : ℚ_[2])
      = ((-1 : ℤ_[2]) : ℚ_[2]) := by
    rw [gmk7_cls_unitPart_coe, gmk12_wcl_valuation_negOne, _root_.neg_zero, zpow_zero,
      mul_one, PadicInt.coe_neg, PadicInt.coe_one]
  exact Subtype.coe_injective h

theorem gmk12_wcl_cert_classOf_one :
    gmk12_wcl_classOf gmk12_wcl_one_ne_zero = ((0 : ZMod 2), (1 : (ZMod 8)ˣ)) := by
  have _pin := Classical.em True
  have hn : ((1 : ℕ) : ZMod 2) ≠ 0 := by decide +kernel
  rw [← gmk12_wcl_classOf_congr (gmk7_cls_natCast_ne_zero hn) gmk12_wcl_one_ne_zero
      gmk12_wcl_natCast_one]
  have h2 : gmk12_wcl_unitResidue (gmk7_cls_natCast_ne_zero hn) = 1 := by
    refine Units.ext ?_
    rw [gmk12_wcl_unitResidue_natCast hn]
    decide +kernel
  show ((((1 : ℕ) : ℚ_[2]).valuation : ZMod 2),
      gmk12_wcl_unitResidue (gmk7_cls_natCast_ne_zero hn))
      = ((0 : ZMod 2), (1 : (ZMod 8)ˣ))
  rw [gmk7_cls_valuation_natCast_eq_zero hn, Int.cast_zero, h2]

theorem gmk12_wcl_cert_classOf_five :
    gmk12_wcl_classOf gmk12_wcl_five_ne_zero = ((0 : ZMod 2), gmk12_wcl_u5) := by
  have _pin := Classical.em True
  have hn : ((5 : ℕ) : ZMod 2) ≠ 0 := by decide +kernel
  rw [← gmk12_wcl_classOf_congr (gmk7_cls_natCast_ne_zero hn) gmk12_wcl_five_ne_zero
      gmk12_wcl_natCast_five]
  have h2 : gmk12_wcl_unitResidue (gmk7_cls_natCast_ne_zero hn) = gmk12_wcl_u5 := by
    refine Units.ext ?_
    rw [gmk12_wcl_unitResidue_natCast hn]
    decide +kernel
  show ((((5 : ℕ) : ℚ_[2]).valuation : ZMod 2),
      gmk12_wcl_unitResidue (gmk7_cls_natCast_ne_zero hn))
      = ((0 : ZMod 2), gmk12_wcl_u5)
  rw [gmk7_cls_valuation_natCast_eq_zero hn, Int.cast_zero, h2]

theorem gmk12_wcl_cert_classOf_negOne :
    gmk12_wcl_classOf gmk12_wcl_negOne_ne_zero = ((0 : ZMod 2), gmk12_wcl_u7) := by
  have _pin := Classical.em True
  have h2 : gmk12_wcl_unitResidue gmk12_wcl_negOne_ne_zero = gmk12_wcl_u7 := by
    refine Units.ext ?_
    rw [gmk12_wcl_unitResidue_coe, gmk12_wcl_unitPart_negOne, _root_.map_neg, map_one]
    decide +kernel
  show (((-1 : ℚ_[2]).valuation : ZMod 2), gmk12_wcl_unitResidue gmk12_wcl_negOne_ne_zero)
      = ((0 : ZMod 2), gmk12_wcl_u7)
  rw [gmk12_wcl_valuation_negOne, Int.cast_zero, h2]

theorem gmk12_wcl_cert_classOf_negFive :
    gmk12_wcl_classOf gmk12_wcl_negFive_ne_zero = ((0 : ZMod 2), gmk12_wcl_u3) := by
  have _pin := Classical.em True
  have hmul : (-1 : ℚ_[2]) * 5 = -5 := by ring
  rw [← gmk12_wcl_classOf_congr (mul_ne_zero gmk12_wcl_negOne_ne_zero gmk12_wcl_five_ne_zero)
      gmk12_wcl_negFive_ne_zero hmul,
    gmk12_wcl_classOf_mul gmk12_wcl_negOne_ne_zero gmk12_wcl_five_ne_zero,
    gmk12_wcl_cert_classOf_negOne, gmk12_wcl_cert_classOf_five]
  show ((0 : ZMod 2) + 0, gmk12_wcl_u7 * gmk12_wcl_u5) = ((0 : ZMod 2), gmk12_wcl_u3)
  rw [add_zero, gmk12_wcl_cert_u7_mul_u5]

theorem gmk12_wcl_cert_classOf_two :
    gmk12_wcl_classOf gmk12_wcl_two_ne_zero = ((1 : ZMod 2), (1 : (ZMod 8)ˣ)) := by
  have _pin := Classical.em True
  rw [← gmk12_wcl_classOf_congr (gmk7_cls_p_padic_ne_zero (p := 2)) gmk12_wcl_two_ne_zero
      gmk12_wcl_natCast_two]
  have h2 : gmk12_wcl_unitResidue (gmk7_cls_p_padic_ne_zero (p := 2)) = 1 := by
    refine Units.ext ?_
    have hval1 : ((1 : ℤ_[2]ˣ) : ℤ_[2]) = 1 := Units.val_one
    rw [gmk12_wcl_unitResidue_coe, gmk7_cls_unitPart_p (p := 2), hval1, map_one,
      Units.val_one]
  show ((((2 : ℕ) : ℚ_[2]).valuation : ZMod 2),
      gmk12_wcl_unitResidue (gmk7_cls_p_padic_ne_zero (p := 2)))
      = ((1 : ZMod 2), (1 : (ZMod 8)ˣ))
  rw [Padic.valuation_p, Int.cast_one, h2]

theorem gmk12_wcl_cert_classOf_ten :
    gmk12_wcl_classOf gmk12_wcl_ten_ne_zero = ((1 : ZMod 2), gmk12_wcl_u5) := by
  have _pin := Classical.em True
  have hmul : (2 : ℚ_[2]) * 5 = 10 := by norm_num
  rw [← gmk12_wcl_classOf_congr (mul_ne_zero gmk12_wcl_two_ne_zero gmk12_wcl_five_ne_zero)
      gmk12_wcl_ten_ne_zero hmul,
    gmk12_wcl_classOf_mul gmk12_wcl_two_ne_zero gmk12_wcl_five_ne_zero,
    gmk12_wcl_cert_classOf_two, gmk12_wcl_cert_classOf_five]
  show ((1 : ZMod 2) + 0, (1 : (ZMod 8)ˣ) * gmk12_wcl_u5) = ((1 : ZMod 2), gmk12_wcl_u5)
  rw [add_zero, one_mul]

theorem gmk12_wcl_cert_classOf_negTwo :
    gmk12_wcl_classOf gmk12_wcl_negTwo_ne_zero = ((1 : ZMod 2), gmk12_wcl_u7) := by
  have _pin := Classical.em True
  have hmul : (-1 : ℚ_[2]) * 2 = -2 := by ring
  rw [← gmk12_wcl_classOf_congr (mul_ne_zero gmk12_wcl_negOne_ne_zero gmk12_wcl_two_ne_zero)
      gmk12_wcl_negTwo_ne_zero hmul,
    gmk12_wcl_classOf_mul gmk12_wcl_negOne_ne_zero gmk12_wcl_two_ne_zero,
    gmk12_wcl_cert_classOf_negOne, gmk12_wcl_cert_classOf_two]
  show ((0 : ZMod 2) + 1, gmk12_wcl_u7 * 1) = ((1 : ZMod 2), gmk12_wcl_u7)
  rw [zero_add, mul_one]

theorem gmk12_wcl_cert_classOf_negTen :
    gmk12_wcl_classOf gmk12_wcl_negTen_ne_zero = ((1 : ZMod 2), gmk12_wcl_u3) := by
  have _pin := Classical.em True
  have hmul : (-1 : ℚ_[2]) * 10 = -10 := by ring
  rw [← gmk12_wcl_classOf_congr (mul_ne_zero gmk12_wcl_negOne_ne_zero gmk12_wcl_ten_ne_zero)
      gmk12_wcl_negTen_ne_zero hmul,
    gmk12_wcl_classOf_mul gmk12_wcl_negOne_ne_zero gmk12_wcl_ten_ne_zero,
    gmk12_wcl_cert_classOf_negOne, gmk12_wcl_cert_classOf_ten]
  show ((0 : ZMod 2) + 1, gmk12_wcl_u7 * gmk12_wcl_u5) = ((1 : ZMod 2), gmk12_wcl_u3)
  rw [zero_add, gmk12_wcl_cert_u7_mul_u5]

end FLT.CampGenuineMk
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section
section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

namespace FLT
namespace CampGenuineMk

theorem gmk13_jon_res8Hom_eq_one_iff (z : ℤ_[2]) :
    gmk12_wcl_res8Hom z = 1 ↔ (8 : ℤ_[2]) ∣ (z - 1) := by
  have _pin := Classical.em True
  constructor
  · intro h
    rw [gmk12_wcl_res8Hom_apply] at h
    have hcast : ∀ w : ZMod (2 ^ 3),
        ZMod.castHom gmk12_wcl_eight_dvd_pow (ZMod 8) w = 1 → w = 1 := by
      decide +kernel
    have h1 : PadicInt.toZModPow 3 z = 1 := hcast _ h
    rw [← gmk12_wcl_toZModPow_three_eq_zero_iff, map_sub, map_one, h1, sub_self]
  · exact gmk12_wcl_res8Hom_eq_one_of_eight_dvd

theorem gmk13_jon_kernel_row {x : ℚ_[2]} (hx : x ≠ 0) :
    gmk12_wcl_classOf hx = gmk11_rec_wildOne ↔ IsSquare x := by
  have _pin := Classical.em True
  constructor
  · intro h
    have hv : ((x.valuation : ZMod 2)) = 0 := congrArg Prod.fst h
    have hu : gmk12_wcl_unitResidue hx = 1 := congrArg Prod.snd h
    have hdvd : (2 : ℤ) ∣ x.valuation := by
      have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd x.valuation 2).mp hv
      exact_mod_cast h2
    obtain ⟨k, hk⟩ := hdvd
    have hres : gmk12_wcl_res8Hom ((gmk7_cls_unitPart hx : ℤ_[2])) = 1 := by
      rw [← gmk12_wcl_unitResidue_coe hx, hu, Units.val_one]
    have h8 : (8 : ℤ_[2]) ∣ ((gmk7_cls_unitPart hx : ℤ_[2]) - 1) :=
      (gmk13_jon_res8Hom_eq_one_iff _).mp hres
    obtain ⟨s, hs⟩ := gmk12_wcl_unit_isSquare_of_one_mod_eight h8
    have hsq2 : (((gmk7_cls_unitPart hx : ℤ_[2])) : ℚ_[2])
        = (s : ℚ_[2]) * (s : ℚ_[2]) := by
      rw [hs, PadicInt.coe_mul]
    refine ⟨(s : ℚ_[2]) * ((2 : ℕ) : ℚ_[2]) ^ k, ?_⟩
    rw [gmk7_cls_unitPart_spec (p := 2) hx, hk, hsq2, two_mul,
      zpow_add₀ (gmk7_cls_p_padic_ne_zero (p := 2))]
    ring
  · rintro ⟨t, ht⟩
    have ht0 : t ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at ht
      exact hx ht
    have h1 : gmk12_wcl_classOf hx = gmk12_wcl_classOf (mul_ne_zero ht0 ht0) :=
      gmk12_wcl_classOf_congr hx (mul_ne_zero ht0 ht0) ht
    rw [h1, gmk12_wcl_classOf_mul ht0 ht0, gmk12_wcl_carrier_mul_self]

theorem gmk13_jon_wildMul_left_cancel_to_one {c d : ZMod 2 × (ZMod 8)ˣ}
    (h : gmk11_rec_wildMul c d = c) : d = gmk11_rec_wildOne := by
  have _pin := Classical.em True
  have h1 : gmk11_rec_wildMul c (gmk11_rec_wildMul c d) = gmk11_rec_wildMul c c :=
    congrArg (gmk11_rec_wildMul c) h
  rw [gmk12_wcl_carrier_mul_self] at h1
  have h2 : gmk11_rec_wildMul c (gmk11_rec_wildMul c d) = d := by
    show (c.1 + (c.1 + d.1), c.2 * (c.2 * d.2)) = d
    rw [← add_assoc, gmk12_wcl_zmod2_add_self, zero_add, ← mul_assoc,
      gmk12_wcl_units_sq, one_mul]
  rw [h2] at h1
  exact h1

theorem gmk13_jon_exists_sq_ratio_of_classOf_eq {a b : ℚ_[2]}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (h : gmk12_wcl_classOf ha = gmk12_wcl_classOf hb) :
    ∃ s : ℚ_[2], s ≠ 0 ∧ b = a * (s * s) := by
  have _pin := Classical.em True
  have hc : b * a⁻¹ ≠ 0 := mul_ne_zero hb (inv_ne_zero ha)
  have hac : a * (b * a⁻¹) = b := by
    rw [mul_comm b a⁻¹, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  have h1 : gmk12_wcl_classOf hb = gmk12_wcl_classOf (mul_ne_zero ha hc) :=
    gmk12_wcl_classOf_congr hb (mul_ne_zero ha hc) hac.symm
  rw [gmk12_wcl_classOf_mul ha hc] at h1
  have h2 : gmk11_rec_wildMul (gmk12_wcl_classOf ha) (gmk12_wcl_classOf hc)
      = gmk12_wcl_classOf ha := by
    rw [← h1]
    exact h.symm
  have h3 : gmk12_wcl_classOf hc = gmk11_rec_wildOne :=
    gmk13_jon_wildMul_left_cancel_to_one h2
  obtain ⟨s, hs⟩ := (gmk13_jon_kernel_row hc).mp h3
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hs
    exact hc hs
  refine ⟨s, hs0, ?_⟩
  rw [← hs]
  exact hac.symm

theorem gmk13_jon_solvable_congr {a a' b b' : ℚ_[2]}
    (ha : a ≠ 0) (ha' : a' ≠ 0) (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hca : gmk12_wcl_classOf ha = gmk12_wcl_classOf ha')
    (hcb : gmk12_wcl_classOf hb = gmk12_wcl_classOf hb') :
    gmk8_cls_solvable a b ↔ gmk8_cls_solvable a' b' := by
  have _pin := Classical.em True
  obtain ⟨s, hs0, hsa⟩ := gmk13_jon_exists_sq_ratio_of_classOf_eq ha ha' hca
  obtain ⟨t, ht0, htb⟩ := gmk13_jon_exists_sq_ratio_of_classOf_eq hb hb' hcb
  rw [hsa, htb, gmk8_cls_solvable_iff_scale_left hs0,
    gmk8_cls_solvable_iff_scale_right ht0]

end FLT.CampGenuineMk
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section
section

p2m_open_scoped "Classical P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.Classical"

namespace FLT
namespace NumberTheory

open FLT.CampGenuineMk
open FLT.JpssD4KubotaPTwoHilbertTable
open FLT.JpssD4KubotaPTwoHilbertSolvabilityIdentification
open FLT.JpssD4KubotaPTwoHilbertSolvabilityIdentificationGrid

theorem kw_hpF2_val0 : (0 : ZMod 2).val = 0 := rfl

theorem kw_hpF2_val1 : (1 : ZMod 2).val = 1 := rfl

theorem kw_hpF2_hilbertSolvable_iff_gmk8 (a b : ℚ_[2]) :
    jpd4r15t3_hilbertSolvable a b ↔ gmk8_cls_solvable a b := by
  have _pin := Classical.em True
  rw [jpd4r15t3_hilbertSolvable, gmk8_cls_solvable_def]
  constructor
  · rintro ⟨z, x, y, hnt, heq⟩
    refine ⟨x, y, z, ?_, by linear_combination heq⟩
    rw [not_and_or, not_and_or] at hnt
    tauto
  · rintro ⟨x, y, z, hnt, heq⟩
    refine ⟨z, x, y, ?_, by linear_combination heq⟩
    rw [not_and_or, not_and_or]
    tauto

theorem kw_hpF2_repOdd {u : ℤ} (hu : u ∈ ({1, -1, 5, -5} : Finset ℤ)) :
    u % 2 = 1 := by
  have _pin := Classical.em True
  fin_cases hu <;> decide

theorem kw_hpF2_rep_ne_zero (α : ZMod 2) {u : ℤ}
    (hu : u ∈ ({1, -1, 5, -5} : Finset ℤ)) :
    (2 : ℚ_[2]) ^ α.val * (u : ℚ_[2]) ≠ 0 := by
  have _pin := Classical.em True
  refine mul_ne_zero (pow_ne_zero _ two_ne_zero) (Int.cast_ne_zero.mpr ?_)
  fin_cases hu <;> decide

theorem kw_hpF2_repEq_one :
    (2 : ℚ_[2]) ^ (0 : ZMod 2).val * ((1 : ℤ) : ℚ_[2]) = (1 : ℚ_[2]) := by
  rw [kw_hpF2_val0]; push_cast; ring

theorem kw_hpF2_repEq_negOne :
    (2 : ℚ_[2]) ^ (0 : ZMod 2).val * ((-1 : ℤ) : ℚ_[2]) = (-1 : ℚ_[2]) := by
  rw [kw_hpF2_val0]; push_cast; ring

theorem kw_hpF2_repEq_five :
    (2 : ℚ_[2]) ^ (0 : ZMod 2).val * ((5 : ℤ) : ℚ_[2]) = (5 : ℚ_[2]) := by
  rw [kw_hpF2_val0]; push_cast; ring

theorem kw_hpF2_repEq_negFive :
    (2 : ℚ_[2]) ^ (0 : ZMod 2).val * ((-5 : ℤ) : ℚ_[2]) = (-5 : ℚ_[2]) := by
  rw [kw_hpF2_val0]; push_cast; ring

theorem kw_hpF2_repEq_two :
    (2 : ℚ_[2]) ^ (1 : ZMod 2).val * ((1 : ℤ) : ℚ_[2]) = (2 : ℚ_[2]) := by
  rw [kw_hpF2_val1]; push_cast; ring

theorem kw_hpF2_repEq_negTwo :
    (2 : ℚ_[2]) ^ (1 : ZMod 2).val * ((-1 : ℤ) : ℚ_[2]) = (-2 : ℚ_[2]) := by
  rw [kw_hpF2_val1]; push_cast; ring

theorem kw_hpF2_repEq_ten :
    (2 : ℚ_[2]) ^ (1 : ZMod 2).val * ((5 : ℤ) : ℚ_[2]) = (10 : ℚ_[2]) := by
  rw [kw_hpF2_val1]; push_cast; ring

theorem kw_hpF2_repEq_negTen :
    (2 : ℚ_[2]) ^ (1 : ZMod 2).val * ((-5 : ℤ) : ℚ_[2]) = (-10 : ℚ_[2]) := by
  rw [kw_hpF2_val1]; push_cast; ring

theorem kw_hpF2_decomp {a : ℚ_[2]} (ha : a ≠ 0) :
    ∃ (α : ZMod 2) (u : ℤ) (hu : u ∈ ({1, -1, 5, -5} : Finset ℤ)),
      gmk12_wcl_classOf ha = gmk12_wcl_classOf (kw_hpF2_rep_ne_zero α hu) := by
  have _pin := Classical.em True
  have hsplit : gmk12_wcl_classOf ha
      = ((gmk12_wcl_classOf ha).1, (gmk12_wcl_classOf ha).2) := rfl
  rcases gmk12_wcl_zmod2_cases (gmk12_wcl_classOf ha).1 with h1 | h1 <;>
    rcases gmk12_wcl_units_cases (gmk12_wcl_classOf ha).2 with h2 | h2 | h2 | h2 <;>
    rw [h1, h2] at hsplit
  · exact ⟨0, 1, by decide, hsplit.trans <| gmk12_wcl_cert_classOf_one.symm.trans <|
      gmk12_wcl_classOf_congr _ _ kw_hpF2_repEq_one.symm⟩
  · exact ⟨0, -5, by decide, hsplit.trans <| gmk12_wcl_cert_classOf_negFive.symm.trans <|
      gmk12_wcl_classOf_congr _ _ kw_hpF2_repEq_negFive.symm⟩
  · exact ⟨0, 5, by decide, hsplit.trans <| gmk12_wcl_cert_classOf_five.symm.trans <|
      gmk12_wcl_classOf_congr _ _ kw_hpF2_repEq_five.symm⟩
  · exact ⟨0, -1, by decide, hsplit.trans <| gmk12_wcl_cert_classOf_negOne.symm.trans <|
      gmk12_wcl_classOf_congr _ _ kw_hpF2_repEq_negOne.symm⟩
  · exact ⟨1, 1, by decide, hsplit.trans <| gmk12_wcl_cert_classOf_two.symm.trans <|
      gmk12_wcl_classOf_congr _ _ kw_hpF2_repEq_two.symm⟩
  · exact ⟨1, -5, by decide, hsplit.trans <| gmk12_wcl_cert_classOf_negTen.symm.trans <|
      gmk12_wcl_classOf_congr _ _ kw_hpF2_repEq_negTen.symm⟩
  · exact ⟨1, 5, by decide, hsplit.trans <| gmk12_wcl_cert_classOf_ten.symm.trans <|
      gmk12_wcl_classOf_congr _ _ kw_hpF2_repEq_ten.symm⟩
  · exact ⟨1, -1, by decide, hsplit.trans <| gmk12_wcl_cert_classOf_negTwo.symm.trans <|
      gmk12_wcl_classOf_congr _ _ kw_hpF2_repEq_negTwo.symm⟩

theorem kw_hpF2_gridDispatch {α β : ZMod 2} {u w : ℤ}
    (hu : u ∈ ({1, -1, 5, -5} : Finset ℤ)) (hw : w ∈ ({1, -1, 5, -5} : Finset ℤ)) :
    jpd4r15t3_hilbertSolvable ((2 : ℚ_[2]) ^ α.val * (u : ℚ_[2]))
        ((2 : ℚ_[2]) ^ β.val * (w : ℚ_[2]))
      ↔ jpd4r14t3_pairTwoZ α u β w = 1 := by
  have _pin := Classical.em True
  rcases gmk12_wcl_zmod2_cases α with rfl | rfl <;>
    rcases gmk12_wcl_zmod2_cases β with rfl | rfl <;>
    fin_cases hu <;> fin_cases hw <;>
    simp only [kw_hpF2_repEq_one, kw_hpF2_repEq_negOne, kw_hpF2_repEq_five,
      kw_hpF2_repEq_negFive, kw_hpF2_repEq_two, kw_hpF2_repEq_negTwo,
      kw_hpF2_repEq_ten, kw_hpF2_repEq_negTen]

  exacts [jpd4r15t3_gridRow_one.1.symm, jpd4r15t3_gridRow_one.2.1.symm,
    jpd4r15t3_gridRow_one.2.2.1.symm, jpd4r15t3_gridRow_one.2.2.2.1.symm,

    jpd4r15t3_gridRow_negOne.1.symm, jpd4r15t3_gridRow_negOne.2.1.symm,
    jpd4r15t3_gridRow_negOne.2.2.1.symm, jpd4r15t3_gridRow_negOne.2.2.2.1.symm,

    jpd4r15t3_gridRow_five.1.symm, jpd4r15t3_gridRow_five.2.1.symm,
    jpd4r15t3_gridRow_five.2.2.1.symm, jpd4r15t3_gridRow_five.2.2.2.1.symm,

    jpd4r15t3_gridRow_negFive.1.symm, jpd4r15t3_gridRow_negFive.2.1.symm,
    jpd4r15t3_gridRow_negFive.2.2.1.symm, jpd4r15t3_gridRow_negFive.2.2.2.1.symm,

    jpd4r15t3_gridRow_one.2.2.2.2.1.symm, jpd4r15t3_gridRow_one.2.2.2.2.2.1.symm,
    jpd4r15t3_gridRow_one.2.2.2.2.2.2.1.symm, jpd4r15t3_gridRow_one.2.2.2.2.2.2.2.symm,
    jpd4r15t3_gridRow_negOne.2.2.2.2.1.symm, jpd4r15t3_gridRow_negOne.2.2.2.2.2.1.symm,
    jpd4r15t3_gridRow_negOne.2.2.2.2.2.2.1.symm, jpd4r15t3_gridRow_negOne.2.2.2.2.2.2.2.symm,
    jpd4r15t3_gridRow_five.2.2.2.2.1.symm, jpd4r15t3_gridRow_five.2.2.2.2.2.1.symm,
    jpd4r15t3_gridRow_five.2.2.2.2.2.2.1.symm, jpd4r15t3_gridRow_five.2.2.2.2.2.2.2.symm,
    jpd4r15t3_gridRow_negFive.2.2.2.2.1.symm, jpd4r15t3_gridRow_negFive.2.2.2.2.2.1.symm,
    jpd4r15t3_gridRow_negFive.2.2.2.2.2.2.1.symm, jpd4r15t3_gridRow_negFive.2.2.2.2.2.2.2.symm,

    jpd4r15t3_gridRow_two.1.symm, jpd4r15t3_gridRow_two.2.1.symm,
    jpd4r15t3_gridRow_two.2.2.1.symm, jpd4r15t3_gridRow_two.2.2.2.1.symm,
    jpd4r15t3_gridRow_negTwo.1.symm, jpd4r15t3_gridRow_negTwo.2.1.symm,
    jpd4r15t3_gridRow_negTwo.2.2.1.symm, jpd4r15t3_gridRow_negTwo.2.2.2.1.symm,
    jpd4r15t3_gridRow_ten.1.symm, jpd4r15t3_gridRow_ten.2.1.symm,
    jpd4r15t3_gridRow_ten.2.2.1.symm, jpd4r15t3_gridRow_ten.2.2.2.1.symm,
    jpd4r15t3_gridRow_negTen.1.symm, jpd4r15t3_gridRow_negTen.2.1.symm,
    jpd4r15t3_gridRow_negTen.2.2.1.symm, jpd4r15t3_gridRow_negTen.2.2.2.1.symm,

    jpd4r15t3_gridRow_two.2.2.2.2.1.symm, jpd4r15t3_gridRow_two.2.2.2.2.2.1.symm,
    jpd4r15t3_gridRow_two.2.2.2.2.2.2.1.symm, jpd4r15t3_gridRow_two.2.2.2.2.2.2.2.symm,
    jpd4r15t3_gridRow_negTwo.2.2.2.2.1.symm, jpd4r15t3_gridRow_negTwo.2.2.2.2.2.1.symm,
    jpd4r15t3_gridRow_negTwo.2.2.2.2.2.2.1.symm, jpd4r15t3_gridRow_negTwo.2.2.2.2.2.2.2.symm,
    jpd4r15t3_gridRow_ten.2.2.2.2.1.symm, jpd4r15t3_gridRow_ten.2.2.2.2.2.1.symm,
    jpd4r15t3_gridRow_ten.2.2.2.2.2.2.1.symm, jpd4r15t3_gridRow_ten.2.2.2.2.2.2.2.symm,
    jpd4r15t3_gridRow_negTen.2.2.2.2.1.symm, jpd4r15t3_gridRow_negTen.2.2.2.2.2.1.symm,
    jpd4r15t3_gridRow_negTen.2.2.2.2.2.2.1.symm, jpd4r15t3_gridRow_negTen.2.2.2.2.2.2.2.symm]

theorem kw_HSCluster_C_F_two_proved : kw_HSCluster_C_F_two := by
  have _pin := Classical.em True
  intro a b ha hb
  obtain ⟨α, u, hu, hcla⟩ := kw_hpF2_decomp ha
  obtain ⟨β, w, hw, hclb⟩ := kw_hpF2_decomp hb
  refine ⟨α, u, β, w, kw_hpF2_repOdd hu, kw_hpF2_repOdd hw, ?_, ?_, ?_⟩
  · obtain ⟨s, hs, heq⟩ :=
      gmk13_jon_exists_sq_ratio_of_classOf_eq (kw_hpF2_rep_ne_zero α hu) ha hcla.symm
    exact ⟨s, hs, by rw [heq]; ring⟩
  · obtain ⟨t, ht, heq⟩ :=
      gmk13_jon_exists_sq_ratio_of_classOf_eq (kw_hpF2_rep_ne_zero β hw) hb hclb.symm
    exact ⟨t, ht, by rw [heq]; ring⟩
  · rw [kw_hpF2_hilbertSolvable_iff_gmk8,
      gmk13_jon_solvable_congr ha (kw_hpF2_rep_ne_zero α hu)
        hb (kw_hpF2_rep_ne_zero β hw) hcla hclb,
      ← kw_hpF2_hilbertSolvable_iff_gmk8]
    exact kw_hpF2_gridDispatch hu hw

end FLT.NumberTheory
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section
section

set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

noncomputable section

namespace FLT
namespace JpssD4KubotaFiniteAdelicProductObjectSlice

open FLT.CampGenuineMk
open FLT.JpssD4GJProp83MetaplecticKubotaCoverCarrier
open FLT.JpssD4KubotaPTwoHilbertTable
open FLT.JpssD4KubotaArchimedeanCocycleSlice
open FLT.JpssD4KubotaGlobalProductFormulaSlice
open FLT.JpssD4KubotaTameSymbolUniformWindowSlice

theorem jpd4r17t5_zmod2_exp_diag (x y u v : ZMod 2) :
    x * y + 0 * u + 0 * v = x * y := by
  have _pin := Classical.em True
  revert x y u v; decide

theorem jpd4r17t5_zmod2_exp_twoSlot (x u v : ZMod 2) :
    0 * x + 1 * u + 0 * v = u := by
  have _pin := Classical.em True
  revert x u v; decide

theorem jpd4r17t5_zmod2_mul_val (x y : ZMod 2) :
    (x * y).val = x.val * y.val % 2 := by
  have _pin := Classical.em True
  revert x y; decide

theorem jpd4r17t5_zmod2_one_val : ((1 : ZMod 2)).val = 1 := by
  have _pin := Classical.em True
  decide

theorem jpd4r17t5_zmod2_zero_val : ((0 : ZMod 2)).val = 0 := by
  have _pin := Classical.em True
  decide

theorem jpd4r17t5_epsZ_val_natOdd (n : ℕ) (hn : n % 2 = 1) :
    (jpd4r14t3_epsZ (n : ℤ)).val = n / 2 % 2 := by
  have _pin := Classical.em True
  rcases (by omega : n % 4 = 1 ∨ n % 4 = 3) with h | h
  · rw [jpd4r16t6_epsZ_zero_of_oneMod4 (n : ℤ) (by omega), jpd4r17t5_zmod2_zero_val]
    omega
  · rw [jpd4r16t6_epsZ_one_of_threeMod4 (n : ℤ) (by omega), jpd4r17t5_zmod2_one_val]
    omega

theorem jpd4r17t5_epsPow_tie (p q : ℕ) (hp : p % 2 = 1) (hq : q % 2 = 1) :
    (-1 : ℤ) ^ ((jpd4r14t3_epsZ (p : ℤ) * jpd4r14t3_epsZ (q : ℤ)).val)
      = (-1 : ℤ) ^ (p / 2 * (q / 2)) := by
  have _pin := Classical.em True
  rw [jpd4r17t5_zmod2_mul_val, jpd4r17t5_epsZ_val_natOdd p hp,
    jpd4r17t5_epsZ_val_natOdd q hq,
    neg_one_pow_eq_pow_mod_two (R := ℤ) (p / 2 * (q / 2)), ← Nat.mul_mod]

theorem jpd4r17t5_epsZ_neg (a : ℤ) (ha : a % 2 = 1) :
    jpd4r14t3_epsZ (-a) = jpd4r14t3_epsZ a + 1 := by
  have _pin := Classical.em True
  obtain ⟨m, hm⟩ : ∃ m, a = 2 * m + 1 := ⟨a / 2, by omega⟩
  have h1 : (-a - 1) / 2 = -m - 1 := by
    rw [show (-a - 1 : ℤ) = 2 * (-m - 1) from by rw [hm]; ring]
    exact Int.mul_ediv_cancel_left _ (by norm_num)
  have h2 : (a - 1) / 2 = m := by
    rw [show (a - 1 : ℤ) = 2 * m from by rw [hm]; ring]
    exact Int.mul_ediv_cancel_left _ (by norm_num)
  unfold jpd4r14t3_epsZ
  rw [h1, h2]
  have hd : (((-m - 1) - (m + 1) : ℤ) : ZMod 2) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨-m - 1, by ring⟩
  push_cast at hd ⊢
  exact sub_eq_zero.mp hd

theorem jpd4r17t5_epsPow_neg_prime (q : ℕ) (hqodd : q % 2 = 1) :
    (-1 : ℤˣ) ^ ((jpd4r14t3_epsZ (-(q : ℤ))).val)
      = gmk6_hil_epsSign q * (-1 : ℤˣ) := by
  have _pin := Classical.em True
  rw [jpd4r17t5_epsZ_neg (q : ℤ) (by omega), gmk6_hil_units_pow_val_add,
    ← jpd4r16t6_epsExponent_bridge q hqodd]
  rcases Int.units_eq_one_or (gmk6_hil_epsSign q) with he | he <;> rw [he] <;>
    decide

theorem jpd4r17t5_omegaZ_zero_of_pmOneMod8 (a : ℤ) (ha : a % 8 = 1 ∨ a % 8 = 7) :
    jpd4r14t3_omegaZ a = 0 := by
  have _pin := Classical.em True
  unfold jpd4r14t3_omegaZ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  rcases ha with h | h
  · obtain ⟨k, hk⟩ : ∃ k, a = 8 * k + 1 := ⟨a / 8, by omega⟩
    rw [show (a ^ 2 - 1 : ℤ) = 8 * (2 * (4 * k ^ 2 + k)) from by rw [hk]; ring,
      Int.mul_ediv_cancel_left _ (by norm_num)]
    exact ⟨4 * k ^ 2 + k, rfl⟩
  · obtain ⟨k, hk⟩ : ∃ k, a = 8 * k + 7 := ⟨a / 8, by omega⟩
    rw [show (a ^ 2 - 1 : ℤ) = 8 * (2 * (4 * k ^ 2 + 7 * k + 3)) from by
        rw [hk]; ring,
      Int.mul_ediv_cancel_left _ (by norm_num)]
    exact ⟨4 * k ^ 2 + 7 * k + 3, rfl⟩

theorem jpd4r17t5_omegaZ_one_of_pmThreeMod8 (a : ℤ) (ha : a % 8 = 3 ∨ a % 8 = 5) :
    jpd4r14t3_omegaZ a = 1 := by
  have _pin := Classical.em True
  have hd : (((a ^ 2 - 1) / 8 - 1 : ℤ) : ZMod 2) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    rcases ha with h | h
    · obtain ⟨k, hk⟩ : ∃ k, a = 8 * k + 3 := ⟨a / 8, by omega⟩
      rw [show (a ^ 2 - 1 : ℤ) = 8 * (8 * k ^ 2 + 6 * k + 1) from by
          rw [hk]; ring,
        Int.mul_ediv_cancel_left _ (by norm_num)]
      exact ⟨4 * k ^ 2 + 3 * k, by ring⟩
    · obtain ⟨k, hk⟩ : ∃ k, a = 8 * k + 5 := ⟨a / 8, by omega⟩
      rw [show (a ^ 2 - 1 : ℤ) = 8 * (8 * k ^ 2 + 10 * k + 3) from by
          rw [hk]; ring,
        Int.mul_ediv_cancel_left _ (by norm_num)]
      exact ⟨4 * k ^ 2 + 5 * k + 1, by ring⟩
  unfold jpd4r14t3_omegaZ
  push_cast at hd
  exact sub_eq_zero.mp hd

theorem jpd4r17t5_omegaPow_eq_chiEight (q : ℕ) (hq : q % 2 = 1) :
    (-1 : ℤ) ^ ((jpd4r14t3_omegaZ (q : ℤ)).val) = ZMod.χ₈ (q : ZMod 8) := by
  have _pin := Classical.em True
  rw [ZMod.χ₈_nat_eq_if_mod_eight, if_neg (by omega : ¬ q % 2 = 0)]
  rcases (by omega : q % 8 = 1 ∨ q % 8 = 3 ∨ q % 8 = 5 ∨ q % 8 = 7) with
    h | h | h | h
  · rw [jpd4r17t5_omegaZ_zero_of_pmOneMod8 (q : ℤ) (Or.inl (by omega)),
      if_pos (Or.inl h), jpd4r17t5_zmod2_zero_val, pow_zero]
  · rw [jpd4r17t5_omegaZ_one_of_pmThreeMod8 (q : ℤ) (Or.inl (by omega)),
      if_neg (by omega), jpd4r17t5_zmod2_one_val, pow_one]
  · rw [jpd4r17t5_omegaZ_one_of_pmThreeMod8 (q : ℤ) (Or.inr (by omega)),
      if_neg (by omega), jpd4r17t5_zmod2_one_val, pow_one]
  · rw [jpd4r17t5_omegaZ_zero_of_pmOneMod8 (q : ℤ) (Or.inr (by omega)),
      if_pos (Or.inr h), jpd4r17t5_zmod2_zero_val, pow_zero]

def jpd4r17t5_oddSupport (a : ℤ) : Finset ℕ :=
  a.natAbs.factorization.support.erase 2

theorem jpd4r17t5_oddSupport_eq_erase_primeFactors (a : ℤ) :
    jpd4r17t5_oddSupport a = a.natAbs.primeFactors.erase 2 := by
  have _pin := Classical.em True
  unfold jpd4r17t5_oddSupport
  rw [Nat.support_factorization]

theorem jpd4r17t5_mem_oddSupport {p : ℕ} (a : ℤ)
    (hp : p ∈ jpd4r17t5_oddSupport a) : p.Prime ∧ p ≠ 2 := by
  have _pin := Classical.em True
  unfold jpd4r17t5_oddSupport at hp
  rw [Finset.mem_erase, Nat.support_factorization] at hp
  exact ⟨Nat.prime_of_mem_primeFactors hp.2, hp.1⟩

theorem jpd4r17t5_erase_two_singleton (q : ℕ) (hq2 : q ≠ 2) :
    ({q} : Finset ℕ).erase 2 = {q} := by
  have _pin := Classical.em True
  ext x
  simp only [Finset.mem_erase, Finset.mem_singleton]
  constructor
  · exact fun hx => hx.2
  · rintro rfl
    exact ⟨hq2, rfl⟩

theorem jpd4r17t5_oddSupport_of_natAbs_one (a : ℤ) (h : a.natAbs = 1) :
    jpd4r17t5_oddSupport a = ∅ := by
  have _pin := Classical.em True
  rw [jpd4r17t5_oddSupport_eq_erase_primeFactors, h, Nat.primeFactors_one,
    Finset.erase_empty]

theorem jpd4r17t5_oddSupport_of_natAbs_prime (a : ℤ) (q : ℕ) (hq : q.Prime)
    (hq2 : q ≠ 2) (h : a.natAbs = q) : jpd4r17t5_oddSupport a = {q} := by
  have _pin := Classical.em True
  rw [jpd4r17t5_oddSupport_eq_erase_primeFactors, h, hq.primeFactors]
  exact jpd4r17t5_erase_two_singleton q hq2

theorem jpd4r17t5_oddSupport_of_natAbs_primeSq (a : ℤ) (q : ℕ) (hq : q.Prime)
    (hq2 : q ≠ 2) (h : a.natAbs = q * q) : jpd4r17t5_oddSupport a = {q} := by
  have _pin := Classical.em True
  rw [jpd4r17t5_oddSupport_eq_erase_primeFactors, h,
    Nat.primeFactors_mul hq.pos.ne' hq.pos.ne', hq.primeFactors,
    Finset.union_self]
  exact jpd4r17t5_erase_two_singleton q hq2

theorem jpd4r17t5_oddSupport_of_natAbs_primePair (a : ℤ) (p q : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (h : a.natAbs = p * q) : jpd4r17t5_oddSupport a = {p, q} := by
  have _pin := Classical.em True
  rw [jpd4r17t5_oddSupport_eq_erase_primeFactors, h,
    Nat.primeFactors_mul hp.pos.ne' hq.pos.ne', hp.primeFactors,
    hq.primeFactors]
  ext x
  simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_insert]
  constructor
  · exact fun hx => hx.2
  · rintro (rfl | rfl)
    · exact ⟨hp2, Or.inl rfl⟩
    · exact ⟨hq2, Or.inr rfl⟩

theorem jpd4r17t5_oddSupport_of_natAbs_twoMulPrime (a : ℤ) (q : ℕ)
    (hq : q.Prime) (hq2 : q ≠ 2) (h : a.natAbs = 2 * q) :
    jpd4r17t5_oddSupport a = {q} := by
  have _pin := Classical.em True
  rw [jpd4r17t5_oddSupport_eq_erase_primeFactors, h,
    Nat.primeFactors_mul (by norm_num) hq.pos.ne', Nat.prime_two.primeFactors,
    hq.primeFactors]
  ext x
  simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_singleton]
  constructor
  · rintro ⟨hx2, rfl | rfl⟩
    · exact absurd rfl hx2
    · rfl
  · rintro rfl
    exact ⟨hq2, Or.inr rfl⟩

def jpd4r17t5_unitPart (p : ℕ) (a : ℤ) : ℤ :=
  a.sign * ((ordCompl[p] a.natAbs : ℕ) : ℤ)

theorem jpd4r17t5_unitPart_decompose (p : ℕ) (a : ℤ) :
    (p : ℤ) ^ (a.natAbs.factorization p) * jpd4r17t5_unitPart p a = a := by
  have _pin := Classical.em True
  unfold jpd4r17t5_unitPart
  calc (p : ℤ) ^ (a.natAbs.factorization p)
        * (a.sign * ((ordCompl[p] a.natAbs : ℕ) : ℤ))
      = a.sign * ((ordProj[p] a.natAbs * ordCompl[p] a.natAbs : ℕ) : ℤ) := by
        push_cast
        ring
    _ = a.sign * (a.natAbs : ℤ) := by
        rw [Nat.ordProj_mul_ordCompl_eq_self]
    _ = a := Int.sign_mul_natAbs a

theorem jpd4r17t5_unitPart_of_not_dvd (p : ℕ) (a : ℤ) (h : ¬ p ∣ a.natAbs) :
    jpd4r17t5_unitPart p a = a := by
  have _pin := Classical.em True
  unfold jpd4r17t5_unitPart
  rw [Nat.factorization_eq_zero_of_not_dvd h, pow_zero, Nat.div_one]
  exact Int.sign_mul_natAbs a

theorem jpd4r17t5_unitPart_natCast_prime (q : ℕ) (hq : q.Prime) :
    jpd4r17t5_unitPart q (q : ℤ) = 1 := by
  have _pin := Classical.em True
  unfold jpd4r17t5_unitPart
  rw [Int.natAbs_natCast, Nat.Prime.factorization_self hq, pow_one,
    Nat.div_self hq.pos, Int.sign_eq_one_of_pos (by exact_mod_cast hq.pos),
    Nat.cast_one, mul_one]

theorem jpd4r17t5_unitPart_neg_natCast_prime (q : ℕ) (hq : q.Prime) :
    jpd4r17t5_unitPart q (-(q : ℤ)) = -1 := by
  have _pin := Classical.em True
  unfold jpd4r17t5_unitPart
  rw [Int.natAbs_neg, Int.natAbs_natCast, Nat.Prime.factorization_self hq,
    pow_one, Nat.div_self hq.pos, Int.sign_neg,
    Int.sign_eq_one_of_pos (by exact_mod_cast hq.pos), Nat.cast_one, mul_one]

theorem jpd4r17t5_unitPart_two_lit : jpd4r17t5_unitPart 2 (2 : ℤ) = 1 := by
  have _pin := Classical.em True
  unfold jpd4r17t5_unitPart
  rw [show ((2 : ℤ)).natAbs = 2 from rfl,
    Nat.Prime.factorization_self Nat.prime_two, pow_one]
  decide

theorem jpd4r17t5_intCast_ne_zero_of_not_dvd (p : ℕ) [Fact p.Prime] (a : ℤ)
    (h : ¬ p ∣ a.natAbs) : ((a : ℤ) : ZMod p) ≠ 0 := by
  have _pin := Classical.em True
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact fun hd => h (Int.natCast_dvd.mp hd)

theorem jpd4r17t5_unitPart_intCast_ne_zero (p : ℕ) [Fact p.Prime] (a : ℤ)
    (ha : a ≠ 0) : ((jpd4r17t5_unitPart p a : ℤ) : ZMod p) ≠ 0 := by
  have _pin := Classical.em True
  refine jpd4r17t5_intCast_ne_zero_of_not_dvd p _ ?_
  have h2 : (jpd4r17t5_unitPart p a).natAbs = ordCompl[p] a.natAbs := by
    unfold jpd4r17t5_unitPart
    rw [Int.natAbs_mul, Int.natAbs_sign_of_ne_zero ha, Int.natAbs_natCast,
      one_mul]
  rw [h2]
  exact Nat.not_dvd_ordCompl (Fact.out : p.Prime) (Int.natAbs_ne_zero.mpr ha)

def jpd4r17t5_classAt (p : ℕ) [Fact p.Prime] (a : ℤ) : gmk6_hil_SquareClass :=
  jpd4r16t6_classOf p ((a.natAbs.factorization p : ZMod 2))
    (jpd4r17t5_unitPart p a)

theorem jpd4r17t5_fitGate_classAt_def (p : ℕ) [Fact p.Prime] (a : ℤ) :
    jpd4r17t5_classAt p a
      = ⟨((a.natAbs.factorization p : ZMod 2)),
          gmk6_hil_legendreSign p (jpd4r17t5_unitPart p a)⟩ := by
  have _pin := Classical.em True
  exact rfl

theorem jpd4r17t5_legendreSign_one (p : ℕ) [Fact p.Prime] :
    gmk6_hil_legendreSign p 1 = 1 := by
  have _pin := Classical.em True
  unfold gmk6_hil_legendreSign
  rw [if_pos (legendreSym.at_one (p := p))]

theorem jpd4r17t5_legendreSign_negOne (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) :
    gmk6_hil_legendreSign q (-1) = gmk6_hil_epsSign q := by
  have _pin := Classical.em True
  have h := gmk6_hil_epsSign_eq_legendre_neg_one q hq2
  unfold gmk6_hil_legendreSign
  rcases Int.units_eq_one_or (gmk6_hil_epsSign q) with he | he
  · rw [he] at h ⊢
    rw [if_pos (show legendreSym q (-1) = 1 by rw [← h]; exact Units.val_one)]
  · rw [he] at h ⊢
    rw [if_neg (show ¬ legendreSym q (-1) = 1 by rw [← h]; decide)]

theorem jpd4r17t5_classAt_of_not_dvd (p : ℕ) [Fact p.Prime] (a : ℤ)
    (h : ¬ p ∣ a.natAbs) :
    jpd4r17t5_classAt p a
      = gmk6_hil_unitClass (gmk6_hil_legendreSign p a) := by
  have _pin := Classical.em True
  rw [jpd4r17t5_fitGate_classAt_def, Nat.factorization_eq_zero_of_not_dvd h,
    Nat.cast_zero, jpd4r17t5_unitPart_of_not_dvd p a h]
  rfl

theorem jpd4r17t5_classAt_natCast_self (q : ℕ) [Fact q.Prime] :
    jpd4r17t5_classAt q (q : ℤ) = gmk6_hil_uniformiserClass := by
  have _pin := Classical.em True
  rw [jpd4r17t5_fitGate_classAt_def, Int.natAbs_natCast,
    Nat.Prime.factorization_self (Fact.out : q.Prime), Nat.cast_one,
    jpd4r17t5_unitPart_natCast_prime q (Fact.out : q.Prime),
    jpd4r17t5_legendreSign_one q]
  rfl

theorem jpd4r17t5_classAt_neg_natCast_self (q : ℕ) [Fact q.Prime] :
    jpd4r17t5_classAt q (-(q : ℤ))
      = (⟨1, gmk6_hil_legendreSign q (-1)⟩ : gmk6_hil_SquareClass) := by
  have _pin := Classical.em True
  rw [jpd4r17t5_fitGate_classAt_def, Int.natAbs_neg, Int.natAbs_natCast,
    Nat.Prime.factorization_self (Fact.out : q.Prime), Nat.cast_one,
    jpd4r17t5_unitPart_neg_natCast_prime q (Fact.out : q.Prime)]

theorem jpd4r17t5_pair_unit_nonUnit (e s t : ℤˣ) :
    gmk6_hil_pair e (gmk6_hil_unitClass s)
        (⟨1, t⟩ : gmk6_hil_SquareClass) = s := by
  have _pin := Classical.em True
  rw [jpd4r16t6_nonUnitClass_decompose t, gmk6_hil_pair_mul_right,
    gmk6_hil_table_unit_uniformiser, gmk6_hil_table_unit_unit, mul_one]

def jpd4r17t5_oddLocalFactor (p : ℕ) (a b : ℤ) : ℤˣ :=
  if hp : p.Prime then
    haveI : Fact p.Prime := ⟨hp⟩
    gmk6_hil_pair (gmk6_hil_epsSign p) (jpd4r17t5_classAt p a)
      (jpd4r17t5_classAt p b)
  else 1

theorem jpd4r17t5_oddLocalFactor_eq (p : ℕ) [hp : Fact p.Prime] (a b : ℤ) :
    jpd4r17t5_oddLocalFactor p a b
      = gmk6_hil_pair (gmk6_hil_epsSign p) (jpd4r17t5_classAt p a)
          (jpd4r17t5_classAt p b) := by
  have _pin := Classical.em True
  unfold jpd4r17t5_oddLocalFactor
  rw [dif_pos hp.out]

def jpd4r17t5_oddComplementProduct (a b : ℤ) : ℤˣ :=
  ∏ p ∈ jpd4r17t5_oddSupport (a * b), jpd4r17t5_oddLocalFactor p a b

def jpd4r17t5_twoFactor (a b : ℤ) : ℤˣ :=
  jpd4r14t3_pairTwoZ ((a.natAbs.factorization 2 : ZMod 2))
    (jpd4r17t5_unitPart 2 a) ((b.natAbs.factorization 2 : ZMod 2))
    (jpd4r17t5_unitPart 2 b)

theorem jpd4r17t5_twoFactor_oddData (a b : ℤ) (ha : ¬ 2 ∣ a.natAbs)
    (hb : ¬ 2 ∣ b.natAbs) :
    jpd4r17t5_twoFactor a b = jpd4r14t3_pairTwoZ 0 a 0 b := by
  have _pin := Classical.em True
  unfold jpd4r17t5_twoFactor
  rw [Nat.factorization_eq_zero_of_not_dvd ha,
    Nat.factorization_eq_zero_of_not_dvd hb, Nat.cast_zero,
    jpd4r17t5_unitPart_of_not_dvd 2 a ha, jpd4r17t5_unitPart_of_not_dvd 2 b hb]

theorem jpd4r17t5_twoFactor_two_left (b : ℤ) (hb : ¬ 2 ∣ b.natAbs) :
    jpd4r17t5_twoFactor (2 : ℤ) b = jpd4r14t3_pairTwoZ 1 1 0 b := by
  have _pin := Classical.em True
  unfold jpd4r17t5_twoFactor
  rw [show ((2 : ℤ)).natAbs = 2 from rfl,
    Nat.Prime.factorization_self Nat.prime_two, Nat.cast_one,
    jpd4r17t5_unitPart_two_lit, Nat.factorization_eq_zero_of_not_dvd hb,
    Nat.cast_zero, jpd4r17t5_unitPart_of_not_dvd 2 b hb]

theorem jpd4r17t5_pairTwo_diag (u v : ℤ) :
    jpd4r14t3_pairTwoZ 0 u 0 v
      = (-1 : ℤˣ) ^ ((jpd4r14t3_epsZ u * jpd4r14t3_epsZ v).val) := by
  have _pin := Classical.em True
  unfold jpd4r14t3_pairTwoZ
  rw [jpd4r17t5_zmod2_exp_diag (jpd4r14t3_epsZ u) (jpd4r14t3_epsZ v)
    (jpd4r14t3_omegaZ v) (jpd4r14t3_omegaZ u)]

theorem jpd4r17t5_pairTwo_twoSlot (v : ℤ) :
    jpd4r14t3_pairTwoZ 1 1 0 v
      = (-1 : ℤˣ) ^ ((jpd4r14t3_omegaZ v).val) := by
  have _pin := Classical.em True
  unfold jpd4r14t3_pairTwoZ
  rw [jpd4r16t6_epsZ_zero_of_oneMod4 1 (by norm_num),
    jpd4r17t5_zmod2_exp_twoSlot (jpd4r14t3_epsZ v) (jpd4r14t3_omegaZ v)
      (jpd4r14t3_omegaZ 1)]

def jpd4r17t5_placeFactor (a b : ℤ) (v : ℕ) : ℤˣ :=
  if v = 0 then jpd4r13t6_hilbR (a : ℝ) (b : ℝ)
  else if v = 2 then jpd4r17t5_twoFactor a b
  else jpd4r17t5_oddLocalFactor v a b

def jpd4r17t5_adelePlaces (a b : ℤ) : Finset ℕ :=
  insert 0 (insert 2 (jpd4r17t5_oddSupport (a * b)))

def jpd4r17t5_allPlacesProduct (a b : ℤ) : ℤˣ :=
  ∏ v ∈ jpd4r17t5_adelePlaces a b, jpd4r17t5_placeFactor a b v

theorem jpd4r17t5_placeFactor_realSlot (a b : ℤ) :
    jpd4r17t5_placeFactor a b 0 = jpd4r13t6_hilbR (a : ℝ) (b : ℝ) := by
  have _pin := Classical.em True
  unfold jpd4r17t5_placeFactor
  rw [if_pos rfl]

theorem jpd4r17t5_placeFactor_twoSlot (a b : ℤ) :
    jpd4r17t5_placeFactor a b 2 = jpd4r17t5_twoFactor a b := by
  have _pin := Classical.em True
  unfold jpd4r17t5_placeFactor
  rw [if_neg (by norm_num : ¬ (2 : ℕ) = 0), if_pos rfl]

theorem jpd4r17t5_placeFactor_oddSlot (a b : ℤ) (r : ℕ)
    (hr : r.Prime ∧ r ≠ 2) :
    jpd4r17t5_placeFactor a b r = jpd4r17t5_oddLocalFactor r a b := by
  have _pin := Classical.em True
  unfold jpd4r17t5_placeFactor
  rw [if_neg hr.1.pos.ne', if_neg hr.2]

theorem jpd4r17t5_fitGate_factorised (a b : ℤ) :
    jpd4r17t5_allPlacesProduct a b
      = jpd4r17t5_twoFactor a b * jpd4r17t5_oddComplementProduct a b
          * jpd4r13t6_hilbR (a : ℝ) (b : ℝ) := by
  have _pin := Classical.em True
  unfold jpd4r17t5_allPlacesProduct jpd4r17t5_adelePlaces
  have h0 : (0 : ℕ) ∉ insert 2 (jpd4r17t5_oddSupport (a * b)) := by
    rw [Finset.mem_insert]
    rintro (h | h)
    · exact absurd h (by norm_num)
    · exact Nat.not_prime_zero (jpd4r17t5_mem_oddSupport (a * b) h).1
  have h2 : (2 : ℕ) ∉ jpd4r17t5_oddSupport (a * b) := fun h =>
    (jpd4r17t5_mem_oddSupport (a * b) h).2 rfl
  rw [Finset.prod_insert h0, Finset.prod_insert h2,
    jpd4r17t5_placeFactor_realSlot, jpd4r17t5_placeFactor_twoSlot,
    Finset.prod_congr rfl
      (fun r hr => jpd4r17t5_placeFactor_oddSlot a b r
        (jpd4r17t5_mem_oddSupport (a * b) hr))]
  unfold jpd4r17t5_oddComplementProduct
  exact mul_comm _ _

theorem jpd4r17t5_negSide_twoInfty_fires_negOne_negPrime (q : ℕ)
    [Fact q.Prime] (hq2 : q ≠ 2) :
    jpd4r14t3_pairTwoZ 0 (-1) 0 (-(q : ℤ))
        * jpd4r13t6_hilbR (-1 : ℝ) (-(q : ℝ)) = gmk6_hil_epsSign q := by
  have _pin := Classical.em True
  have hq := (Fact.out : q.Prime)
  have hqodd : q % 2 = 1 := Nat.odd_iff.mp (hq.odd_of_ne_two hq2)
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq.pos
  rw [jpd4r14t4_hilbR_neg_neg (-1 : ℝ) (-(q : ℝ)) (by norm_num) (by linarith),
    jpd4r17t5_pairTwo_diag, jpd4r14t3_repCoherence.2.2.2.2.2.2.2.2.1, one_mul,
    jpd4r17t5_epsPow_neg_prime q hqodd, mul_assoc,
    show ((-1 : ℤˣ) * -1) = 1 from by decide, mul_one]

theorem jpd4r17t5_complementValue_negOne_negPrime (q : ℕ) [Fact q.Prime]
    (hq2 : q ≠ 2) :
    jpd4r17t5_oddComplementProduct (-1) (-(q : ℤ)) = gmk6_hil_epsSign q := by
  have _pin := Classical.em True
  have hq := (Fact.out : q.Prime)
  unfold jpd4r17t5_oddComplementProduct
  rw [show ((-1 : ℤ) * -(q : ℤ)) = (q : ℤ) from by ring,
    jpd4r17t5_oddSupport_of_natAbs_prime (q : ℤ) q hq hq2
      (Int.natAbs_natCast q)]
  simp only [Finset.prod_singleton]
  rw [jpd4r17t5_oddLocalFactor_eq q,
    jpd4r17t5_classAt_of_not_dvd q (-1)
      (by rw [Int.natAbs_neg, Int.natAbs_one]; exact hq.not_dvd_one),
    jpd4r17t5_classAt_neg_natCast_self q, jpd4r17t5_legendreSign_negOne q hq2,
    jpd4r17t5_pair_unit_nonUnit]

theorem jpd4r17t5_allPlaces_signWindow :
    ∀ u ∈ ([1, -1] : List ℤ), ∀ v ∈ ([1, -1] : List ℤ),
      jpd4r17t5_allPlacesProduct u v = 1 := by
  have _pin := Classical.em True
  have hone : ∀ w ∈ ([1, -1] : List ℤ), w.natAbs = 1 := by decide
  intro u hu v hv
  have hu1 := hone u hu
  have hv1 := hone v hv
  rw [jpd4r17t5_fitGate_factorised]
  unfold jpd4r17t5_oddComplementProduct
  rw [jpd4r17t5_oddSupport_of_natAbs_one (u * v)
      (by rw [Int.natAbs_mul, hu1, hv1]),
    Finset.prod_empty, mul_one,
    jpd4r17t5_twoFactor_oddData u v (by rw [hu1]; norm_num)
      (by rw [hv1]; norm_num)]
  exact jpd4r15t2_signWindow_reciprocity u hu v hv

theorem jpd4r17t5_allPlaces_distinctOddPrimes (p q : ℕ) [Fact p.Prime]
    [Fact q.Prime] (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q) :
    jpd4r17t5_allPlacesProduct (p : ℤ) (q : ℤ) = 1 := by
  have _pin := Classical.em True
  have hp := (Fact.out : p.Prime)
  have hq := (Fact.out : q.Prime)
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have hqodd : q % 2 = 1 := Nat.odd_iff.mp (hq.odd_of_ne_two hq2)
  have hpdq : ¬ p ∣ q := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)
  have hqdp : ¬ q ∣ p := fun h =>
    hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp h).symm
  have h2p : ¬ (2 : ℕ) ∣ ((p : ℤ)).natAbs := by rw [Int.natAbs_natCast]; omega
  have h2q : ¬ (2 : ℕ) ∣ ((q : ℤ)).natAbs := by rw [Int.natAbs_natCast]; omega
  have hpow : ∀ (u : ℤˣ) (n : ℕ), ((u ^ n : ℤˣ) : ℤ) = (u : ℤ) ^ n :=
    fun u n => map_pow (Units.coeHom ℤ) u n
  rw [jpd4r17t5_fitGate_factorised]
  unfold jpd4r17t5_oddComplementProduct
  rw [jpd4r17t5_oddSupport_of_natAbs_primePair _ p q hp hq hp2 hq2
      (by rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast])]
  simp only [Finset.prod_pair hpq]
  rw [jpd4r17t5_oddLocalFactor_eq p, jpd4r17t5_oddLocalFactor_eq q,
    jpd4r17t5_classAt_natCast_self p, jpd4r17t5_classAt_natCast_self q,
    jpd4r17t5_classAt_of_not_dvd p (q : ℤ)
      (by rw [Int.natAbs_natCast]; exact hpdq),
    jpd4r17t5_classAt_of_not_dvd q (p : ℤ)
      (by rw [Int.natAbs_natCast]; exact hqdp),
    gmk6_hil_table_uniformiser_unit, gmk6_hil_table_unit_uniformiser,
    jpd4r17t5_twoFactor_oddData _ _ h2p h2q, jpd4r17t5_pairTwo_diag,
    Int.cast_natCast, Int.cast_natCast,
    jpd4r14t4_hilbR_left_nonneg (p : ℝ) (q : ℝ) (Nat.cast_nonneg p), mul_one]
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, Units.val_one, hpow, Units.val_neg,
    Units.val_one,
    gmk6_hil_legendreSign_coe p (q : ℤ)
      (jpd4r17t5_intCast_ne_zero_of_not_dvd p (q : ℤ)
        (by rw [Int.natAbs_natCast]; exact hpdq)),
    gmk6_hil_legendreSign_coe q (p : ℤ)
      (jpd4r17t5_intCast_ne_zero_of_not_dvd q (p : ℤ)
        (by rw [Int.natAbs_natCast]; exact hqdp)),
    jpd4r17t5_epsPow_tie p q hpodd hqodd,
    mul_comm (legendreSym p (q : ℤ)) (legendreSym q (p : ℤ)),
    legendreSym.quadratic_reciprocity hp2 hq2 hpq, ← pow_add]
  exact Even.neg_one_pow ⟨p / 2 * (q / 2), rfl⟩

theorem jpd4r17t5_allPlaces_two_oddPrime (q : ℕ) [Fact q.Prime]
    (hq2 : q ≠ 2) :
    jpd4r17t5_allPlacesProduct (2 : ℤ) (q : ℤ) = 1 := by
  have _pin := Classical.em True
  have hq := (Fact.out : q.Prime)
  have hqodd : q % 2 = 1 := Nat.odd_iff.mp (hq.odd_of_ne_two hq2)
  have hqd2 : ¬ q ∣ 2 := fun h =>
    hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h)
  have h2q : ¬ (2 : ℕ) ∣ ((q : ℤ)).natAbs := by rw [Int.natAbs_natCast]; omega
  have hpow : ∀ (u : ℤˣ) (n : ℕ), ((u ^ n : ℤˣ) : ℤ) = (u : ℤ) ^ n :=
    fun u n => map_pow (Units.coeHom ℤ) u n
  rw [jpd4r17t5_fitGate_factorised]
  unfold jpd4r17t5_oddComplementProduct
  rw [jpd4r17t5_oddSupport_of_natAbs_twoMulPrime _ q hq hq2
      (by rw [show ((2 : ℤ) * (q : ℤ)) = ((2 * q : ℕ) : ℤ) from by
          push_cast; ring,
        Int.natAbs_natCast])]
  simp only [Finset.prod_singleton]
  rw [jpd4r17t5_oddLocalFactor_eq q, jpd4r17t5_classAt_natCast_self q,
    jpd4r17t5_classAt_of_not_dvd q (2 : ℤ) (show ¬ q ∣ 2 from hqd2),
    gmk6_hil_table_unit_uniformiser, jpd4r17t5_twoFactor_two_left _ h2q,
    jpd4r17t5_pairTwo_twoSlot,
    show ((2 : ℤ) : ℝ) = (2 : ℝ) from by norm_num, Int.cast_natCast,
    jpd4r14t4_hilbR_left_nonneg (2 : ℝ) (q : ℝ) (by norm_num), mul_one]
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_one, hpow, Units.val_neg, Units.val_one,
    gmk6_hil_legendreSign_coe q (2 : ℤ)
      (jpd4r17t5_intCast_ne_zero_of_not_dvd q (2 : ℤ)
        (show ¬ q ∣ 2 from hqd2)),
    legendreSym.at_two hq2, ← jpd4r17t5_omegaPow_eq_chiEight q hqodd,
    ← pow_add]
  exact Even.neg_one_pow ⟨(jpd4r14t3_omegaZ (q : ℤ)).val, rfl⟩

theorem jpd4r17t5_allPlaces_uniformiserSelf (q : ℕ) [Fact q.Prime]
    (hq2 : q ≠ 2) :
    jpd4r17t5_allPlacesProduct (q : ℤ) (q : ℤ) = 1 := by
  have _pin := Classical.em True
  have hq := (Fact.out : q.Prime)
  have hqodd : q % 2 = 1 := Nat.odd_iff.mp (hq.odd_of_ne_two hq2)
  have h2q : ¬ (2 : ℕ) ∣ ((q : ℤ)).natAbs := by rw [Int.natAbs_natCast]; omega
  rw [jpd4r17t5_fitGate_factorised]
  unfold jpd4r17t5_oddComplementProduct
  rw [jpd4r17t5_oddSupport_of_natAbs_primeSq _ q hq hq2
      (by rw [Int.natAbs_mul, Int.natAbs_natCast])]
  simp only [Finset.prod_singleton]
  rw [jpd4r17t5_oddLocalFactor_eq q, jpd4r17t5_classAt_natCast_self q,
    jpd4r17t5_twoFactor_oddData _ _ h2q h2q, Int.cast_natCast,
    mul_comm (jpd4r14t3_pairTwoZ 0 (q : ℤ) 0 (q : ℤ))
      (gmk6_hil_pair (gmk6_hil_epsSign q) gmk6_hil_uniformiserClass
        gmk6_hil_uniformiserClass)]
  exact jpd4r16t6_reciprocity_uniformiserSelf q hq2

theorem jpd4r17t5_allPlaces_negOne_negPrime (q : ℕ) [Fact q.Prime]
    (hq2 : q ≠ 2) :
    jpd4r17t5_allPlacesProduct (-1) (-(q : ℤ)) = 1 := by
  have _pin := Classical.em True
  have hq := (Fact.out : q.Prime)
  have hqodd : q % 2 = 1 := Nat.odd_iff.mp (hq.odd_of_ne_two hq2)
  have hqneg : ¬ (2 : ℕ) ∣ ((-(q : ℤ))).natAbs := by
    rw [Int.natAbs_neg, Int.natAbs_natCast]; omega
  rw [jpd4r17t5_fitGate_factorised,
    jpd4r17t5_twoFactor_oddData _ _ (by norm_num) hqneg,
    jpd4r17t5_complementValue_negOne_negPrime q hq2,
    show ((-1 : ℤ) : ℝ) = (-1 : ℝ) from by norm_num,
    show ((-(q : ℤ) : ℤ) : ℝ) = -(q : ℝ) from by push_cast; ring,
    mul_right_comm, jpd4r17t5_negSide_twoInfty_fires_negOne_negPrime q hq2]
  exact gmk6_hil_units_mul_self _

end FLT.JpssD4KubotaFiniteAdelicProductObjectSlice
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section
section

p2m_open_scoped "Classical P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.Classical"

namespace FLT
namespace NumberTheory

open FLT.CampGenuineMk
open FLT.JpssD4KubotaPTwoHilbertTable
open FLT.JpssD4GJProp83MetaplecticKubotaCoverCarrier
open FLT.JpssD4KubotaTameSymbolUniformWindowSlice
open FLT.JpssD4KubotaFiniteAdelicProductObjectSlice
open FLT.JpssD4KubotaArchimedeanCocycleSlice

theorem kw_hpG_classOf_congr {p : ℕ} [Fact p.Prime] {x y : ℚ_[p]}
    (hx : x ≠ 0) (hy : y ≠ 0) (h : x = y) :
    gmk7_cls_classOf hx = gmk7_cls_classOf hy := by
  have _pin := Classical.em True
  subst h; rfl

theorem kw_hpG_legendreSign_mul {p : ℕ} [Fact p.Prime] {u v : ℤ}
    (hu : (u : ZMod p) ≠ 0) (hv : (v : ZMod p) ≠ 0) :
    gmk6_hil_legendreSign p (u * v)
      = gmk6_hil_legendreSign p u * gmk6_hil_legendreSign p v := by
  have _pin := Classical.em True
  have huv : ((u * v : ℤ) : ZMod p) ≠ 0 := by
    rw [Int.cast_mul]; exact mul_ne_zero hu hv
  refine Units.ext ?_
  rw [Units.val_mul, gmk6_hil_legendreSign_coe p (u * v) huv,
    gmk6_hil_legendreSign_coe p u hu, gmk6_hil_legendreSign_coe p v hv]
  exact legendreSym.mul p u v

theorem kw_hpG_negOne_zmod_ne_zero {p : ℕ} [Fact p.Prime] :
    ((-1 : ℤ) : ZMod p) ≠ 0 := by
  have _pin := Classical.em True
  rw [Int.cast_neg, Int.cast_one]
  exact neg_ne_zero.mpr one_ne_zero

theorem kw_hpG_classOf_negOne {p : ℕ} [Fact p.Prime] (_hp2 : p ≠ 2) :
    gmk7_cls_classOf (p := p) (neg_ne_zero.mpr one_ne_zero)
      = gmk6_hil_unitClassOf p (-1) := by
  have _pin := Classical.em True
  have hv : (-1 : ℚ_[p]).valuation = 0 :=
    gmk7_cls_valuation_eq_zero_of_norm_one (neg_ne_zero.mpr one_ne_zero)
      (by rw [norm_neg, norm_one])
  refine gmk6_hil_SquareClass_ext ?_ ?_
  · show (((-1 : ℚ_[p]).valuation : ℤ) : ZMod 2) = 0
    rw [hv, Int.cast_zero]
  · show gmk7_cls_sign (p := p) (neg_ne_zero.mpr one_ne_zero)
      = gmk6_hil_legendreSign p (-1)
    have hup : ((gmk7_cls_unitPart (p := p) (neg_ne_zero.mpr one_ne_zero)
        : ℤ_[p]) : ℚ_[p]) = ((-1 : ℤ_[p]) : ℚ_[p]) := by
      rw [gmk7_cls_unitPart_coe, hv, _root_.neg_zero, zpow_zero, mul_one]
      simp
    unfold gmk7_cls_sign gmk6_hil_legendreSign legendreSym gmk7_cls_residue
    rw [Subtype.coe_injective hup, _root_.map_neg, map_one, Int.cast_neg, Int.cast_one]

theorem kw_hpG_uniformiserClass_pow (e : ℕ) :
    (gmk6_hil_uniformiserClass : gmk6_hil_SquareClass) ^ e
      = ⟨((e : ℕ) : ZMod 2), 1⟩ := by
  have _pin := Classical.em True
  induction e with
  | zero => refine gmk6_hil_SquareClass_ext ?_ ?_ <;> simp
  | succ n ih =>
    rw [pow_succ, ih]
    refine gmk6_hil_SquareClass_ext ?_ ?_
    · show ((n : ℕ) : ZMod 2) + (1 : ZMod 2) = (((n + 1 : ℕ)) : ZMod 2)
      rw [Nat.cast_add, Nat.cast_one]
    · show (1 : ℤˣ) * 1 = 1; exact one_mul 1

theorem kw_hpG_classOf_p_pow {p : ℕ} [Fact p.Prime] (e : ℕ) :
    gmk7_cls_classOf (p := p) (pow_ne_zero e (gmk7_cls_p_padic_ne_zero (p := p)))
      = gmk6_hil_uniformiserClass ^ e := by
  have _pin := Classical.em True
  have hpne : ((p : ℕ) : ℚ_[p]) ≠ 0 := gmk7_cls_p_padic_ne_zero (p := p)
  induction e with
  | zero =>
    rw [kw_hpG_classOf_congr _ (one_ne_zero : (1 : ℚ_[p]) ≠ 0) (pow_zero _),
      pow_zero, gmk7_cls_classOf_one]
  | succ n ih =>
    rw [kw_hpG_classOf_congr _ (mul_ne_zero (pow_ne_zero n hpne) hpne)
        (pow_succ _ _),
      gmk7_cls_classOf_mul (pow_ne_zero n hpne) hpne, ih, gmk7_cls_classOf_p,
      pow_succ]

theorem kw_hpG_ne_zero_of_zmod_ne_zero {p : ℕ} {a : ℤ}
    (ha : (a : ZMod p) ≠ 0) : a ≠ 0 := by
  have _pin := Classical.em True
  exact fun h ↦ ha (by rw [h, Int.cast_zero])

theorem kw_hpG_classOf_intCast_coprime {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {a : ℤ} (ha : (a : ZMod p) ≠ 0) :
    gmk7_cls_classOf (p := p)
        (Int.cast_ne_zero.mpr (kw_hpG_ne_zero_of_zmod_ne_zero ha))
      = gmk6_hil_unitClassOf p a := by
  have _pin := Classical.em True
  have ha0 : a ≠ 0 := kw_hpG_ne_zero_of_zmod_ne_zero ha
  rcases lt_or_gt_of_ne ha0 with hneg | hpos
  ·
    have hnat : ((a.natAbs : ℕ) : ℤ) = -a := by
      rw [Int.natCast_natAbs, abs_of_neg hneg]
    have hna : ((a.natAbs : ℕ) : ZMod p) ≠ 0 := by
      have : (((a.natAbs : ℕ) : ℤ) : ZMod p) ≠ 0 := by
        rw [hnat, Int.cast_neg]; exact neg_ne_zero.mpr ha
      simpa only [Int.cast_natCast] using this
    have heq : ((a : ℤ) : ℚ_[p]) = (-1 : ℚ_[p]) * ((a.natAbs : ℕ) : ℚ_[p]) := by
      rw [show ((a.natAbs : ℕ) : ℚ_[p]) = (((a.natAbs : ℕ) : ℤ) : ℚ_[p]) from
        (Int.cast_natCast _).symm, hnat, Int.cast_neg]
      ring
    have hne1 : (-1 : ℚ_[p]) ≠ 0 := neg_ne_zero.mpr one_ne_zero
    have hne2 : ((a.natAbs : ℕ) : ℚ_[p]) ≠ 0 := gmk7_cls_natCast_ne_zero hna
    rw [kw_hpG_classOf_congr _ (mul_ne_zero hne1 hne2) heq,
      gmk7_cls_classOf_mul hne1 hne2, kw_hpG_classOf_negOne hp2,
      gmk7_cls_classOf_natCast_eq_unitClassOf hna]
    refine gmk6_hil_SquareClass_ext (by simp [gmk6_hil_unitClassOf,
      gmk6_hil_unitClass]) ?_
    show gmk6_hil_legendreSign p (-1) * gmk6_hil_legendreSign p (a.natAbs : ℤ)
      = gmk6_hil_legendreSign p a
    have hnaZ : (((a.natAbs : ℕ) : ℤ) : ZMod p) ≠ 0 := by
      rw [Int.cast_natCast]; exact hna
    rw [← kw_hpG_legendreSign_mul kw_hpG_negOne_zmod_ne_zero hnaZ,
      show (-1 : ℤ) * ((a.natAbs : ℕ) : ℤ) = a from by rw [hnat]; ring]
  ·
    have hnat : ((a.natAbs : ℕ) : ℤ) = a := by
      rw [Int.natCast_natAbs, abs_of_pos hpos]
    have hna : ((a.natAbs : ℕ) : ZMod p) ≠ 0 := by
      have : (((a.natAbs : ℕ) : ℤ) : ZMod p) ≠ 0 := by rw [hnat]; exact ha
      simpa only [Int.cast_natCast] using this
    have heq : ((a : ℤ) : ℚ_[p]) = ((a.natAbs : ℕ) : ℚ_[p]) := by
      rw [show ((a.natAbs : ℕ) : ℚ_[p]) = (((a.natAbs : ℕ) : ℤ) : ℚ_[p]) from
        (Int.cast_natCast _).symm, hnat]
    rw [kw_hpG_classOf_congr _ (gmk7_cls_natCast_ne_zero hna) heq,
      gmk7_cls_classOf_natCast_eq_unitClassOf hna]
    unfold gmk6_hil_unitClassOf
    rw [hnat]

theorem kw_hpG_classOf_eq_classAt {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {a : ℤ} (ha : a ≠ 0) :
    gmk7_cls_classOf (p := p) (Int.cast_ne_zero.mpr ha) = jpd4r17t5_classAt p a := by
  have _pin := Classical.em True
  set e := a.natAbs.factorization p with he
  set u := jpd4r17t5_unitPart p a with hu
  have hdec : ((a : ℤ) : ℚ_[p]) = ((p : ℕ) : ℚ_[p]) ^ e * ((u : ℤ) : ℚ_[p]) := by
    have h := jpd4r17t5_unitPart_decompose p a
    rw [← hu, ← he] at h
    calc ((a : ℤ) : ℚ_[p]) = (((p : ℤ) ^ e * u : ℤ) : ℚ_[p]) := by rw [h]
      _ = ((p : ℕ) : ℚ_[p]) ^ e * ((u : ℤ) : ℚ_[p]) := by push_cast; ring
  have hune : ((u : ℤ) : ZMod p) ≠ 0 := jpd4r17t5_unitPart_intCast_ne_zero p a ha
  have hpne : ((p : ℕ) : ℚ_[p]) ≠ 0 := gmk7_cls_p_padic_ne_zero (p := p)
  have hune' : ((u : ℤ) : ℚ_[p]) ≠ 0 :=
    Int.cast_ne_zero.mpr (kw_hpG_ne_zero_of_zmod_ne_zero hune)
  rw [kw_hpG_classOf_congr _ (mul_ne_zero (pow_ne_zero e hpne) hune') hdec,
    gmk7_cls_classOf_mul (pow_ne_zero e hpne) hune',
    kw_hpG_classOf_p_pow e, kw_hpG_uniformiserClass_pow e,
    kw_hpG_classOf_intCast_coprime hp2 hune,
    jpd4r17t5_fitGate_classAt_def]
  refine gmk6_hil_SquareClass_ext ?_ ?_
  · show ((e : ℕ) : ZMod 2) + 0 = ((a.natAbs.factorization p : ℕ) : ZMod 2)
    rw [he, add_zero]
  · show (1 : ℤˣ) * gmk6_hil_legendreSign p u
      = gmk6_hil_legendreSign p (jpd4r17t5_unitPart p a)
    rw [hu, one_mul]

theorem kw_hpG_FsymbOdd_eq_oddLocalFactor {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    kw_hpFsymbOdd a b ha hb p = jpd4r17t5_oddLocalFactor p a b := by
  have _pin := Classical.em True
  unfold kw_hpFsymbOdd
  rw [jpd4r17t5_oddLocalFactor_eq,
    kw_hpG_classOf_eq_classAt hp2 ha, kw_hpG_classOf_eq_classAt hp2 hb]

theorem kw_hpG_ord2_eq (a : ℤ) :
    kw_hpOrd2 a = a.natAbs.factorization 2 := by
  have _pin := Classical.em True
  unfold kw_hpOrd2
  exact (Nat.factorization_def a.natAbs Nat.prime_two).symm

theorem kw_hpG_odd2_eq {a : ℤ} (_ha : a ≠ 0) :
    kw_hpOdd2 a = jpd4r17t5_unitPart 2 a := by
  have _pin := Classical.em True
  have h2e : (2 : ℤ) ^ a.natAbs.factorization 2 ≠ 0 :=
    pow_ne_zero _ two_ne_zero
  have hdec : (2 : ℤ) ^ a.natAbs.factorization 2 * jpd4r17t5_unitPart 2 a = a := by
    have h := jpd4r17t5_unitPart_decompose 2 a
    rwa [show ((2 : ℕ) : ℤ) = (2 : ℤ) from rfl] at h
  unfold kw_hpOdd2
  rw [kw_hpG_ord2_eq]
  calc a / (2 : ℤ) ^ a.natAbs.factorization 2
      = (2 : ℤ) ^ a.natAbs.factorization 2 * jpd4r17t5_unitPart 2 a
          / (2 : ℤ) ^ a.natAbs.factorization 2 := by rw [hdec]
    _ = jpd4r17t5_unitPart 2 a := Int.mul_ediv_cancel_left _ h2e

theorem kw_hpG_support_eq {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (2 * a.natAbs * b.natAbs).primeFactors \ {2} = jpd4r17t5_oddSupport (a * b) := by
  have _pin := Classical.em True
  have hab : a.natAbs * b.natAbs ≠ 0 :=
    mul_ne_zero (Int.natAbs_ne_zero.mpr ha) (Int.natAbs_ne_zero.mpr hb)
  rw [jpd4r17t5_oddSupport_eq_erase_primeFactors, Int.natAbs_mul,
    ← Finset.sdiff_singleton_eq_erase,
    show (2 * a.natAbs * b.natAbs) = 2 * (a.natAbs * b.natAbs) from by ring,
    Nat.primeFactors_mul two_ne_zero hab, Nat.Prime.primeFactors Nat.prime_two]
  ext q
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton]
  tauto

theorem kw_hpG_bridge {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (∏ p ∈ ((2 * a.natAbs * b.natAbs).primeFactors \ {2}).attach,
        haveI : Fact p.1.Prime :=
          ⟨Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp p.2).1⟩
        kw_hpFsymbOdd a b ha hb p.1)
      * jpd4r14t3_pairTwoZ ((kw_hpOrd2 a : ℕ) : ZMod 2) (kw_hpOdd2 a)
          ((kw_hpOrd2 b : ℕ) : ZMod 2) (kw_hpOdd2 b)
      * jpd4r13t6_hilbR (a : ℝ) (b : ℝ)
    = jpd4r17t5_allPlacesProduct a b := by
  have _pin := Classical.em True
  rw [jpd4r17t5_fitGate_factorised,
    mul_comm (jpd4r17t5_twoFactor a b) (jpd4r17t5_oddComplementProduct a b)]
  congr 1
  congr 1
  ·
    rw [show jpd4r17t5_oddComplementProduct a b
          = ∏ p ∈ jpd4r17t5_oddSupport (a * b), jpd4r17t5_oddLocalFactor p a b from rfl,
      ← kw_hpG_support_eq ha hb,
      (Finset.prod_attach _ (fun p ↦ jpd4r17t5_oddLocalFactor p a b)).symm]
    refine Finset.prod_congr rfl fun p _ ↦ ?_
    have hp2 : p.1 ≠ 2 := fun h ↦ (Finset.mem_sdiff.mp p.2).2
      (Finset.mem_singleton.mpr h)
    haveI : Fact p.1.Prime :=
      ⟨Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp p.2).1⟩
    exact kw_hpG_FsymbOdd_eq_oddLocalFactor hp2 ha hb
  ·
    unfold jpd4r17t5_twoFactor
    rw [kw_hpG_ord2_eq, kw_hpG_ord2_eq, kw_hpG_odd2_eq ha, kw_hpG_odd2_eq hb]

theorem kw_hpG_unitPart_mul (p : ℕ) {a a' : ℤ} (_ha : a ≠ 0) (_ha' : a' ≠ 0) :
    jpd4r17t5_unitPart p (a * a')
      = jpd4r17t5_unitPart p a * jpd4r17t5_unitPart p a' := by
  have _pin := Classical.em True
  unfold jpd4r17t5_unitPart
  rw [Int.sign_mul, Int.natAbs_mul,
    Nat.ordCompl_mul a.natAbs a'.natAbs p]
  push_cast
  ring

theorem kw_hpG_unitPart_two_odd {a : ℤ} (ha : a ≠ 0) :
    (jpd4r17t5_unitPart 2 a) % 2 = 1 := by
  have _pin := Classical.em True
  have h := jpd4r17t5_unitPart_intCast_ne_zero 2 a ha
  rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  omega

theorem kw_hpG_oddLocalFactor_mul_left {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {a a' b : ℤ} (ha : a ≠ 0) (ha' : a' ≠ 0) (_hb : b ≠ 0) :
    jpd4r17t5_oddLocalFactor p (a * a') b
      = jpd4r17t5_oddLocalFactor p a b * jpd4r17t5_oddLocalFactor p a' b := by
  have _pin := Classical.em True
  rw [jpd4r17t5_oddLocalFactor_eq, jpd4r17t5_oddLocalFactor_eq,
    jpd4r17t5_oddLocalFactor_eq, ← kw_hpG_classOf_eq_classAt hp2 (mul_ne_zero ha ha'),
    ← kw_hpG_classOf_eq_classAt hp2 ha, ← kw_hpG_classOf_eq_classAt hp2 ha',
    kw_hpG_classOf_congr _ (mul_ne_zero (Int.cast_ne_zero.mpr ha)
      (Int.cast_ne_zero.mpr ha')) (by push_cast; ring),
    gmk7_cls_classOf_mul (Int.cast_ne_zero.mpr ha) (Int.cast_ne_zero.mpr ha'),
    gmk6_hil_pair_mul_left]

theorem kw_hpG_oddLocalFactor_transparent {p : ℕ} [Fact p.Prime]
    {a b : ℤ} (hpa : ¬ p ∣ a.natAbs) (hpb : ¬ p ∣ b.natAbs) :
    jpd4r17t5_oddLocalFactor p a b = 1 := by
  have _pin := Classical.em True
  rw [jpd4r17t5_oddLocalFactor_eq, jpd4r17t5_classAt_of_not_dvd p a hpa,
    jpd4r17t5_classAt_of_not_dvd p b hpb, gmk6_hil_table_unit_unit]

theorem kw_hpG_epsZ_mul_odd {u v : ℤ} (hu : u % 2 = 1) (hv : v % 2 = 1) :
    jpd4r14t3_epsZ (u * v) = jpd4r14t3_epsZ u + jpd4r14t3_epsZ v := by
  have _pin := Classical.em True
  obtain ⟨k, hk⟩ : ∃ k, u = 2 * k + 1 := ⟨u / 2, by omega⟩
  obtain ⟨m, hm⟩ : ∃ m, v = 2 * m + 1 := ⟨v / 2, by omega⟩
  unfold jpd4r14t3_epsZ
  have h1 : (u * v - 1) / 2 = 2 * k * m + k + m := by
    rw [show (u * v - 1 : ℤ) = 2 * (2 * k * m + k + m) from by rw [hk, hm]; ring]
    exact Int.mul_ediv_cancel_left _ (by norm_num)
  have h2 : (u - 1) / 2 = k := by
    rw [show (u - 1 : ℤ) = 2 * k from by rw [hk]; ring]
    exact Int.mul_ediv_cancel_left _ (by norm_num)
  have h3 : (v - 1) / 2 = m := by
    rw [show (v - 1 : ℤ) = 2 * m from by rw [hm]; ring]
    exact Int.mul_ediv_cancel_left _ (by norm_num)
  rw [h1, h2, h3, ← Int.cast_add,
    show (2 * k * m + k + m : ℤ) = (k + m) + 2 * (k * m) from by ring,
    Int.cast_add, Int.cast_mul,
    show ((2 : ℤ) : ZMod 2) = 0 from by decide,
    zero_mul, add_zero]

theorem kw_hpG_eight_dvd_sq_sub_one {u : ℤ} (hu : u % 2 = 1) :
    (8 : ℤ) ∣ u ^ 2 - 1 := by
  have _pin := Classical.em True
  obtain ⟨k, hk⟩ : ∃ k, u = 2 * k + 1 := ⟨u / 2, by omega⟩
  have h2 : (2 : ℤ) ∣ k * (k + 1) := by
    rcases Int.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · exact ⟨j * (k + 1), by rw [hj]; ring⟩
    · exact ⟨k * (j + 1), by rw [hj]; ring⟩
  obtain ⟨K, hK⟩ := h2
  exact ⟨K, by rw [show (u ^ 2 - 1 : ℤ) = 4 * (k * (k + 1)) from by
    rw [hk]; ring, hK]; ring⟩

theorem kw_hpG_omegaZ_mul_odd {u v : ℤ} (hu : u % 2 = 1) (hv : v % 2 = 1) :
    jpd4r14t3_omegaZ (u * v) = jpd4r14t3_omegaZ u + jpd4r14t3_omegaZ v := by
  have _pin := Classical.em True
  obtain ⟨K, hK⟩ := kw_hpG_eight_dvd_sq_sub_one hu
  obtain ⟨M, hM⟩ := kw_hpG_eight_dvd_sq_sub_one hv
  unfold jpd4r14t3_omegaZ
  rw [show ((u * v) ^ 2 - 1 : ℤ)
        = (u ^ 2 - 1) + (v ^ 2 - 1) + (u ^ 2 - 1) * (v ^ 2 - 1) from by ring,
    hK, hM, show (8 * K + 8 * M + 8 * K * (8 * M) : ℤ)
        = 8 * (K + M + 2 * (4 * K * M)) from by ring,
    Int.mul_ediv_cancel_left _ (by norm_num),
    Int.mul_ediv_cancel_left _ (by norm_num),
    Int.mul_ediv_cancel_left _ (by norm_num),
    ← Int.cast_add,
    show (K + M + 2 * (4 * K * M) : ℤ) = (K + M) + 2 * (4 * K * M) from by ring,
    Int.cast_add, Int.cast_mul,
    show ((2 : ℤ) : ZMod 2) = 0 from by decide,
    zero_mul, add_zero]

theorem kw_hpG_twoFactor_mul_left {a a' b : ℤ} (ha : a ≠ 0) (ha' : a' ≠ 0)
    (_hb : b ≠ 0) :
    jpd4r17t5_twoFactor (a * a') b
      = jpd4r17t5_twoFactor a b * jpd4r17t5_twoFactor a' b := by
  have _pin := Classical.em True
  unfold jpd4r17t5_twoFactor jpd4r14t3_pairTwoZ
  rw [kw_hpG_unitPart_mul 2 ha ha',
    kw_hpG_epsZ_mul_odd (kw_hpG_unitPart_two_odd ha)
      (kw_hpG_unitPart_two_odd ha'),
    kw_hpG_omegaZ_mul_odd (kw_hpG_unitPart_two_odd ha)
      (kw_hpG_unitPart_two_odd ha'),
    Int.natAbs_mul, Nat.factorization_mul (Int.natAbs_ne_zero.mpr ha)
      (Int.natAbs_ne_zero.mpr ha')]
  simp only [Finsupp.add_apply, Nat.cast_add]
  rw [← gmk6_hil_units_pow_val_add]
  congr 2
  ring

theorem kw_hpG_hilbR_mul_left {a a' : ℤ} (ha : a ≠ 0) (ha' : a' ≠ 0) (b : ℤ) :
    jpd4r13t6_hilbR ((a * a' : ℤ) : ℝ) (b : ℝ)
      = jpd4r13t6_hilbR (a : ℝ) (b : ℝ) * jpd4r13t6_hilbR (a' : ℝ) (b : ℝ) := by
  have _pin := Classical.em True
  rcases lt_or_ge (b : ℝ) 0 with hb0 | hb0
  · rcases lt_or_gt_of_ne ha with hla | hla <;>
      rcases lt_or_gt_of_ne ha' with hla' | hla' <;>
      simp only [Int.cast_mul] <;>
      [(rw [jpd4r14t4_hilbR_left_nonneg _ _
          (le_of_lt (mul_pos_of_neg_of_neg (by exact_mod_cast hla)
            (by exact_mod_cast hla'))),
        jpd4r14t4_hilbR_neg_neg _ _ (by exact_mod_cast hla) hb0,
        jpd4r14t4_hilbR_neg_neg _ _ (by exact_mod_cast hla') hb0]; decide);
       (rw [jpd4r14t4_hilbR_neg_neg _ _
          (mul_neg_of_neg_of_pos (by exact_mod_cast hla)
            (by exact_mod_cast hla')) hb0,
        jpd4r14t4_hilbR_neg_neg _ _ (by exact_mod_cast hla) hb0,
        jpd4r14t4_hilbR_left_nonneg _ _ (le_of_lt (by exact_mod_cast hla'))]; decide);
       (rw [jpd4r14t4_hilbR_neg_neg _ _
          (mul_neg_of_pos_of_neg (by exact_mod_cast hla)
            (by exact_mod_cast hla')) hb0,
        jpd4r14t4_hilbR_left_nonneg _ _ (le_of_lt (by exact_mod_cast hla)),
        jpd4r14t4_hilbR_neg_neg _ _ (by exact_mod_cast hla') hb0]; decide);
       (rw [jpd4r14t4_hilbR_left_nonneg _ _
          (le_of_lt (mul_pos (show (0:ℝ) < a from by exact_mod_cast hla)
            (by exact_mod_cast hla'))),
        jpd4r14t4_hilbR_left_nonneg _ _ (le_of_lt (by exact_mod_cast hla)),
        jpd4r14t4_hilbR_left_nonneg _ _ (le_of_lt (by exact_mod_cast hla'))];
        decide)]
  · rw [jpd4r14t4_hilbR_right_nonneg _ _ hb0,
      jpd4r14t4_hilbR_right_nonneg _ _ hb0,
      jpd4r14t4_hilbR_right_nonneg _ _ hb0, one_mul]

theorem kw_hpG_oddSupport_subset {a b : ℤ} (hb : b ≠ 0)
    (hdvd : a.natAbs ∣ b.natAbs) :
    jpd4r17t5_oddSupport a ⊆ jpd4r17t5_oddSupport b := by
  have _pin := Classical.em True
  rw [jpd4r17t5_oddSupport_eq_erase_primeFactors,
    jpd4r17t5_oddSupport_eq_erase_primeFactors]
  exact Finset.erase_subset_erase _
    (Nat.primeFactors_mono hdvd (Int.natAbs_ne_zero.mpr hb))

theorem kw_hpG_oddComplementProduct_extend {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    {S : Finset ℕ} (hsub : jpd4r17t5_oddSupport (a * b) ⊆ S)
    (hSp : ∀ p ∈ S, p.Prime ∧ p ≠ 2) :
    jpd4r17t5_oddComplementProduct a b
      = ∏ p ∈ S, jpd4r17t5_oddLocalFactor p a b := by
  have _pin := Classical.em True
  unfold jpd4r17t5_oddComplementProduct
  have habne : (a * b).natAbs ≠ 0 := by
    rw [Int.natAbs_mul]
    exact mul_ne_zero (Int.natAbs_ne_zero.mpr ha) (Int.natAbs_ne_zero.mpr hb)
  refine Finset.prod_subset hsub ?_
  intro p hpS hpnab
  obtain ⟨hpp, hp2⟩ := hSp p hpS
  haveI : Fact p.Prime := ⟨hpp⟩
  have hnab : ¬ p ∣ (a * b).natAbs := fun hd ↦ hpnab (by
    rw [jpd4r17t5_oddSupport_eq_erase_primeFactors, Finset.mem_erase]
    exact ⟨hp2, Nat.mem_primeFactors.mpr ⟨hpp, hd, habne⟩⟩)
  rw [Int.natAbs_mul] at hnab
  exact kw_hpG_oddLocalFactor_transparent
    (fun hd ↦ hnab (Dvd.dvd.mul_right hd _))
    (fun hd ↦ hnab (Dvd.dvd.mul_left hd _))

theorem kw_hpG_allPlacesProduct_mul_left {a a' b : ℤ} (ha : a ≠ 0)
    (ha' : a' ≠ 0) (hb : b ≠ 0) :
    jpd4r17t5_allPlacesProduct (a * a') b
      = jpd4r17t5_allPlacesProduct a b * jpd4r17t5_allPlacesProduct a' b := by
  have _pin := Classical.em True
  set S := jpd4r17t5_oddSupport (a * a' * b) with hS
  have hSp : ∀ p ∈ S, p.Prime ∧ p ≠ 2 := fun p hp ↦
    jpd4r17t5_mem_oddSupport _ hp
  have hne := mul_ne_zero (mul_ne_zero ha ha') hb
  have hsub1 : jpd4r17t5_oddSupport (a * b) ⊆ S := by
    rw [hS]; exact kw_hpG_oddSupport_subset hne
      (by rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul]
          exact Nat.mul_dvd_mul_right (Nat.dvd_mul_right _ _) _)
  have hsub2 : jpd4r17t5_oddSupport (a' * b) ⊆ S := by
    rw [hS]; exact kw_hpG_oddSupport_subset hne
      (by rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul]
          exact Nat.mul_dvd_mul_right (Nat.dvd_mul_left _ _) _)
  rw [jpd4r17t5_fitGate_factorised, jpd4r17t5_fitGate_factorised,
    jpd4r17t5_fitGate_factorised,
    kw_hpG_oddComplementProduct_extend (mul_ne_zero ha ha') hb
      subset_rfl hSp,
    kw_hpG_oddComplementProduct_extend ha hb hsub1 hSp,
    kw_hpG_oddComplementProduct_extend ha' hb hsub2 hSp,
    kw_hpG_twoFactor_mul_left ha ha' hb, kw_hpG_hilbR_mul_left ha ha' b]
  have hodd : ∀ p ∈ S, jpd4r17t5_oddLocalFactor p (a * a') b
      = jpd4r17t5_oddLocalFactor p a b * jpd4r17t5_oddLocalFactor p a' b := by
    intro p hp
    haveI : Fact p.Prime := ⟨(hSp p hp).1⟩
    exact kw_hpG_oddLocalFactor_mul_left (hSp p hp).2 ha ha' hb
  rw [Finset.prod_congr rfl hodd, Finset.prod_mul_distrib]
  simp only [mul_comm, mul_left_comm, mul_assoc]

theorem kw_hpG_pairTwoZ_symm (α : ZMod 2) (u : ℤ) (β : ZMod 2) (v : ℤ) :
    jpd4r14t3_pairTwoZ α u β v = jpd4r14t3_pairTwoZ β v α u := by
  have _pin := Classical.em True
  unfold jpd4r14t3_pairTwoZ
  congr 2
  ring

theorem kw_hpG_allPlacesProduct_symm (a b : ℤ) :
    jpd4r17t5_allPlacesProduct a b = jpd4r17t5_allPlacesProduct b a := by
  have _pin := Classical.em True
  rw [jpd4r17t5_fitGate_factorised, jpd4r17t5_fitGate_factorised,
    jpd4r13t6_hilbR_symm]
  congr 1
  congr 1
  · unfold jpd4r17t5_twoFactor
    exact kw_hpG_pairTwoZ_symm _ _ _ _
  · unfold jpd4r17t5_oddComplementProduct
    rw [mul_comm a b]
    refine Finset.prod_congr rfl fun p hp ↦ ?_
    haveI : Fact p.Prime := ⟨(jpd4r17t5_mem_oddSupport _ hp).1⟩
    rw [jpd4r17t5_oddLocalFactor_eq, jpd4r17t5_oddLocalFactor_eq,
      gmk6_hil_pair_symm]

theorem kw_hpG_allPlacesProduct_mul_right {a b b' : ℤ} (ha : a ≠ 0)
    (hb : b ≠ 0) (hb' : b' ≠ 0) :
    jpd4r17t5_allPlacesProduct a (b * b')
      = jpd4r17t5_allPlacesProduct a b * jpd4r17t5_allPlacesProduct a b' := by
  have _pin := Classical.em True
  rw [kw_hpG_allPlacesProduct_symm, kw_hpG_allPlacesProduct_mul_left hb hb' ha,
    kw_hpG_allPlacesProduct_symm b a, kw_hpG_allPlacesProduct_symm b' a]

theorem kw_hpG_allPlaces_two_two :
    jpd4r17t5_allPlacesProduct (2 : ℤ) (2 : ℤ) = 1 := by
  have _pin := Classical.em True
  rw [jpd4r17t5_fitGate_factorised]
  unfold jpd4r17t5_oddComplementProduct
  rw [show jpd4r17t5_oddSupport ((2 : ℤ) * 2) = ∅ from by
      rw [jpd4r17t5_oddSupport_eq_erase_primeFactors,
        show ((2 : ℤ) * 2).natAbs = 2 * 2 from rfl,
        Nat.primeFactors_mul two_ne_zero two_ne_zero,
        Nat.Prime.primeFactors Nat.prime_two, Finset.union_self]
      simp,
    Finset.prod_empty, mul_one,
    jpd4r14t4_hilbR_left_nonneg _ _ (by norm_num), mul_one]
  unfold jpd4r17t5_twoFactor
  rw [jpd4r17t5_unitPart_two_lit, show ((2 : ℤ)).natAbs = 2 from rfl,
    Nat.Prime.factorization_self Nat.prime_two, Nat.cast_one]
  decide

theorem kw_hpG_allPlaces_negOne_two :
    jpd4r17t5_allPlacesProduct (-1 : ℤ) (2 : ℤ) = 1 := by
  have _pin := Classical.em True
  rw [jpd4r17t5_fitGate_factorised]
  unfold jpd4r17t5_oddComplementProduct
  rw [show jpd4r17t5_oddSupport ((-1 : ℤ) * 2) = ∅ from by
      rw [jpd4r17t5_oddSupport_eq_erase_primeFactors,
        show ((-1 : ℤ) * 2).natAbs = 2 from rfl,
        Nat.Prime.primeFactors Nat.prime_two]
      simp,
    Finset.prod_empty, mul_one,
    jpd4r14t4_hilbR_right_nonneg _ _ (by norm_num), mul_one]
  unfold jpd4r17t5_twoFactor
  rw [jpd4r17t5_unitPart_two_lit, show ((2 : ℤ)).natAbs = 2 from rfl,
    Nat.Prime.factorization_self Nat.prime_two, Nat.cast_one,
    jpd4r17t5_unitPart_of_not_dvd 2 (-1 : ℤ) (by decide),
    show ((-1 : ℤ)).natAbs = 1 from rfl,
    Nat.factorization_one, Finsupp.zero_apply, Nat.cast_zero]
  decide

theorem kw_hpG_allPlaces_negOne_oddPrime (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) :
    jpd4r17t5_allPlacesProduct (-1 : ℤ) (q : ℤ) = 1 := by
  have _pin := Classical.em True
  have hq0 : (q : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).pos.ne'
  have hkey : jpd4r17t5_allPlacesProduct (-1 : ℤ) ((-1 : ℤ) * (q : ℤ))
      = jpd4r17t5_allPlacesProduct (-1 : ℤ) (-1 : ℤ)
        * jpd4r17t5_allPlacesProduct (-1 : ℤ) (q : ℤ) :=
    kw_hpG_allPlacesProduct_mul_right (by norm_num) (by norm_num) hq0
  rw [show ((-1 : ℤ) * (q : ℤ)) = -(q : ℤ) from by ring,
    jpd4r17t5_allPlaces_negOne_negPrime q hq2,
    jpd4r17t5_allPlaces_signWindow (-1) (by simp) (-1) (by simp)] at hkey
  rwa [one_mul, eq_comm] at hkey

theorem kw_hpG_allPlaces_one_left (b : ℤ) :
    jpd4r17t5_allPlacesProduct (1 : ℤ) b = 1 := by
  have _pin := Classical.em True
  rw [jpd4r17t5_fitGate_factorised,
    jpd4r14t4_hilbR_left_nonneg _ _ (by norm_num), mul_one]
  unfold jpd4r17t5_oddComplementProduct jpd4r17t5_twoFactor
  rw [show ((1 : ℤ)).natAbs = 1 from rfl, Nat.factorization_one,
    Finsupp.zero_apply, Nat.cast_zero,
    jpd4r17t5_unitPart_of_not_dvd 2 (1 : ℤ) (by decide)]
  have hodd' : ∀ p ∈ jpd4r17t5_oddSupport ((1 : ℤ) * b),
      jpd4r17t5_oddLocalFactor p (1 : ℤ) b = 1 := fun p hp ↦ by
    haveI : Fact p.Prime := ⟨(jpd4r17t5_mem_oddSupport _ hp).1⟩
    rw [jpd4r17t5_oddLocalFactor_eq, jpd4r17t5_classAt_of_not_dvd p (1 : ℤ)
        (by simp only [show ((1 : ℤ)).natAbs = 1 from rfl, Nat.dvd_one]
            exact (jpd4r17t5_mem_oddSupport _ hp).1.one_lt.ne'),
      jpd4r17t5_legendreSign_one, gmk6_hil_unitClass_one, gmk6_hil_pair_one_left]
  rw [Finset.prod_congr rfl hodd', Finset.prod_const_one, mul_one]
  unfold jpd4r14t3_pairTwoZ
  rw [show jpd4r14t3_epsZ (1 : ℤ) = 0 from by unfold jpd4r14t3_epsZ; decide,
    show jpd4r14t3_omegaZ (1 : ℤ) = 0 from by unfold jpd4r14t3_omegaZ; decide]
  simp

theorem kw_hpG_allPlaces_natPrime_natPrime (p q : ℕ) [Fact p.Prime]
    [Fact q.Prime] :
    jpd4r17t5_allPlacesProduct (p : ℤ) (q : ℤ) = 1 := by
  have _pin := Classical.em True
  rcases eq_or_ne p 2 with hp2 | hp2 <;> rcases eq_or_ne q 2 with hq2 | hq2
  · subst hp2; subst hq2; exact kw_hpG_allPlaces_two_two
  · subst hp2; exact jpd4r17t5_allPlaces_two_oddPrime q hq2
  · subst hq2
    rw [kw_hpG_allPlacesProduct_symm]
    exact jpd4r17t5_allPlaces_two_oddPrime p hp2
  · rcases eq_or_ne p q with hpq | hpq
    · subst hpq; exact jpd4r17t5_allPlaces_uniformiserSelf p hp2
    · exact jpd4r17t5_allPlaces_distinctOddPrimes p q hp2 hq2 hpq

theorem kw_hpG_allPlaces_negOne_intPrime {q : ℤ} (hq : Prime q) :
    jpd4r17t5_allPlacesProduct (-1 : ℤ) q = 1 := by
  have _pin := Classical.em True
  have hq0 : q.natAbs.Prime := Int.prime_iff_natAbs_prime.mp hq
  haveI : Fact q.natAbs.Prime := ⟨hq0⟩
  have hatom : jpd4r17t5_allPlacesProduct (-1 : ℤ) ((q.natAbs : ℕ) : ℤ) = 1 := by
    rcases eq_or_ne q.natAbs 2 with h2 | h2
    · rw [h2]; exact_mod_cast kw_hpG_allPlaces_negOne_two
    · exact kw_hpG_allPlaces_negOne_oddPrime q.natAbs h2
  rcases lt_or_gt_of_ne hq.ne_zero with hneg | hpos
  · rw [show q = (-1 : ℤ) * ((q.natAbs : ℕ) : ℤ) from by
        rw [Int.natCast_natAbs, abs_of_neg hneg]; ring,
      kw_hpG_allPlacesProduct_mul_right (by norm_num) (by norm_num)
        (Nat.cast_ne_zero.mpr hq0.pos.ne'),
      jpd4r17t5_allPlaces_signWindow (-1) (by simp) (-1) (by simp), one_mul,
      hatom]
  · rw [show q = ((q.natAbs : ℕ) : ℤ) from by
        rw [Int.natCast_natAbs, abs_of_pos hpos], hatom]

theorem kw_hpG_allPlaces_negOne_left {b : ℤ} (hb : b ≠ 0) :
    jpd4r17t5_allPlacesProduct (-1 : ℤ) b = 1 := by
  have _pin := Classical.em True
  revert hb
  refine UniqueFactorizationMonoid.induction_on_prime b ?_ ?_ ?_
  · intro h; exact absurd rfl h
  · intro u hu _
    rcases Int.isUnit_iff.mp hu with rfl | rfl
    · exact jpd4r17t5_allPlaces_signWindow (-1) (by simp) 1 (by simp)
    · exact jpd4r17t5_allPlaces_signWindow (-1) (by simp) (-1) (by simp)
  · intro c q hc hq ih _
    rw [kw_hpG_allPlacesProduct_mul_right (by norm_num) hq.ne_zero hc, ih hc,
      mul_one, kw_hpG_allPlaces_negOne_intPrime hq]

theorem kw_hpG_allPlaces_natPrime_left (p : ℕ) [Fact p.Prime] {b : ℤ}
    (hb : b ≠ 0) :
    jpd4r17t5_allPlacesProduct (p : ℤ) b = 1 := by
  have _pin := Classical.em True
  have hp0 : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).pos.ne'
  revert hb
  refine UniqueFactorizationMonoid.induction_on_prime b ?_ ?_ ?_
  · intro h; exact absurd rfl h
  · intro u hu _
    rcases Int.isUnit_iff.mp hu with rfl | rfl
    · rw [kw_hpG_allPlacesProduct_symm]; exact kw_hpG_allPlaces_one_left _
    · rw [kw_hpG_allPlacesProduct_symm]
      exact kw_hpG_allPlaces_negOne_left hp0
  · intro c q hc hq ih _
    rw [kw_hpG_allPlacesProduct_mul_right hp0 hq.ne_zero hc, ih hc, mul_one]
    have hq0 : q.natAbs.Prime := Int.prime_iff_natAbs_prime.mp hq
    haveI : Fact q.natAbs.Prime := ⟨hq0⟩
    rcases lt_or_gt_of_ne hq.ne_zero with hneg | hpos
    · rw [show q = (-1 : ℤ) * ((q.natAbs : ℕ) : ℤ) from by
          rw [Int.natCast_natAbs, abs_of_neg hneg]; ring,
        kw_hpG_allPlacesProduct_mul_right hp0 (by norm_num)
          (Nat.cast_ne_zero.mpr hq0.pos.ne'),
        kw_hpG_allPlacesProduct_symm (p : ℤ) (-1 : ℤ),
        kw_hpG_allPlaces_negOne_left hp0, one_mul,
        kw_hpG_allPlaces_natPrime_natPrime p q.natAbs]
    · rw [show q = ((q.natAbs : ℕ) : ℤ) from by
          rw [Int.natCast_natAbs, abs_of_pos hpos],
        kw_hpG_allPlaces_natPrime_natPrime p q.natAbs]

theorem kw_hpG_allPlacesProduct_eq_one {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    jpd4r17t5_allPlacesProduct a b = 1 := by
  have _pin := Classical.em True
  revert ha
  refine UniqueFactorizationMonoid.induction_on_prime a ?_ ?_ ?_
  · intro h; exact absurd rfl h
  · intro u hu _
    rcases Int.isUnit_iff.mp hu with rfl | rfl
    · exact kw_hpG_allPlaces_one_left b
    · exact kw_hpG_allPlaces_negOne_left hb
  · intro c q hc hq ih _
    rw [kw_hpG_allPlacesProduct_mul_left hq.ne_zero hc hb, ih hc, mul_one]
    have hq0 : q.natAbs.Prime := Int.prime_iff_natAbs_prime.mp hq
    haveI : Fact q.natAbs.Prime := ⟨hq0⟩
    rcases lt_or_gt_of_ne hq.ne_zero with hneg | hpos
    · rw [show q = (-1 : ℤ) * ((q.natAbs : ℕ) : ℤ) from by
          rw [Int.natCast_natAbs, abs_of_neg hneg]; ring,
        kw_hpG_allPlacesProduct_mul_left (by norm_num)
          (Nat.cast_ne_zero.mpr hq0.pos.ne') hb,
        kw_hpG_allPlaces_negOne_left hb, one_mul,
        kw_hpG_allPlaces_natPrime_left q.natAbs hb]
    · rw [show q = ((q.natAbs : ℕ) : ℤ) from by
          rw [Int.natCast_natAbs, abs_of_pos hpos],
        kw_hpG_allPlaces_natPrime_left q.natAbs hb]

theorem kw_HSCluster_C_G_formulaProduct_proved :
    kw_HSCluster_C_G_formulaProduct := by
  have _pin := Classical.em True
  intro a b ha hb
  rw [kw_hpG_bridge ha hb]
  exact kw_hpG_allPlacesProduct_eq_one ha hb

end FLT.NumberTheory
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section
section

p2m_open "IsDedekindDomain P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.IsDedekindDomain.HeightOneSpectrum NumberField P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.NumberField"
p2m_open_scoped "Classical P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.Classical"

namespace FLT
namespace NumberTheory

open FLT.CampGenuineMk
open FLT.JpssD4KubotaPTwoHilbertSolvabilityIdentification

theorem kw_hpSolvAt_ringEquiv {K : Type*} [Field K]
    (a b : ℚ) (v : HeightOneSpectrum (𝓞 ℚ))
    (φ : v.adicCompletion ℚ ≃+* K) :
    kw_hpSolvAt a b v ↔
      ∃ z x y : K, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
        z ^ 2 - (a : K) * x ^ 2 - (b : K) * y ^ 2 = 0 := by
  have _pin := Classical.em True
  have halg : ∀ q : ℚ, algebraMap ℚ (v.adicCompletion ℚ) q
      = (q : v.adicCompletion ℚ) := fun q ↦ eq_ratCast _ q
  constructor
  · rintro ⟨z, x, y, hnt, heq⟩
    refine ⟨φ z, φ x, φ y,
      fun ⟨hz, hx, hy⟩ ↦ hnt ⟨φ.injective (by rw [hz, _root_.map_zero]),
        φ.injective (by rw [hx, _root_.map_zero]), φ.injective (by rw [hy, _root_.map_zero])⟩, ?_⟩
    have h := congrArg φ heq
    simpa only [halg, map_sub, map_mul, map_pow, map_ratCast, _root_.map_zero] using h
  · rintro ⟨z, x, y, hnt, heq⟩
    refine ⟨φ.symm z, φ.symm x, φ.symm y,
      fun ⟨hz, hx, hy⟩ ↦ hnt ⟨φ.symm.injective (by rw [hz, _root_.map_zero]),
        φ.symm.injective (by rw [hx, _root_.map_zero]),
        φ.symm.injective (by rw [hy, _root_.map_zero])⟩, ?_⟩
    have h := congrArg φ.symm heq
    simp only [halg, map_sub, map_mul, map_pow, map_ratCast, _root_.map_zero] at h ⊢
    exact h

section PadicEquivSection

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

private noncomputable def kw_hp_padicCast {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (h : p = q) :
    ℚ_[p] ≃+* ℚ_[q] := by
  subst h; exact RingEquiv.refl _

theorem kw_hpSolvAt_iff_jpd4_two_proved : kw_hpSolvAt_iff_jpd4_two := by
  have _pin := Classical.em True
  intro a b _ha _hb v hp2
  have φ : v.adicCompletion ℚ ≃+* ℚ_[2] :=
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toRingEquiv.trans
      (kw_hp_padicCast hp2)
  exact kw_hpSolvAt_ringEquiv a b v φ

theorem kw_hpSolvAt_iff_gmk8_odd_proved : kw_hpSolvAt_iff_gmk8_odd := by
  have _pin := Classical.em True
  intro a b _ha _hb v _hp2
  rw [kw_hpSolvAt_ringEquiv a b v
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toRingEquiv,
    gmk8_cls_solvable_def]
  constructor
  · rintro ⟨z, x, y, hnt, heq⟩
    refine ⟨x, y, z, ?_, by linear_combination heq⟩
    by_contra h; push Not at h
    exact hnt ⟨h.2.2, h.1, h.2.1⟩
  · rintro ⟨x, y, z, hnt, heq⟩
    refine ⟨z, x, y, fun ⟨hz, hx, hy⟩ ↦ ?_, by linear_combination heq⟩
    rcases hnt with h | h | h
    · exact h hx
    · exact h hy
    · exact h hz

end PadicEquivSection
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end FLT.NumberTheory
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section
section

p2m_open "IsDedekindDomain P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.IsDedekindDomain.HeightOneSpectrum NumberField P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.NumberField"
p2m_open_scoped "Classical P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.Classical"

namespace FLT
namespace NumberTheory

noncomputable def kw_hp_supp (a b : ℚ) : Finset (HeightOneSpectrum (𝓞 ℚ)) :=
  let N : ℕ := 2 * (a.num.natAbs * a.den * (b.num.natAbs * b.den))
  N.primeFactors.attach.image fun pp ↦
    Rat.HeightOneSpectrum.primesEquiv.symm
      ⟨pp.1, Nat.prime_of_mem_primeFactors pp.2⟩

noncomputable def kw_hp_Rf (a b : ℚ) : Finset (HeightOneSpectrum (𝓞 ℚ)) :=
  (kw_hp_supp a b).filter fun v ↦ ¬ kw_hpSolvAt a b v

theorem kw_hp_solvAt_of_notMem_supp (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∉ kw_hp_supp a b) :
    kw_hpSolvAt a b v := by
  have _pin := Classical.em True

  let N : ℕ := 2 * (a.num.natAbs * a.den * (b.num.natAbs * b.den))
  have hN : N ≠ 0 := by
    have : a.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr ha)
    have : b.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hb)
    positivity
  let p : ℕ := (Rat.HeightOneSpectrum.primesEquiv v : ℕ)
  have hpprime : p.Prime := (Rat.HeightOneSpectrum.primesEquiv v).2
  have hpN : ¬ p ∣ N := by
    intro hdvd
    apply hv
    simp only [kw_hp_supp, Finset.mem_image, Finset.mem_attach, true_and,
      Subtype.exists]
    exact ⟨p, Nat.mem_primeFactors.mpr ⟨hpprime, hdvd, hN⟩, by
      simp only [Equiv.symm_apply_eq]; exact Subtype.ext rfl⟩
  have hp2 : p ≠ 2 := fun h ↦ hpN (h ▸ dvd_mul_right 2 _)
  haveI hpfact : Fact p.Prime := ⟨hpprime⟩
  have hpa : ‖(a : ℚ_[p])‖ = 1 := kw_hjoint_padic_norm_ratCast_eq_one
    (fun h ↦ hpN (Dvd.dvd.mul_left (Dvd.dvd.mul_right (Dvd.dvd.mul_right h _) _) 2))
    (fun h ↦ hpN (Dvd.dvd.mul_left (Dvd.dvd.mul_right (Dvd.dvd.mul_left h _) _) 2))
  have hpb : ‖(b : ℚ_[p])‖ = 1 := kw_hjoint_padic_norm_ratCast_eq_one
    (fun h ↦ hpN (Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_right h _) _) 2))
    (fun h ↦ hpN (Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_left h _) _) 2))
  have hsplit : kw_isSplitAtPlace a b v :=
    kw_hjoint_isSplitAtPlace_of_units
      kw_hjoint_padic_ternaryIsotropic_proved a b ha hb v hp2 hpa hpb

  exact (not_iff_not.mp (kw_HSCluster_A_fin_proved a b ha hb v)).mp hsplit

theorem kw_hp_Rf_mem_iff (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    v ∈ kw_hp_Rf a b ↔ ¬ kw_hpSolvAt a b v := by
  have _pin := Classical.em True
  simp only [kw_hp_Rf, Finset.mem_filter]
  constructor
  · exact fun ⟨_, h⟩ ↦ h
  · intro hns
    exact ⟨by_contra fun hv ↦ hns (kw_hp_solvAt_of_notMem_supp a b ha hb v hv), hns⟩

abbrev kw_hp_W_parityStep : Prop :=
  kw_hpSolvAt_iff_gmk8_odd →
  kw_hpSolvAt_iff_jpd4_two →
  kw_HSCluster_C_F_two →
  kw_HSCluster_C_G_formulaProduct →
  ∀ (a b : ℚ) (_ : a ≠ 0) (_ : b ≠ 0),
    Even ((kw_hp_Rf a b).card + (if (a : ℝ) < 0 ∧ (b : ℝ) < 0 then 1 else 0))

theorem kw_HSCluster_C_W_wire_of_parityStep (hW2 : kw_hp_W_parityStep) :
    kw_HSCluster_C_W_wire := by
  have _pin := Classical.em True
  intro hOdd hTwo hF2 hG a b ha hb
  exact ⟨kw_hp_Rf a b, fun v ↦ kw_hp_Rf_mem_iff a b ha hb v,
    hW2 hOdd hTwo hF2 hG a b ha hb⟩

end FLT.NumberTheory
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section
section

p2m_open "IsDedekindDomain P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.IsDedekindDomain.HeightOneSpectrum NumberField P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.NumberField"
p2m_open_scoped "Classical P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.Classical"

namespace FLT
namespace NumberTheory

open FLT.CampGenuineMk
open FLT.JpssD4KubotaPTwoHilbertTable
open FLT.JpssD4KubotaPTwoHilbertSolvabilityIdentification
open FLT.JpssD4GJProp83MetaplecticKubotaCoverCarrier
open FLT.JpssD4KubotaTameSymbolUniformWindowSlice

theorem kw_hp_units_neg_one_iff (u : ℤˣ) : u = -1 ↔ ¬ u = 1 := by
  have _pin := Classical.em True
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp

theorem kw_hp_units_prod_parity {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℤˣ) :
    ∏ i ∈ s, f i = 1 ↔ Even (s.filter (fun i ↦ f i = -1)).card := by
  have _pin := Classical.em True
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.filter_insert]
    rcases Int.units_eq_one_or (f a) with hfa | hfa
    · simp [hfa, ih]
    · rw [if_pos hfa, Finset.card_insert_of_notMem
        (fun h ↦ ha (Finset.mem_of_mem_filter _ h)), Nat.even_add_one, hfa,
        show ∀ x : ℤˣ, (-1) * x = 1 ↔ ¬ x = 1 from fun x ↦ by
          rcases Int.units_eq_one_or x with rfl | rfl <;> simp]
      exact ih.not

theorem kw_hp_epsZ_omegaZ_congr8 {u v : ℤ} (hu : u % 2 = 1) (hv : v % 2 = 1)
    (h8 : (8 : ℤ) ∣ u - v) :
    jpd4r14t3_epsZ u = jpd4r14t3_epsZ v ∧
      jpd4r14t3_omegaZ u = jpd4r14t3_omegaZ v := by
  have _pin := Classical.em True
  refine ⟨?_, ?_⟩
  · rcases (show u % 4 = 1 ∨ u % 4 = 3 by omega) with h4 | h4
    · rw [jpd4r16t6_epsZ_zero_of_oneMod4 u h4,
        jpd4r16t6_epsZ_zero_of_oneMod4 v (by omega)]
    · rw [jpd4r16t6_epsZ_one_of_threeMod4 u h4,
        jpd4r16t6_epsZ_one_of_threeMod4 v (by omega)]
  ·
    have h8u : (8 : ℤ) ∣ u ^ 2 - 1 := by
      obtain ⟨k, hk⟩ : ∃ k, u = 2 * k + 1 := ⟨(u - 1) / 2, by omega⟩
      obtain ⟨m, hm⟩ := Int.even_mul_succ_self k
      exact ⟨m, by rw [hk]; linear_combination 4 * hm⟩
    have h8v : (8 : ℤ) ∣ v ^ 2 - 1 := by
      obtain ⟨k, hk⟩ : ∃ k, v = 2 * k + 1 := ⟨(v - 1) / 2, by omega⟩
      obtain ⟨m, hm⟩ := Int.even_mul_succ_self k
      exact ⟨m, by rw [hk]; linear_combination 4 * hm⟩
    have h16 : (16 : ℤ) ∣ u ^ 2 - v ^ 2 := by
      obtain ⟨j, hj⟩ := h8
      obtain ⟨l, hl⟩ : ∃ l, u + v = 2 * l := ⟨(u + v) / 2, by omega⟩
      exact ⟨j * l, by linear_combination (u + v) * hj + 8 * j * hl⟩
    unfold jpd4r14t3_omegaZ
    rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
    omega

theorem kw_hp_ord2_odd2_decomp {c : ℤ} (hc : c ≠ 0) :
    c = 2 ^ kw_hpOrd2 c * kw_hpOdd2 c ∧ kw_hpOdd2 c % 2 = 1 := by
  have _pin := Classical.em True
  simp only [kw_hpOrd2, kw_hpOdd2]
  have hdvd : (2 : ℤ) ^ padicValNat 2 c.natAbs ∣ c := by
    have h := Int.natCast_dvd_natCast.mpr
      (pow_padicValNat_dvd : (2:ℕ) ^ padicValNat 2 c.natAbs ∣ c.natAbs)
    simpa using h.trans (Int.natAbs_dvd.mpr dvd_rfl)
  refine ⟨(Int.mul_ediv_cancel' hdvd).symm, ?_⟩
  rcases Int.even_or_odd (c / 2 ^ padicValNat 2 c.natAbs) with ⟨k, hk⟩ | ⟨k, hk⟩
  · exfalso
    have hsucc : (2 : ℤ) ^ (padicValNat 2 c.natAbs + 1) ∣ c :=
      ⟨k, by rw [pow_succ, mul_assoc, two_mul, ← hk, Int.mul_ediv_cancel' hdvd]⟩
    have habs : (2 : ℕ) ^ (padicValNat 2 c.natAbs + 1) ∣ c.natAbs :=
      Int.natCast_dvd_natCast.mp (by simpa using Int.dvd_natAbs.mpr hsucc)
    exact absurd ((padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hc)).mp habs)
      (by omega)
  · rw [hk]; omega

theorem kw_hp_zmod8_units_sq : ∀ u : (ZMod (2 ^ 3))ˣ, u ^ 2 = 1 := by
  have _pin := Classical.em True; decide

theorem kw_hp_val2_odd_int {m : ℤ} (hm : m % 2 = 1) :
    (m : ℚ_[2]).valuation = 0 := by
  have _pin := Classical.em True
  have : ((m : ℤ) : ℚ_[2]) = (((m : ℤ) : ℚ) : ℚ_[2]) := by push_cast; ring
  rw [this, Padic.valuation_ratCast, padicValRat.of_int,
    padicValInt.eq_zero_of_not_dvd (fun h ↦ by omega)]
  simp

theorem kw_hp_F2_decomp_match {c : ℤ} (hc : c ≠ 0)
    {γ : ZMod 2} {m : ℤ} (hm : m % 2 = 1) {s : ℚ_[2]} (hs : s ≠ 0)
    (hdec : (c : ℚ_[2]) = (2 : ℚ_[2]) ^ γ.val * (m : ℚ_[2]) * s ^ 2) :
    ((kw_hpOrd2 c : ℕ) : ZMod 2) = γ ∧
      jpd4r14t3_epsZ (kw_hpOdd2 c) = jpd4r14t3_epsZ m ∧
      jpd4r14t3_omegaZ (kw_hpOdd2 c) = jpd4r14t3_omegaZ m := by
  have _pin := Classical.em True
  obtain ⟨hfact, hodd⟩ := kw_hp_ord2_odd2_decomp hc
  have hm0 : (m : ℚ_[2]) ≠ 0 := Int.cast_ne_zero.mpr (by omega)
  have h20 : (2 : ℚ_[2]) ≠ 0 := two_ne_zero

  let t : ℤ_[2]ˣ := gmk7_cls_unitPart (p := 2) hs
  have hs_spec : s = ((t : ℤ_[2]) : ℚ_[2]) * (2 : ℚ_[2]) ^ s.valuation :=
    gmk7_cls_unitPart_spec hs
  have ht0 : ((t : ℤ_[2]) : ℚ_[2]) ≠ 0 := by
    simp only [ne_eq, PadicInt.coe_eq_zero]; exact t.ne_zero
  have hpp : ((2 : ℕ) : ℚ_[2]) = (2 : ℚ_[2]) := by norm_num
  have hv2 : (2 : ℚ_[2]).valuation = 1 := by
    rw [← hpp]; exact_mod_cast Padic.valuation_p (p := 2)
  have htv : ((t : ℤ_[2]) : ℚ_[2]).valuation = 0 := by
    rw [gmk7_cls_unitPart_coe hs, Padic.valuation_mul hs
      (zpow_ne_zero _ (hpp ▸ h20)), Padic.valuation_zpow, hpp, hv2, mul_one]
    ring

  have hs2 : s ^ 2 = ((t : ℤ_[2]) : ℚ_[2]) ^ 2 * (2 : ℚ_[2]) ^ (2 * s.valuation) := by
    conv_lhs => rw [hs_spec]
    rw [mul_pow, show (2:ℤ) * s.valuation = s.valuation + s.valuation by ring,
      zpow_add₀ h20, sq, sq]
    try ring
  have hkey : (2 : ℚ_[2]) ^ (kw_hpOrd2 c : ℤ) * (kw_hpOdd2 c : ℚ_[2])
      = (2 : ℚ_[2]) ^ ((γ.val : ℤ) + 2 * s.valuation)
        * ((m : ℚ_[2]) * ((t : ℤ_[2]) : ℚ_[2]) ^ 2) := by
    have hL : (2 : ℚ_[2]) ^ (kw_hpOrd2 c : ℤ) * (kw_hpOdd2 c : ℚ_[2])
        = (c : ℚ_[2]) := by
      rw [zpow_natCast]; exact_mod_cast hfact.symm
    rw [hL, hdec, hs2, zpow_add₀ h20, zpow_natCast]; ring

  have hval : (kw_hpOrd2 c : ℤ) = (γ.val : ℤ) + 2 * s.valuation := by
    have hodd0 : (kw_hpOdd2 c : ℚ_[2]) ≠ 0 := Int.cast_ne_zero.mpr (by omega)
    have hvL : ((2:ℚ_[2]) ^ (kw_hpOrd2 c : ℤ) * (kw_hpOdd2 c : ℚ_[2])).valuation
        = (kw_hpOrd2 c : ℤ) := by
      rw [Padic.valuation_mul (zpow_ne_zero _ h20) hodd0,
        kw_hp_val2_odd_int hodd, add_zero, Padic.valuation_zpow, hv2, mul_one]
    have hvR : ((2:ℚ_[2]) ^ ((γ.val:ℤ) + 2*s.valuation)
        * ((m:ℚ_[2]) * ((t:ℤ_[2]):ℚ_[2])^2)).valuation
        = (γ.val : ℤ) + 2 * s.valuation := by
      rw [Padic.valuation_mul (zpow_ne_zero _ h20) (mul_ne_zero hm0 (pow_ne_zero _ ht0)),
        Padic.valuation_mul hm0 (pow_ne_zero _ ht0), kw_hp_val2_odd_int hm,
        Padic.valuation_pow, Padic.valuation_zpow, hv2, mul_one, htv]
      ring
    linarith [hvL ▸ hvR ▸ congrArg Padic.valuation hkey]
  refine ⟨?_, ?_⟩
  ·
    have h1 : ((kw_hpOrd2 c : ℤ) : ZMod 2) = ((γ.val : ℤ) : ZMod 2) := by
      rw [hval, Int.cast_add, Int.cast_mul,
        show ((2 : ℤ) : ZMod 2) = 0 from by decide, zero_mul, add_zero]
    rw [show ((kw_hpOrd2 c : ℕ) : ZMod 2) = ((kw_hpOrd2 c : ℤ) : ZMod 2) by
        push_cast; ring, h1]
    simp [ZMod.natCast_val]
  ·
    have hunit : (kw_hpOdd2 c : ℚ_[2])
        = (m : ℚ_[2]) * ((t : ℤ_[2]) : ℚ_[2]) ^ 2 := by
      have h2e : (2 : ℚ_[2]) ^ (kw_hpOrd2 c : ℤ)
          = (2 : ℚ_[2]) ^ ((γ.val : ℤ) + 2 * s.valuation) := by rw [hval]
      have hk2 := hkey; rw [h2e] at hk2
      exact mul_left_cancel₀ (zpow_ne_zero _ h20) hk2
    have hZ2 : ((kw_hpOdd2 c : ℤ) : ℤ_[2])
        = (m : ℤ_[2]) * ((t : ℤ_[2])) ^ 2 := by
      apply PadicInt.coe_injective_s18
      push_cast
      exact_mod_cast hunit
    have h8eq : ((kw_hpOdd2 c : ℤ) : ZMod (2^3)) = ((m : ℤ) : ZMod (2^3)) := by
      have h := congrArg (PadicInt.toZModPow (p := 2) 3) hZ2
      rw [map_mul, map_pow, map_intCast, map_intCast] at h
      have htsq : (PadicInt.toZModPow (p := 2) 3 (t : ℤ_[2])) ^ 2 = 1 := by
        have hu : IsUnit (PadicInt.toZModPow (p := 2) 3 (t : ℤ_[2])) :=
          t.isUnit.map (PadicInt.toZModPow (p := 2) 3)
        obtain ⟨U, hU⟩ := hu
        rw [← hU, ← Units.val_pow_eq_pow_val, kw_hp_zmod8_units_sq U, Units.val_one]
      rw [htsq, mul_one] at h
      exact h
    have h8dvd : (8 : ℤ) ∣ kw_hpOdd2 c - m := by
      have := (ZMod.intCast_eq_intCast_iff' (kw_hpOdd2 c) m (2^3)).mp h8eq
      omega
    exact kw_hp_epsZ_omegaZ_congr8 hodd hm h8dvd

theorem kw_hp_pairTwoZ_F2_match {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    {α β : ZMod 2} {u w : ℤ} (hu : u % 2 = 1) (hw : w % 2 = 1)
    {s t : ℚ_[2]} (hs : s ≠ 0) (ht : t ≠ 0)
    (hda : (a : ℚ_[2]) = (2 : ℚ_[2]) ^ α.val * (u : ℚ_[2]) * s ^ 2)
    (hdb : (b : ℚ_[2]) = (2 : ℚ_[2]) ^ β.val * (w : ℚ_[2]) * t ^ 2) :
    jpd4r14t3_pairTwoZ ((kw_hpOrd2 a : ℕ) : ZMod 2) (kw_hpOdd2 a)
      ((kw_hpOrd2 b : ℕ) : ZMod 2) (kw_hpOdd2 b)
      = jpd4r14t3_pairTwoZ α u β w := by
  have _pin := Classical.em True
  obtain ⟨hα, hε, hω⟩ := kw_hp_F2_decomp_match ha hu hs hda
  obtain ⟨hβ, hε', hω'⟩ := kw_hp_F2_decomp_match hb hw ht hdb
  unfold jpd4r14t3_pairTwoZ; rw [hα, hβ, hε, hε', hω, hω']

theorem kw_hp_solvAt_intReduce (a b : ℚ)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    kw_hpSolvAt ((a.num * a.den : ℤ) : ℚ) ((b.num * b.den : ℤ) : ℚ) v
      ↔ kw_hpSolvAt a b v := by
  have _pin := Classical.em True
  have had : (a.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr a.den_nz
  have hbd : (b.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr b.den_nz
  have hnum : ∀ q : ℚ, (q.num : ℚ) = q * (q.den : ℚ) := fun q ↦ by
    have h := Rat.num_div_den q
    field_simp at h; linarith [h]
  have ha' : ((a.num * a.den : ℤ) : ℚ) = a * (a.den : ℚ) ^ 2 := by
    push_cast; rw [hnum a, sq]; ring
  have hb' : ((b.num * b.den : ℤ) : ℚ) = b * (b.den : ℚ) ^ 2 := by
    push_cast; rw [hnum b, sq]; ring
  rw [ha', hb', kw_hpSolvAt_symm, kw_hpSolvAt_sqScale_left _ _ (b.den : ℚ) hbd,
    kw_hpSolvAt_symm, kw_hpSolvAt_sqScale_left _ _ (a.den : ℚ) had]

theorem kw_hp_sign_intReduce (a : ℚ) :
    ((a.num * a.den : ℤ) : ℝ) < 0 ↔ (a : ℝ) < 0 := by
  have _pin := Classical.em True
  have hnum : (a.num : ℝ) = (a : ℝ) * (a.den : ℝ) := by
    have h := Rat.num_div_den a
    have h' := congrArg (Rat.cast (K := ℝ)) h
    have hd : (a.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr a.den_nz
    push_cast at h'; field_simp at h'; linarith [h']
  rw [show ((a.num * a.den : ℤ) : ℝ) = (a : ℝ) * (a.den : ℝ) ^ 2 by
    push_cast; rw [hnum, sq]; ring]
  have hd : (0 : ℝ) < (a.den : ℝ) ^ 2 := by positivity
  exact mul_neg_iff.trans (by
    constructor
    · rintro (⟨_, h⟩ | ⟨h, _⟩)
      · exact absurd h (not_lt.mpr hd.le)
      · exact h
    · exact fun h ↦ Or.inr ⟨h, hd⟩)

theorem kw_hp_numDen_ne_zero {a : ℚ} (ha : a ≠ 0) :
    (a.num * a.den : ℤ) ≠ 0 :=
  mul_ne_zero (Rat.num_ne_zero.mpr ha) (Int.natCast_ne_zero.mpr a.den_nz)

theorem kw_hp_FsymbOdd_eq_solvSign
    (hOdd : kw_hpSolvAt_iff_gmk8_odd)
    (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0)
    (v : HeightOneSpectrum (𝓞 ℚ))
    (hp2 : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) ≠ 2) :
    kw_hpFsymbOdd (a.num * a.den) (b.num * b.den)
        (kw_hp_numDen_ne_zero ha) (kw_hp_numDen_ne_zero hb)
        (Rat.HeightOneSpectrum.primesEquiv v : ℕ)
      = if ¬ kw_hpSolvAt a b v then -1 else 1 := by
  have _pin := Classical.em True
  set a' : ℤ := a.num * a.den
  set b' : ℤ := b.num * b.den
  have ha' : a' ≠ 0 := kw_hp_numDen_ne_zero ha
  have hb' : b' ≠ 0 := kw_hp_numDen_ne_zero hb
  set p := (Rat.HeightOneSpectrum.primesEquiv v : ℕ)
  have hiff : kw_hpSolvAt a b v ↔ kw_hpFsymbOdd a' b' ha' hb' p = 1 := by
    rw [← kw_hp_solvAt_intReduce a b v,
      hOdd (a':ℚ) (b':ℚ) (by exact_mod_cast ha') (by exact_mod_cast hb') v hp2,
      kw_hpFsymbOdd, ← gmk9_ser_solvability_pair hp2
        (Int.cast_ne_zero.mpr ha') (Int.cast_ne_zero.mpr hb')]

    push_cast
    rfl
  rcases Int.units_eq_one_or (kw_hpFsymbOdd a' b' ha' hb' p) with hF | hF
  · rw [hF, if_neg (not_not.mpr (hiff.mpr hF))]
  · rw [hF, if_pos (hiff.not.mpr ((kw_hp_units_neg_one_iff _).mp hF))]

noncomputable def kw_hp_vTwo : HeightOneSpectrum (𝓞 ℚ) :=
  Rat.HeightOneSpectrum.primesEquiv.symm ⟨2, Nat.prime_two⟩

theorem kw_hp_vTwo_primesEquiv :
    (Rat.HeightOneSpectrum.primesEquiv kw_hp_vTwo : ℕ) = 2 := by
  have _pin := Classical.em True
  simp [kw_hp_vTwo, Equiv.apply_symm_apply]

theorem kw_hp_pairTwoZ_eq_solvSign
    (hTwo : kw_hpSolvAt_iff_jpd4_two) (hF2 : kw_HSCluster_C_F_two)
    (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    jpd4r14t3_pairTwoZ
        ((kw_hpOrd2 (a.num * a.den) : ℕ) : ZMod 2) (kw_hpOdd2 (a.num * a.den))
        ((kw_hpOrd2 (b.num * b.den) : ℕ) : ZMod 2) (kw_hpOdd2 (b.num * b.den))
      = if ¬ kw_hpSolvAt a b kw_hp_vTwo then -1 else 1 := by
  have _pin := Classical.em True
  set a' : ℤ := a.num * a.den with ha'd
  set b' : ℤ := b.num * b.den with hb'd
  have ha' : a' ≠ 0 := kw_hp_numDen_ne_zero ha
  have hb' : b' ≠ 0 := kw_hp_numDen_ne_zero hb
  obtain ⟨α, u, β, w, huodd, hwodd, ⟨s, hs, hda⟩, ⟨t, ht, hdb⟩, hiff⟩ :=
    hF2 (a' : ℚ_[2]) (b' : ℚ_[2]) (Int.cast_ne_zero.mpr ha') (Int.cast_ne_zero.mpr hb')
  rw [kw_hp_pairTwoZ_F2_match ha' hb' huodd hwodd hs ht hda hdb]
  have hTwov : kw_hpSolvAt a b kw_hp_vTwo
      ↔ jpd4r15t3_hilbertSolvable (a' : ℚ_[2]) (b' : ℚ_[2]) := by
    rw [← kw_hp_solvAt_intReduce a b kw_hp_vTwo]
    have h := hTwo (a':ℚ) (b':ℚ) (by exact_mod_cast ha') (by exact_mod_cast hb')
      kw_hp_vTwo kw_hp_vTwo_primesEquiv
    rw [ha'd, hb'd] at h ⊢
    convert h using 2 <;> push_cast <;> rfl
  rcases Int.units_eq_one_or (jpd4r14t3_pairTwoZ α u β w) with hP | hP
  · rw [hP, if_neg (not_not.mpr (hTwov.mpr (hiff.mpr hP)))]
  · rw [hP, if_pos (hTwov.not.mpr (hiff.not.mpr
      ((kw_hp_units_neg_one_iff _).mp hP)))]

theorem kw_hp_W_parityStep_proved : kw_hp_W_parityStep := by
  have _pin := Classical.em True
  intro hOdd hTwo hF2 hG a b ha hb

  set a' : ℤ := a.num * a.den with ha'd
  set b' : ℤ := b.num * b.den with hb'd
  have ha' : a' ≠ 0 := kw_hp_numDen_ne_zero ha
  have hb' : b' ≠ 0 := kw_hp_numDen_ne_zero hb
  set N : ℕ := 2 * (a.num.natAbs * a.den * (b.num.natAbs * b.den)) with hNd
  have hNne : N ≠ 0 := by
    have h1 : a.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr ha)
    have h2 : b.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hb)
    positivity
  have hNeq : 2 * a'.natAbs * b'.natAbs = N := by
    simp only [ha'd, hb'd, Int.natAbs_mul, Int.natAbs_natCast, hNd]; ring
  have h2N : 2 ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two,
      ⟨a.num.natAbs * a.den * (b.num.natAbs * b.den), hNd⟩, hNne⟩

  let emb : {p // p ∈ N.primeFactors} → HeightOneSpectrum (𝓞 ℚ) := fun pp ↦
    Rat.HeightOneSpectrum.primesEquiv.symm ⟨pp.1, Nat.prime_of_mem_primeFactors pp.2⟩
  let σ : {p // p ∈ N.primeFactors} → ℤˣ := fun pp ↦
    if ¬ kw_hpSolvAt a b (emb pp) then -1 else 1
  have hemb_inj : Function.Injective emb := fun p q h ↦ Subtype.ext (by
    have := congrArg (fun v ↦ (Rat.HeightOneSpectrum.primesEquiv v : ℕ)) h
    simpa [emb, Equiv.apply_symm_apply] using this)

  have hσiff : ∀ pp, σ pp = -1 ↔ ¬ kw_hpSolvAt a b (emb pp) := fun pp ↦ by
    simp only [σ]
    by_cases h : kw_hpSolvAt a b (emb pp)
    · rw [if_neg (not_not.mpr h)]
      exact ⟨fun hc ↦ absurd hc (by decide), fun hc ↦ absurd h hc⟩
    · rw [if_pos h]; exact ⟨fun _ ↦ h, fun _ ↦ rfl⟩
  have hRf_card : (kw_hp_Rf a b).card
      = (N.primeFactors.attach.filter (fun pp ↦ σ pp = -1)).card := by
    rw [kw_hp_Rf, show kw_hp_supp a b = N.primeFactors.attach.image emb from rfl,
      Finset.filter_image, Finset.card_image_of_injective _ hemb_inj]
    exact congrArg Finset.card (Finset.filter_congr fun pp _ ↦ (hσiff pp).symm)

  have hprod : (∏ pp ∈ N.primeFactors.attach, σ pp)
      * jpd4r13t6_hilbR (a' : ℝ) (b' : ℝ) = 1 := by

    have h2att : (⟨2, h2N⟩ : {p // p ∈ N.primeFactors}) ∈ N.primeFactors.attach :=
      Finset.mem_attach _ _
    rw [← Finset.mul_prod_erase _ _ h2att]

    have hσ2 : σ ⟨2, h2N⟩
        = jpd4r14t3_pairTwoZ ((kw_hpOrd2 a' : ℕ) : ZMod 2) (kw_hpOdd2 a')
          ((kw_hpOrd2 b' : ℕ) : ZMod 2) (kw_hpOdd2 b') := by
      rw [ha'd, hb'd, kw_hp_pairTwoZ_eq_solvSign hTwo hF2 a b ha hb]
      simp only [σ, emb]; rfl

    have hσodd : ∀ pp ∈ N.primeFactors.attach.erase ⟨2, h2N⟩,
        σ pp = kw_hpFsymbOdd a' b' ha' hb'
          (Rat.HeightOneSpectrum.primesEquiv (emb pp) : ℕ) := by
      intro pp hpp
      have hvp : (Rat.HeightOneSpectrum.primesEquiv (emb pp) : ℕ) = pp.1 := by
        simp only [emb, Equiv.apply_symm_apply]
      have hpp2 : (Rat.HeightOneSpectrum.primesEquiv (emb pp) : ℕ) ≠ 2 :=
        hvp ▸ fun h ↦ (Finset.mem_erase.mp hpp).1 (Subtype.ext h)
      show σ pp = kw_hpFsymbOdd (a.num * a.den) (b.num * b.den)
        (kw_hp_numDen_ne_zero ha) (kw_hp_numDen_ne_zero hb) _
      rw [kw_hp_FsymbOdd_eq_solvSign hOdd a b ha hb (emb pp) hpp2]
    rw [hσ2, Finset.prod_congr rfl hσodd]

    have hGab := hG a' b' ha' hb'
    have hprod_match : (∏ pp ∈ N.primeFactors.attach.erase ⟨2, h2N⟩,
          kw_hpFsymbOdd a' b' ha' hb'
            (Rat.HeightOneSpectrum.primesEquiv (emb pp) : ℕ))
        = ∏ p ∈ ((2 * a'.natAbs * b'.natAbs).primeFactors \ {2}).attach,
            haveI : Fact p.1.Prime :=
              ⟨Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp p.2).1⟩
            kw_hpFsymbOdd a' b' ha' hb' p.1 := by
      have hpf : N.primeFactors = (2 * a'.natAbs * b'.natAbs).primeFactors :=
        congrArg Nat.primeFactors hNeq.symm
      refine Finset.prod_bij
        (i := fun pp hpp ↦ ⟨pp.1, Finset.mem_sdiff.mpr
          ⟨hpf ▸ pp.2, fun h ↦ (Finset.mem_erase.mp hpp).1
            (Subtype.ext (Finset.mem_singleton.mp h))⟩⟩)
        (fun _ _ ↦ Finset.mem_attach _ _) ?_ ?_ ?_
      · intro p _ q _ h
        exact Subtype.ext (Subtype.mk_eq_mk.mp h)
      · intro pp _
        refine ⟨⟨pp.1, hpf.symm ▸ (Finset.mem_sdiff.mp pp.2).1⟩,
          Finset.mem_erase.mpr ⟨fun h ↦ (Finset.mem_sdiff.mp pp.2).2
            (Finset.mem_singleton.mpr (congrArg Subtype.val h)),
            Finset.mem_attach _ _⟩, Subtype.ext rfl⟩
      · intro pp _
        simp only [emb, Equiv.apply_symm_apply]
    rw [hprod_match, mul_comm (jpd4r14t3_pairTwoZ _ _ _ _)]
    exact hGab

  have hhilbR : jpd4r13t6_hilbR (a' : ℝ) (b' : ℝ)
      = if (a : ℝ) < 0 ∧ (b : ℝ) < 0 then (-1 : ℤˣ) else 1 := by
    unfold jpd4r13t6_hilbR
    rw [ha'd, hb'd]
    simp only [kw_hp_sign_intReduce]
  rw [hhilbR] at hprod
  rw [hRf_card]
  have hpe := kw_hp_units_prod_parity N.primeFactors.attach σ
  by_cases hinf : (a : ℝ) < 0 ∧ (b : ℝ) < 0
  · rw [if_pos hinf, mul_neg_one, neg_eq_iff_eq_neg] at hprod
    rw [if_pos hinf, Nat.even_add_one]
    exact hpe.not.mp ((kw_hp_units_neg_one_iff _).mp hprod)
  · rw [if_neg hinf, mul_one] at hprod
    rw [if_neg hinf, add_zero]
    exact hpe.mp hprod

end FLT.NumberTheory
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section
section

suppress_compilation

p2m_open "IsDedekindDomain P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.IsDedekindDomain NumberField P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.NumberField QuaternionAlgebra P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.QuaternionAlgebra"
p2m_open_scoped "Quaternion P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.Quaternion"

namespace FLT
namespace NumberTheory

p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.IsDedekindDomain.HeightOneSpectrum"

section SubstrateHandles

variable {a b : ℚ}

theorem kw_hg1fc_dirichletAP_pin {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a)
    (N : ℕ) : ∃ p > N, p.Prime ∧ (p : ZMod q) = a :=
  Nat.forall_exists_prime_gt_and_eq_mod ha N

end SubstrateHandles
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end FLT.NumberTheory
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section
section

suppress_compilation

p2m_open "IsDedekindDomain P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.IsDedekindDomain NumberField P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.NumberField QuaternionAlgebra P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.QuaternionAlgebra"
p2m_open_scoped "Quaternion P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.Quaternion"

namespace FLT
namespace NumberTheory

p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.IsDedekindDomain.HeightOneSpectrum"

section QuaternBridge

variable {F : Type} [Field F] [CharZero F]

theorem kw_hg1fc_quaternIsotropic_of_pureNrdRep {a b c : F}
    (h : kw_pureNrdRep F a b c) :
    ∃ x y z w : F, ¬ (x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0) ∧
      -a * x ^ 2 - b * y ^ 2 + a * b * z ^ 2 - c * w ^ 2 = 0 := by
  obtain ⟨x, y, z, heq⟩ := h
  exact ⟨x, y, z, 1, fun ⟨_, _, _, h1⟩ ↦ one_ne_zero h1, by linear_combination heq⟩

theorem kw_hg1fc_pureNrdRep_of_quaternIsotropic {a b c : F} (ha : a ≠ 0) (hb : b ≠ 0)
    (hUniv : kw_isotropicPureNrdUniversal)
    (h : ∃ x y z w : F, ¬ (x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0) ∧
      -a * x ^ 2 - b * y ^ 2 + a * b * z ^ 2 - c * w ^ 2 = 0) :
    kw_pureNrdRep F a b c := by
  obtain ⟨x, y, z, w, hnt, heq⟩ := h
  by_cases hw : w = 0
  ·
    subst hw
    simp only [ne_eq, mul_zero, sub_zero, zero_pow, OfNat.ofNat_ne_zero,
      not_false_eq_true] at heq
    exact hUniv F a b ha hb ⟨x, y, z, fun ⟨hx, hy, hz⟩ ↦ hnt ⟨hx, hy, hz, rfl⟩, heq⟩ c
  ·
    refine ⟨x / w, y / w, z / w, ?_⟩
    have hw2 : w ^ 2 ≠ 0 := pow_ne_zero 2 hw
    field_simp
    linear_combination heq

end QuaternBridge
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section LegendreDescent

def kw_hg1fc_legendreSolvable (a b : ℤ) : Prop :=
  ∃ x y z : ℚ, ¬ (x = 0 ∧ y = 0 ∧ z = 0) ∧ z * z = (a : ℚ) * (x * x) + (b : ℚ) * (y * y)

theorem kw_hg1fc_legendreSolvable_sqScale {a b : ℤ} {u : ℤ} (hu : u ≠ 0) :
    kw_hg1fc_legendreSolvable a b ↔ kw_hg1fc_legendreSolvable a (b * u ^ 2) := by
  have huQ : (u : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hu
  constructor
  · rintro ⟨x, y, z, hnt, heq⟩
    refine ⟨x * u, y, z * u, ?_, ?_⟩
    · rintro ⟨hx, hy, hz⟩
      exact hnt ⟨(mul_eq_zero.mp hx).resolve_right huQ, hy,
        (mul_eq_zero.mp hz).resolve_right huQ⟩
    · push_cast; ring_nf; linear_combination (u : ℚ) ^ 2 * heq
  · rintro ⟨x, y, z, hnt, heq⟩
    refine ⟨x, y * u, z, ?_, ?_⟩
    · rintro ⟨hx, hy, hz⟩
      exact hnt ⟨hx, (mul_eq_zero.mp hy).resolve_right huQ, hz⟩
    · push_cast at heq ⊢; linear_combination heq

theorem kw_hg1fc_legendreSolvable_symm {a b : ℤ} :
    kw_hg1fc_legendreSolvable a b ↔ kw_hg1fc_legendreSolvable b a := by
  constructor <;>
    · rintro ⟨x, y, z, hnt, heq⟩
      exact ⟨y, x, z, fun ⟨h1, h2, h3⟩ ↦ hnt ⟨h2, h1, h3⟩, by linear_combination heq⟩

theorem kw_hg1fc_legendreSolvable_of_isSquare {a b : ℤ} (ha : IsSquare a) (ha0 : a ≠ 0) :
    kw_hg1fc_legendreSolvable a b := by
  obtain ⟨r, hr⟩ := ha
  exact ⟨1, 0, r, fun ⟨h1, _, _⟩ ↦ one_ne_zero h1, by push_cast [hr]; ring⟩

theorem kw_hg1fc_legendre_normTransfer {a b b' t : ℤ} (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hbb' : b * b' = t ^ 2 - a) :
    kw_hg1fc_legendreSolvable a b ↔ kw_hg1fc_legendreSolvable a b' := by

  have key : ∀ {B B' : ℤ}, B ≠ 0 → B * B' = t ^ 2 - a →
      kw_hg1fc_legendreSolvable a B → kw_hg1fc_legendreSolvable a B' := by
    intro B B' hB hBB' ⟨x, y, z, hnt, heq⟩
    have hBQ : (B : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hB
    by_cases hy : y = 0
    ·

      subst hy
      simp only [mul_zero, add_zero] at heq
      have hx : x ≠ 0 := by
        intro hx0
        refine hnt ⟨hx0, rfl, mul_self_eq_zero.mp ?_⟩
        rw [heq, hx0]; ring
      exact ⟨1, 0, z / x, fun ⟨h1, _, _⟩ ↦ one_ne_zero h1, by
        field_simp; linear_combination heq⟩
    ·
      refine ⟨(z + t * x) / B, y, (z * t + a * x) / B, fun ⟨_, hy0, _⟩ ↦ hy hy0, ?_⟩
      have hBB'Q : (B : ℚ) * (B' : ℚ) = (t : ℚ) ^ 2 - (a : ℚ) := by exact_mod_cast hBB'
      have brahm : (z * (t : ℚ) + (a : ℚ) * x) ^ 2 - (a : ℚ) * (z + (t : ℚ) * x) ^ 2
          = (B : ℚ) ^ 2 * ((B' : ℚ) * (y * y)) := by
        have h1 : z * z - (a : ℚ) * (x * x) = (B : ℚ) * (y * y) := by linear_combination heq
        linear_combination ((t : ℚ) ^ 2 - (a : ℚ)) * h1 - (B : ℚ) * (y * y) * hBB'Q
      field_simp
      linear_combination brahm
  exact ⟨key hb hbb', key hb' (by linear_combination hbb')⟩

theorem kw_hg1fc_exists_small_sqrtMod {a b : ℤ} (hb : b ≠ 0)
    (h : ∃ s, b ∣ s ^ 2 - a) : ∃ t : ℤ, b ∣ t ^ 2 - a ∧ 2 * t.natAbs ≤ b.natAbs := by
  obtain ⟨s, hs⟩ := h
  have hn : 0 < b.natAbs := Int.natAbs_pos.mpr hb
  set t := Int.bmod s b.natAbs with ht_def
  refine ⟨t, ?_, ?_⟩
  ·
    have hts : b ∣ t - s :=
      (Int.natAbs_dvd.mp (Int.dvd_bmod_sub_self (x := s) (m := b.natAbs)))
    have hfact : t ^ 2 - a = (t - s) * (t + s) + (s ^ 2 - a) := by ring
    rw [hfact]
    exact dvd_add (Dvd.dvd.mul_right hts _) hs
  ·
    have h1 : -((b.natAbs : ℤ) / 2) ≤ t := Int.le_bmod hn
    have h2 : t < ((b.natAbs : ℤ) + 1) / 2 := Int.bmod_lt hn
    omega

theorem kw_hg1fc_descent_bound {a b t : ℤ} (hb : b ≠ 0) (hdvd : b ∣ t ^ 2 - a)
    (ht : 2 * t.natAbs ≤ b.natAbs) (hab : a.natAbs ≤ b.natAbs)
    (hb2 : 2 ≤ b.natAbs) :
    ((t ^ 2 - a) / b).natAbs < b.natAbs := by
  set b' := (t ^ 2 - a) / b with hb'_def
  have hbb' : b * b' = t ^ 2 - a := by rw [hb'_def]; exact Int.mul_ediv_cancel' hdvd

  have hmul : b.natAbs * b'.natAbs = (t ^ 2 - a).natAbs := by
    rw [← Int.natAbs_mul, hbb']
  have hsub : (t ^ 2 - a).natAbs ≤ t.natAbs ^ 2 + a.natAbs := by
    calc (t ^ 2 - a).natAbs ≤ (t ^ 2).natAbs + a.natAbs := Int.natAbs_sub_le _ _
      _ = t.natAbs ^ 2 + a.natAbs := by rw [Int.natAbs_pow]

  have hsq : 4 * t.natAbs ^ 2 ≤ b.natAbs ^ 2 := by
    calc 4 * t.natAbs ^ 2 = (2 * t.natAbs) ^ 2 := by ring
      _ ≤ b.natAbs ^ 2 := Nat.pow_le_pow_left ht 2

  have hn : 0 < b.natAbs := Int.natAbs_pos.mpr hb
  have h4 : 4 * b'.natAbs ≤ b.natAbs + 4 := by
    refine Nat.le_of_mul_le_mul_left ?_ hn
    calc b.natAbs * (4 * b'.natAbs) = 4 * (b.natAbs * b'.natAbs) := by ring
      _ = 4 * (t ^ 2 - a).natAbs := by rw [hmul]
      _ ≤ 4 * (t.natAbs ^ 2 + a.natAbs) := by omega
      _ ≤ b.natAbs ^ 2 + 4 * b.natAbs := by omega
      _ = b.natAbs * (b.natAbs + 4) := by ring
  omega

end LegendreDescent
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section PropagationEngine

variable {F : Type*} [Field F]

theorem kw_hg1fc_ternaryIso_normTransfer {a b b' t : F} (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hbb' : b * b' = t ^ 2 - a) :
    (∃ x y z : F, ¬ (x = 0 ∧ y = 0 ∧ z = 0) ∧ z * z = a * (x * x) + b * (y * y)) ↔
      ∃ x y z : F, ¬ (x = 0 ∧ y = 0 ∧ z = 0) ∧ z * z = a * (x * x) + b' * (y * y) := by
  have key : ∀ {B B' : F}, B ≠ 0 → B * B' = t ^ 2 - a →
      (∃ x y z : F, ¬ (x = 0 ∧ y = 0 ∧ z = 0) ∧ z * z = a * (x * x) + B * (y * y)) →
      ∃ x y z : F, ¬ (x = 0 ∧ y = 0 ∧ z = 0) ∧ z * z = a * (x * x) + B' * (y * y) := by
    intro B B' hB hBB' ⟨x, y, z, hnt, heq⟩
    by_cases hy : y = 0
    ·
      subst hy
      simp only [mul_zero, add_zero] at heq
      have hx : x ≠ 0 := fun hx0 ↦ hnt ⟨hx0, rfl,
        mul_self_eq_zero.mp (by rw [heq, hx0]; ring)⟩
      exact ⟨1, 0, z / x, fun ⟨h1, _, _⟩ ↦ one_ne_zero h1, by
        field_simp; linear_combination heq⟩
    ·
      refine ⟨(z + t * x) / B, y, (z * t + a * x) / B, fun ⟨_, hy0, _⟩ ↦ hy hy0, ?_⟩
      have brahm : (z * t + a * x) ^ 2 - a * (z + t * x) ^ 2 = B ^ 2 * (B' * (y * y)) := by
        have h1 : z * z - a * (x * x) = B * (y * y) := by linear_combination heq
        linear_combination (t ^ 2 - a) * h1 - B * (y * y) * hBB'
      field_simp
      linear_combination brahm
  exact ⟨key hb hbb', key hb' (by linear_combination hbb')⟩

theorem kw_hg1fc_hpSolvAt_normTransfer {a b b' t : ℚ} (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hbb' : b * b' = t ^ 2 - a) (v : HeightOneSpectrum (𝓞 ℚ)) :
    kw_hpSolvAt a b v ↔ kw_hpSolvAt a b' v := by

  let φ := algebraMap ℚ (v.adicCompletion ℚ)
  have hφinj : Function.Injective φ := (algebraMap ℚ _).injective
  have hbF : φ b ≠ 0 := fun h ↦ hb (hφinj (h.trans (_root_.map_zero φ).symm))
  have hb'F : φ b' ≠ 0 := fun h ↦ hb' (hφinj (h.trans (_root_.map_zero φ).symm))
  have hbb'F : φ b * φ b' = φ t ^ 2 - φ a := by
    rw [← map_mul, ← map_pow, ← map_sub, hbb']

  have shape : ∀ c : ℚ, kw_hpSolvAt a c v ↔
      ∃ x y z : v.adicCompletion ℚ, ¬ (x = 0 ∧ y = 0 ∧ z = 0) ∧
        z * z = φ a * (x * x) + φ c * (y * y) := by
    intro c
    constructor
    · rintro ⟨z, x, y, hnt, heq⟩
      exact ⟨x, y, z, fun ⟨hx, hy, hz⟩ ↦ hnt ⟨hz, hx, hy⟩, by linear_combination heq⟩
    · rintro ⟨x, y, z, hnt, heq⟩
      exact ⟨z, x, y, fun ⟨hz, hx, hy⟩ ↦ hnt ⟨hx, hy, hz⟩, by linear_combination heq⟩
  rw [shape b, shape b']
  exact kw_hg1fc_ternaryIso_normTransfer hbF hb'F hbb'F

end PropagationEngine
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

def kw_hg1fc_hpSolvAt_implies_sqrtMod : Prop :=
  ∀ (a b : ℤ), a ≠ 0 → Squarefree b → b ≠ 0 →
    (∀ v : HeightOneSpectrum (𝓞 ℚ), kw_hpSolvAt (a : ℚ) (b : ℚ) v) →
    ∃ s : ℤ, b ∣ s ^ 2 - a

section LegendreMain

theorem kw_hg1fc_hpSolvAt_sqScale_right (a b : ℚ) (s : ℚ) (hs : s ≠ 0)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    kw_hpSolvAt a (b * s ^ 2) v ↔ kw_hpSolvAt a b v := by
  rw [kw_hpSolvAt_symm, kw_hpSolvAt_sqScale_left b a s hs, kw_hpSolvAt_symm]

theorem kw_hg1fc_int_sq_mul_squarefree {n : ℤ} (hn : n ≠ 0) :
    ∃ m u : ℤ, m * u ^ 2 = n ∧ Squarefree m ∧ u ≠ 0 ∧ m ≠ 0 ∧
      m.natAbs ≤ n.natAbs ∧ (0 < n → 0 < m) := by
  obtain ⟨m₀, u₀, heq, hsqf⟩ := Nat.sq_mul_squarefree n.natAbs
  have hn1 : 1 ≤ n.natAbs := Int.natAbs_pos.mpr hn
  have hu₀ : 0 < u₀ := by
    rcases Nat.eq_zero_or_pos u₀ with h | h
    · exact absurd heq (by simp [h]; omega)
    · exact h
  have hdvd : (u₀ : ℤ) ^ 2 ∣ n := Int.natAbs_dvd_natAbs.mp <| by
    simp only [Int.natAbs_pow, Int.natAbs_natCast]
    exact ⟨m₀, by linarith [heq]⟩
  set m : ℤ := n / (u₀ : ℤ) ^ 2 with hm_def
  have hmul : m * (u₀ : ℤ) ^ 2 = n := Int.ediv_mul_cancel hdvd
  have hm0 : m ≠ 0 := fun h ↦ hn (by rw [← hmul, h, zero_mul])
  have habs : m.natAbs * u₀ ^ 2 = n.natAbs := by
    have h := congrArg Int.natAbs hmul
    simpa [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] using h
  have hu2 : 0 < u₀ ^ 2 := by positivity
  have hmabs : m.natAbs = m₀ :=
    Nat.eq_of_mul_eq_mul_right hu2 (habs.trans (by linarith [heq]))
  refine ⟨m, (u₀ : ℤ), hmul, ?_, by exact_mod_cast hu₀.ne', hm0, ?_, ?_⟩
  · rw [← Int.squarefree_natAbs, hmabs]; exact hsqf
  · calc m.natAbs = m₀ := hmabs
      _ ≤ u₀ ^ 2 * m₀ := Nat.le_mul_of_pos_left _ hu2
      _ = n.natAbs := heq
  · intro hpos
    have hu2Z : (0 : ℤ) < (u₀ : ℤ) ^ 2 := by positivity
    by_contra hle
    have hmle : m ≤ 0 := not_lt.mp hle
    have : m * (u₀ : ℤ) ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hmle hu2Z.le
    linarith [hmul]

theorem kw_hg1fc_legendre_descent (hQR : kw_hg1fc_hpSolvAt_implies_sqrtMod) :
    ∀ a b : ℤ, a ≠ 0 → b ≠ 0 → Squarefree a → Squarefree b →
      ¬ (a < 0 ∧ b < 0) →
      (∀ v : HeightOneSpectrum (𝓞 ℚ), kw_hpSolvAt (a : ℚ) (b : ℚ) v) →
      kw_hg1fc_legendreSolvable a b := by

  suffices key : ∀ n : ℕ, ∀ a b : ℤ, a.natAbs + b.natAbs = n →
      a ≠ 0 → b ≠ 0 → Squarefree a → Squarefree b → ¬ (a < 0 ∧ b < 0) →
      (∀ v, kw_hpSolvAt (a : ℚ) (b : ℚ) v) → kw_hg1fc_legendreSolvable a b from
    fun a b ↦ key _ a b rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro a b hn ha hb hasf hbsf hsgn hv

  have step : ∀ a' b' : ℤ, a'.natAbs + b'.natAbs = n →
      a' ≠ 0 → b' ≠ 0 → Squarefree a' → Squarefree b' → ¬ (a' < 0 ∧ b' < 0) →
      (∀ v, kw_hpSolvAt (a' : ℚ) (b' : ℚ) v) → a'.natAbs ≤ b'.natAbs →
      kw_hg1fc_legendreSolvable a' b' := by
    clear hn ha hb hasf hbsf hsgn hv a b
    intro a b hsum ha hb hasf hbsf hsgn hv hab
    have hb1 : 1 ≤ b.natAbs := le_trans (Int.natAbs_pos.mpr ha) hab

    rcases Nat.lt_or_ge b.natAbs 2 with hblt | hb2
    · have hbeq : b.natAbs = 1 := by omega
      have haeq : a.natAbs = 1 := le_antisymm (hab.trans_eq hbeq) (Int.natAbs_pos.mpr ha)
      rcases Int.natAbs_eq_iff.mp haeq with rfl | rfl
      · exact kw_hg1fc_legendreSolvable_of_isSquare (by simpa using isSquare_one) ha
      · rcases Int.natAbs_eq_iff.mp hbeq with rfl | rfl
        · exact kw_hg1fc_legendreSolvable_symm.mpr
            (kw_hg1fc_legendreSolvable_of_isSquare (by simpa using isSquare_one) hb)
        · exact absurd ⟨by simp, by simp⟩ hsgn

    obtain ⟨t, hdvd, hsmall⟩ :=
      kw_hg1fc_exists_small_sqrtMod hb (hQR a b ha hbsf hb hv)
    set b₁ : ℤ := (t ^ 2 - a) / b with hb₁_def
    have hbb₁ : b * b₁ = t ^ 2 - a := Int.mul_ediv_cancel' hdvd
    rcases eq_or_ne b₁ 0 with hb₁0 | hb₁0
    ·
      have hat : a = t ^ 2 := by have h := hbb₁; rw [hb₁0, mul_zero] at h; linarith
      exact kw_hg1fc_legendreSolvable_of_isSquare ⟨t, by rw [hat, sq]⟩ ha

    have hb₁lt : b₁.natAbs < b.natAbs :=
      hb₁_def ▸ kw_hg1fc_descent_bound hb hdvd hsmall hab hb2
    obtain ⟨b₂, u, humul, hb₂sf, hu0, hb₂0, hb₂le, hb₂pos⟩ :=
      kw_hg1fc_int_sq_mul_squarefree hb₁0
    have huQ : (u : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hu0

    have hv₂ : ∀ v, kw_hpSolvAt (a : ℚ) (b₂ : ℚ) v := by
      intro v
      have hbb₁Q : (b : ℚ) * (b₁ : ℚ) = (t : ℚ) ^ 2 - (a : ℚ) := by exact_mod_cast hbb₁
      have h1 : kw_hpSolvAt (a : ℚ) (b₁ : ℚ) v :=
        (kw_hg1fc_hpSolvAt_normTransfer (Int.cast_ne_zero.mpr hb)
          (Int.cast_ne_zero.mpr hb₁0) hbb₁Q v).mp (hv v)
      have hcast : (b₁ : ℚ) = (b₂ : ℚ) * (u : ℚ) ^ 2 := by exact_mod_cast humul.symm
      rw [hcast] at h1
      exact (kw_hg1fc_hpSolvAt_sqScale_right (a : ℚ) (b₂ : ℚ) (u : ℚ) huQ v).mp h1

    have hsgn₂ : ¬ (a < 0 ∧ b₂ < 0) := by
      rintro ⟨haneg, hb₂neg⟩
      have hbpos : 0 < b := (lt_or_gt_of_ne hb).resolve_left (fun h ↦ hsgn ⟨haneg, h⟩)
      have hb₁pos : 0 < b₁ := by
        have hprod : 0 < b * b₁ := by rw [hbb₁]; nlinarith [sq_nonneg t]
        exact (mul_pos_iff_of_pos_left hbpos).mp hprod
      exact absurd (hb₂pos hb₁pos) (not_lt_of_gt hb₂neg)

    have hsolv₂ : kw_hg1fc_legendreSolvable a b₂ :=
      IH (a.natAbs + b₂.natAbs) (by omega) a b₂ rfl ha hb₂0 hasf hb₂sf hsgn₂ hv₂

    have hsolv₁ : kw_hg1fc_legendreSolvable a b₁ := by
      have h := (kw_hg1fc_legendreSolvable_sqScale (a := a) (b := b₂) hu0).mp hsolv₂
      rwa [humul] at h
    exact (kw_hg1fc_legendre_normTransfer hb hb₁0 hbb₁).mpr hsolv₁

  rcases le_total a.natAbs b.natAbs with hab | hab
  · exact step a b hn ha hb hasf hbsf hsgn hv hab
  · exact kw_hg1fc_legendreSolvable_symm.mpr <|
      step b a (by omega) hb ha hbsf hasf (fun ⟨h1, h2⟩ ↦ hsgn ⟨h2, h1⟩)
        (fun v ↦ (kw_hpSolvAt_symm (a : ℚ) (b : ℚ) v).mp (hv v)) hab

theorem kw_hg1fc_legendreSolvable_sqScale_left {a b : ℤ} {u : ℤ} (hu : u ≠ 0) :
    kw_hg1fc_legendreSolvable a b ↔ kw_hg1fc_legendreSolvable (a * u ^ 2) b := by
  rw [kw_hg1fc_legendreSolvable_symm, kw_hg1fc_legendreSolvable_sqScale hu,
    kw_hg1fc_legendreSolvable_symm]

end LegendreMain
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section TernaryLocalGlobal

theorem kw_hg1fc_ternaryIsotropy_localGlobal
    (hQR : kw_hg1fc_hpSolvAt_implies_sqrtMod) {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hv : ∀ v : HeightOneSpectrum (𝓞 ℚ), kw_hpSolvAt a b v)
    (hR : ¬ ((a : ℝ) < 0 ∧ (b : ℝ) < 0)) :
    ∃ x y z : ℚ, ¬ (x = 0 ∧ y = 0 ∧ z = 0) ∧ z * z = a * (x * x) + b * (y * y) := by

  set A : ℤ := a.num * a.den with hA_def
  set B : ℤ := b.num * b.den with hB_def
  have hA0 : A ≠ 0 := kw_hp_numDen_ne_zero ha
  have hB0 : B ≠ 0 := kw_hp_numDen_ne_zero hb
  have hdA : (a.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr a.den_nz
  have hdB : (b.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr b.den_nz
  have hnum : ∀ q : ℚ, (q.num : ℚ) = q * (q.den : ℚ) := fun q ↦ by
    have h := Rat.num_div_den q; field_simp at h; linear_combination h
  have haA : a * (a.den : ℚ) ^ 2 = (A : ℚ) := by
    push_cast [hA_def]; linear_combination -(a.den : ℚ) * hnum a
  have hbB : b * (b.den : ℚ) ^ 2 = (B : ℚ) := by
    push_cast [hB_def]; linear_combination -(b.den : ℚ) * hnum b

  obtain ⟨A₀, uA, huAmul, hA₀sf, huA0, hA₀0, -, hA₀pos⟩ :=
    kw_hg1fc_int_sq_mul_squarefree hA0
  obtain ⟨B₀, uB, huBmul, hB₀sf, huB0, hB₀0, -, hB₀pos⟩ :=
    kw_hg1fc_int_sq_mul_squarefree hB0
  have huAQ : (uA : ℚ) ≠ 0 := Int.cast_ne_zero.mpr huA0
  have huBQ : (uB : ℚ) ≠ 0 := Int.cast_ne_zero.mpr huB0

  have hv₀ : ∀ v, kw_hpSolvAt (A₀ : ℚ) (B₀ : ℚ) v := by
    intro v
    have h1 : kw_hpSolvAt (A : ℚ) (B : ℚ) v :=
      (kw_hp_solvAt_intReduce a b v).mpr (hv v)
    have hAcast : (A : ℚ) = (A₀ : ℚ) * (uA : ℚ) ^ 2 := by exact_mod_cast huAmul.symm
    have hBcast : (B : ℚ) = (B₀ : ℚ) * (uB : ℚ) ^ 2 := by exact_mod_cast huBmul.symm
    rw [hAcast, hBcast] at h1
    exact (kw_hg1fc_hpSolvAt_sqScale_right _ _ _ huBQ v).mp
      ((kw_hpSolvAt_sqScale_left _ _ _ huAQ v).mp h1)

  have hsgn₀ : ¬ (A₀ < 0 ∧ B₀ < 0) := by
    rintro ⟨hAneg, hBneg⟩
    have huA2 : (0 : ℤ) < uA ^ 2 := by positivity
    have huB2 : (0 : ℤ) < uB ^ 2 := by positivity
    have hAlt : A < 0 := huAmul ▸ mul_neg_of_neg_of_pos hAneg huA2
    have hBlt : B < 0 := huBmul ▸ mul_neg_of_neg_of_pos hBneg huB2
    exact hR ⟨(kw_hp_sign_intReduce a).mp (by exact_mod_cast hAlt),
      (kw_hp_sign_intReduce b).mp (by exact_mod_cast hBlt)⟩

  have hsolvAB : kw_hg1fc_legendreSolvable A B := by
    have h₀ := kw_hg1fc_legendre_descent hQR A₀ B₀ hA₀0 hB₀0 hA₀sf hB₀sf hsgn₀ hv₀
    have h₁ := (kw_hg1fc_legendreSolvable_sqScale (a := A₀) (b := B₀) huB0).mp h₀
    have h₂ := (kw_hg1fc_legendreSolvable_sqScale_left (a := A₀) (b := B₀ * uB ^ 2)
      huA0).mp h₁
    rwa [huAmul, huBmul] at h₂

  obtain ⟨x, y, z, hnt, heq⟩ := hsolvAB
  refine ⟨x * (a.den : ℚ), y * (b.den : ℚ), z, ?_, ?_⟩
  · rintro ⟨hX, hY, hZ⟩
    exact hnt ⟨(mul_eq_zero.mp hX).resolve_right hdA,
      (mul_eq_zero.mp hY).resolve_right hdB, hZ⟩
  ·
    rw [← haA, ← hbB] at heq
    linear_combination heq

end TernaryLocalGlobal
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section HilbertProductAllButOne

theorem kw_hg1fc_C_hilbertProduct_proved (a b : ℚ) :
    kw_HSCluster_C_hilbertProduct a b :=
  kw_HSCluster_C_W_wire_of_parityStep kw_hp_W_parityStep_proved
    kw_hpSolvAt_iff_gmk8_odd_proved kw_hpSolvAt_iff_jpd4_two_proved
    kw_HSCluster_C_F_two_proved kw_HSCluster_C_G_formulaProduct_proved a b

theorem kw_hg1fc_ternaryIsotropy_localGlobal_butOne
    (hQR : kw_hg1fc_hpSolvAt_implies_sqrtMod) {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (v₀ : HeightOneSpectrum (𝓞 ℚ))
    (hv : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ v₀ → kw_hpSolvAt a b v)
    (hR : ¬ ((a : ℝ) < 0 ∧ (b : ℝ) < 0)) :
    ∃ x y z : ℚ, ¬ (x = 0 ∧ y = 0 ∧ z = 0) ∧ z * z = a * (x * x) + b * (y * y) := by

  refine kw_hg1fc_ternaryIsotropy_localGlobal hQR ha hb (fun v ↦ ?_) hR
  by_contra hns
  obtain ⟨Rf, hRf, hEven⟩ := kw_hg1fc_C_hilbertProduct_proved a b ha hb
  have hsub : Rf ⊆ {v₀} := fun w hw ↦ Finset.mem_singleton.mpr <| by
    by_contra hne
    exact (hRf w).mp hw (hv w hne)
  have hv0 : v = v₀ := by
    by_contra hne; exact hns (hv v hne)
  subst hv0
  have hmem : v ∈ Rf := (hRf v).mpr hns
  have hcard : Rf.card = 1 := le_antisymm
    (Finset.card_le_card hsub |>.trans_eq (Finset.card_singleton v))
    (Finset.one_le_card.mpr ⟨v, hmem⟩)
  rw [if_neg hR, add_zero, hcard] at hEven
  exact (Nat.not_even_one) hEven

end HilbertProductAllButOne
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section QuaternLocalGlobal

def kw_hg1fc_quaternIsotropy_localGlobal : Prop :=
  ∀ (a b c : ℚ), a ≠ 0 → b ≠ 0 → c ≠ 0 →
    (∀ v : HeightOneSpectrum (𝓞 ℚ),
      ∃ x y z w : v.adicCompletion ℚ, ¬ (x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0) ∧
        -(algebraMap ℚ _ a) * x ^ 2 - (algebraMap ℚ _ b) * y ^ 2
          + (algebraMap ℚ _ a) * (algebraMap ℚ _ b) * z ^ 2
          - (algebraMap ℚ _ c) * w ^ 2 = 0) →
    (∃ x y z w : ℝ, ¬ (x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0) ∧
        -(a : ℝ) * x ^ 2 - (b : ℝ) * y ^ 2 + (a : ℝ) * (b : ℝ) * z ^ 2
          - (c : ℝ) * w ^ 2 = 0) →
    ∃ x y z w : ℚ, ¬ (x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0) ∧
      -a * x ^ 2 - b * y ^ 2 + a * b * z ^ 2 - c * w ^ 2 = 0

end QuaternLocalGlobal
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section MainTheorem

theorem kw_HSCluster_pureNrdLocalGlobal_of_hUniv_of_hQ4
    (hUniv : kw_isotropicPureNrdUniversal)
    (hQ4 : kw_hg1fc_quaternIsotropy_localGlobal)
    {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) :
    kw_HSCluster_pureNrdLocalGlobal a b := by
  intro c hc hvFin hReal

  refine kw_hg1fc_pureNrdRep_of_quaternIsotropic ha hb hUniv ?_

  refine hQ4 a b c ha hb hc (fun v ↦ ?_) ?_
  ·
    haveI : CharZero (v.adicCompletion ℚ) :=
      charZero_of_injective_algebraMap (algebraMap ℚ _).injective
    exact kw_hg1fc_quaternIsotropic_of_pureNrdRep (F := v.adicCompletion ℚ) (hvFin v)
  ·
    have h := kw_hg1fc_quaternIsotropic_of_pureNrdRep (F := ℝ) hReal
    have heq : ∀ q : ℚ, algebraMap ℚ ℝ q = (q : ℝ) := fun q ↦ eq_ratCast _ q
    simpa only [heq] using h

end MainTheorem
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end FLT.NumberTheory
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section
section

suppress_compilation

p2m_open "IsDedekindDomain P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.IsDedekindDomain NumberField P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.NumberField QuaternionAlgebra P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.QuaternionAlgebra"
p2m_open_scoped "Quaternion P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.Quaternion Classical P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.Classical"

namespace FLT
namespace NumberTheory

p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.IsDedekindDomain.HeightOneSpectrum"

section CommonValue

variable {F : Type*} [Field F] [CharZero F]

theorem kw_hg1fc_binaryIsotropic_universal {A B : F} (hA : A ≠ 0) (hB : B ≠ 0)
    {x₀ y₀ : F} (hnt : ¬ (x₀ = 0 ∧ y₀ = 0)) (heq : A * x₀ ^ 2 + B * y₀ ^ 2 = 0)
    (d : F) : ∃ x y : F, A * x ^ 2 + B * y ^ 2 = d := by

  have hx₀ : x₀ ≠ 0 := by
    rintro rfl
    simp only [ne_eq, zero_pow, OfNat.ofNat_ne_zero, not_false_eq_true, mul_zero,
      zero_add, mul_eq_zero, pow_eq_zero_iff] at heq
    exact hnt ⟨rfl, heq.resolve_left hB⟩
  have hy₀ : y₀ ≠ 0 := by
    rintro rfl
    simp only [ne_eq, zero_pow, OfNat.ofNat_ne_zero, not_false_eq_true, mul_zero,
      add_zero, mul_eq_zero, pow_eq_zero_iff] at heq
    exact hnt ⟨heq.resolve_left hA, rfl⟩

  have hB_eq : B = -(A * x₀ ^ 2) / y₀ ^ 2 := by
    field_simp; linear_combination heq
  refine ⟨(A + d) / (2 * A), y₀ * (d - A) / (2 * A * x₀), ?_⟩
  rw [hB_eq]
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  field_simp
  ring

theorem kw_hg1fc_quatern_localCommonValue {a b c : F} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) {x y z w : F} (hnt : ¬ (x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0))
    (heq : -a * x ^ 2 - b * y ^ 2 + a * b * z ^ 2 - c * w ^ 2 = 0) :
    ∃ d : F, d ≠ 0 ∧ (∃ X Y : F, a * X ^ 2 + b * Y ^ 2 = d) ∧
      (∃ Z W : F, a * b * Z ^ 2 - c * W ^ 2 = d) := by
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have heq' : a * x ^ 2 + b * y ^ 2 = a * b * z ^ 2 - c * w ^ 2 := by linear_combination -heq
  by_cases hd : a * x ^ 2 + b * y ^ 2 = 0
  ·
    have hzw : a * b * z ^ 2 - c * w ^ 2 = 0 := heq' ▸ hd
    by_cases hxy : x = 0 ∧ y = 0
    ·
      have hzw_nt : ¬ (z = 0 ∧ w = 0) := fun ⟨hz, hw⟩ ↦ hnt ⟨hxy.1, hxy.2, hz, hw⟩
      have hzw' : a * b * z ^ 2 + (-c) * w ^ 2 = 0 := by linear_combination hzw
      obtain ⟨Z, W, hZW⟩ :=
        kw_hg1fc_binaryIsotropic_universal hab (neg_ne_zero.mpr hc) hzw_nt hzw' a
      exact ⟨a, ha, ⟨1, 0, by ring⟩, ⟨Z, W, by linear_combination hZW⟩⟩
    ·
      obtain ⟨X, Y, hXY⟩ :=
        kw_hg1fc_binaryIsotropic_universal ha hb hxy hd (a * b)
      exact ⟨a * b, hab, ⟨X, Y, hXY⟩, ⟨1, 0, by ring⟩⟩
  · exact ⟨a * x ^ 2 + b * y ^ 2, hd, ⟨x, y, rfl⟩, ⟨z, w, heq'.symm⟩⟩

end CommonValue
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

def kw_hg1fc_sqClass_weakApprox : Prop :=
  ∀ (T : Finset (HeightOneSpectrum (𝓞 ℚ))), kw_hp_vTwo ∈ T →
    ∀ (tgt : ∀ v ∈ T, v.adicCompletion ℚ), (∀ v (hv : v ∈ T), tgt v hv ≠ 0) →
    ∀ (σ : ℝ), σ ≠ 0 →
    ∃ (d : ℚ) (q : HeightOneSpectrum (𝓞 ℚ)), d ≠ 0 ∧ q ∉ T ∧
      (∀ v (hv : v ∈ T), ∃ s : v.adicCompletion ℚ,
        algebraMap ℚ _ d = tgt v hv * s ^ 2) ∧
      (∃ s : ℝ, (d : ℝ) = σ * s ^ 2) ∧
      kw_hp_supp d d ⊆ insert q T

section Assemble

theorem kw_hg1fc_mem_hp_supp_iff (X Y : ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    v ∈ kw_hp_supp X Y ↔ (Rat.HeightOneSpectrum.primesEquiv v : ℕ)
      ∈ (2 * (X.num.natAbs * X.den * (Y.num.natAbs * Y.den))).primeFactors := by
  simp only [kw_hp_supp, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
  constructor
  · rintro ⟨p, hp, heq⟩
    have : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = p := by
      rw [← heq, Equiv.apply_symm_apply]
    exact this ▸ hp
  · intro hp
    exact ⟨_, hp, by simp only [Equiv.symm_apply_eq]; exact Subtype.ext rfl⟩

theorem kw_hg1fc_hp_supp_neg_right (X Y : ℚ) :
    kw_hp_supp X (-Y) = kw_hp_supp X Y := by
  ext v
  rw [kw_hg1fc_mem_hp_supp_iff, kw_hg1fc_mem_hp_supp_iff,
    Rat.neg_num, Int.natAbs_neg, Rat.neg_den]

theorem kw_hg1fc_hp_supp_mul_subset {A B d : ℚ} (hA : A ≠ 0) (hB : B ≠ 0) (hd : d ≠ 0) :
    kw_hp_supp (A * d) (B * d) ⊆ kw_hp_supp A B ∪ kw_hp_supp d d := by
  have hAd : A * d ≠ 0 := mul_ne_zero hA hd
  have hBd : B * d ≠ 0 := mul_ne_zero hB hd

  have hnum : ∀ X : ℚ, (X * d).num.natAbs ∣ X.num.natAbs * d.num.natAbs := fun X ↦ by
    have h := Rat.num_mul_num_eq_num_mul_gcd X d
    exact Int.natAbs_dvd_natAbs.mpr ⟨_, h⟩ |>.trans (by rw [Int.natAbs_mul])
  have hden : ∀ X : ℚ, (X * d).den ∣ X.den * d.den := fun X ↦ Rat.mul_den_dvd X d
  intro v hv
  rw [kw_hg1fc_mem_hp_supp_iff] at hv
  rw [Finset.mem_union, kw_hg1fc_mem_hp_supp_iff, kw_hg1fc_mem_hp_supp_iff]
  set p := (Rat.HeightOneSpectrum.primesEquiv v : ℕ)
  have hpprime : p.Prime := (Rat.HeightOneSpectrum.primesEquiv v).2
  obtain ⟨-, hpdvd, hN0⟩ := Nat.mem_primeFactors.mp hv
  have hNAB : 2 * (A.num.natAbs * A.den * (B.num.natAbs * B.den)) ≠ 0 := by
    have : A.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hA)
    have : B.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hB)
    positivity
  have hNdd : 2 * (d.num.natAbs * d.den * (d.num.natAbs * d.den)) ≠ 0 := by
    have : d.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hd)
    positivity

  simp only [Nat.mem_primeFactors, hpprime, hNAB, hNdd, true_and, ne_eq, not_false_eq_true,
    and_true]
  rcases (hpprime.dvd_mul.mp hpdvd) with h2 | hrest
  · exact Or.inl (Dvd.dvd.mul_right h2 _)
  rcases (hpprime.dvd_mul.mp hrest) with hl | hr
  · rcases (hpprime.dvd_mul.mp hl) with hn | hde
    · rcases (hpprime.dvd_mul.mp (hn.trans (hnum A))) with hAn | hdn
      · exact Or.inl (Dvd.dvd.mul_left (Dvd.dvd.mul_right (Dvd.dvd.mul_right hAn _) _) 2)
      · exact Or.inr (Dvd.dvd.mul_left (Dvd.dvd.mul_right (Dvd.dvd.mul_right hdn _) _) 2)
    · rcases (hpprime.dvd_mul.mp (hde.trans (hden A))) with hAd | hdd
      · exact Or.inl (Dvd.dvd.mul_left (Dvd.dvd.mul_right (Dvd.dvd.mul_left hAd _) _) 2)
      · exact Or.inr (Dvd.dvd.mul_left (Dvd.dvd.mul_right (Dvd.dvd.mul_left hdd _) _) 2)
  · rcases (hpprime.dvd_mul.mp hr) with hn | hde
    · rcases (hpprime.dvd_mul.mp (hn.trans (hnum B))) with hBn | hdn
      · exact Or.inl (Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_right hBn _) _) 2)
      · exact Or.inr (Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_right hdn _) _) 2)
    · rcases (hpprime.dvd_mul.mp (hde.trans (hden B))) with hBd | hdd
      · exact Or.inl (Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_left hBd _) _) 2)
      · exact Or.inr (Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_left hdd _) _) 2)

theorem kw_hg1fc_hpSolvAt_of_binRep_sqClass {A B d : ℚ}
    (v : HeightOneSpectrum (𝓞 ℚ)) {dv : v.adicCompletion ℚ} (hdv : dv ≠ 0)
    {x y : v.adicCompletion ℚ}
    (hrep : algebraMap ℚ _ A * x ^ 2 + algebraMap ℚ _ B * y ^ 2 = dv)
    {s : v.adicCompletion ℚ} (hs : s ≠ 0) (hsq : algebraMap ℚ _ d = dv * s ^ 2) :
    kw_hpSolvAt (A * d) (B * d) v := by
  refine ⟨dv * s, x, y, fun ⟨h0, _, _⟩ ↦ ?_, ?_⟩
  · exact (mul_ne_zero hdv hs) h0
  · simp only [map_mul]
    linear_combination -dv * hsq - algebraMap ℚ (v.adicCompletion ℚ) d * hrep

theorem kw_hg1fc_realSign_of_binRep_sqClass {A B σ d : ℝ} (hσ : σ ≠ 0)
    {X Y : ℝ} (hrep : A * X ^ 2 + B * Y ^ 2 = σ) {s : ℝ} (hsq : d = σ * s ^ 2) :
    ¬ (A * d < 0 ∧ B * d < 0) := by
  rintro ⟨h1, h2⟩
  have hσd : σ * d = A * d * X ^ 2 + B * d * Y ^ 2 := by linear_combination -(d * hrep)
  have hle : σ * d ≤ 0 := hσd ▸ add_nonpos
    (mul_nonpos_of_nonpos_of_nonneg h1.le (sq_nonneg X))
    (mul_nonpos_of_nonpos_of_nonneg h2.le (sq_nonneg Y))
  have heq : σ * d = (σ * s) ^ 2 := by rw [hsq]; ring
  have hσs := sq_eq_zero_iff.mp (le_antisymm (heq ▸ hle) (sq_nonneg _))
  rcases mul_eq_zero.mp hσs with h | h
  · exact hσ h
  · rw [hsq, h] at h1; simp at h1

theorem kw_hg1fc_quaternIsotropy_localGlobal_of_hQR_of_hSqAp
    (hQR : kw_hg1fc_hpSolvAt_implies_sqrtMod)
    (hSqAp : kw_hg1fc_sqClass_weakApprox) :
    kw_hg1fc_quaternIsotropy_localGlobal := by
  intro a b c ha hb hc hvFin hReal
  have hab : a * b ≠ 0 := mul_ne_zero ha hb

  set T := kw_hp_supp a b ∪ kw_hp_supp (a * b) c with hT_def
  have hv2T : kw_hp_vTwo ∈ T := by
    refine Finset.mem_union_left _ ((kw_hg1fc_mem_hp_supp_iff a b _).mpr ?_)
    rw [kw_hp_vTwo_primesEquiv]
    have h1 : a.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr ha)
    have h2 : b.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hb)
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_mul_right 2 _, by positivity⟩

  have hCV : ∀ v ∈ T, ∃ dv : v.adicCompletion ℚ, dv ≠ 0 ∧
      (∃ x y, algebraMap ℚ _ a * x ^ 2 + algebraMap ℚ _ b * y ^ 2 = dv) ∧
      (∃ z w, algebraMap ℚ _ a * algebraMap ℚ _ b * z ^ 2
        - algebraMap ℚ _ c * w ^ 2 = dv) := fun v _ ↦ by
    haveI : CharZero (v.adicCompletion ℚ) :=
      charZero_of_injective_algebraMap (algebraMap ℚ _).injective
    have haF := (map_ne_zero_iff _ (algebraMap ℚ (v.adicCompletion ℚ)).injective).mpr ha
    have hbF := (map_ne_zero_iff _ (algebraMap ℚ (v.adicCompletion ℚ)).injective).mpr hb
    have hcF := (map_ne_zero_iff _ (algebraMap ℚ (v.adicCompletion ℚ)).injective).mpr hc
    obtain ⟨x, y, z, w, hnt, heq⟩ := hvFin v
    exact kw_hg1fc_quatern_localCommonValue haF hbF hcF hnt heq
  choose tgt htgt0 hrep1 hrep2 using hCV

  obtain ⟨xR, yR, zR, wR, hntR, heqR⟩ := hReal
  obtain ⟨σ, hσ0, ⟨XR, YR, hrepR1⟩, ⟨ZR, WR, hrepR2⟩⟩ :=
    kw_hg1fc_quatern_localCommonValue (F := ℝ)
      (Rat.cast_ne_zero.mpr ha) (Rat.cast_ne_zero.mpr hb) (Rat.cast_ne_zero.mpr hc)
      hntR heqR

  obtain ⟨d, q, hd0, hqT, hmatch, ⟨sR, hsqR⟩, hsuppd⟩ :=
    hSqAp T hv2T tgt htgt0 σ hσ0
  have had : a * d ≠ 0 := mul_ne_zero ha hd0
  have hbd : b * d ≠ 0 := mul_ne_zero hb hd0
  have habd : a * b * d ≠ 0 := mul_ne_zero hab hd0
  have hncd : -(c * d) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero hc hd0)
  have hdF : ∀ v : HeightOneSpectrum (𝓞 ℚ), algebraMap ℚ (v.adicCompletion ℚ) d ≠ 0 :=
    fun v ↦ (map_ne_zero_iff _ (algebraMap ℚ _).injective).mpr hd0

  have hv1 : ∀ v, v ≠ q → kw_hpSolvAt (a * d) (b * d) v := by
    intro v hvq
    by_cases hvT : v ∈ T
    · obtain ⟨s, hsq⟩ := hmatch v hvT
      obtain ⟨X, Y, hXY⟩ := hrep1 v hvT
      have hs : s ≠ 0 := fun h ↦ hdF v (by rw [hsq, h]; ring)
      exact kw_hg1fc_hpSolvAt_of_binRep_sqClass v (htgt0 v hvT) hXY hs hsq
    · refine kw_hp_solvAt_of_notMem_supp (a * d) (b * d) had hbd v (fun hvs ↦ ?_)
      rcases Finset.mem_union.mp (kw_hg1fc_hp_supp_mul_subset ha hb hd0 hvs) with h | h
      · exact hvT (Finset.mem_union_left _ h)
      · rcases Finset.mem_insert.mp (hsuppd h) with h | h
        · exact hvq h
        · exact hvT h

  have hv2 : ∀ v, v ≠ q → kw_hpSolvAt (a * b * d) (-(c * d)) v := by
    intro v hvq
    have heq : -(c * d) = (-c) * d := by ring
    by_cases hvT : v ∈ T
    · obtain ⟨s, hsq⟩ := hmatch v hvT
      obtain ⟨Z, W, hZW⟩ := hrep2 v hvT
      have hs : s ≠ 0 := fun h ↦ hdF v (by rw [hsq, h]; ring)
      have hZW' : algebraMap ℚ _ (a * b) * Z ^ 2 + algebraMap ℚ _ (-c) * W ^ 2
          = tgt v hvT := by simp only [map_mul, _root_.map_neg]; linear_combination hZW
      rw [heq]
      exact kw_hg1fc_hpSolvAt_of_binRep_sqClass v (htgt0 v hvT) hZW' hs hsq
    · refine kw_hp_solvAt_of_notMem_supp (a * b * d) (-(c * d)) habd hncd v (fun hvs ↦ ?_)
      rw [heq] at hvs
      have hsub := kw_hg1fc_hp_supp_mul_subset hab (neg_ne_zero.mpr hc) hd0 hvs
      rw [kw_hg1fc_hp_supp_neg_right] at hsub
      rcases Finset.mem_union.mp hsub with h | h
      · exact hvT (Finset.mem_union_right _ h)
      · rcases Finset.mem_insert.mp (hsuppd h) with h | h
        · exact hvq h
        · exact hvT h

  have hR1 : ¬ ((↑(a * d) : ℝ) < 0 ∧ (↑(b * d) : ℝ) < 0) := by
    push_cast
    exact kw_hg1fc_realSign_of_binRep_sqClass hσ0 hrepR1 hsqR
  have hR2 : ¬ ((↑(a * b * d) : ℝ) < 0 ∧ (↑(-(c * d)) : ℝ) < 0) := by
    push_cast; rw [← neg_mul]
    have hrepR2' : (a : ℝ) * b * ZR ^ 2 + (-(c : ℝ)) * WR ^ 2 = σ := by
      linear_combination hrepR2
    exact kw_hg1fc_realSign_of_binRep_sqClass hσ0 hrepR2' hsqR

  obtain ⟨x₁, y₁, z₁, hnt1, heq1⟩ :=
    kw_hg1fc_ternaryIsotropy_localGlobal_butOne hQR had hbd q hv1 hR1
  obtain ⟨x₂, y₂, z₂, hnt2, heq2⟩ :=
    kw_hg1fc_ternaryIsotropy_localGlobal_butOne hQR habd hncd q hv2 hR2

  by_cases hz1 : z₁ = 0
  · refine ⟨x₁, y₁, 0, 0, fun ⟨hx, hy, _, _⟩ ↦ hnt1 ⟨hx, hy, hz1⟩, ?_⟩
    have h' : d * (a * x₁ ^ 2 + b * y₁ ^ 2) = 0 := by
      have h : a * d * (x₁ * x₁) + b * d * (y₁ * y₁) = 0 := by rw [← heq1, hz1]; ring
      linear_combination h
    linear_combination -((mul_eq_zero.mp h').resolve_left hd0)
  by_cases hz2 : z₂ = 0
  · refine ⟨0, 0, x₂, y₂, fun ⟨_, _, hx, hy⟩ ↦ hnt2 ⟨hx, hy, hz2⟩, ?_⟩
    have h' : d * (a * b * x₂ ^ 2 - c * y₂ ^ 2) = 0 := by
      have h : a * b * d * (x₂ * x₂) + -(c * d) * (y₂ * y₂) = 0 := by rw [← heq2, hz2]; ring
      linear_combination h
    linear_combination ((mul_eq_zero.mp h').resolve_left hd0)
  refine ⟨x₁ * z₂, y₁ * z₂, x₂ * z₁, y₂ * z₁, ?_, ?_⟩
  · rintro ⟨hX, hY, _, _⟩
    have hx1 : x₁ = 0 := (mul_eq_zero.mp hX).resolve_right hz2
    have hy1 : y₁ = 0 := (mul_eq_zero.mp hY).resolve_right hz2
    exact hz1 (mul_self_eq_zero.mp (by rw [heq1, hx1, hy1]; ring))
  ·
    have e1 : z₁ * z₁ = d * (a * (x₁ * x₁) + b * (y₁ * y₁)) := by linear_combination heq1
    have e2 : z₂ * z₂ = d * (a * b * (x₂ * x₂) - c * (y₂ * y₂)) := by linear_combination heq2
    have key : z₁ * z₁ * (a * b * (x₂ * x₂) - c * (y₂ * y₂))
        = z₂ * z₂ * (a * (x₁ * x₁) + b * (y₁ * y₁)) := by rw [e1, e2]; ring
    linear_combination key

end Assemble
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

theorem kw_HSCluster_pureNrdLocalGlobal_of_hUniv_of_hQR_of_hSqAp
    (hUniv : kw_isotropicPureNrdUniversal)
    (hQR : kw_hg1fc_hpSolvAt_implies_sqrtMod)
    (hSqAp : kw_hg1fc_sqClass_weakApprox)
    {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) :
    kw_HSCluster_pureNrdLocalGlobal a b :=
  kw_HSCluster_pureNrdLocalGlobal_of_hUniv_of_hQ4 hUniv
    (kw_hg1fc_quaternIsotropy_localGlobal_of_hQR_of_hSqAp hQR hSqAp) ha hb

end FLT.NumberTheory
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section
section

p2m_open "IsDedekindDomain P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.IsDedekindDomain NumberField P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.NumberField"
p2m_open_scoped "Classical P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.Classical Function P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.Function"

namespace FLT
namespace NumberTheory

p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.IsDedekindDomain.HeightOneSpectrum"
open FLT.CampGenuineMk

theorem kw_hg1fc_sqAp_localRep {p : ℕ} [hp : Fact p.Prime] {τ : ℚ_[p]} (hτ : τ ≠ 0) :
    ∃ e m : ℕ, e < 2 ∧ ¬ p ∣ m ∧
      ∀ n : ℤ, (p : ℤ) ^ 3 ∣ n - m →
        ∃ s : ℚ_[p], (n : ℚ_[p]) * (p : ℚ_[p]) ^ e = τ * s ^ 2 := by
  have hpne : (p : ℚ_[p]) ≠ 0 := gmk7_cls_p_padic_ne_zero
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt

  set w : ℤ := τ.valuation with hw_def
  set e : ℕ := (w % 2).toNat with he_def
  have hmod := Int.emod_two_eq_zero_or_one w
  have he_eq : (e : ℤ) = w % 2 :=
    Int.toNat_of_nonneg (Int.emod_nonneg w two_ne_zero)
  have he2 : e < 2 := by omega
  obtain ⟨k, hk⟩ : ∃ k : ℤ, w = e + 2 * k :=
    ⟨w / 2, by have := Int.mul_ediv_add_emod w 2; omega⟩

  set u : ℤ_[p]ˣ := gmk7_cls_unitPart hτ with hu_def
  have huτ : τ = ((u : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ w := gmk7_cls_unitPart_spec hτ
  set m : ℕ := (PadicInt.toZModPow 3 (u : ℤ_[p])).val with hm_def

  have hmu_mem : (m : ℤ_[p]) - (u : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ 3} := by
    rw [← PadicInt.ker_toZModPow 3, RingHom.mem_ker, map_sub, map_natCast,
      hm_def, ZMod.natCast_val, ZMod.cast_id, sub_self]
  have hp3eq : ((p : ℝ) ^ (-(3 : ℕ) : ℤ)) = (p : ℝ)⁻¹ ^ 3 := by
    rw [_root_.zpow_neg, zpow_natCast, inv_pow]
  have hmu_norm : ‖((m : ℤ_[p]) : ℚ_[p]) - ((u : ℤ_[p]) : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ ^ 3 := by
    have h := (PadicInt.norm_le_pow_iff_mem_span_pow
      ((m : ℤ_[p]) - (u : ℤ_[p])) 3).mpr hmu_mem
    rwa [hp3eq, ← PadicInt.padic_norm_e_of_padicInt, PadicInt.coe_sub] at h

  have hplt : (p : ℝ)⁻¹ ^ 3 < ‖(2 : ℚ_[p])‖ ^ 2 := by
    rcases eq_or_ne p 2 with hp2 | hp2
    · subst hp2
      have h2 : ‖(2 : ℚ_[2])‖ = 2⁻¹ := by simpa using Padic.norm_p (p := 2)
      rw [h2]; norm_num
    · have h2u : ‖(2 : ℚ_[p])‖ = 1 := by
        rw [show ‖(2 : ℚ_[p])‖ = ‖(2 : ℤ_[p])‖ from rfl]
        refine le_antisymm (PadicInt.norm_le_one _)
          (not_lt.mp (mt (PadicInt.norm_int_lt_one_iff_dvd (2 : ℤ)).mp ?_))
        exact_mod_cast fun h ↦ hp2
          ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h)
      rw [h2u, one_pow]
      exact pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hp1) (by omega)

  have hunorm : ‖((u : ℤ_[p]) : ℚ_[p])‖ = 1 := by
    rw [PadicInt.padic_norm_e_of_padicInt]; exact PadicInt.isUnit_iff.mp u.isUnit
  have hp2le1 : ‖(2 : ℚ_[p])‖ ^ 2 ≤ 1 := by
    rw [show ‖(2 : ℚ_[p])‖ = ‖(2 : ℤ_[p])‖ from rfl]
    exact pow_le_one₀ (norm_nonneg _) (PadicInt.norm_le_one _)
  have hmu_lt1 : ‖((m : ℤ_[p]) : ℚ_[p]) - ((u : ℤ_[p]) : ℚ_[p])‖ < 1 :=
    hmu_norm.trans_lt (hplt.trans_le hp2le1)
  have hpm : ¬ p ∣ m := fun hdvd ↦ by
    have hm1 : ‖((m : ℤ_[p]) : ℚ_[p])‖ < 1 := by
      rw [show ((m : ℤ_[p]) : ℚ_[p]) = (((m : ℤ) : ℤ_[p]) : ℚ_[p]) from by push_cast; ring,
        PadicInt.padic_norm_e_of_padicInt, PadicInt.norm_int_lt_one_iff_dvd]
      exact_mod_cast hdvd
    have : ‖((u : ℤ_[p]) : ℚ_[p])‖ < 1 := by
      calc ‖((u : ℤ_[p]) : ℚ_[p])‖ = ‖((u : ℤ_[p]) : ℚ_[p]) - ((m : ℤ_[p]) : ℚ_[p])
              + ((m : ℤ_[p]) : ℚ_[p])‖ := by ring_nf
        _ ≤ max ‖((u : ℤ_[p]) : ℚ_[p]) - ((m : ℤ_[p]) : ℚ_[p])‖
              ‖((m : ℤ_[p]) : ℚ_[p])‖ := IsUltrametricDist.norm_add_le_max _ _
        _ < 1 := max_lt (by rw [norm_sub_rev]; exact hmu_lt1) hm1
    exact absurd hunorm (ne_of_lt this)
  refine ⟨e, m, he2, hpm, fun n hn ↦ ?_⟩

  have hnm_norm : ‖((n - m : ℤ) : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ ^ 3 := by
    have h := (PadicInt.norm_int_le_pow_iff_dvd (p := p) (k := n - m) (n := 3)).mpr
      (by exact_mod_cast hn)
    rwa [hp3eq, ← PadicInt.padic_norm_e_of_padicInt, PadicInt.coe_intCast] at h
  have hnu_norm : ‖(n : ℚ_[p]) - ((u : ℤ_[p]) : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ ^ 3 := by
    have heq : (n : ℚ_[p]) - ((u : ℤ_[p]) : ℚ_[p])
        = ((n - m : ℤ) : ℚ_[p])
          + (((m : ℤ_[p]) : ℚ_[p]) - ((u : ℤ_[p]) : ℚ_[p])) := by push_cast; ring
    exact heq ▸ (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hnm_norm hmu_norm)
  have hune : ((u : ℤ_[p]) : ℚ_[p]) ≠ 0 := fun h ↦ by simp [h] at hunorm

  obtain ⟨t, ht⟩ := kw_hjoint_padic_isSquare_of_close_one
    (show ‖(n : ℚ_[p]) / ((u : ℤ_[p]) : ℚ_[p]) - 1‖ < ‖(2 : ℚ_[p])‖ ^ 2 from by
      rw [div_sub_one hune, norm_div, hunorm, div_one]; exact hnu_norm.trans_lt hplt)

  have ht' : (n : ℚ_[p]) = ((u : ℤ_[p]) : ℚ_[p]) * (t * t) := by
    field_simp [hune] at ht; linear_combination ht
  have hpe : (p : ℚ_[p]) ^ w * ((p : ℚ_[p]) ^ (-k) * (p : ℚ_[p]) ^ (-k))
      = (p : ℚ_[p]) ^ e := by
    rw [← zpow_add₀ hpne, ← zpow_add₀ hpne, ← zpow_natCast (p : ℚ_[p]) e]
    congr 1; omega
  refine ⟨(p : ℚ_[p]) ^ (-k) * t, ?_⟩
  calc (n : ℚ_[p]) * (p : ℚ_[p]) ^ e
      = ((u : ℤ_[p]) : ℚ_[p]) * (t * t) * (p : ℚ_[p]) ^ e := by rw [ht']
    _ = ((u : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ w
        * ((p : ℚ_[p]) ^ (-k) * t * ((p : ℚ_[p]) ^ (-k) * t)) := by rw [← hpe]; ring
    _ = τ * ((p : ℚ_[p]) ^ (-k) * t) ^ 2 := by rw [← huτ, sq]

section Transport

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

theorem kw_hg1fc_sqAp_localRep_transport (v : HeightOneSpectrum (𝓞 ℚ))
    {τ : v.adicCompletion ℚ} (hτ : τ ≠ 0) :
    ∃ e m : ℕ, e < 2 ∧ ¬ (Rat.HeightOneSpectrum.primesEquiv v : ℕ) ∣ m ∧
      ∀ n : ℤ, ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℤ) ^ 3 ∣ n - m →
        ∃ s : v.adicCompletion ℚ,
          (((n * (Rat.HeightOneSpectrum.primesEquiv v : ℕ) ^ e : ℤ) : ℚ)
              : v.adicCompletion ℚ) = τ * s ^ 2 := by
  haveI : Fact (Rat.HeightOneSpectrum.primesEquiv v : ℕ).Prime :=
    kw_hjoint_instFactPrimePrimesEquiv v
  let φ : v.adicCompletion ℚ ≃+* ℚ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)] :=
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toRingEquiv
  have hτ' : φ τ ≠ 0 := fun h ↦ hτ (φ.injective (h.trans (_root_.map_zero φ).symm))
  obtain ⟨e, m, he2, hpm, H⟩ := kw_hg1fc_sqAp_localRep hτ'
  refine ⟨e, m, he2, hpm, fun n hn ↦ ?_⟩
  obtain ⟨s, hs⟩ := H n hn
  refine ⟨φ.symm s, ?_⟩
  apply φ.injective
  rw [map_mul, map_pow, RingEquiv.apply_symm_apply, map_ratCast, ← hs]
  push_cast; ring

end Transport
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section Main

p2m_open_scoped "Function P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.Function"

theorem kw_hg1fc_sqClass_weakApprox_proved : kw_hg1fc_sqClass_weakApprox := by
  intro T hv2T tgt htgt σ hσ
  classical

  choose e m he2 hpm H using fun vv : T ↦
    kw_hg1fc_sqAp_localRep_transport vv.1 (htgt vv.1 vv.2)

  let pr : T → ℕ := fun vv ↦ (Rat.HeightOneSpectrum.primesEquiv vv.1 : ℕ)
  have hpr_prime : ∀ vv : T, (pr vv).Prime :=
    fun vv ↦ (Rat.HeightOneSpectrum.primesEquiv vv.1).2
  have hpr_inj : Function.Injective pr := fun a b hab ↦ Subtype.ext
    (Rat.HeightOneSpectrum.primesEquiv.injective (Subtype.ext hab))
  have hpr_pos : ∀ vv, 0 < pr vv := fun vv ↦ (hpr_prime vv).pos
  set σ' : ℤ := if 0 < σ then 1 else -1 with hσ'_def
  have hσ' : σ' = 1 ∨ σ' = -1 := by rw [hσ'_def]; split <;> simp
  have hσ'0 : σ' ≠ 0 := by rcases hσ' with h | h <;> simp [h]
  have hσ'abs : σ'.natAbs = 1 := by rcases hσ' with h | h <;> simp [h]
  have hσσ' : 0 < σ * (σ' : ℝ) := by
    rcases lt_or_gt_of_ne hσ with h | h
    · have : σ' = -1 := by rw [hσ'_def]; simp [not_lt.mpr h.le]
      rw [this]; push_cast; nlinarith
    · have : σ' = 1 := by rw [hσ'_def]; simp [h]
      rw [this]; push_cast; nlinarith
  let P : ℕ := ∏ vv : T, pr vv ^ e vv
  have hP0 : 0 < P := Finset.prod_pos fun vv _ ↦ Nat.pow_pos (hpr_pos vv)
  let cN : T → ℕ := fun vv ↦ ∏ w ∈ Finset.univ.erase vv, pr w ^ e w
  have hcN_cop : ∀ vv : T, (cN vv).Coprime (pr vv) := fun vv ↦
    Nat.Coprime.prod_left fun w hw ↦ Nat.Coprime.pow_left _
      ((Nat.coprime_primes (hpr_prime w) (hpr_prime vv)).mpr
        fun h ↦ (Finset.mem_erase.mp hw).1 (hpr_inj h))
  have hP_split : ∀ vv : T, P = cN vv * pr vv ^ e vv := fun vv ↦
    (Finset.prod_erase_mul _ _ (Finset.mem_univ vv)).symm

  let mo : T → ℕ := fun vv ↦ pr vv ^ 3
  have hmo_cop : Pairwise (Nat.Coprime on mo) := fun a b hab ↦ Nat.Coprime.pow _ _
    ((Nat.coprime_primes (hpr_prime a) (hpr_prime b)).mpr fun h ↦ hab (hpr_inj h))
  let M : ℕ := ∏ vv : T, mo vv
  haveI : NeZero M := ⟨Finset.prod_ne_zero_iff.mpr
    fun vv _ ↦ (Nat.pow_pos (hpr_pos vv) (n := 3)).ne'⟩
  haveI : ∀ vv : T, NeZero (mo vv) :=
    fun vv ↦ ⟨(Nat.pow_pos (hpr_pos vv) (n := 3)).ne'⟩
  let crt : ZMod M ≃+* ∀ vv : T, ZMod (mo vv) := ZMod.prodEquivPi mo hmo_cop
  have hcrt_nat : ∀ (x : ℕ) (vv : T), crt (x : ZMod M) vv = (x : ZMod (mo vv)) :=
    fun x vv ↦ by
      have := map_natCast crt.toRingHom x
      simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at this
      rw [this]; rfl

  have hcu : ∀ vv : T, IsUnit (σ' * (cN vv : ℤ) : ZMod (mo vv)) := fun vv ↦ by
    refine IsUnit.mul ?_ ?_
    · rcases hσ' with h | h <;> simp [h]
    · rw [Int.cast_natCast, ZMod.isUnit_iff_coprime]
      exact (hcN_cop vv).pow_right _
  have hmu : ∀ vv : T, IsUnit ((m vv : ℕ) : ZMod (mo vv)) := fun vv ↦ by
    rw [ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.pow_right _
      ((hpr_prime vv).coprime_iff_not_dvd.mpr (hpm vv)).symm
  let f : ∀ vv : T, ZMod (mo vv) :=
    fun vv ↦ ((m vv : ℕ) : ZMod (mo vv)) * (hcu vv).unit⁻¹
  have hfu : IsUnit (crt.symm f) := by
    have hfpi : IsUnit f := Pi.isUnit_iff.mpr
      fun vv ↦ (hmu vv).mul (hcu vv).unit⁻¹.isUnit
    exact hfpi.map crt.symm.toRingHom

  obtain ⟨q, hqN, hqp, hqr⟩ :=
    kw_hg1fc_dirichletAP_pin hfu (Finset.univ.sup pr)
  have hqT' : ∀ vv : T, q ≠ pr vv := fun vv h ↦
    absurd (h ▸ hqN) (not_lt.mpr (Finset.le_sup (Finset.mem_univ vv)))
  let qv : HeightOneSpectrum (𝓞 ℚ) := Rat.HeightOneSpectrum.primesEquiv.symm ⟨q, hqp⟩
  have hqv_pr : (Rat.HeightOneSpectrum.primesEquiv qv : ℕ) = q := by
    simp [qv, Equiv.apply_symm_apply]
  have hqvT : qv ∉ T := fun h ↦ hqT' ⟨qv, h⟩ hqv_pr.symm

  set d : ℚ := ((σ' * q * P : ℤ) : ℚ) with hd_def
  have hdZ : (σ' * q * P : ℤ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hσ'0 (Int.natCast_ne_zero.mpr hqp.ne_zero))
      (Int.natCast_ne_zero.mpr hP0.ne')
  have hd0 : d ≠ 0 := by rw [hd_def]; exact_mod_cast hdZ
  refine ⟨d, qv, hd0, hqvT, ?_, ?_, ?_⟩
  ·
    intro v hv
    set vv : T := ⟨v, hv⟩

    have h1 : ((q : ℕ) : ZMod (mo vv)) = f vv := by
      rw [← hcrt_nat q vv, hqr, crt.apply_symm_apply]
    have h2 : ((q : ℕ) : ZMod (mo vv)) * (σ' * (cN vv : ℤ) : ZMod (mo vv))
        = ((m vv : ℕ) : ZMod (mo vv)) := by
      rw [h1, show f vv = ((m vv : ℕ) : ZMod (mo vv)) * ↑(hcu vv).unit⁻¹ from rfl,
        mul_assoc, IsUnit.val_inv_mul, mul_one]
    have hcong : (((q : ℤ) * (σ' * cN vv) - m vv : ℤ) : ZMod (mo vv)) = 0 := by
      rw [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, ← h2,
        Int.cast_mul, Int.cast_natCast, sub_self]
    have hdvd : ((pr vv : ℤ)) ^ 3 ∣ (q : ℤ) * (σ' * cN vv) - m vv := by
      have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (mo vv)).mp hcong
      exact_mod_cast h
    obtain ⟨s, hs⟩ := H vv ((q : ℤ) * (σ' * cN vv)) hdvd
    refine ⟨s, ?_⟩

    rw [eq_ratCast (algebraMap ℚ (v.adicCompletion ℚ)) d,
      show d = (((q : ℤ) * (σ' * cN vv) * (pr vv) ^ e vv : ℤ) : ℚ) from by
        rw [hd_def, hP_split vv]; push_cast; ring]
    exact hs
  ·
    have hdσ : 0 < (d : ℝ) / σ := by
      have hqP : (0 : ℝ) < (q : ℝ) * (P : ℝ) :=
        mul_pos (by exact_mod_cast hqp.pos) (by exact_mod_cast hP0)
      have hdR : (d : ℝ) = (σ' : ℝ) * ((q : ℝ) * (P : ℝ)) := by
        rw [hd_def]; push_cast; ring
      have hmul : 0 < σ * (d : ℝ) := by rw [hdR, ← mul_assoc]; exact mul_pos hσσ' hqP
      calc (0 : ℝ) < σ * (d : ℝ) / (σ * σ) :=
            div_pos hmul (mul_self_pos.mpr hσ)
        _ = (d : ℝ) / σ := by rw [mul_div_mul_left _ _ hσ]
    exact ⟨Real.sqrt ((d : ℝ) / σ), by
      rw [Real.sq_sqrt hdσ.le]; field_simp⟩
  ·
    intro v hv
    rw [kw_hg1fc_mem_hp_supp_iff] at hv
    set ℓ : ℕ := (Rat.HeightOneSpectrum.primesEquiv v : ℕ) with hℓ_def
    have hℓp : ℓ.Prime := (Rat.HeightOneSpectrum.primesEquiv v).2

    have hnum : d.num = σ' * q * P := Rat.num_intCast _
    have hden : d.den = 1 := Rat.den_intCast _
    have hnabs : d.num.natAbs = q * P := by
      rw [hnum, Int.natAbs_mul, Int.natAbs_mul, hσ'abs, one_mul,
        Int.natAbs_natCast, Int.natAbs_natCast]
    rw [hden, mul_one, hnabs] at hv

    have hℓdvd : ℓ ∣ 2 * (q * P) * (q * P) := by
      have := (Nat.mem_primeFactors.mp hv).2.1; ring_nf at this ⊢; exact this
    have hcases : ℓ = 2 ∨ ℓ ∣ q * P := by
      rcases hℓp.dvd_mul.mp hℓdvd with h | h
      · rcases hℓp.dvd_mul.mp h with h2 | hqP
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hℓp Nat.prime_two).mp h2)
        · exact Or.inr hqP
      · exact Or.inr h
    rcases hcases with hℓ2 | hqP
    ·
      refine Finset.mem_insert_of_mem ?_
      have : v = kw_hp_vTwo := Rat.HeightOneSpectrum.primesEquiv.injective
        (Subtype.ext (hℓ2.trans kw_hp_vTwo_primesEquiv.symm))
      exact this ▸ hv2T
    · rcases hℓp.dvd_mul.mp hqP with hq | hP
      ·
        have hℓq : ℓ = q := (Nat.prime_dvd_prime_iff_eq hℓp hqp).mp hq
        refine Finset.mem_insert.mpr (Or.inl ?_)
        exact Rat.HeightOneSpectrum.primesEquiv.injective
          (Subtype.ext (hℓq.trans hqv_pr.symm))
      ·
        have hex : ∃ w : T, ℓ ∣ pr w ^ e w :=
          (Prime.dvd_finsetProd_iff hℓp.prime _).mp hP |>.imp fun w ⟨_, h⟩ ↦ h
        obtain ⟨w, hw⟩ := hex
        have : ℓ = pr w :=
          (Nat.prime_dvd_prime_iff_eq hℓp (hpr_prime w)).mp (hℓp.dvd_of_dvd_pow hw)
        refine Finset.mem_insert_of_mem ?_
        have : v = w.1 := Rat.HeightOneSpectrum.primesEquiv.injective
          (Subtype.ext (hℓ_def ▸ this :
            (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = pr w))
        exact this ▸ w.2

end Main
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

theorem kw_HSCluster_pureNrdLocalGlobal_of_hUniv_of_hQR
    (hUniv : kw_isotropicPureNrdUniversal)
    (hQR : kw_hg1fc_hpSolvAt_implies_sqrtMod)
    {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) :
    kw_HSCluster_pureNrdLocalGlobal a b :=
  kw_HSCluster_pureNrdLocalGlobal_of_hUniv_of_hQR_of_hSqAp hUniv hQR
    kw_hg1fc_sqClass_weakApprox_proved ha hb

end FLT.NumberTheory
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section
section

namespace FLT
namespace NumberTheory

theorem kw_isotropicPureNrdUniversal_proved : kw_isotropicPureNrdUniversal := by
  have _pin := Classical.em True
  intro F _ _ a b ha hb ⟨x₀, y₀, z₀, hne, hQ0⟩ c
  have h4 : (4 : F) ≠ 0 := by norm_num
  have hsplit : x₀ ≠ 0 ∨ y₀ ≠ 0 ∨ z₀ ≠ 0 := by
    by_contra h
    simp only [not_or, not_not] at h
    exact hne ⟨h.1, h.2.1, h.2.2⟩
  rcases hsplit with hx0 | hy0 | hz0
  ·

    have hrel : -b * y₀ ^ 2 + a * b * z₀ ^ 2 = a * x₀ ^ 2 := by linear_combination hQ0
    have hden : (4 : F) * a * x₀ ^ 2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero h4 ha) (pow_ne_zero 2 hx0)
    set lam := c / (4 * a * x₀ ^ 2) with hlam
    refine ⟨x₀ * (1 - lam), y₀ * (1 + lam), z₀ * (1 + lam), ?_⟩
    have hexp : -a * (x₀ * (1 - lam)) ^ 2 - b * (y₀ * (1 + lam)) ^ 2
        + a * b * (z₀ * (1 + lam)) ^ 2
        = -a * x₀ ^ 2 * (1 - lam) ^ 2
          + (-b * y₀ ^ 2 + a * b * z₀ ^ 2) * (1 + lam) ^ 2 := by ring
    rw [hexp, hrel]
    have hkey : -a * x₀ ^ 2 * (1 - lam) ^ 2 + a * x₀ ^ 2 * (1 + lam) ^ 2
        = a * x₀ ^ 2 * (4 * lam) := by ring
    rw [hkey, hlam]
    field_simp [hden]
  ·
    have hrel : -a * x₀ ^ 2 + a * b * z₀ ^ 2 = b * y₀ ^ 2 := by linear_combination hQ0
    have hden : (4 : F) * b * y₀ ^ 2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero h4 hb) (pow_ne_zero 2 hy0)
    set mu := c / (4 * b * y₀ ^ 2) with hmu
    refine ⟨x₀ * (1 + mu), y₀ * (1 - mu), z₀ * (1 + mu), ?_⟩
    have hexp : -a * (x₀ * (1 + mu)) ^ 2 - b * (y₀ * (1 - mu)) ^ 2
        + a * b * (z₀ * (1 + mu)) ^ 2
        = -b * y₀ ^ 2 * (1 - mu) ^ 2
          + (-a * x₀ ^ 2 + a * b * z₀ ^ 2) * (1 + mu) ^ 2 := by ring
    rw [hexp, hrel]
    have hkey : -b * y₀ ^ 2 * (1 - mu) ^ 2 + b * y₀ ^ 2 * (1 + mu) ^ 2
        = b * y₀ ^ 2 * (4 * mu) := by ring
    rw [hkey, hmu]
    field_simp [hden]
  ·
    have hrel : a * x₀ ^ 2 + b * y₀ ^ 2 = a * b * z₀ ^ 2 := by linear_combination -hQ0
    have hden : (4 : F) * (a * b) * z₀ ^ 2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero h4 (mul_ne_zero ha hb)) (pow_ne_zero 2 hz0)
    set nu := -c / (4 * (a * b) * z₀ ^ 2) with hnu
    refine ⟨x₀ * (1 + nu), y₀ * (1 + nu), z₀ * (1 - nu), ?_⟩
    have hexp : -a * (x₀ * (1 + nu)) ^ 2 - b * (y₀ * (1 + nu)) ^ 2
        + a * b * (z₀ * (1 - nu)) ^ 2
        = -(a * x₀ ^ 2 + b * y₀ ^ 2) * (1 + nu) ^ 2
          + a * b * z₀ ^ 2 * (1 - nu) ^ 2 := by ring
    rw [hexp, hrel]
    have hkey : -(a * b * z₀ ^ 2) * (1 + nu) ^ 2 + a * b * z₀ ^ 2 * (1 - nu) ^ 2
        = a * b * z₀ ^ 2 * (-4 * nu) := by ring
    rw [hkey, hnu]
    field_simp [hden]

end FLT.NumberTheory
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section
section

set_option maxHeartbeats 8000000

suppress_compilation

p2m_open "IsDedekindDomain P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.IsDedekindDomain NumberField P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.NumberField QuaternionAlgebra P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.QuaternionAlgebra"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.IsDedekindDomain.HeightOneSpectrum"
open FLT.CampGenuineMk

namespace FLT
namespace NumberTheory

section SquareClassWitness

end SquareClassWitness
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section GlueHelper

variable {p : ℕ} [Fact p.Prime]

end GlueHelper
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section PadicOdd

variable {p : ℕ} [Fact p.Prime]

end PadicOdd
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section PadicTwo

end PadicTwo
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

local instance kw_ldq_instFactPrimePrimesEquiv (v : HeightOneSpectrum (𝓞 ℚ)) :
    Fact (Rat.HeightOneSpectrum.primesEquiv v : ℕ).Prime :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

section PadicEquivHelper

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

noncomputable def kw_ldq_padicRingEquiv (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.adicCompletion ℚ ≃+* ℚ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)] :=
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toRingEquiv

end PadicEquivHelper
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

noncomputable def kw_ldq_padicCast {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) :
    ℚ_[p] ≃+* ℚ_[q] := by
  subst h; exact RingEquiv.refl _

theorem kw_ldq_isSquare_ringEquiv {F K : Type*} [CommRing F] [CommRing K]
    (φ : F ≃+* K) {x : F} : IsSquare (φ x) ↔ IsSquare x := by
  refine ⟨fun ⟨r, hr⟩ => ⟨φ.symm r, φ.injective ?_⟩, fun ⟨r, hr⟩ => ⟨φ r, ?_⟩⟩
  · rw [map_mul, RingEquiv.apply_symm_apply, hr]
  · rw [hr, map_mul]

theorem kw_ldq_hpSolvAt_iff_gmk8 {p : ℕ} [Fact p.Prime]
    (a b : ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) (φ : v.adicCompletion ℚ ≃+* ℚ_[p]) :
    kw_hpSolvAt a b v ↔ gmk8_cls_solvable (p := p) (a : ℚ_[p]) (b : ℚ_[p]) := by
  rw [kw_hpSolvAt_ringEquiv a b v φ, gmk8_cls_solvable_def]
  constructor
  · rintro ⟨z, x, y, hnt, heq⟩
    refine ⟨x, y, z, ?_, by linear_combination heq⟩
    by_contra h; simp only [not_or, not_not] at h
    exact hnt ⟨h.2.2, h.1, h.2.1⟩
  · rintro ⟨x, y, z, hnt, heq⟩
    refine ⟨z, x, y, fun ⟨hz, hx, hy⟩ => ?_, by linear_combination heq⟩
    rcases hnt with h | h | h
    · exact h hx
    · exact h hy
    · exact h hz

end FLT.NumberTheory
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

section
section

set_option maxHeartbeats 3200000

suppress_compilation

p2m_open "IsDedekindDomain P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.IsDedekindDomain NumberField P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.NumberField IsDedekindDomain.HeightOneSpectrum P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.IsDedekindDomain.HeightOneSpectrum"
open FLT.CampGenuineMk

namespace FLT
namespace NumberTheory

section IntCastHelpers

variable {p : ℕ} [Fact p.Prime]

theorem kw_hg1fc_s24c_intCast_padic_ne_zero {a : ℤ} (hpa : ¬ (p : ℤ) ∣ a) :
    (a : ℚ_[p]) ≠ 0 := by
  exact Int.cast_ne_zero.mpr fun h ↦ hpa (h ▸ dvd_zero _)

theorem kw_hg1fc_s24c_norm_intCast_eq_one {a : ℤ} (hpa : ¬ (p : ℤ) ∣ a) :
    ‖(a : ℤ_[p])‖ = 1 := by
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp ?_)
  exact fun h ↦ hpa ((PadicInt.norm_int_lt_one_iff_dvd a).mp h)

theorem kw_hg1fc_s24c_intCast_valuation_zero {a : ℤ} (hpa : ¬ (p : ℤ) ∣ a) :
    (a : ℚ_[p]).valuation = 0 := by
  refine gmk7_cls_valuation_eq_zero_of_norm_one (kw_hg1fc_s24c_intCast_padic_ne_zero hpa) ?_
  rw [← PadicInt.coe_intCast, PadicInt.padic_norm_e_of_padicInt]
  exact kw_hg1fc_s24c_norm_intCast_eq_one hpa

theorem kw_hg1fc_s24c_residue_intCast {a : ℤ} (hpa : ¬ (p : ℤ) ∣ a)
    (haP : (a : ℚ_[p]) ≠ 0) :
    gmk7_cls_residue haP = (a : ZMod p) := by
  have hup : ((gmk7_cls_unitPart haP : ℤ_[p]) : ℚ_[p]) = ((a : ℤ_[p]) : ℚ_[p]) := by
    rw [gmk7_cls_unitPart_coe, kw_hg1fc_s24c_intCast_valuation_zero hpa, _root_.neg_zero,
      zpow_zero, mul_one, PadicInt.coe_intCast]
  have : (gmk7_cls_unitPart haP : ℤ_[p]) = (a : ℤ_[p]) := Subtype.coe_injective hup
  unfold gmk7_cls_residue
  rw [this, map_intCast]

theorem kw_hg1fc_s24c_intCast_valuation_one {b : ℤ} (hb0 : b ≠ 0)
    (hpb : (p : ℤ) ∣ b) (hsf : Squarefree b) :
    (b : ℚ_[p]).valuation = 1 := by
  obtain ⟨b', rfl⟩ := hpb
  have hpnat : (p : ℤ).natAbs = p := Int.natAbs_natCast p
  have hb'0 : b' ≠ 0 := right_ne_zero_of_mul hb0

  have hpb' : ¬ (p : ℤ) ∣ b' := fun ⟨c, hc⟩ ↦ by
    have hu := hsf (p : ℤ) ⟨c, by rw [hc]; ring⟩
    rw [Int.isUnit_iff_natAbs_eq, hpnat] at hu
    exact (Fact.out (p := p.Prime)).ne_one hu
  push_cast
  rw [Padic.valuation_mul (Nat.cast_ne_zero.mpr (Fact.out (p := p.Prime)).ne_zero)
    (Int.cast_ne_zero.mpr hb'0), Padic.valuation_p,
    kw_hg1fc_s24c_intCast_valuation_zero hpb', add_zero]

end IntCastHelpers
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

theorem s18_isSquare_zmod_two : ∀ x : ZMod 2, IsSquare x := by decide

theorem s18_hil_pair_zero_one_eq_one_imp :
    ∀ e sa sb : ℤˣ, FLT.CampGenuineMk.gmk6_hil_pair e ⟨0, sa⟩ ⟨1, sb⟩ = 1 → sa = 1 := by decide

noncomputable abbrev kw_hg1fc_s24c_placeAbove {p : ℕ} (hp : p.Prime) :
    HeightOneSpectrum (𝓞 ℚ) :=
  Rat.HeightOneSpectrum.primesEquiv.symm ⟨p, hp⟩

theorem kw_hg1fc_s24c_perPrime_isSquare_zmod {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a b : ℤ} (hb0 : b ≠ 0) (hpa : ¬ (p : ℤ) ∣ a) (hpb : (p : ℤ) ∣ b)
    (hsf : Squarefree b)
    (hsolv : kw_hpSolvAt (a : ℚ) (b : ℚ) (kw_hg1fc_s24c_placeAbove hp)) :
    IsSquare ((a : ZMod p)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set v : HeightOneSpectrum (𝓞 ℚ) := kw_hg1fc_s24c_placeAbove hp with hv_def

  haveI : Fact (Rat.HeightOneSpectrum.primesEquiv v : ℕ).Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  have hvp : (Rat.HeightOneSpectrum.primesEquiv v : ℕ) = p := by
    have : Rat.HeightOneSpectrum.primesEquiv v = (⟨p, hp⟩ : Nat.Primes) :=
      Equiv.apply_symm_apply _ _
    simp [this]

  let φ : v.adicCompletion ℚ ≃+* ℚ_[p] :=
    (kw_ldq_padicRingEquiv v).trans (kw_ldq_padicCast hvp)

  have hg8 : gmk8_cls_solvable (p := p) (a : ℚ_[p]) (b : ℚ_[p]) := by
    have := (kw_ldq_hpSolvAt_iff_gmk8 (a : ℚ) (b : ℚ) v φ).mp hsolv
    simpa only [Rat.cast_intCast] using this

  have haP : (a : ℚ_[p]) ≠ 0 := kw_hg1fc_s24c_intCast_padic_ne_zero hpa
  have hbP : (b : ℚ_[p]) ≠ 0 := Int.cast_ne_zero.mpr hb0

  have hhil : gmk6_hil_pair (gmk6_hil_epsSign p) (gmk7_cls_classOf haP)
      (gmk7_cls_classOf hbP) = 1 := (gmk9_ser_solvability_pair hp2 haP hbP).mp hg8

  have hva : (gmk7_cls_classOf haP).valParity = 0 := by
    show ((a : ℚ_[p]).valuation : ZMod 2) = 0
    rw [kw_hg1fc_s24c_intCast_valuation_zero hpa, Int.cast_zero]
  have hvb : (gmk7_cls_classOf hbP).valParity = 1 := by
    show ((b : ℚ_[p]).valuation : ZMod 2) = 1
    rw [kw_hg1fc_s24c_intCast_valuation_one hb0 hpb hsf, Int.cast_one]

  have hsign : gmk7_cls_sign haP = 1 := by
    have heqa : gmk7_cls_classOf haP = ⟨0, gmk7_cls_sign haP⟩ :=
      gmk6_hil_SquareClass_ext hva rfl
    have heqb : gmk7_cls_classOf hbP = ⟨1, gmk7_cls_sign hbP⟩ :=
      gmk6_hil_SquareClass_ext hvb rfl
    rw [heqa, heqb] at hhil
    exact s18_hil_pair_zero_one_eq_one_imp
      (gmk6_hil_epsSign p) (gmk7_cls_sign haP) (gmk7_cls_sign hbP) hhil

  have hres : IsSquare (gmk7_cls_residue haP) := (gmk7_cls_sign_eq_one_iff haP).mp hsign
  rwa [kw_hg1fc_s24c_residue_intCast hpa haP] at hres

theorem kw_hg1fc_s24c_prod_isSquare {M N : Type*} [Monoid M] [Monoid N] {x : M} {y : N} :
    IsSquare (x, y) ↔ IsSquare x ∧ IsSquare y := by
  refine ⟨fun ⟨r, hr⟩ ↦ ⟨⟨r.1, congrArg Prod.fst hr⟩, ⟨r.2, congrArg Prod.snd hr⟩⟩,
    fun ⟨⟨r, hr⟩, ⟨s, hs⟩⟩ ↦ ⟨(r, s), ?_⟩⟩
  exact Prod.ext hr hs

theorem kw_hg1fc_s24c_isSquare_zmod_of_primeFactors {a : ℤ} :
    ∀ n : ℕ, Squarefree n → (∀ p : ℕ, p.Prime → p ∣ n → IsSquare ((a : ZMod p))) →
      IsSquare ((a : ZMod n)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hsf hpsq
    rcases eq_or_ne n 1 with rfl | hn1
    · exact ⟨0, Subsingleton.elim _ _⟩
    ·
      have hn0 : n ≠ 0 := hsf.ne_zero
      obtain ⟨p, hpp, m, rfl⟩ := Nat.exists_prime_and_dvd hn1
      have hm0 : m ≠ 0 := fun h ↦ hn0 (by simp [h])
      have hmlt : m < p * m := by
        have h1 : 1 * m < p * m :=
          (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero hm0)).mpr hpp.one_lt
        simpa using h1

      have hpm : ¬ p ∣ m := fun ⟨c, hc⟩ ↦
        hpp.ne_one (Nat.isUnit_iff.mp (hsf p ⟨c, by rw [hc]; ring⟩))
      have hcop : Nat.Coprime p m := (hpp.coprime_iff_not_dvd).mpr hpm

      have hsfm : Squarefree m := hsf.squarefree_of_dvd (dvd_mul_left m p)
      have hmSq : IsSquare ((a : ZMod m)) := ih m hmlt hsfm
        (fun q hq hqm ↦ hpsq q hq (hqm.mul_left p))
      have hpSq : IsSquare ((a : ZMod p)) := hpsq p hpp (dvd_mul_right p m)

      refine (kw_ldq_isSquare_ringEquiv (ZMod.chineseRemainder hcop)).mp ?_
      rw [map_intCast]
      exact kw_hg1fc_s24c_prod_isSquare.mpr ⟨hpSq, hmSq⟩

theorem kw_hg1fc_hpSolvAt_implies_sqrtMod_proved :
    kw_hg1fc_hpSolvAt_implies_sqrtMod := by
  intro a b ha0 hsf hb0 hsolvable

  have hperprime : ∀ p : ℕ, p.Prime → p ∣ b.natAbs → IsSquare ((a : ZMod p)) := by
    intro p hp hpb
    haveI : Fact p.Prime := ⟨hp⟩
    by_cases hp2 : p = 2
    ·
      subst hp2; exact s18_isSquare_zmod_two _
    · by_cases hpa : (p : ℤ) ∣ a
      ·
        exact ⟨0, ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mpr hpa).trans (mul_zero 0).symm⟩
      ·
        exact kw_hg1fc_s24c_perPrime_isSquare_zmod hp hp2 hb0 hpa
          (Int.natCast_dvd.mpr hpb) hsf (hsolvable _)

  have hsfN : Squarefree b.natAbs := Int.squarefree_natAbs.mpr hsf
  obtain ⟨r, hr⟩ := kw_hg1fc_s24c_isSquare_zmod_of_primeFactors b.natAbs hsfN hperprime

  haveI : NeZero b.natAbs := ⟨Int.natAbs_ne_zero.mpr hb0⟩
  refine ⟨(r.val : ℤ), Int.natAbs_dvd.mp ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast [ZMod.natCast_val, sq]
  rw [← hr, sub_self]

end FLT.NumberTheory
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.CampGenuineMk"

theorem solution
    (F : Type) [Field F] [CharZero F] (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hiso : ∃ x y z : F, ¬ (x = 0 ∧ y = 0 ∧ z = 0) ∧ -a * x ^ 2 - b * y ^ 2 + a * b * z ^ 2 = 0)
    (c : F) :
    ∃ x y z : F, -a * x ^ 2 - b * y ^ 2 + a * b * z ^ 2 = c :=
  FLT.NumberTheory.kw_isotropicPureNrdUniversal_proved F a b ha hb hiso c

end S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero
end P2MW
export P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero (solution)
