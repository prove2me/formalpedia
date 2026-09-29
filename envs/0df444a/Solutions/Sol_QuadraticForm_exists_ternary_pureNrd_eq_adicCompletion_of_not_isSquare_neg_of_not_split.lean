-- Prove2me | solution 1 for QuadraticForm.exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/8362da48-37b2-586c-b99f-5db7dc15922e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

namespace Classical
p2m_export "Classical" "em by_cases not_not"
p2m_open "Classical"
end Classical
namespace ENNReal
p2m_export "ENNReal" "coe_zero coe_natCast eq_div_iff coe_add coe_injective coe_ne_zero coe_sub coe_mul coe_one"
p2m_open "ENNReal"
end ENNReal
namespace FLT
namespace CampGenuineMk
end FLT.CampGenuineMk
namespace FLT
namespace GL1FujisakiFiniteShadow
end FLT.GL1FujisakiFiniteShadow
namespace FLT
namespace JpssD4GJProp83MetaplecticKubotaCoverCarrier
end FLT.JpssD4GJProp83MetaplecticKubotaCoverCarrier
namespace FLT
namespace JpssD4KubotaArchimedeanCocycleSlice
end FLT.JpssD4KubotaArchimedeanCocycleSlice
namespace FLT
namespace JpssD4KubotaPTwoHilbertSolvabilityIdentification
end FLT.JpssD4KubotaPTwoHilbertSolvabilityIdentification
namespace FLT
namespace JpssD4KubotaPTwoHilbertTable
end FLT.JpssD4KubotaPTwoHilbertTable
namespace FLT
namespace JpssD4KubotaTameSymbolUniformWindowSlice
end FLT.JpssD4KubotaTameSymbolUniformWindowSlice
namespace FreyPackage
end FreyPackage
namespace IsDedekindDomain
p2m_export "IsDedekindDomain" "HeightOneSpectrum.instAlgebraAdicCompletion HeightOneSpectrum.adicCompletion FiniteAdeleRing HeightOneSpectrum"
p2m_open "IsDedekindDomain"
end IsDedekindDomain
namespace IsDedekindDomain
p2m_export "IsDedekindDomain" "HeightOneSpectrum.instAlgebraAdicCompletion HeightOneSpectrum.adicCompletion FiniteAdeleRing HeightOneSpectrum"
namespace HeightOneSpectrum
p2m_export "IsDedekindDomain.HeightOneSpectrum" "instAlgebraAdicCompletion adicCompletion valuation"
p2m_open "IsDedekindDomain.HeightOneSpectrum IsDedekindDomain"
end IsDedekindDomain.HeightOneSpectrum
namespace Matrix
p2m_export "Matrix" "J ext algebraMap_matrix_apply comp one_apply zpow_neg of map mul_apply"
p2m_open "Matrix"
end Matrix
namespace MeasureTheory
p2m_open "MeasureTheory"
end MeasureTheory
namespace ModularCurve
end ModularCurve
namespace NNReal
p2m_export "NNReal" "sub_div coe_one coe_zero coe_ne_zero"
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
p2m_export "Polynomial" "C X coe_one derivative_C coe_neg aeval aeval_C map derivative_X comp algebra coe_mul coe_sub eval_X coe_injective eval_C flt coe_zero derivative_sq derivative_sub coe_add derivative aeval_X ext funext ring eval"
p2m_open "Polynomial"
end Polynomial
namespace Quaternion
p2m_export "Quaternion" "coe_injective coe_zero coe_sub coe_mul finrank_eq_four coe_one coe_natCast coe_add ext coe_neg"
p2m_open "Quaternion"
end Quaternion
namespace QuaternionAlgebra
p2m_export "QuaternionAlgebra" "re coe_mul finrank_eq_four coe_neg coe_injective coe_one coe_algebraMap mk_mul_mk coe_sub coe_add imK coe_zero imJ imI Basis neg_mk coe_natCast"
p2m_open "QuaternionAlgebra"
end QuaternionAlgebra
namespace Rat
p2m_export "Rat" "pos cast_ofNat HeightOneSpectrum.primesEquiv neg_zero cast_id cast_add castHom cast_zero cast_ne_zero cast_pow cast_one HeightOneSpectrum.adicCompletion.padicEquiv ext"
namespace FiniteAdeleRing
p2m_open "Rat"
end Rat.FiniteAdeleRing
namespace TensorProduct
p2m_export "TensorProduct" "congr ext map"
p2m_open "TensorProduct"
end TensorProduct
namespace TopologicalSpace
p2m_open "TopologicalSpace"
end TopologicalSpace
namespace TotallyDefiniteQuaternionAlgebra
end TotallyDefiniteQuaternionAlgebra

namespace PadicInt
p2m_export "PadicInt" "ker_toZMod norm_p toZMod norm_units valuation_mul coe_neg coe_add coe_natCast maximalIdeal_eq_span_p coe_mul toZModPow padic_norm_e_of_padicInt norm_le_one valuation valuation_p le_valuation_add coe_sub ext norm_lt_one_iff_dvd mul_inv ker_toZModPow algebra coe_one coe_zero coe_ne_zero mkUnits mkUnits_eq norm_eq_zpow_neg_valuation"
p2m_open "PadicInt"
theorem coe_injective_s18 {p : ℕ} [Fact p.Prime] : Function.Injective ((↑) : ℤ_[p] → ℚ_[p]) :=
  Subtype.val_injective
end PadicInt

theorem charZero_adicCompletion_s18 {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    CharZero (v.adicCompletion K) :=
  ((algebraMap K (v.adicCompletion K)).charZero_iff (algebraMap K (v.adicCompletion K)).injective).mp inferInstance

namespace S18Inst
scoped instance instCharZeroAdicCompletionRingOfIntegers_s18 {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    CharZero (v.adicCompletion K) := charZero_adicCompletion_s18 v
end S18Inst

section S18Body
open scoped S18Inst

scoped instance fact_prime_two_s18 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
scoped instance fact_prime_three_s18 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
scoped instance fact_prime_seven_s18 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
scoped instance fact_prime_five_s18 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
scoped instance fact_prime_thirteen_s18 : Fact (Nat.Prime 13) := ⟨by norm_num⟩

section
section

suppress_compilation

p2m_open "IsDedekindDomain P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.IsDedekindDomain NumberField P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.NumberField QuaternionAlgebra P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.QuaternionAlgebra"
p2m_open_scoped "Quaternion P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.Quaternion"

namespace FLT
namespace NumberTheory

p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.IsDedekindDomain.HeightOneSpectrum"

def kw_pureNrdRep (F : Type*) [CommRing F] (a b c : F) : Prop :=
  ∃ x y z : F, -a * x ^ 2 - b * y ^ 2 + a * b * z ^ 2 = c

end FLT.NumberTheory

end

end

section
section

suppress_compilation

p2m_open "IsDedekindDomain P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.IsDedekindDomain NumberField P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.NumberField QuaternionAlgebra P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.QuaternionAlgebra"
p2m_open_scoped "TensorProduct P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.TensorProduct Quaternion P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.Quaternion Polynomial P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.Polynomial"
open ModularCurve

namespace FLT
namespace NumberTheory

open TotallyDefiniteQuaternionAlgebra FreyPackage
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.IsDedekindDomain.HeightOneSpectrum"

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

p2m_open "Polynomial P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.Polynomial"

variable (p : ℕ) [Fact p.Prime]

end RatStrongApprox

section LocalIrredAtoms

p2m_open "Polynomial P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.Polynomial"

variable (a b : ℚ) (p : ℕ) [Fact p.Prime]

end LocalIrredAtoms

section LocalGlobalEmbed

p2m_open "Polynomial P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.Polynomial"

variable (a b : ℚ)

end LocalGlobalEmbed

section MainWire

p2m_open "Polynomial P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.Polynomial"

variable (a b : ℚ) (p : ℕ) [Fact p.Prime]

end MainWire

end FLT.NumberTheory

end

end

section
section

suppress_compilation

p2m_open "IsDedekindDomain P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.IsDedekindDomain NumberField P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.NumberField QuaternionAlgebra P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.QuaternionAlgebra"
p2m_open_scoped "Quaternion P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.Quaternion"

namespace FLT
namespace NumberTheory

p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.IsDedekindDomain.HeightOneSpectrum"

def kw_localDivQuatPureNrdRep (a b : ℚ) : Prop :=
  ∀ (v : HeightOneSpectrum (𝓞 ℚ)), ¬ kw_isSplitAtPlace a b v →
    ∀ c : v.adicCompletion ℚ, ¬ IsSquare (-c) →
      kw_pureNrdRep (v.adicCompletion ℚ) (algebraMap ℚ _ a) (algebraMap ℚ _ b) c

section SquareIdentity

variable {F : Type*} [CommRing F] {a b : F}

end SquareIdentity

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

p2m_open "IsDedekindDomain P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.IsDedekindDomain.HeightOneSpectrum NumberField P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.NumberField QuaternionAlgebra P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.QuaternionAlgebra"
open ModularCurve

namespace FLT
namespace NumberTheory

open TotallyDefiniteQuaternionAlgebra FreyPackage
p2m_open_scoped "Classical P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.Classical"

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

end SubAtoms

section SplitEngine

p2m_open "Matrix P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.Matrix"

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

p2m_open "Matrix P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.Matrix"

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

p2m_open "Matrix P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.Matrix"

end AInfProof

section BCofiniteProof

open FLT.CampGenuineMk

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

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

def gmk6_hil_epsSign (p : ℕ) : ℤˣ :=
  if p % 4 = 1 then 1 else -1

end FLT.CampGenuineMk
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT"

end
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

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
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

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
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

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
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

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
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

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
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

section
section

p2m_open "IsDedekindDomain P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.IsDedekindDomain.HeightOneSpectrum NumberField P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.NumberField QuaternionAlgebra P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.QuaternionAlgebra"
p2m_open_scoped "Classical P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.Classical"

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

end FLT.NumberTheory
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

section
section

p2m_open "IsDedekindDomain P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.IsDedekindDomain.HeightOneSpectrum NumberField P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.NumberField"
p2m_open_scoped "Classical P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.Classical"

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

end PadicEquivSection
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

end FLT.NumberTheory
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

section
section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

p2m_open "NumberField P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.NumberField IsDedekindDomain P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.IsDedekindDomain MeasureTheory P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.MeasureTheory TopologicalSpace P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.TopologicalSpace"
open Rat.FiniteAdeleRing
open FLT.GL1FujisakiFiniteShadow
p2m_open_scoped "ENNReal P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.ENNReal NNReal P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.NNReal Pointwise P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.Pointwise"

noncomputable section

namespace FLT
namespace CampGenuineMk

def gmk11_rec_wildEps (u : (ZMod 8)ˣ) : ZMod 2 :=
  (((u : ZMod 8).val / 2 : ℕ) : ZMod 2)

def gmk11_rec_wildOmega (u : (ZMod 8)ˣ) : ZMod 2 :=
  ((((u : ZMod 8).val ^ 2 - 1) / 8 : ℕ) : ZMod 2)

def gmk11_rec_wildPair (x y : ZMod 2 × (ZMod 8)ˣ) : ℤˣ :=
  (-1 : ℤˣ) ^ (gmk11_rec_wildEps x.2 * gmk11_rec_wildEps y.2
      + x.1 * gmk11_rec_wildOmega y.2
      + y.1 * gmk11_rec_wildOmega x.2).val

def gmk11_rec_wildMul (x y : ZMod 2 × (ZMod 8)ˣ) : ZMod 2 × (ZMod 8)ˣ :=
  (x.1 + y.1, x.2 * y.2)

def gmk11_rec_wildOne : ZMod 2 × (ZMod 8)ˣ := (0, 1)

theorem gmk11_rec_wildPair_symm (x y : ZMod 2 × (ZMod 8)ˣ) :
    gmk11_rec_wildPair x y = gmk11_rec_wildPair y x := by
  have _pin := Classical.em True
  unfold gmk11_rec_wildPair
  have h : gmk11_rec_wildEps x.2 * gmk11_rec_wildEps y.2
        + x.1 * gmk11_rec_wildOmega y.2 + y.1 * gmk11_rec_wildOmega x.2
      = gmk11_rec_wildEps y.2 * gmk11_rec_wildEps x.2
        + y.1 * gmk11_rec_wildOmega x.2 + x.1 * gmk11_rec_wildOmega y.2 := by
    ring
  rw [h]

end FLT.CampGenuineMk
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"
end
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

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

theorem gmk12_wcl_wildMul_one (c : ZMod 2 × (ZMod 8)ˣ) :
    gmk11_rec_wildMul c gmk11_rec_wildOne = c := by
  have _pin := Classical.em True
  show (c.1 + 0, c.2 * 1) = c
  rw [add_zero, mul_one]

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

theorem gmk12_wcl_surjective_reps (c : ZMod 2 × (ZMod 8)ˣ) :
    ∃ (x : ℚ_[2]) (hx : x ≠ 0), gmk12_wcl_classOf hx = c := by
  have _pin := Classical.em True
  obtain ⟨a, u⟩ := c
  rcases gmk12_wcl_zmod2_cases a with rfl | rfl <;>
    rcases gmk12_wcl_units_cases u with rfl | rfl | rfl | rfl
  · exact ⟨1, gmk12_wcl_one_ne_zero, gmk12_wcl_cert_classOf_one⟩
  · exact ⟨-5, gmk12_wcl_negFive_ne_zero, gmk12_wcl_cert_classOf_negFive⟩
  · exact ⟨5, gmk12_wcl_five_ne_zero, gmk12_wcl_cert_classOf_five⟩
  · exact ⟨-1, gmk12_wcl_negOne_ne_zero, gmk12_wcl_cert_classOf_negOne⟩
  · exact ⟨2, gmk12_wcl_two_ne_zero, gmk12_wcl_cert_classOf_two⟩
  · exact ⟨-10, gmk12_wcl_negTen_ne_zero, gmk12_wcl_cert_classOf_negTen⟩
  · exact ⟨10, gmk12_wcl_ten_ne_zero, gmk12_wcl_cert_classOf_ten⟩
  · exact ⟨-2, gmk12_wcl_negTwo_ne_zero, gmk12_wcl_cert_classOf_negTwo⟩

end FLT.CampGenuineMk
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

section
section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

namespace FLT
namespace CampGenuineMk

theorem gmk12_wsv_norm_two : ‖(2 : ℤ_[2])‖ = 2⁻¹ := by
  have _pin := Classical.em True
  have h := PadicInt.norm_p (p := 2)
  simpa using h

theorem gmk12_wsv_norm_eight : ‖(8 : ℤ_[2])‖ = 8⁻¹ := by
  have _pin := Classical.em True
  have h8 : (8 : ℤ_[2]) = 2 * (2 * 2) := by norm_num
  rw [h8, norm_mul, norm_mul, gmk12_wsv_norm_two]
  norm_num

theorem gmk12_wsv_isSquare_of_norm_band {u : ℤ_[2]}
    (h : ‖u - 1‖ < ‖(2 : ℤ_[2])‖ ^ 2) : IsSquare u := by
  have _pin := Classical.em True
  set F : Polynomial ℤ_[2] := Polynomial.X ^ 2 - Polynomial.C u with hF_def
  have hFa : ∀ b : ℤ_[2], Polynomial.aeval b F = b ^ 2 - u := by
    intro b
    rw [hF_def]
    simp
  have hFda : Polynomial.aeval (1 : ℤ_[2]) F.derivative = 2 := by
    rw [hF_def, Polynomial.derivative_sub, Polynomial.derivative_C,
      Polynomial.derivative_sq, Polynomial.derivative_X, sub_zero, mul_one,
      map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    simp
  have hF1 : Polynomial.aeval (1 : ℤ_[2]) F = -(u - 1) := by
    rw [hFa]
    ring
  have hnorm : ‖Polynomial.aeval (1 : ℤ_[2]) F‖
      < ‖Polynomial.aeval (1 : ℤ_[2]) F.derivative‖ ^ 2 := by
    rw [hF1, hFda, norm_neg]
    exact h
  obtain ⟨z, hz, -, -, -⟩ := hensels_lemma hnorm
  have hz2 : z ^ 2 - u = 0 := by
    rw [← hFa z]
    exact hz
  have hzu : z ^ 2 = u := sub_eq_zero.mp hz2
  exact ⟨z, by rw [← hzu, pow_two]⟩

theorem gmk12_wsv_isSquare_of_one_mod_eight {u : ℤ_[2]}
    (h : (8 : ℤ_[2]) ∣ (u - 1)) : IsSquare u := by
  have _pin := Classical.em True
  apply gmk12_wsv_isSquare_of_norm_band
  obtain ⟨c, hc⟩ := h
  rw [hc, norm_mul, gmk12_wsv_norm_eight, gmk12_wsv_norm_two]
  have hcle : ‖c‖ ≤ 1 := PadicInt.norm_le_one c
  have hcnn : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  nlinarith

theorem gmk12_wsv_dominant_ne_zero_of_nontrivial {x y z : ℚ_[2]}
    (hnt : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) (h1 : ‖x‖ ≤ ‖z‖) (h2 : ‖y‖ ≤ ‖z‖) :
    z ≠ 0 := by
  have _pin := Classical.em True
  intro h0
  rw [h0, norm_zero] at h1 h2
  rcases hnt with h | h | h
  · exact h (norm_le_zero_iff.mp h1)
  · exact h (norm_le_zero_iff.mp h2)
  · exact h h0

theorem gmk12_wsv_cert_cell_five_five :
    gmk8_cls_solvable (5 : ℚ_[2]) (5 : ℚ_[2]) := by
  have _pin := Classical.em True
  exact ⟨2, 1, 5, Or.inl (by norm_num), by norm_num⟩

theorem gmk12_wsv_cert_cell_two_seven :
    gmk8_cls_solvable (2 : ℚ_[2]) (7 : ℚ_[2]) := by
  have _pin := Classical.em True
  exact ⟨1, 1, 3, Or.inl one_ne_zero, by norm_num⟩

theorem gmk12_wsv_cert_cell_three_five :
    gmk8_cls_solvable (3 : ℚ_[2]) (5 : ℚ_[2]) := by
  have _pin := Classical.em True
  have h17 : (8 : ℤ_[2]) ∣ ((17 : ℤ_[2]) - 1) := ⟨2, by norm_num⟩
  obtain ⟨s, hs⟩ := gmk12_wsv_isSquare_of_one_mod_eight h17
  refine ⟨2, 1, (s : ℚ_[2]), Or.inl (by norm_num), ?_⟩
  rw [← PadicInt.coe_mul, ← hs,
    show (17 : ℤ_[2]) = ((17 : ℕ) : ℤ_[2]) from Nat.cast_ofNat.symm,
    PadicInt.coe_natCast]
  norm_num

theorem gmk12_wsv_cert_cell_five_seven :
    gmk8_cls_solvable (5 : ℚ_[2]) (7 : ℚ_[2]) := by
  have _pin := Classical.em True
  have h33 : (8 : ℤ_[2]) ∣ ((33 : ℤ_[2]) - 1) := ⟨4, by norm_num⟩
  obtain ⟨s, hs⟩ := gmk12_wsv_isSquare_of_one_mod_eight h33
  refine ⟨1, 2, (s : ℚ_[2]), Or.inl one_ne_zero, ?_⟩
  rw [← PadicInt.coe_mul, ← hs,
    show (33 : ℤ_[2]) = ((33 : ℕ) : ℤ_[2]) from Nat.cast_ofNat.symm,
    PadicInt.coe_natCast]
  norm_num

end FLT.CampGenuineMk
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

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

theorem gmk13_jon_natCast_three : ((3 : ℕ) : ℚ_[2]) = (3 : ℚ_[2]) := by
  have _pin := Classical.em True
  norm_num

theorem gmk13_jon_natCast_seven : ((7 : ℕ) : ℚ_[2]) = (7 : ℚ_[2]) := by
  have _pin := Classical.em True
  norm_num

theorem gmk13_jon_three_ne_zero : (3 : ℚ_[2]) ≠ 0 := by
  have _pin := Classical.em True
  rw [← gmk13_jon_natCast_three]
  exact gmk7_cls_natCast_ne_zero (show ((3 : ℕ) : ZMod 2) ≠ 0 by decide +kernel)

theorem gmk13_jon_seven_ne_zero : (7 : ℚ_[2]) ≠ 0 := by
  have _pin := Classical.em True
  rw [← gmk13_jon_natCast_seven]
  exact gmk7_cls_natCast_ne_zero (show ((7 : ℕ) : ZMod 2) ≠ 0 by decide +kernel)

theorem gmk13_jon_cert_classOf_three :
    gmk12_wcl_classOf gmk13_jon_three_ne_zero = ((0 : ZMod 2), gmk12_wcl_u3) := by
  have _pin := Classical.em True
  have hn : ((3 : ℕ) : ZMod 2) ≠ 0 := by decide +kernel
  rw [← gmk12_wcl_classOf_congr (gmk7_cls_natCast_ne_zero hn) gmk13_jon_three_ne_zero
      gmk13_jon_natCast_three]
  have h2 : gmk12_wcl_unitResidue (gmk7_cls_natCast_ne_zero hn) = gmk12_wcl_u3 := by
    refine Units.ext ?_
    rw [gmk12_wcl_unitResidue_natCast hn]
    decide +kernel
  show ((((3 : ℕ) : ℚ_[2]).valuation : ZMod 2),
      gmk12_wcl_unitResidue (gmk7_cls_natCast_ne_zero hn))
      = ((0 : ZMod 2), gmk12_wcl_u3)
  rw [gmk7_cls_valuation_natCast_eq_zero hn, Int.cast_zero, h2]

theorem gmk13_jon_cert_classOf_seven :
    gmk12_wcl_classOf gmk13_jon_seven_ne_zero = ((0 : ZMod 2), gmk12_wcl_u7) := by
  have _pin := Classical.em True
  have hn : ((7 : ℕ) : ZMod 2) ≠ 0 := by decide +kernel
  rw [← gmk12_wcl_classOf_congr (gmk7_cls_natCast_ne_zero hn) gmk13_jon_seven_ne_zero
      gmk13_jon_natCast_seven]
  have h2 : gmk12_wcl_unitResidue (gmk7_cls_natCast_ne_zero hn) = gmk12_wcl_u7 := by
    refine Units.ext ?_
    rw [gmk12_wcl_unitResidue_natCast hn]
    decide +kernel
  show ((((7 : ℕ) : ℚ_[2]).valuation : ZMod 2),
      gmk12_wcl_unitResidue (gmk7_cls_natCast_ne_zero hn))
      = ((0 : ZMod 2), gmk12_wcl_u7)
  rw [gmk7_cls_valuation_natCast_eq_zero hn, Int.cast_zero, h2]

theorem gmk13_jon_div_norm_le {a d : ℚ_[2]} (hd : d ≠ 0) (h : ‖a‖ ≤ ‖d‖) :
    ‖a / d‖ ≤ 1 := by
  have _pin := Classical.em True
  rw [norm_div]
  exact (div_le_one (norm_pos_iff.mpr hd)).mpr h

theorem gmk13_jon_div_sq_eq {Aq Bq x y z d : ℚ_[2]}
    (heq : z * z = Aq * (x * x) + Bq * (y * y)) :
    z / d * (z / d) = Aq * (x / d * (x / d)) + Bq * (y / d * (y / d)) := by
  have _pin := Classical.em True
  rw [div_mul_div_comm, div_mul_div_comm, div_mul_div_comm, heq]
  ring

theorem gmk13_jon_int_obstruction {A B : ℤ_[2]} {α β : ZMod (2 ^ 3)}
    (hA : PadicInt.toZModPow 3 A = α) (hB : PadicInt.toZModPow 3 B = β)
    (hfin : ∀ a b c : ZMod (2 ^ 3), (a = 1 ∨ b = 1 ∨ c = 1) →
      c * c ≠ α * (a * a) + β * (b * b))
    (X Y Z : ℤ_[2]) (hone : X = 1 ∨ Y = 1 ∨ Z = 1)
    (heq : Z * Z = A * (X * X) + B * (Y * Y)) : False := by
  have _pin := Classical.em True
  have hmod := congrArg (PadicInt.toZModPow 3) heq
  simp only [map_add, map_mul, hA, hB] at hmod
  rcases hone with h1 | h1 | h1
  · exact hfin _ _ _ (Or.inl (by rw [h1, map_one])) hmod
  · exact hfin _ _ _ (Or.inr (Or.inl (by rw [h1, map_one]))) hmod
  · exact hfin _ _ _ (Or.inr (Or.inr (by rw [h1, map_one]))) hmod

theorem gmk13_jon_unit_ball_obstruction {A B : ℤ_[2]} {α β : ZMod (2 ^ 3)}
    (hA : PadicInt.toZModPow 3 A = α) (hB : PadicInt.toZModPow 3 B = β)
    (hfin : ∀ a b c : ZMod (2 ^ 3), (a = 1 ∨ b = 1 ∨ c = 1) →
      c * c ≠ α * (a * a) + β * (b * b))
    {xq yq zq : ℚ_[2]} (hx : ‖xq‖ ≤ 1) (hy : ‖yq‖ ≤ 1) (hz : ‖zq‖ ≤ 1)
    (hone : xq = 1 ∨ yq = 1 ∨ zq = 1) :
    zq * zq ≠ (A : ℚ_[2]) * (xq * xq) + (B : ℚ_[2]) * (yq * yq) := by
  have _pin := Classical.em True
  intro heq
  refine gmk13_jon_int_obstruction hA hB hfin ⟨xq, hx⟩ ⟨yq, hy⟩ ⟨zq, hz⟩ ?_ ?_
  · rcases hone with h1 | h1 | h1
    · refine Or.inl (PadicInt.ext ?_)
      show xq = ((1 : ℤ_[2]) : ℚ_[2])
      rw [h1, PadicInt.coe_one]
    · refine Or.inr (Or.inl (PadicInt.ext ?_))
      show yq = ((1 : ℤ_[2]) : ℚ_[2])
      rw [h1, PadicInt.coe_one]
    · refine Or.inr (Or.inr (PadicInt.ext ?_))
      show zq = ((1 : ℤ_[2]) : ℚ_[2])
      rw [h1, PadicInt.coe_one]
  · exact PadicInt.ext heq

theorem gmk13_jon_not_solvable_of_mod8_cert {A B : ℤ_[2]} {α β : ZMod (2 ^ 3)}
    (hA : PadicInt.toZModPow 3 A = α) (hB : PadicInt.toZModPow 3 B = β)
    (hfin : ∀ a b c : ZMod (2 ^ 3), (a = 1 ∨ b = 1 ∨ c = 1) →
      c * c ≠ α * (a * a) + β * (b * b)) :
    ¬gmk8_cls_solvable ((A : ℚ_[2])) ((B : ℚ_[2])) := by
  have _pin := Classical.em True
  rintro ⟨x, y, z, hnt, heq⟩
  rcases le_total ‖x‖ ‖y‖ with h1 | h1
  · rcases le_total ‖y‖ ‖z‖ with h2 | h2
    · have hz0 : z ≠ 0 :=
        gmk12_wsv_dominant_ne_zero_of_nontrivial hnt (h1.trans h2) h2
      exact gmk13_jon_unit_ball_obstruction hA hB hfin
        (gmk13_jon_div_norm_le hz0 (h1.trans h2)) (gmk13_jon_div_norm_le hz0 h2)
        (gmk13_jon_div_norm_le hz0 le_rfl)
        (Or.inr (Or.inr (div_self hz0))) (gmk13_jon_div_sq_eq heq)
    · have hnt' : x ≠ 0 ∨ z ≠ 0 ∨ y ≠ 0 := by tauto
      have hy0 : y ≠ 0 := gmk12_wsv_dominant_ne_zero_of_nontrivial hnt' h1 h2
      exact gmk13_jon_unit_ball_obstruction hA hB hfin
        (gmk13_jon_div_norm_le hy0 h1) (gmk13_jon_div_norm_le hy0 le_rfl)
        (gmk13_jon_div_norm_le hy0 h2)
        (Or.inr (Or.inl (div_self hy0))) (gmk13_jon_div_sq_eq heq)
  · rcases le_total ‖x‖ ‖z‖ with h2 | h2
    · have hz0 : z ≠ 0 :=
        gmk12_wsv_dominant_ne_zero_of_nontrivial hnt h2 (h1.trans h2)
      exact gmk13_jon_unit_ball_obstruction hA hB hfin
        (gmk13_jon_div_norm_le hz0 h2) (gmk13_jon_div_norm_le hz0 (h1.trans h2))
        (gmk13_jon_div_norm_le hz0 le_rfl)
        (Or.inr (Or.inr (div_self hz0))) (gmk13_jon_div_sq_eq heq)
    · have hnt' : y ≠ 0 ∨ z ≠ 0 ∨ x ≠ 0 := by tauto
      have hx0 : x ≠ 0 := gmk12_wsv_dominant_ne_zero_of_nontrivial hnt' h1 h2
      exact gmk13_jon_unit_ball_obstruction hA hB hfin
        (gmk13_jon_div_norm_le hx0 le_rfl) (gmk13_jon_div_norm_le hx0 h1)
        (gmk13_jon_div_norm_le hx0 h2)
        (Or.inl (div_self hx0)) (gmk13_jon_div_sq_eq heq)

theorem gmk13_jon_coe_three : (((3 : ℤ_[2])) : ℚ_[2]) = (3 : ℚ_[2]) := by
  have _pin := Classical.em True
  rw [show (3 : ℤ_[2]) = ((3 : ℕ) : ℤ_[2]) from Nat.cast_ofNat.symm,
    PadicInt.coe_natCast]
  exact Nat.cast_ofNat

theorem gmk13_jon_coe_seven : (((7 : ℤ_[2])) : ℚ_[2]) = (7 : ℚ_[2]) := by
  have _pin := Classical.em True
  rw [show (7 : ℤ_[2]) = ((7 : ℕ) : ℤ_[2]) from Nat.cast_ofNat.symm,
    PadicInt.coe_natCast]
  exact Nat.cast_ofNat

theorem gmk13_jon_toZModPow_three_three :
    PadicInt.toZModPow 3 (3 : ℤ_[2]) = (3 : ZMod (2 ^ 3)) := by
  have _pin := Classical.em True
  rw [show (3 : ℤ_[2]) = ((3 : ℕ) : ℤ_[2]) from Nat.cast_ofNat.symm, map_natCast]
  exact Nat.cast_ofNat

theorem gmk13_jon_toZModPow_three_seven :
    PadicInt.toZModPow 3 (7 : ℤ_[2]) = (7 : ZMod (2 ^ 3)) := by
  have _pin := Classical.em True
  rw [show (7 : ℤ_[2]) = ((7 : ℕ) : ℤ_[2]) from Nat.cast_ofNat.symm, map_natCast]
  exact Nat.cast_ofNat

theorem gmk13_jon_mod8_cert_three_three :
    ∀ a b c : ZMod (2 ^ 3), (a = 1 ∨ b = 1 ∨ c = 1) →
      c * c ≠ (3 : ZMod (2 ^ 3)) * (a * a) + (3 : ZMod (2 ^ 3)) * (b * b) := by
  have _pin := Classical.em True
  decide +kernel

theorem gmk13_jon_mod8_cert_three_seven :
    ∀ a b c : ZMod (2 ^ 3), (a = 1 ∨ b = 1 ∨ c = 1) →
      c * c ≠ (3 : ZMod (2 ^ 3)) * (a * a) + (7 : ZMod (2 ^ 3)) * (b * b) := by
  have _pin := Classical.em True
  decide +kernel

theorem gmk13_jon_mod8_cert_seven_seven :
    ∀ a b c : ZMod (2 ^ 3), (a = 1 ∨ b = 1 ∨ c = 1) →
      c * c ≠ (7 : ZMod (2 ^ 3)) * (a * a) + (7 : ZMod (2 ^ 3)) * (b * b) := by
  have _pin := Classical.em True
  decide +kernel

theorem gmk13_jon_cert_cell_one_left (v : ℚ_[2]) :
    gmk8_cls_solvable (1 : ℚ_[2]) v := by
  have _pin := Classical.em True
  exact ⟨1, 0, 1, Or.inl one_ne_zero, by norm_num⟩

theorem gmk13_jon_cert_cell_one_right (u : ℚ_[2]) :
    gmk8_cls_solvable u (1 : ℚ_[2]) := by
  have _pin := Classical.em True
  exact ⟨0, 1, 1, Or.inr (Or.inl one_ne_zero), by norm_num⟩

theorem gmk13_jon_cert_cell_five_three :
    gmk8_cls_solvable (5 : ℚ_[2]) (3 : ℚ_[2]) := by
  have _pin := Classical.em True
  exact gmk8_cls_solvable_swap gmk12_wsv_cert_cell_three_five

theorem gmk13_jon_cert_cell_seven_five :
    gmk8_cls_solvable (7 : ℚ_[2]) (5 : ℚ_[2]) := by
  have _pin := Classical.em True
  exact gmk8_cls_solvable_swap gmk12_wsv_cert_cell_five_seven

theorem gmk13_jon_cert_cell_three_three_not_solvable :
    ¬gmk8_cls_solvable (3 : ℚ_[2]) (3 : ℚ_[2]) := by
  have _pin := Classical.em True
  have h := gmk13_jon_not_solvable_of_mod8_cert gmk13_jon_toZModPow_three_three
    gmk13_jon_toZModPow_three_three gmk13_jon_mod8_cert_three_three
  rwa [gmk13_jon_coe_three] at h

theorem gmk13_jon_cert_cell_three_seven_not_solvable :
    ¬gmk8_cls_solvable (3 : ℚ_[2]) (7 : ℚ_[2]) := by
  have _pin := Classical.em True
  have h := gmk13_jon_not_solvable_of_mod8_cert gmk13_jon_toZModPow_three_three
    gmk13_jon_toZModPow_three_seven gmk13_jon_mod8_cert_three_seven
  rwa [gmk13_jon_coe_three, gmk13_jon_coe_seven] at h

theorem gmk13_jon_cert_cell_seven_three_not_solvable :
    ¬gmk8_cls_solvable (7 : ℚ_[2]) (3 : ℚ_[2]) := by
  have _pin := Classical.em True
  exact fun h =>
    gmk13_jon_cert_cell_three_seven_not_solvable (gmk8_cls_solvable_swap h)

theorem gmk13_jon_cert_cell_seven_seven_not_solvable :
    ¬gmk8_cls_solvable (7 : ℚ_[2]) (7 : ℚ_[2]) := by
  have _pin := Classical.em True
  have h := gmk13_jon_not_solvable_of_mod8_cert gmk13_jon_toZModPow_three_seven
    gmk13_jon_toZModPow_three_seven gmk13_jon_mod8_cert_seven_seven
  rwa [gmk13_jon_coe_seven] at h

theorem gmk13_jon_pin_wildPair_iff_solvable {x y : ℚ_[2]}
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hxv : (gmk12_wcl_classOf hx).1 = 0) (hyv : (gmk12_wcl_classOf hy).1 = 0) :
    gmk11_rec_wildPair (gmk12_wcl_classOf hx) (gmk12_wcl_classOf hy) = 1
      ↔ gmk8_cls_solvable x y := by
  have _pin := Classical.em True
  have hcx : gmk12_wcl_classOf hx = ((0 : ZMod 2), (gmk12_wcl_classOf hx).2) := by
    rw [← hxv]
  have hcy : gmk12_wcl_classOf hy = ((0 : ZMod 2), (gmk12_wcl_classOf hy).2) := by
    rw [← hyv]
  rcases gmk12_wcl_units_cases (gmk12_wcl_classOf hx).2 with hu | hu | hu | hu <;>
      rcases gmk12_wcl_units_cases (gmk12_wcl_classOf hy).2 with hv | hv | hv | hv <;>
      rw [hu] at hcx <;> rw [hv] at hcy <;> rw [hcx, hcy]

  · exact iff_of_true (by decide +kernel)
      ((gmk13_jon_solvable_congr gmk12_wcl_one_ne_zero hx gmk12_wcl_one_ne_zero hy
        (gmk12_wcl_cert_classOf_one.trans hcx.symm)
        (gmk12_wcl_cert_classOf_one.trans hcy.symm)).mp
        (gmk13_jon_cert_cell_one_left 1))
  · exact iff_of_true (by decide +kernel)
      ((gmk13_jon_solvable_congr gmk12_wcl_one_ne_zero hx gmk13_jon_three_ne_zero hy
        (gmk12_wcl_cert_classOf_one.trans hcx.symm)
        (gmk13_jon_cert_classOf_three.trans hcy.symm)).mp
        (gmk13_jon_cert_cell_one_left 3))
  · exact iff_of_true (by decide +kernel)
      ((gmk13_jon_solvable_congr gmk12_wcl_one_ne_zero hx gmk12_wcl_five_ne_zero hy
        (gmk12_wcl_cert_classOf_one.trans hcx.symm)
        (gmk12_wcl_cert_classOf_five.trans hcy.symm)).mp
        (gmk13_jon_cert_cell_one_left 5))
  · exact iff_of_true (by decide +kernel)
      ((gmk13_jon_solvable_congr gmk12_wcl_one_ne_zero hx gmk13_jon_seven_ne_zero hy
        (gmk12_wcl_cert_classOf_one.trans hcx.symm)
        (gmk13_jon_cert_classOf_seven.trans hcy.symm)).mp
        (gmk13_jon_cert_cell_one_left 7))

  · exact iff_of_true (by decide +kernel)
      ((gmk13_jon_solvable_congr gmk13_jon_three_ne_zero hx gmk12_wcl_one_ne_zero hy
        (gmk13_jon_cert_classOf_three.trans hcx.symm)
        (gmk12_wcl_cert_classOf_one.trans hcy.symm)).mp
        (gmk13_jon_cert_cell_one_right 3))
  · exact iff_of_false (by decide +kernel)
      (fun hsv => gmk13_jon_cert_cell_three_three_not_solvable
        ((gmk13_jon_solvable_congr gmk13_jon_three_ne_zero hx gmk13_jon_three_ne_zero hy
          (gmk13_jon_cert_classOf_three.trans hcx.symm)
          (gmk13_jon_cert_classOf_three.trans hcy.symm)).mpr hsv))
  · exact iff_of_true (by decide +kernel)
      ((gmk13_jon_solvable_congr gmk13_jon_three_ne_zero hx gmk12_wcl_five_ne_zero hy
        (gmk13_jon_cert_classOf_three.trans hcx.symm)
        (gmk12_wcl_cert_classOf_five.trans hcy.symm)).mp
        gmk12_wsv_cert_cell_three_five)
  · exact iff_of_false (by decide +kernel)
      (fun hsv => gmk13_jon_cert_cell_three_seven_not_solvable
        ((gmk13_jon_solvable_congr gmk13_jon_three_ne_zero hx gmk13_jon_seven_ne_zero hy
          (gmk13_jon_cert_classOf_three.trans hcx.symm)
          (gmk13_jon_cert_classOf_seven.trans hcy.symm)).mpr hsv))

  · exact iff_of_true (by decide +kernel)
      ((gmk13_jon_solvable_congr gmk12_wcl_five_ne_zero hx gmk12_wcl_one_ne_zero hy
        (gmk12_wcl_cert_classOf_five.trans hcx.symm)
        (gmk12_wcl_cert_classOf_one.trans hcy.symm)).mp
        (gmk13_jon_cert_cell_one_right 5))
  · exact iff_of_true (by decide +kernel)
      ((gmk13_jon_solvable_congr gmk12_wcl_five_ne_zero hx gmk13_jon_three_ne_zero hy
        (gmk12_wcl_cert_classOf_five.trans hcx.symm)
        (gmk13_jon_cert_classOf_three.trans hcy.symm)).mp
        gmk13_jon_cert_cell_five_three)
  · exact iff_of_true (by decide +kernel)
      ((gmk13_jon_solvable_congr gmk12_wcl_five_ne_zero hx gmk12_wcl_five_ne_zero hy
        (gmk12_wcl_cert_classOf_five.trans hcx.symm)
        (gmk12_wcl_cert_classOf_five.trans hcy.symm)).mp
        gmk12_wsv_cert_cell_five_five)
  · exact iff_of_true (by decide +kernel)
      ((gmk13_jon_solvable_congr gmk12_wcl_five_ne_zero hx gmk13_jon_seven_ne_zero hy
        (gmk12_wcl_cert_classOf_five.trans hcx.symm)
        (gmk13_jon_cert_classOf_seven.trans hcy.symm)).mp
        gmk12_wsv_cert_cell_five_seven)

  · exact iff_of_true (by decide +kernel)
      ((gmk13_jon_solvable_congr gmk13_jon_seven_ne_zero hx gmk12_wcl_one_ne_zero hy
        (gmk13_jon_cert_classOf_seven.trans hcx.symm)
        (gmk12_wcl_cert_classOf_one.trans hcy.symm)).mp
        (gmk13_jon_cert_cell_one_right 7))
  · exact iff_of_false (by decide +kernel)
      (fun hsv => gmk13_jon_cert_cell_seven_three_not_solvable
        ((gmk13_jon_solvable_congr gmk13_jon_seven_ne_zero hx gmk13_jon_three_ne_zero hy
          (gmk13_jon_cert_classOf_seven.trans hcx.symm)
          (gmk13_jon_cert_classOf_three.trans hcy.symm)).mpr hsv))
  · exact iff_of_true (by decide +kernel)
      ((gmk13_jon_solvable_congr gmk13_jon_seven_ne_zero hx gmk12_wcl_five_ne_zero hy
        (gmk13_jon_cert_classOf_seven.trans hcx.symm)
        (gmk12_wcl_cert_classOf_five.trans hcy.symm)).mp
        gmk13_jon_cert_cell_seven_five)
  · exact iff_of_false (by decide +kernel)
      (fun hsv => gmk13_jon_cert_cell_seven_seven_not_solvable
        ((gmk13_jon_solvable_congr gmk13_jon_seven_ne_zero hx gmk13_jon_seven_ne_zero hy
          (gmk13_jon_cert_classOf_seven.trans hcx.symm)
          (gmk13_jon_cert_classOf_seven.trans hcy.symm)).mpr hsv))

end FLT.CampGenuineMk
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

section
section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

namespace FLT
namespace CampGenuineMk

theorem gmk14_uni_int_obstruction {n : ℕ} {A B : ℤ_[2]} {α β : ZMod (2 ^ n)}
    (hA : PadicInt.toZModPow n A = α) (hB : PadicInt.toZModPow n B = β)
    (hfin : ∀ a b c : ZMod (2 ^ n), (a = 1 ∨ b = 1 ∨ c = 1) →
      c * c ≠ α * (a * a) + β * (b * b))
    (X Y Z : ℤ_[2]) (hone : X = 1 ∨ Y = 1 ∨ Z = 1)
    (heq : Z * Z = A * (X * X) + B * (Y * Y)) : False := by
  have _pin := Classical.em True
  have hmod := congrArg (PadicInt.toZModPow n) heq
  simp only [map_add, map_mul, hA, hB] at hmod
  rcases hone with h1 | h1 | h1
  · exact hfin _ _ _ (Or.inl (by rw [h1, map_one])) hmod
  · exact hfin _ _ _ (Or.inr (Or.inl (by rw [h1, map_one]))) hmod
  · exact hfin _ _ _ (Or.inr (Or.inr (by rw [h1, map_one]))) hmod

theorem gmk14_uni_unit_ball_obstruction {n : ℕ} {A B : ℤ_[2]} {α β : ZMod (2 ^ n)}
    (hA : PadicInt.toZModPow n A = α) (hB : PadicInt.toZModPow n B = β)
    (hfin : ∀ a b c : ZMod (2 ^ n), (a = 1 ∨ b = 1 ∨ c = 1) →
      c * c ≠ α * (a * a) + β * (b * b))
    {xq yq zq : ℚ_[2]} (hx : ‖xq‖ ≤ 1) (hy : ‖yq‖ ≤ 1) (hz : ‖zq‖ ≤ 1)
    (hone : xq = 1 ∨ yq = 1 ∨ zq = 1) :
    zq * zq ≠ (A : ℚ_[2]) * (xq * xq) + (B : ℚ_[2]) * (yq * yq) := by
  have _pin := Classical.em True
  intro heq
  refine gmk14_uni_int_obstruction hA hB hfin ⟨xq, hx⟩ ⟨yq, hy⟩ ⟨zq, hz⟩ ?_ ?_
  · rcases hone with h1 | h1 | h1
    · refine Or.inl (PadicInt.ext ?_)
      show xq = ((1 : ℤ_[2]) : ℚ_[2])
      rw [h1, PadicInt.coe_one]
    · refine Or.inr (Or.inl (PadicInt.ext ?_))
      show yq = ((1 : ℤ_[2]) : ℚ_[2])
      rw [h1, PadicInt.coe_one]
    · refine Or.inr (Or.inr (PadicInt.ext ?_))
      show zq = ((1 : ℤ_[2]) : ℚ_[2])
      rw [h1, PadicInt.coe_one]
  · exact PadicInt.ext heq

theorem gmk14_uni_not_solvable_of_modpow_cert {n : ℕ} {A B : ℤ_[2]}
    {α β : ZMod (2 ^ n)}
    (hA : PadicInt.toZModPow n A = α) (hB : PadicInt.toZModPow n B = β)
    (hfin : ∀ a b c : ZMod (2 ^ n), (a = 1 ∨ b = 1 ∨ c = 1) →
      c * c ≠ α * (a * a) + β * (b * b)) :
    ¬gmk8_cls_solvable ((A : ℚ_[2])) ((B : ℚ_[2])) := by
  have _pin := Classical.em True
  rintro ⟨x, y, z, hnt, heq⟩
  rcases le_total ‖x‖ ‖y‖ with h1 | h1
  · rcases le_total ‖y‖ ‖z‖ with h2 | h2
    · have hz0 : z ≠ 0 :=
        gmk12_wsv_dominant_ne_zero_of_nontrivial hnt (h1.trans h2) h2
      exact gmk14_uni_unit_ball_obstruction hA hB hfin
        (gmk13_jon_div_norm_le hz0 (h1.trans h2)) (gmk13_jon_div_norm_le hz0 h2)
        (gmk13_jon_div_norm_le hz0 le_rfl)
        (Or.inr (Or.inr (div_self hz0))) (gmk13_jon_div_sq_eq heq)
    · have hnt' : x ≠ 0 ∨ z ≠ 0 ∨ y ≠ 0 := by tauto
      have hy0 : y ≠ 0 := gmk12_wsv_dominant_ne_zero_of_nontrivial hnt' h1 h2
      exact gmk14_uni_unit_ball_obstruction hA hB hfin
        (gmk13_jon_div_norm_le hy0 h1) (gmk13_jon_div_norm_le hy0 le_rfl)
        (gmk13_jon_div_norm_le hy0 h2)
        (Or.inr (Or.inl (div_self hy0))) (gmk13_jon_div_sq_eq heq)
  · rcases le_total ‖x‖ ‖z‖ with h2 | h2
    · have hz0 : z ≠ 0 :=
        gmk12_wsv_dominant_ne_zero_of_nontrivial hnt h2 (h1.trans h2)
      exact gmk14_uni_unit_ball_obstruction hA hB hfin
        (gmk13_jon_div_norm_le hz0 h2) (gmk13_jon_div_norm_le hz0 (h1.trans h2))
        (gmk13_jon_div_norm_le hz0 le_rfl)
        (Or.inr (Or.inr (div_self hz0))) (gmk13_jon_div_sq_eq heq)
    · have hnt' : y ≠ 0 ∨ z ≠ 0 ∨ x ≠ 0 := by tauto
      have hx0 : x ≠ 0 := gmk12_wsv_dominant_ne_zero_of_nontrivial hnt' h1 h2
      exact gmk14_uni_unit_ball_obstruction hA hB hfin
        (gmk13_jon_div_norm_le hx0 le_rfl) (gmk13_jon_div_norm_le hx0 h1)
        (gmk13_jon_div_norm_le hx0 h2)
        (Or.inl (div_self hx0)) (gmk13_jon_div_sq_eq heq)

theorem gmk14_uni_coe_two : (((2 : ℤ_[2])) : ℚ_[2]) = (2 : ℚ_[2]) := by
  have _pin := Classical.em True
  rw [show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) from Nat.cast_ofNat.symm,
    PadicInt.coe_natCast]
  exact Nat.cast_ofNat

theorem gmk14_uni_coe_five : (((5 : ℤ_[2])) : ℚ_[2]) = (5 : ℚ_[2]) := by
  have _pin := Classical.em True
  rw [show (5 : ℤ_[2]) = ((5 : ℕ) : ℤ_[2]) from Nat.cast_ofNat.symm,
    PadicInt.coe_natCast]
  exact Nat.cast_ofNat

theorem gmk14_uni_coe_ten : (((10 : ℤ_[2])) : ℚ_[2]) = (10 : ℚ_[2]) := by
  have _pin := Classical.em True
  rw [show (10 : ℤ_[2]) = ((10 : ℕ) : ℤ_[2]) from Nat.cast_ofNat.symm,
    PadicInt.coe_natCast]
  exact Nat.cast_ofNat

theorem gmk14_uni_coe_negTen : (((-10 : ℤ_[2])) : ℚ_[2]) = (-10 : ℚ_[2]) := by
  have _pin := Classical.em True
  rw [PadicInt.coe_neg, gmk14_uni_coe_ten]

theorem gmk14_uni_coe_negTwo : (((-2 : ℤ_[2])) : ℚ_[2]) = (-2 : ℚ_[2]) := by
  have _pin := Classical.em True
  rw [PadicInt.coe_neg, gmk14_uni_coe_two]

theorem gmk14_uni_toZModPow_four_two :
    PadicInt.toZModPow 4 (2 : ℤ_[2]) = (2 : ZMod (2 ^ 4)) := by
  have _pin := Classical.em True
  rw [show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) from Nat.cast_ofNat.symm, map_natCast]
  exact Nat.cast_ofNat

theorem gmk14_uni_toZModPow_four_three :
    PadicInt.toZModPow 4 (3 : ℤ_[2]) = (3 : ZMod (2 ^ 4)) := by
  have _pin := Classical.em True
  rw [show (3 : ℤ_[2]) = ((3 : ℕ) : ℤ_[2]) from Nat.cast_ofNat.symm, map_natCast]
  exact Nat.cast_ofNat

theorem gmk14_uni_toZModPow_four_five :
    PadicInt.toZModPow 4 (5 : ℤ_[2]) = (5 : ZMod (2 ^ 4)) := by
  have _pin := Classical.em True
  rw [show (5 : ℤ_[2]) = ((5 : ℕ) : ℤ_[2]) from Nat.cast_ofNat.symm, map_natCast]
  exact Nat.cast_ofNat

theorem gmk14_uni_toZModPow_four_seven :
    PadicInt.toZModPow 4 (7 : ℤ_[2]) = (7 : ZMod (2 ^ 4)) := by
  have _pin := Classical.em True
  rw [show (7 : ℤ_[2]) = ((7 : ℕ) : ℤ_[2]) from Nat.cast_ofNat.symm, map_natCast]
  exact Nat.cast_ofNat

theorem gmk14_uni_toZModPow_four_ten :
    PadicInt.toZModPow 4 (10 : ℤ_[2]) = (10 : ZMod (2 ^ 4)) := by
  have _pin := Classical.em True
  rw [show (10 : ℤ_[2]) = ((10 : ℕ) : ℤ_[2]) from Nat.cast_ofNat.symm, map_natCast]
  exact Nat.cast_ofNat

theorem gmk14_uni_toZModPow_four_negTen :
    PadicInt.toZModPow 4 (-10 : ℤ_[2]) = (6 : ZMod (2 ^ 4)) := by
  have _pin := Classical.em True
  rw [_root_.map_neg, gmk14_uni_toZModPow_four_ten]
  decide +kernel

theorem gmk14_uni_toZModPow_four_negTwo :
    PadicInt.toZModPow 4 (-2 : ℤ_[2]) = (14 : ZMod (2 ^ 4)) := by
  have _pin := Classical.em True
  rw [_root_.map_neg, gmk14_uni_toZModPow_four_two]
  decide +kernel

theorem gmk14_uni_cert_cell_three_two_not_solvable :
    ¬gmk8_cls_solvable (3 : ℚ_[2]) (2 : ℚ_[2]) := by
  have _pin := Classical.em True
  have h := gmk14_uni_not_solvable_of_modpow_cert
    gmk14_uni_toZModPow_four_three gmk14_uni_toZModPow_four_two
    (by decide +kernel)
  rwa [gmk13_jon_coe_three, gmk14_uni_coe_two] at h

theorem gmk14_uni_cert_cell_three_ten_not_solvable :
    ¬gmk8_cls_solvable (3 : ℚ_[2]) (10 : ℚ_[2]) := by
  have _pin := Classical.em True
  have h := gmk14_uni_not_solvable_of_modpow_cert
    gmk14_uni_toZModPow_four_three gmk14_uni_toZModPow_four_ten
    (by decide +kernel)
  rwa [gmk13_jon_coe_three, gmk14_uni_coe_ten] at h

theorem gmk14_uni_cert_cell_five_two_not_solvable :
    ¬gmk8_cls_solvable (5 : ℚ_[2]) (2 : ℚ_[2]) := by
  have _pin := Classical.em True
  have h := gmk14_uni_not_solvable_of_modpow_cert
    gmk14_uni_toZModPow_four_five gmk14_uni_toZModPow_four_two
    (by decide +kernel)
  rwa [gmk14_uni_coe_five, gmk14_uni_coe_two] at h

theorem gmk14_uni_cert_cell_five_negTen_not_solvable :
    ¬gmk8_cls_solvable (5 : ℚ_[2]) (-10 : ℚ_[2]) := by
  have _pin := Classical.em True
  have h := gmk14_uni_not_solvable_of_modpow_cert
    gmk14_uni_toZModPow_four_five gmk14_uni_toZModPow_four_negTen
    (by decide +kernel)
  rwa [gmk14_uni_coe_five, gmk14_uni_coe_negTen] at h

theorem gmk14_uni_cert_cell_five_ten_not_solvable :
    ¬gmk8_cls_solvable (5 : ℚ_[2]) (10 : ℚ_[2]) := by
  have _pin := Classical.em True
  have h := gmk14_uni_not_solvable_of_modpow_cert
    gmk14_uni_toZModPow_four_five gmk14_uni_toZModPow_four_ten
    (by decide +kernel)
  rwa [gmk14_uni_coe_five, gmk14_uni_coe_ten] at h

theorem gmk14_uni_cert_cell_five_negTwo_not_solvable :
    ¬gmk8_cls_solvable (5 : ℚ_[2]) (-2 : ℚ_[2]) := by
  have _pin := Classical.em True
  have h := gmk14_uni_not_solvable_of_modpow_cert
    gmk14_uni_toZModPow_four_five gmk14_uni_toZModPow_four_negTwo
    (by decide +kernel)
  rwa [gmk14_uni_coe_five, gmk14_uni_coe_negTwo] at h

theorem gmk14_uni_cert_cell_seven_negTen_not_solvable :
    ¬gmk8_cls_solvable (7 : ℚ_[2]) (-10 : ℚ_[2]) := by
  have _pin := Classical.em True
  have h := gmk14_uni_not_solvable_of_modpow_cert
    gmk14_uni_toZModPow_four_seven gmk14_uni_toZModPow_four_negTen
    (by decide +kernel)
  rwa [gmk13_jon_coe_seven, gmk14_uni_coe_negTen] at h

theorem gmk14_uni_cert_cell_seven_negTwo_not_solvable :
    ¬gmk8_cls_solvable (7 : ℚ_[2]) (-2 : ℚ_[2]) := by
  have _pin := Classical.em True
  have h := gmk14_uni_not_solvable_of_modpow_cert
    gmk14_uni_toZModPow_four_seven gmk14_uni_toZModPow_four_negTwo
    (by decide +kernel)
  rwa [gmk13_jon_coe_seven, gmk14_uni_coe_negTwo] at h

theorem gmk14_uni_cert_cell_two_negTen_not_solvable :
    ¬gmk8_cls_solvable (2 : ℚ_[2]) (-10 : ℚ_[2]) := by
  have _pin := Classical.em True
  have h := gmk14_uni_not_solvable_of_modpow_cert
    gmk14_uni_toZModPow_four_two gmk14_uni_toZModPow_four_negTen
    (by decide +kernel)
  rwa [gmk14_uni_coe_two, gmk14_uni_coe_negTen] at h

theorem gmk14_uni_cert_cell_two_ten_not_solvable :
    ¬gmk8_cls_solvable (2 : ℚ_[2]) (10 : ℚ_[2]) := by
  have _pin := Classical.em True
  have h := gmk14_uni_not_solvable_of_modpow_cert
    gmk14_uni_toZModPow_four_two gmk14_uni_toZModPow_four_ten
    (by decide +kernel)
  rwa [gmk14_uni_coe_two, gmk14_uni_coe_ten] at h

theorem gmk14_uni_cert_cell_negTen_negTen_not_solvable :
    ¬gmk8_cls_solvable (-10 : ℚ_[2]) (-10 : ℚ_[2]) := by
  have _pin := Classical.em True
  have h := gmk14_uni_not_solvable_of_modpow_cert
    gmk14_uni_toZModPow_four_negTen gmk14_uni_toZModPow_four_negTen
    (by decide +kernel)
  rwa [gmk14_uni_coe_negTen] at h

theorem gmk14_uni_cert_cell_ten_negTwo_not_solvable :
    ¬gmk8_cls_solvable (10 : ℚ_[2]) (-2 : ℚ_[2]) := by
  have _pin := Classical.em True
  have h := gmk14_uni_not_solvable_of_modpow_cert
    gmk14_uni_toZModPow_four_ten gmk14_uni_toZModPow_four_negTwo
    (by decide +kernel)
  rwa [gmk14_uni_coe_ten, gmk14_uni_coe_negTwo] at h

theorem gmk14_uni_cert_cell_negTwo_negTwo_not_solvable :
    ¬gmk8_cls_solvable (-2 : ℚ_[2]) (-2 : ℚ_[2]) := by
  have _pin := Classical.em True
  have h := gmk14_uni_not_solvable_of_modpow_cert
    gmk14_uni_toZModPow_four_negTwo gmk14_uni_toZModPow_four_negTwo
    (by decide +kernel)
  rwa [gmk14_uni_coe_negTwo] at h

theorem gmk14_uni_cert_cell_three_negTwo :
    gmk8_cls_solvable (3 : ℚ_[2]) (-2 : ℚ_[2]) := by
  have _pin := Classical.em True
  exact ⟨1, 1, 1, Or.inl one_ne_zero, by norm_num⟩

theorem gmk14_uni_cert_cell_seven_two :
    gmk8_cls_solvable (7 : ℚ_[2]) (2 : ℚ_[2]) := by
  have _pin := Classical.em True
  exact ⟨1, 1, 3, Or.inl one_ne_zero, by norm_num⟩

theorem gmk14_uni_cert_cell_two_two :
    gmk8_cls_solvable (2 : ℚ_[2]) (2 : ℚ_[2]) := by
  have _pin := Classical.em True
  exact ⟨1, 1, 2, Or.inl one_ne_zero, by norm_num⟩

theorem gmk14_uni_cert_cell_two_negTwo :
    gmk8_cls_solvable (2 : ℚ_[2]) (-2 : ℚ_[2]) := by
  have _pin := Classical.em True
  exact ⟨1, 1, 0, Or.inl one_ne_zero, by norm_num⟩

theorem gmk14_uni_cert_cell_negTen_ten :
    gmk8_cls_solvable (-10 : ℚ_[2]) (10 : ℚ_[2]) := by
  have _pin := Classical.em True
  exact ⟨1, 1, 0, Or.inl one_ne_zero, by norm_num⟩

theorem gmk14_uni_cert_cell_ten_negTen :
    gmk8_cls_solvable (10 : ℚ_[2]) (-10 : ℚ_[2]) := by
  have _pin := Classical.em True
  exact ⟨1, 1, 0, Or.inl one_ne_zero, by norm_num⟩

theorem gmk14_uni_cert_cell_ten_ten :
    gmk8_cls_solvable (10 : ℚ_[2]) (10 : ℚ_[2]) := by
  have _pin := Classical.em True
  exact ⟨1, 3, 10, Or.inl one_ne_zero, by norm_num⟩

theorem gmk14_uni_cert_cell_three_negTen :
    gmk8_cls_solvable (3 : ℚ_[2]) (-10 : ℚ_[2]) := by
  have _pin := Classical.em True
  have h7 : (8 : ℤ_[2]) ∣ ((-7 : ℤ_[2]) - 1) := ⟨-1, by norm_num⟩
  obtain ⟨s, hs⟩ := gmk12_wsv_isSquare_of_one_mod_eight h7
  refine ⟨1, 1, (s : ℚ_[2]), Or.inl one_ne_zero, ?_⟩
  rw [← PadicInt.coe_mul, ← hs, PadicInt.coe_neg, gmk13_jon_coe_seven]
  norm_num

theorem gmk14_uni_cert_cell_seven_ten :
    gmk8_cls_solvable (7 : ℚ_[2]) (10 : ℚ_[2]) := by
  have _pin := Classical.em True
  have h17 : (8 : ℤ_[2]) ∣ ((17 : ℤ_[2]) - 1) := ⟨2, by norm_num⟩
  obtain ⟨s, hs⟩ := gmk12_wsv_isSquare_of_one_mod_eight h17
  refine ⟨1, 1, (s : ℚ_[2]), Or.inl one_ne_zero, ?_⟩
  rw [← PadicInt.coe_mul, ← hs,
    show (17 : ℤ_[2]) = ((17 : ℕ) : ℤ_[2]) from Nat.cast_ofNat.symm,
    PadicInt.coe_natCast]
  norm_num

theorem gmk14_uni_cert_cell_negTen_negTwo :
    gmk8_cls_solvable (-10 : ℚ_[2]) (-2 : ℚ_[2]) := by
  have _pin := Classical.em True
  have h7 : (8 : ℤ_[2]) ∣ ((-7 : ℤ_[2]) - 1) := ⟨-1, by norm_num⟩
  obtain ⟨s, hs⟩ := gmk12_wsv_isSquare_of_one_mod_eight h7
  refine ⟨1, 3, 2 * (s : ℚ_[2]), Or.inl one_ne_zero, ?_⟩
  have hss : (s : ℚ_[2]) * (s : ℚ_[2]) = -7 := by
    rw [← PadicInt.coe_mul, ← hs, PadicInt.coe_neg, gmk13_jon_coe_seven]
  linear_combination 4 * hss

end FLT.CampGenuineMk
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

section
section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

namespace FLT
namespace CampGenuineMk

theorem gmk14_uni_cell_transport {x y r s : ℚ_[2]} {c d : ZMod 2 × (ZMod 8)ˣ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0)
    (hcr : gmk12_wcl_classOf hr = c) (hcs : gmk12_wcl_classOf hs = d)
    (hcx : gmk12_wcl_classOf hx = c) (hcy : gmk12_wcl_classOf hy = d)
    (hcell : gmk11_rec_wildPair c d = 1 ↔ gmk8_cls_solvable r s) :
    gmk11_rec_wildPair (gmk12_wcl_classOf hx) (gmk12_wcl_classOf hy) = 1
      ↔ gmk8_cls_solvable x y := by
  have _pin := Classical.em True
  rw [hcx, hcy, hcell]
  exact gmk13_jon_solvable_congr hr hx hs hy
    (hcr.trans hcx.symm) (hcs.trans hcy.symm)

theorem gmk14_uni_pin_wildPair_iff_solvable_full {x y : ℚ_[2]}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    gmk11_rec_wildPair (gmk12_wcl_classOf hx) (gmk12_wcl_classOf hy) = 1
      ↔ gmk8_cls_solvable x y := by
  have _pin := Classical.em True
  rcases gmk12_wcl_zmod2_cases (gmk12_wcl_classOf hx).1 with hxv | hxv
  · rcases gmk12_wcl_zmod2_cases (gmk12_wcl_classOf hy).1 with hyv | hyv

    · exact gmk13_jon_pin_wildPair_iff_solvable hx hy hxv hyv

    · have hcx : gmk12_wcl_classOf hx
          = ((0 : ZMod 2), (gmk12_wcl_classOf hx).2) := by
        rw [← hxv]
      have hcy : gmk12_wcl_classOf hy
          = ((1 : ZMod 2), (gmk12_wcl_classOf hy).2) := by
        rw [← hyv]
      rcases gmk12_wcl_units_cases (gmk12_wcl_classOf hx).2 with hu | hu | hu | hu <;>
          rcases gmk12_wcl_units_cases (gmk12_wcl_classOf hy).2 with hv | hv | hv | hv <;>
          rw [hu] at hcx <;> rw [hv] at hcy

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_one_ne_zero gmk12_wcl_two_ne_zero
          gmk12_wcl_cert_classOf_one gmk12_wcl_cert_classOf_two hcx hcy
          (iff_of_true (by decide +kernel)
          (gmk13_jon_cert_cell_one_left 2))

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_one_ne_zero gmk12_wcl_negTen_ne_zero
          gmk12_wcl_cert_classOf_one gmk12_wcl_cert_classOf_negTen hcx hcy
          (iff_of_true (by decide +kernel)
          (gmk13_jon_cert_cell_one_left (-10)))

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_one_ne_zero gmk12_wcl_ten_ne_zero
          gmk12_wcl_cert_classOf_one gmk12_wcl_cert_classOf_ten hcx hcy
          (iff_of_true (by decide +kernel)
          (gmk13_jon_cert_cell_one_left 10))

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_one_ne_zero gmk12_wcl_negTwo_ne_zero
          gmk12_wcl_cert_classOf_one gmk12_wcl_cert_classOf_negTwo hcx hcy
          (iff_of_true (by decide +kernel)
          (gmk13_jon_cert_cell_one_left (-2)))

      · exact gmk14_uni_cell_transport hx hy gmk13_jon_three_ne_zero gmk12_wcl_two_ne_zero
          gmk13_jon_cert_classOf_three gmk12_wcl_cert_classOf_two hcx hcy
          (iff_of_false (by decide +kernel)
          (gmk14_uni_cert_cell_three_two_not_solvable))

      · exact gmk14_uni_cell_transport hx hy gmk13_jon_three_ne_zero gmk12_wcl_negTen_ne_zero
          gmk13_jon_cert_classOf_three gmk12_wcl_cert_classOf_negTen hcx hcy
          (iff_of_true (by decide +kernel)
          (gmk14_uni_cert_cell_three_negTen))

      · exact gmk14_uni_cell_transport hx hy gmk13_jon_three_ne_zero gmk12_wcl_ten_ne_zero
          gmk13_jon_cert_classOf_three gmk12_wcl_cert_classOf_ten hcx hcy
          (iff_of_false (by decide +kernel)
          (gmk14_uni_cert_cell_three_ten_not_solvable))

      · exact gmk14_uni_cell_transport hx hy gmk13_jon_three_ne_zero gmk12_wcl_negTwo_ne_zero
          gmk13_jon_cert_classOf_three gmk12_wcl_cert_classOf_negTwo hcx hcy
          (iff_of_true (by decide +kernel)
          (gmk14_uni_cert_cell_three_negTwo))

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_five_ne_zero gmk12_wcl_two_ne_zero
          gmk12_wcl_cert_classOf_five gmk12_wcl_cert_classOf_two hcx hcy
          (iff_of_false (by decide +kernel)
          (gmk14_uni_cert_cell_five_two_not_solvable))

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_five_ne_zero gmk12_wcl_negTen_ne_zero
          gmk12_wcl_cert_classOf_five gmk12_wcl_cert_classOf_negTen hcx hcy
          (iff_of_false (by decide +kernel)
          (gmk14_uni_cert_cell_five_negTen_not_solvable))

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_five_ne_zero gmk12_wcl_ten_ne_zero
          gmk12_wcl_cert_classOf_five gmk12_wcl_cert_classOf_ten hcx hcy
          (iff_of_false (by decide +kernel)
          (gmk14_uni_cert_cell_five_ten_not_solvable))

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_five_ne_zero gmk12_wcl_negTwo_ne_zero
          gmk12_wcl_cert_classOf_five gmk12_wcl_cert_classOf_negTwo hcx hcy
          (iff_of_false (by decide +kernel)
          (gmk14_uni_cert_cell_five_negTwo_not_solvable))

      · exact gmk14_uni_cell_transport hx hy gmk13_jon_seven_ne_zero gmk12_wcl_two_ne_zero
          gmk13_jon_cert_classOf_seven gmk12_wcl_cert_classOf_two hcx hcy
          (iff_of_true (by decide +kernel)
          (gmk14_uni_cert_cell_seven_two))

      · exact gmk14_uni_cell_transport hx hy gmk13_jon_seven_ne_zero gmk12_wcl_negTen_ne_zero
          gmk13_jon_cert_classOf_seven gmk12_wcl_cert_classOf_negTen hcx hcy
          (iff_of_false (by decide +kernel)
          (gmk14_uni_cert_cell_seven_negTen_not_solvable))

      · exact gmk14_uni_cell_transport hx hy gmk13_jon_seven_ne_zero gmk12_wcl_ten_ne_zero
          gmk13_jon_cert_classOf_seven gmk12_wcl_cert_classOf_ten hcx hcy
          (iff_of_true (by decide +kernel)
          (gmk14_uni_cert_cell_seven_ten))

      · exact gmk14_uni_cell_transport hx hy gmk13_jon_seven_ne_zero gmk12_wcl_negTwo_ne_zero
          gmk13_jon_cert_classOf_seven gmk12_wcl_cert_classOf_negTwo hcx hcy
          (iff_of_false (by decide +kernel)
          (gmk14_uni_cert_cell_seven_negTwo_not_solvable))
  · rcases gmk12_wcl_zmod2_cases (gmk12_wcl_classOf hy).1 with hyv | hyv

    · have hcx : gmk12_wcl_classOf hx
          = ((1 : ZMod 2), (gmk12_wcl_classOf hx).2) := by
        rw [← hxv]
      have hcy : gmk12_wcl_classOf hy
          = ((0 : ZMod 2), (gmk12_wcl_classOf hy).2) := by
        rw [← hyv]
      rcases gmk12_wcl_units_cases (gmk12_wcl_classOf hx).2 with hu | hu | hu | hu <;>
          rcases gmk12_wcl_units_cases (gmk12_wcl_classOf hy).2 with hv | hv | hv | hv <;>
          rw [hu] at hcx <;> rw [hv] at hcy

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_two_ne_zero gmk12_wcl_one_ne_zero
          gmk12_wcl_cert_classOf_two gmk12_wcl_cert_classOf_one hcx hcy
          (iff_of_true (by decide +kernel)
          (gmk13_jon_cert_cell_one_right 2))

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_two_ne_zero gmk13_jon_three_ne_zero
          gmk12_wcl_cert_classOf_two gmk13_jon_cert_classOf_three hcx hcy
          (iff_of_false (by decide +kernel)
          (fun hsv => gmk14_uni_cert_cell_three_two_not_solvable
            (gmk8_cls_solvable_swap hsv)))

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_two_ne_zero gmk12_wcl_five_ne_zero
          gmk12_wcl_cert_classOf_two gmk12_wcl_cert_classOf_five hcx hcy
          (iff_of_false (by decide +kernel)
          (fun hsv => gmk14_uni_cert_cell_five_two_not_solvable
            (gmk8_cls_solvable_swap hsv)))

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_two_ne_zero gmk13_jon_seven_ne_zero
          gmk12_wcl_cert_classOf_two gmk13_jon_cert_classOf_seven hcx hcy
          (iff_of_true (by decide +kernel)
          (gmk12_wsv_cert_cell_two_seven))

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_negTen_ne_zero gmk12_wcl_one_ne_zero
          gmk12_wcl_cert_classOf_negTen gmk12_wcl_cert_classOf_one hcx hcy
          (iff_of_true (by decide +kernel)
          (gmk13_jon_cert_cell_one_right (-10)))

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_negTen_ne_zero gmk13_jon_three_ne_zero
          gmk12_wcl_cert_classOf_negTen gmk13_jon_cert_classOf_three hcx hcy
          (iff_of_true (by decide +kernel)
          (gmk8_cls_solvable_swap gmk14_uni_cert_cell_three_negTen))

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_negTen_ne_zero gmk12_wcl_five_ne_zero
          gmk12_wcl_cert_classOf_negTen gmk12_wcl_cert_classOf_five hcx hcy
          (iff_of_false (by decide +kernel)
          (fun hsv => gmk14_uni_cert_cell_five_negTen_not_solvable
            (gmk8_cls_solvable_swap hsv)))

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_negTen_ne_zero gmk13_jon_seven_ne_zero
          gmk12_wcl_cert_classOf_negTen gmk13_jon_cert_classOf_seven hcx hcy
          (iff_of_false (by decide +kernel)
          (fun hsv => gmk14_uni_cert_cell_seven_negTen_not_solvable
            (gmk8_cls_solvable_swap hsv)))

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_ten_ne_zero gmk12_wcl_one_ne_zero
          gmk12_wcl_cert_classOf_ten gmk12_wcl_cert_classOf_one hcx hcy
          (iff_of_true (by decide +kernel)
          (gmk13_jon_cert_cell_one_right 10))

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_ten_ne_zero gmk13_jon_three_ne_zero
          gmk12_wcl_cert_classOf_ten gmk13_jon_cert_classOf_three hcx hcy
          (iff_of_false (by decide +kernel)
          (fun hsv => gmk14_uni_cert_cell_three_ten_not_solvable
            (gmk8_cls_solvable_swap hsv)))

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_ten_ne_zero gmk12_wcl_five_ne_zero
          gmk12_wcl_cert_classOf_ten gmk12_wcl_cert_classOf_five hcx hcy
          (iff_of_false (by decide +kernel)
          (fun hsv => gmk14_uni_cert_cell_five_ten_not_solvable
            (gmk8_cls_solvable_swap hsv)))

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_ten_ne_zero gmk13_jon_seven_ne_zero
          gmk12_wcl_cert_classOf_ten gmk13_jon_cert_classOf_seven hcx hcy
          (iff_of_true (by decide +kernel)
          (gmk8_cls_solvable_swap gmk14_uni_cert_cell_seven_ten))

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_negTwo_ne_zero gmk12_wcl_one_ne_zero
          gmk12_wcl_cert_classOf_negTwo gmk12_wcl_cert_classOf_one hcx hcy
          (iff_of_true (by decide +kernel)
          (gmk13_jon_cert_cell_one_right (-2)))

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_negTwo_ne_zero gmk13_jon_three_ne_zero
          gmk12_wcl_cert_classOf_negTwo gmk13_jon_cert_classOf_three hcx hcy
          (iff_of_true (by decide +kernel)
          (gmk8_cls_solvable_swap gmk14_uni_cert_cell_three_negTwo))

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_negTwo_ne_zero gmk12_wcl_five_ne_zero
          gmk12_wcl_cert_classOf_negTwo gmk12_wcl_cert_classOf_five hcx hcy
          (iff_of_false (by decide +kernel)
          (fun hsv => gmk14_uni_cert_cell_five_negTwo_not_solvable
            (gmk8_cls_solvable_swap hsv)))

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_negTwo_ne_zero gmk13_jon_seven_ne_zero
          gmk12_wcl_cert_classOf_negTwo gmk13_jon_cert_classOf_seven hcx hcy
          (iff_of_false (by decide +kernel)
          (fun hsv => gmk14_uni_cert_cell_seven_negTwo_not_solvable
            (gmk8_cls_solvable_swap hsv)))

    · have hcx : gmk12_wcl_classOf hx
          = ((1 : ZMod 2), (gmk12_wcl_classOf hx).2) := by
        rw [← hxv]
      have hcy : gmk12_wcl_classOf hy
          = ((1 : ZMod 2), (gmk12_wcl_classOf hy).2) := by
        rw [← hyv]
      rcases gmk12_wcl_units_cases (gmk12_wcl_classOf hx).2 with hu | hu | hu | hu <;>
          rcases gmk12_wcl_units_cases (gmk12_wcl_classOf hy).2 with hv | hv | hv | hv <;>
          rw [hu] at hcx <;> rw [hv] at hcy

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_two_ne_zero gmk12_wcl_two_ne_zero
          gmk12_wcl_cert_classOf_two gmk12_wcl_cert_classOf_two hcx hcy
          (iff_of_true (by decide +kernel)
          (gmk14_uni_cert_cell_two_two))

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_two_ne_zero gmk12_wcl_negTen_ne_zero
          gmk12_wcl_cert_classOf_two gmk12_wcl_cert_classOf_negTen hcx hcy
          (iff_of_false (by decide +kernel)
          (gmk14_uni_cert_cell_two_negTen_not_solvable))

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_two_ne_zero gmk12_wcl_ten_ne_zero
          gmk12_wcl_cert_classOf_two gmk12_wcl_cert_classOf_ten hcx hcy
          (iff_of_false (by decide +kernel)
          (gmk14_uni_cert_cell_two_ten_not_solvable))

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_two_ne_zero gmk12_wcl_negTwo_ne_zero
          gmk12_wcl_cert_classOf_two gmk12_wcl_cert_classOf_negTwo hcx hcy
          (iff_of_true (by decide +kernel)
          (gmk14_uni_cert_cell_two_negTwo))

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_negTen_ne_zero gmk12_wcl_two_ne_zero
          gmk12_wcl_cert_classOf_negTen gmk12_wcl_cert_classOf_two hcx hcy
          (iff_of_false (by decide +kernel)
          (fun hsv => gmk14_uni_cert_cell_two_negTen_not_solvable
            (gmk8_cls_solvable_swap hsv)))

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_negTen_ne_zero gmk12_wcl_negTen_ne_zero
          gmk12_wcl_cert_classOf_negTen gmk12_wcl_cert_classOf_negTen hcx hcy
          (iff_of_false (by decide +kernel)
          (gmk14_uni_cert_cell_negTen_negTen_not_solvable))

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_negTen_ne_zero gmk12_wcl_ten_ne_zero
          gmk12_wcl_cert_classOf_negTen gmk12_wcl_cert_classOf_ten hcx hcy
          (iff_of_true (by decide +kernel)
          (gmk14_uni_cert_cell_negTen_ten))

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_negTen_ne_zero gmk12_wcl_negTwo_ne_zero
          gmk12_wcl_cert_classOf_negTen gmk12_wcl_cert_classOf_negTwo hcx hcy
          (iff_of_true (by decide +kernel)
          (gmk14_uni_cert_cell_negTen_negTwo))

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_ten_ne_zero gmk12_wcl_two_ne_zero
          gmk12_wcl_cert_classOf_ten gmk12_wcl_cert_classOf_two hcx hcy
          (iff_of_false (by decide +kernel)
          (fun hsv => gmk14_uni_cert_cell_two_ten_not_solvable
            (gmk8_cls_solvable_swap hsv)))

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_ten_ne_zero gmk12_wcl_negTen_ne_zero
          gmk12_wcl_cert_classOf_ten gmk12_wcl_cert_classOf_negTen hcx hcy
          (iff_of_true (by decide +kernel)
          (gmk14_uni_cert_cell_ten_negTen))

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_ten_ne_zero gmk12_wcl_ten_ne_zero
          gmk12_wcl_cert_classOf_ten gmk12_wcl_cert_classOf_ten hcx hcy
          (iff_of_true (by decide +kernel)
          (gmk14_uni_cert_cell_ten_ten))

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_ten_ne_zero gmk12_wcl_negTwo_ne_zero
          gmk12_wcl_cert_classOf_ten gmk12_wcl_cert_classOf_negTwo hcx hcy
          (iff_of_false (by decide +kernel)
          (gmk14_uni_cert_cell_ten_negTwo_not_solvable))

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_negTwo_ne_zero gmk12_wcl_two_ne_zero
          gmk12_wcl_cert_classOf_negTwo gmk12_wcl_cert_classOf_two hcx hcy
          (iff_of_true (by decide +kernel)
          (gmk8_cls_solvable_swap gmk14_uni_cert_cell_two_negTwo))

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_negTwo_ne_zero gmk12_wcl_negTen_ne_zero
          gmk12_wcl_cert_classOf_negTwo gmk12_wcl_cert_classOf_negTen hcx hcy
          (iff_of_true (by decide +kernel)
          (gmk8_cls_solvable_swap gmk14_uni_cert_cell_negTen_negTwo))

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_negTwo_ne_zero gmk12_wcl_ten_ne_zero
          gmk12_wcl_cert_classOf_negTwo gmk12_wcl_cert_classOf_ten hcx hcy
          (iff_of_false (by decide +kernel)
          (fun hsv => gmk14_uni_cert_cell_ten_negTwo_not_solvable
            (gmk8_cls_solvable_swap hsv)))

      · exact gmk14_uni_cell_transport hx hy gmk12_wcl_negTwo_ne_zero gmk12_wcl_negTwo_ne_zero
          gmk12_wcl_cert_classOf_negTwo gmk12_wcl_cert_classOf_negTwo hcx hcy
          (iff_of_false (by decide +kernel)
          (gmk14_uni_cert_cell_negTwo_negTwo_not_solvable))

end FLT.CampGenuineMk
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

section
section

set_option maxHeartbeats 8000000

suppress_compilation

p2m_open "IsDedekindDomain P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.IsDedekindDomain NumberField P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.NumberField QuaternionAlgebra P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.QuaternionAlgebra"
p2m_open "IsDedekindDomain.HeightOneSpectrum P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.IsDedekindDomain.HeightOneSpectrum"
open FLT.CampGenuineMk

namespace FLT
namespace NumberTheory

section SquareClassWitness

local instance kw_ldq_instDecEq : DecidableEq gmk6_hil_SquareClass := fun x y =>
  decidable_of_iff (x.valParity = y.valParity ∧ x.unitSign = y.unitSign)
    ⟨fun ⟨h1, h2⟩ => gmk6_hil_SquareClass_ext h1 h2, fun h => h ▸ ⟨rfl, rfl⟩⟩

local instance kw_ldq_instFintype : Fintype gmk6_hil_SquareClass :=
  Fintype.ofEquiv (ZMod 2 × ℤˣ)
    { toFun := fun ⟨a, u⟩ => ⟨a, u⟩
      invFun := fun c => ⟨c.valParity, c.unitSign⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem kw_ldq_squareClass_witness (e : ℤˣ) (A B N : gmk6_hil_SquareClass)
    (hAB : gmk6_hil_pair e A B = -1) (hN : N ≠ 1) :
    ∃ ξ : gmk6_hil_SquareClass,
      gmk6_hil_pair e (A * ξ) (B * ξ) = 1 ∧
      gmk6_hil_pair e (A * B * ξ) (N * ξ) = 1 := by
  have hZ : ∀ w : ZMod 2, w = 0 ∨ w = 1 := by decide
  obtain ⟨aα, au⟩ := A
  obtain ⟨bα, bu⟩ := B
  obtain ⟨nα, nu⟩ := N
  revert hAB hN
  rcases Int.units_eq_one_or e with rfl | rfl <;>
    rcases hZ aα with rfl | rfl <;> rcases Int.units_eq_one_or au with rfl | rfl <;>
    rcases hZ bα with rfl | rfl <;> rcases Int.units_eq_one_or bu with rfl | rfl <;>
    rcases hZ nα with rfl | rfl <;> rcases Int.units_eq_one_or nu with rfl | rfl <;>
    decide

end SquareClassWitness
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

theorem kw_ldq_wildClass_witness (A B N : ZMod 2 × (ZMod 8)ˣ)
    (hAB : gmk11_rec_wildPair A B = -1) (hN : N ≠ gmk11_rec_wildOne) :
    ∃ ξ : ZMod 2 × (ZMod 8)ˣ,
      gmk11_rec_wildPair (gmk11_rec_wildMul A ξ) (gmk11_rec_wildMul B ξ) = 1 ∧
      gmk11_rec_wildPair (gmk11_rec_wildMul (gmk11_rec_wildMul A B) ξ)
        (gmk11_rec_wildMul N ξ) = 1 := by
  revert hAB hN
  obtain ⟨aα, au⟩ := A
  obtain ⟨bα, bu⟩ := B
  obtain ⟨nα, nu⟩ := N
  rcases gmk12_wcl_zmod2_cases aα with rfl | rfl <;>
    rcases gmk12_wcl_units_cases au with rfl | rfl | rfl | rfl <;>
    rcases gmk12_wcl_zmod2_cases bα with rfl | rfl <;>
    rcases gmk12_wcl_units_cases bu with rfl | rfl | rfl | rfl <;>
    rcases gmk12_wcl_zmod2_cases nα with rfl | rfl <;>
    rcases gmk12_wcl_units_cases nu with rfl | rfl | rfl | rfl <;>
    decide +kernel

theorem kw_ldq_pureNrdRep_ringEquiv {F K : Type*} [CommRing F] [CommRing K]
    (φ : F ≃+* K) {a b c : F}
    (h : kw_pureNrdRep K (φ a) (φ b) (φ c)) :
    kw_pureNrdRep F a b c := by
  obtain ⟨x, y, z, hxyz⟩ := h
  refine ⟨φ.symm x, φ.symm y, φ.symm z, φ.injective ?_⟩
  simp only [map_add, map_sub, _root_.map_neg, map_mul, map_pow, RingEquiv.apply_symm_apply]
  linear_combination hxyz

section GlueHelper

variable {p : ℕ} [Fact p.Prime]

theorem kw_ldq_pureNrdRep_of_twoSolvable
    {a b c d : ℚ_[p]} (hd : d ≠ 0)
    (hram : ¬ gmk8_cls_solvable a b)
    (hsolv1 : gmk8_cls_solvable (a * d) (b * d))
    (hsolv2 : gmk8_cls_solvable (a * b * d) (-c * d))
    (hnsqabd : ¬ IsSquare (a * b * d)) :
    kw_pureNrdRep ℚ_[p] a b c := by
  obtain ⟨X₁, Y₁, Z₁, hnt1, heq1⟩ := hsolv1
  obtain ⟨X₂, Y₂, Z₂, hnt2, heq2⟩ := hsolv2

  have hZ1 : Z₁ ≠ 0 := by
    intro hZ1z
    have h0 : d * (a * (X₁ * X₁) + b * (Y₁ * Y₁)) = 0 := by
      linear_combination -heq1 + Z₁ * hZ1z
    have h0' : a * (X₁ * X₁) + b * (Y₁ * Y₁) = 0 :=
      (mul_eq_zero.mp h0).resolve_left hd
    have hnt1' : X₁ ≠ 0 ∨ Y₁ ≠ 0 ∨ (0 : ℚ_[p]) ≠ 0 := by
      rcases hnt1 with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact absurd hZ1z h
    exact hram ⟨X₁, Y₁, 0, hnt1', by linear_combination -h0'⟩

  have hY2 : Y₂ ≠ 0 := by
    intro hY2z
    have heq2' : Z₂ * Z₂ = a * b * d * (X₂ * X₂) := by
      linear_combination heq2 + (-c * d * Y₂) * hY2z
    have hX2 : X₂ ≠ 0 := by
      intro hX2z
      have hZ2 : Z₂ = 0 := by
        have : Z₂ * Z₂ = 0 := by rw [heq2', hX2z]; ring
        exact mul_self_eq_zero.mp this
      rcases hnt2 with h | h | h
      · exact h hX2z
      · exact h hY2z
      · exact h hZ2
    exact hnsqabd ⟨Z₂ / X₂, by
      rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hX2 hX2)]; exact heq2'.symm⟩

  have hW : (Y₂ * Z₁ : ℚ_[p]) ≠ 0 := mul_ne_zero hY2 hZ1
  have hkey : -a * (X₁ * Z₂) ^ 2 - b * (Y₁ * Z₂) ^ 2 + a * b * (X₂ * Z₁) ^ 2
      = c * (Y₂ * Z₁) ^ 2 := by
    have hprod : (a * (X₁ * X₁) + b * (Y₁ * Y₁)) * (Z₂ * Z₂)
        = (a * b * (X₂ * X₂) - c * (Y₂ * Y₂)) * (Z₁ * Z₁) := by
      have hg1 : Z₁ * Z₁ = d * (a * (X₁ * X₁) + b * (Y₁ * Y₁)) := by
        linear_combination heq1
      have hg2 : Z₂ * Z₂ = d * (a * b * (X₂ * X₂) - c * (Y₂ * Y₂)) := by
        linear_combination heq2
      rw [hg1, hg2]; ring
    linear_combination -hprod
  refine ⟨X₁ * Z₂ / (Y₂ * Z₁), Y₁ * Z₂ / (Y₂ * Z₁), X₂ * Z₁ / (Y₂ * Z₁), ?_⟩
  rw [div_pow, div_pow, div_pow, ← mul_div_assoc, ← mul_div_assoc, ← mul_div_assoc,
    div_sub_div_same, ← add_div, hkey, mul_div_assoc,
    div_self (pow_ne_zero 2 hW), mul_one]

end GlueHelper
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

section PadicOdd

variable {p : ℕ} [Fact p.Prime]

theorem kw_ldq_isSquare_of_classOf_eq_one (hp2 : p ≠ 2) {x : ℚ_[p]} (hx : x ≠ 0)
    (h : gmk7_cls_classOf hx = 1) : IsSquare x := by
  obtain ⟨s, _, hs⟩ := gmk8_cls_exists_sq_ratio_of_classOf_eq hp2
    (one_ne_zero (α := ℚ_[p])) hx (gmk7_cls_classOf_one.trans h.symm)
  exact ⟨s, hs.trans (one_mul _)⟩

theorem kw_ldq_pureNrdRep_padic_odd (hp2 : p ≠ 2)
    {a b c : ℚ_[p]} (ha : a ≠ 0) (hb : b ≠ 0)
    (hram : ¬ gmk8_cls_solvable a b) (hnsq : ¬ IsSquare (-c)) :
    kw_pureNrdRep ℚ_[p] a b c := by

  have hc : c ≠ 0 := fun h =>
    hnsq ⟨0, by rw [h, _root_.neg_zero, mul_zero]⟩
  have hnc : (-c : ℚ_[p]) ≠ 0 := neg_ne_zero.mpr hc
  have hab : (a * b : ℚ_[p]) ≠ 0 := mul_ne_zero ha hb

  set e : ℤˣ := gmk6_hil_epsSign p
  set A : gmk6_hil_SquareClass := gmk7_cls_classOf ha
  set B : gmk6_hil_SquareClass := gmk7_cls_classOf hb
  set N : gmk6_hil_SquareClass := gmk7_cls_classOf hnc

  have hAB : gmk6_hil_pair e A B = -1 := by
    rcases Int.units_eq_one_or (gmk6_hil_pair e A B) with h1 | h1
    · exact absurd ((gmk9_ser_solvability_pair hp2 ha hb).mpr h1) hram
    · exact h1

  have hN : N ≠ 1 := fun h => hnsq (kw_ldq_isSquare_of_classOf_eq_one hp2 hnc h)

  obtain ⟨ξ, h1, h2⟩ := kw_ldq_squareClass_witness e A B N hAB hN

  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  obtain ⟨u0, hu0⟩ := FiniteField.exists_nonsquare (F := ZMod p) hchar
  have hu00 : u0 ≠ 0 := fun h => hu0 ⟨0, by rw [h, mul_zero]⟩
  have hn : ((u0.val : ℕ) : ZMod p) ≠ 0 := by
    rw [ZMod.natCast_val, ZMod.cast_id]; exact hu00
  have hns : ¬ IsSquare (((u0.val : ℕ) : ZMod p)) := by
    rw [ZMod.natCast_val, ZMod.cast_id]; exact hu0
  let d : ℚ_[p] := gmk9_ser_rep (p := p) u0.val ξ
  have hd : d ≠ 0 := gmk9_ser_rep_ne_zero hn ξ
  have hξ : gmk7_cls_classOf hd = ξ := gmk9_ser_classOf_rep hp2 hn hns ξ

  have hsolv1 : gmk8_cls_solvable (a * d) (b * d) := by
    rw [gmk9_ser_solvability_pair hp2 (mul_ne_zero ha hd) (mul_ne_zero hb hd),
      gmk7_cls_classOf_mul ha hd, gmk7_cls_classOf_mul hb hd, hξ]
    exact h1

  have hsolv2 : gmk8_cls_solvable (a * b * d) (-c * d) := by
    rw [gmk9_ser_solvability_pair hp2 (mul_ne_zero hab hd) (mul_ne_zero hnc hd),
      gmk7_cls_classOf_mul hab hd, gmk7_cls_classOf_mul hnc hd, hξ,
      gmk7_cls_classOf_mul ha hb]
    exact h2

  have hnsqabd : ¬ IsSquare (a * b * d) := by
    intro hsq
    have hABξ : A * B * ξ = 1 := by
      have h := gmk7_cls_classOf_eq_one_of_isSquare (mul_ne_zero hab hd) hsq
      rwa [gmk7_cls_classOf_mul hab hd, hξ, gmk7_cls_classOf_mul ha hb] at h
    have hξAB : ξ = A * B := by
      calc ξ = A * B * (A * B) * ξ := by rw [gmk7_cls_carrier_mul_self, one_mul]
        _ = A * B * (A * B * ξ) := by rw [mul_assoc]
        _ = A * B := by rw [hABξ, mul_one]
    have hBA : gmk6_hil_pair e B A = 1 := by
      have := h1; rw [hξAB] at this
      rwa [show A * (A * B) = B by rw [← mul_assoc, gmk7_cls_carrier_mul_self, one_mul],
        show B * (A * B) = A by rw [mul_comm A B, ← mul_assoc,
          gmk7_cls_carrier_mul_self, one_mul]] at this
    exact absurd (hBA.symm.trans (gmk6_hil_pair_symm e B A) |>.trans hAB) (by decide)
  exact kw_ldq_pureNrdRep_of_twoSolvable hd hram hsolv1 hsolv2 hnsqabd

end PadicOdd
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

section PadicTwo

theorem kw_ldq_wildMul_comm (x y : ZMod 2 × (ZMod 8)ˣ) :
    gmk11_rec_wildMul x y = gmk11_rec_wildMul y x := by
  show (x.1 + y.1, x.2 * y.2) = (y.1 + x.1, y.2 * x.2)
  rw [add_comm, mul_comm]

theorem kw_ldq_wildMul_assoc (x y z : ZMod 2 × (ZMod 8)ˣ) :
    gmk11_rec_wildMul (gmk11_rec_wildMul x y) z
      = gmk11_rec_wildMul x (gmk11_rec_wildMul y z) := by
  show (x.1 + y.1 + z.1, x.2 * y.2 * z.2) = (x.1 + (y.1 + z.1), x.2 * (y.2 * z.2))
  rw [add_assoc, mul_assoc]

theorem kw_ldq_pureNrdRep_padic_two
    {a b c : ℚ_[2]} (ha : a ≠ 0) (hb : b ≠ 0)
    (hram : ¬ gmk8_cls_solvable a b) (hnsq : ¬ IsSquare (-c)) :
    kw_pureNrdRep ℚ_[2] a b c := by
  have hc : c ≠ 0 := fun h => hnsq ⟨0, by rw [h, _root_.neg_zero, mul_zero]⟩
  have hnc : (-c : ℚ_[2]) ≠ 0 := neg_ne_zero.mpr hc
  have hab : (a * b : ℚ_[2]) ≠ 0 := mul_ne_zero ha hb

  set A := gmk12_wcl_classOf ha
  set B := gmk12_wcl_classOf hb
  set N := gmk12_wcl_classOf hnc

  have hAB : gmk11_rec_wildPair A B = -1 := by
    rcases Int.units_eq_one_or (gmk11_rec_wildPair A B) with h1 | h1
    · exact absurd ((gmk14_uni_pin_wildPair_iff_solvable_full ha hb).mp h1) hram
    · exact h1

  have hN : N ≠ gmk11_rec_wildOne := fun h =>
    hnsq ((gmk13_jon_kernel_row hnc).mp h)

  obtain ⟨ξ, h1, h2⟩ := kw_ldq_wildClass_witness A B N hAB hN

  obtain ⟨d, hd, hξ⟩ := gmk12_wcl_surjective_reps ξ

  have hsolv1 : gmk8_cls_solvable (a * d) (b * d) := by
    rw [← gmk14_uni_pin_wildPair_iff_solvable_full (mul_ne_zero ha hd) (mul_ne_zero hb hd),
      gmk12_wcl_classOf_mul ha hd, gmk12_wcl_classOf_mul hb hd, hξ]
    exact h1

  have hsolv2 : gmk8_cls_solvable (a * b * d) (-c * d) := by
    rw [← gmk14_uni_pin_wildPair_iff_solvable_full
        (mul_ne_zero hab hd) (mul_ne_zero hnc hd),
      gmk12_wcl_classOf_mul hab hd, gmk12_wcl_classOf_mul hnc hd, hξ,
      gmk12_wcl_classOf_mul ha hb]
    exact h2

  have hnsqabd : ¬ IsSquare (a * b * d) := by
    intro hsq
    have hABξ : gmk11_rec_wildMul (gmk11_rec_wildMul A B) ξ = gmk11_rec_wildOne := by
      have h := (gmk13_jon_kernel_row (mul_ne_zero hab hd)).mpr hsq
      rwa [gmk12_wcl_classOf_mul hab hd, hξ, gmk12_wcl_classOf_mul ha hb] at h
    have hξAB : ξ = gmk11_rec_wildMul A B := by
      calc ξ = gmk11_rec_wildMul ξ gmk11_rec_wildOne := (gmk12_wcl_wildMul_one ξ).symm
        _ = gmk11_rec_wildMul ξ
              (gmk11_rec_wildMul (gmk11_rec_wildMul A B) (gmk11_rec_wildMul A B)) := by
            rw [gmk12_wcl_carrier_mul_self]
        _ = gmk11_rec_wildMul (gmk11_rec_wildMul (gmk11_rec_wildMul A B) ξ)
              (gmk11_rec_wildMul A B) := by
            rw [← kw_ldq_wildMul_assoc, kw_ldq_wildMul_comm ξ _,
              kw_ldq_wildMul_assoc]
        _ = gmk11_rec_wildMul A B := by
            rw [hABξ, kw_ldq_wildMul_comm, gmk12_wcl_wildMul_one]
    have hAξ : gmk11_rec_wildMul A ξ = B := by
      rw [hξAB, ← kw_ldq_wildMul_assoc, gmk12_wcl_carrier_mul_self,
        kw_ldq_wildMul_comm, gmk12_wcl_wildMul_one]
    have hBξ : gmk11_rec_wildMul B ξ = A := by
      rw [hξAB, kw_ldq_wildMul_comm A B, ← kw_ldq_wildMul_assoc,
        gmk12_wcl_carrier_mul_self, kw_ldq_wildMul_comm, gmk12_wcl_wildMul_one]
    rw [hAξ, hBξ, gmk11_rec_wildPair_symm] at h1
    exact absurd (h1.symm.trans hAB) (by decide)
  exact kw_ldq_pureNrdRep_of_twoSolvable hd hram hsolv1 hsolv2 hnsqabd

end PadicTwo
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

local instance kw_ldq_instFactPrimePrimesEquiv (v : HeightOneSpectrum (𝓞 ℚ)) :
    Fact (Rat.HeightOneSpectrum.primesEquiv v : ℕ).Prime :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

section PadicEquivHelper

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

noncomputable def kw_ldq_padicRingEquiv (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.adicCompletion ℚ ≃+* ℚ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)] :=
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toRingEquiv

end PadicEquivHelper
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

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

theorem kw_localDivQuatPureNrdRep_proved (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    kw_localDivQuatPureNrdRep a b := by
  intro v hns c hnsq
  set p := (Rat.HeightOneSpectrum.primesEquiv v : ℕ)

  have hAfin := kw_HSCluster_A_fin_proved a b ha hb v
  by_cases hp2 : p = 2
  ·
    let φ : v.adicCompletion ℚ ≃+* ℚ_[2] :=
      (kw_ldq_padicRingEquiv v).trans (kw_ldq_padicCast hp2)
    have hφq : ∀ (f : ℚ →+* v.adicCompletion ℚ) (q : ℚ), φ (f q) = (q : ℚ_[2]) :=
      fun f q => eq_ratCast (φ.toRingHom.comp f) q
    have haP : (a : ℚ_[2]) ≠ 0 := Rat.cast_ne_zero.mpr ha
    have hbP : (b : ℚ_[2]) ≠ 0 := Rat.cast_ne_zero.mpr hb
    have hram : ¬ gmk8_cls_solvable (p := 2) (a : ℚ_[2]) (b : ℚ_[2]) := fun hs =>
      (hAfin.mp hns) ((kw_ldq_hpSolvAt_iff_gmk8 a b v φ).mpr hs)
    have hnsq' : ¬ IsSquare (-(φ c)) := fun hs => hnsq <| by
      rw [← _root_.map_neg] at hs
      exact (kw_ldq_isSquare_ringEquiv φ).mp hs
    refine kw_ldq_pureNrdRep_ringEquiv φ ?_
    rw [hφq _ a, hφq _ b]
    exact kw_ldq_pureNrdRep_padic_two haP hbP hram hnsq'
  ·
    let φ : v.adicCompletion ℚ ≃+* ℚ_[p] := kw_ldq_padicRingEquiv v
    have hφq : ∀ (f : ℚ →+* v.adicCompletion ℚ) (q : ℚ), φ (f q) = (q : ℚ_[p]) :=
      fun f q => eq_ratCast (φ.toRingHom.comp f) q
    have haP : (a : ℚ_[p]) ≠ 0 := Rat.cast_ne_zero.mpr ha
    have hbP : (b : ℚ_[p]) ≠ 0 := Rat.cast_ne_zero.mpr hb
    have hram : ¬ gmk8_cls_solvable (p := p) (a : ℚ_[p]) (b : ℚ_[p]) := fun hs =>
      (hAfin.mp hns) ((kw_ldq_hpSolvAt_iff_gmk8 a b v φ).mpr hs)
    have hnsq' : ¬ IsSquare (-(φ c)) := fun hs => hnsq <| by
      rw [← _root_.map_neg] at hs
      exact (kw_ldq_isSquare_ringEquiv φ).mp hs
    refine kw_ldq_pureNrdRep_ringEquiv φ ?_
    rw [hφq _ a, hφq _ b]
    exact kw_ldq_pureNrdRep_padic_odd hp2 haP hbP hram hnsq'

end FLT.NumberTheory
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

end
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

end S18Body
p2m_reactivate "P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split.FLT.CampGenuineMk"

theorem s18_algebraMap_rat_eq {A : Type*} [DivisionRing A] (hA : CharZero A) [inst : Algebra ℚ A] :
    (algebraMap ℚ A : ℚ →+* A) = @algebraMap ℚ A _ _ (@DivisionRing.toRatAlgebra A _ hA) :=
  Subsingleton.elim _ _

theorem solution
    (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (hv : ¬ Nonempty (QuaternionAlgebra (v.adicCompletion ℚ)
        (algebraMap ℚ (v.adicCompletion ℚ) a) 0 (algebraMap ℚ (v.adicCompletion ℚ) b)
          ≃ₐ[v.adicCompletion ℚ] Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (c : v.adicCompletion ℚ) (hc : ¬ IsSquare (-c)) :
    ∃ x y z : v.adicCompletion ℚ,
      -(algebraMap ℚ (v.adicCompletion ℚ) a) * x ^ 2 - (algebraMap ℚ (v.adicCompletion ℚ) b) * y ^ 2
        + (algebraMap ℚ (v.adicCompletion ℚ) a) * (algebraMap ℚ (v.adicCompletion ℚ) b) * z ^ 2 = c := by
  rw [s18_algebraMap_rat_eq (charZero_adicCompletion_s18 v)] at hv ⊢
  exact FLT.NumberTheory.kw_localDivQuatPureNrdRep_proved a b ha hb v hv c hc

end S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split
end P2MW
export P2MW.S_QuadraticForm_exists_ternary_pureNrd_eq_adicCompletion_of_not_isSquare_neg_of_not_split (solution)
