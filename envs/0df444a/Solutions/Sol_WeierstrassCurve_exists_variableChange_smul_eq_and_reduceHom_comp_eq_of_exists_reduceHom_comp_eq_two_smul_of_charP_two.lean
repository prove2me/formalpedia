-- Prove2me | solution 1 for WeierstrassCurve.exists_variableChange_smul_eq_and_reduceHom_comp_eq_of_exists_reduceHom_comp_eq_two_smul_of_charP_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/2dc81ccb-2061-5e7e-9120-42d99e3571a2

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_ReduceHom
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_RatPointHom
import Definitions.Def_WeierstrassCurve_PointAddEquivOfEq
import Definitions.Def_DualIsogenyAPI
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_FibrePoly
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_two_smul_comp_eq_comp_of_comp_self_add_smul_eq_smul
import Theorems.Thm_WeierstrassCurve_comp_ratPointHom_iterateFrobenius_eq_of_comp_eq_comp
import Theorems.Thm_WeierstrassCurve_exists_reduceHom_comp_eq_of_exists_reduceHom_comp_eq_map_iterateFrobenius
import Theorems.Thm_WeierstrassCurve_exists_ne_zero_and_char_nsmul_eq_zero_of_comp_self_add_smul_eq_smul_of_dvd_of_not_dvd
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_reduceHom_comp_eq_comp_reduceHom
import Theorems.Thm_WeierstrassCurve_exists_map_residue_eq_and_map_subtype_j_eq
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero
import Theorems.Thm_WeierstrassCurve_exists_isDualPair_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_WeierstrassCurve_exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero
import Theorems.Thm_WeierstrassCurve_exists_addEquiv_point_variableChange
import Theorems.Thm_ModularCurve_modularPolynomial_kronecker
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ValuationSubring_exists_pow_prime_pow_eq_self_of_isAlgebraic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_and_reduceHom_comp_eq_of_exists_reduceHom_comp_eq_two_smul_of_charP_two
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄"
p2m_attr_erase "simp" "compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.veluX_empty AddMonoid.End.dualEndDataOfSurjective_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndDataOfSurjective_norm"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

p2m_open "IsLocalRing WeierstrassCurve P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_and_reduceHom_comp_eq_of_exists_reduceHom_comp_eq_two_smul_of_charP_two.WeierstrassCurve Polynomial"
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine isUnit_Δ Affine.negY a₃ map_map a₁ map map_j isElliptic_iff Affine.Point.some exists_variableChange_of_j_eq isIntegral_iff Affine.Point.some.inj reduction IsIntegral toAffine Affine.Point map_Δ Affine.Point.some_ne_zero Δ VariableChange Affine.Point.neg_some map_variableChange baseChange j evalEvalBC IsRationallyRepresented rationalHomSet zero_mem_rationalHomSet id_mem_rationalHomSet reduceHom map_residue_Δ_ne_zero_iff Affine.vcYInv Affine.Point.vcInvFun Affine.Point.equivOfVariableChangeEq pointAddEquivOfEq pointAddEquivOfEq_refl exists_mem_rationalHomSet_two_smul_comp_eq_comp_of_comp_self_add_smul_eq_smul comp_ratPointHom_iterateFrobenius_eq_of_comp_eq_comp exists_reduceHom_comp_eq_of_exists_reduceHom_comp_eq_map_iterateFrobenius exists_ne_zero_and_char_nsmul_eq_zero_of_comp_self_add_smul_eq_smul_of_dvd_of_not_dvd exists_mem_rationalHomSet_reduceHom_comp_eq_comp_reduceHom exists_map_residue_eq_and_map_subtype_j_eq exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero exists_isDualPair_of_mem_rationalHomSet surjective_of_mem_rationalHomSet comp_mem_rationalHomSet add_mem_rationalHomSet card_torsion_of_isAlgClosed exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero exists_addEquiv_point_variableChange"
namespace TwoDescentPlace
p2m_open "WeierstrassCurve"

section HomSet

variable {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [DecidableEq k]

theorem isRationallyRepresented_neg_id (W : WeierstrassCurve F) :
    IsRationallyRepresented k W W (-(AddMonoidHom.id _)) := by
  refine ⟨C X, 1, -X - C (C W.a₁ * X + C W.a₃), 1, ∅, Set.finite_empty, fun x y h _ => ?_⟩
  have e0 : evalEvalBC k (1 : F[X][Y]) x y = 1 := by simp [evalEvalBC, Polynomial.evalEval]
  have e1 : evalEvalBC k (C X : F[X][Y]) x y = x := by simp [evalEvalBC, Polynomial.evalEval]
  have e2 : evalEvalBC k (-X - C (C W.a₁ * X + C W.a₃) : F[X][Y]) x y =
      (W.baseChange k).toAffine.negY x y := by
    simp [evalEvalBC, Polynomial.evalEval, Affine.negY, WeierstrassCurve.baseChange]
    ring
  refine ⟨by rw [e0]; exact one_ne_zero, by rw [e0]; exact one_ne_zero, ?_⟩
  rw [e0, e1, e2, div_one, div_one, AddMonoidHom.neg_apply, AddMonoidHom.id_apply,
    Affine.Point.neg_some]
  exact ⟨_, rfl⟩

theorem neg_id_mem_rationalHomSet (W : WeierstrassCurve F) :
    (-(AddMonoidHom.id _) : (W.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point) ∈
      rationalHomSet k W W :=
  Or.inr (isRationallyRepresented_neg_id k W)

variable {k}

theorem neg_mem_rationalHomSet {W₁ W₂ : WeierstrassCurve F}
    {α : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
    (hα : α ∈ rationalHomSet k W₁ W₂) : -α ∈ rationalHomSet k W₁ W₂ := by
  have h := WeierstrassCurve.comp_mem_rationalHomSet k W₁ W₂ W₂ hα (neg_id_mem_rationalHomSet k W₂)
  have e : (-(AddMonoidHom.id _)).comp α = -α := by ext P; simp
  rwa [e] at h

variable [IsAlgClosed k]

theorem sub_mem_rationalHomSet {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic]
    {α β : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
    (hα : α ∈ rationalHomSet k W₁ W₂) (hβ : β ∈ rationalHomSet k W₁ W₂) :
    α - β ∈ rationalHomSet k W₁ W₂ := by
  rw [sub_eq_add_neg]
  exact WeierstrassCurve.add_mem_rationalHomSet k W₁ W₂ hα (neg_mem_rationalHomSet hβ)

theorem zsmul_mem_rationalHomSet {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic]
    {α : (W₁.baseChange k).toAffine.Point →+ (W₂.baseChange k).toAffine.Point}
    (hα : α ∈ rationalHomSet k W₁ W₂) (n : ℤ) : n • α ∈ rationalHomSet k W₁ W₂ := by
  induction n using Int.induction_on with
  | zero => rw [zero_zsmul]; exact zero_mem_rationalHomSet k W₁ W₂
  | succ n ih =>
    rw [add_zsmul, one_zsmul]
    exact WeierstrassCurve.add_mem_rationalHomSet k W₁ W₂ ih hα
  | pred n ih =>
    rw [sub_zsmul, one_zsmul]
    exact sub_mem_rationalHomSet ih hα

theorem zsmul_id_mem_rationalHomSet (W : WeierstrassCurve F) [W.IsElliptic] (n : ℤ) :
    (n • AddMonoidHom.id _ : (W.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point) ∈
      rationalHomSet k W W :=
  zsmul_mem_rationalHomSet (id_mem_rationalHomSet k W) n

end HomSet

section Torsion

variable (k : Type*) [Field k]

theorem exists_prime_gt_natCast_ne_zero (M : ℕ) : ∃ ℓ : ℕ, ℓ.Prime ∧ M < ℓ ∧ (ℓ : k) ≠ 0 := by
  obtain ⟨ℓ₁, h₁, hp₁⟩ := Nat.exists_infinite_primes (M + 1)
  obtain ⟨ℓ₂, h₂, hp₂⟩ := Nat.exists_infinite_primes (ℓ₁ + 1)
  by_cases hz₁ : (ℓ₁ : k) = 0
  · refine ⟨ℓ₂, hp₂, by omega, fun hz₂ => ?_⟩
    have d₁ : ringChar k ∣ ℓ₁ := (ringChar.spec k ℓ₁).mp hz₁
    have d₂ : ringChar k ∣ ℓ₂ := (ringChar.spec k ℓ₂).mp hz₂
    have hne : ℓ₁ ≠ ℓ₂ := by omega
    have hcop : Nat.Coprime ℓ₁ ℓ₂ := (Nat.coprime_primes hp₁ hp₂).mpr hne
    have h1 : ringChar k ∣ 1 := by
      have := Nat.dvd_gcd d₁ d₂
      rwa [hcop] at this
    have : ringChar k = 1 := Nat.dvd_one.mp h1
    exact absurd this (CharP.ringChar_ne_one)
  · exact ⟨ℓ₁, hp₁, by omega, hz₁⟩

variable {k} [DecidableEq k] [IsAlgClosed k]

theorem exists_ne_zero_nsmul_eq_zero (W : WeierstrassCurve k) [W.IsElliptic] {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hℓk : (ℓ : k) ≠ 0) : ∃ Q : W.toAffine.Point, Q ≠ 0 ∧ (ℓ : ℤ) • Q = 0 := by
  have hcard : Nat.card (Submodule.torsionBy ℤ (W.baseChange k).toAffine.Point (ℓ : ℤ)) = ℓ ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed (K := k) W hℓk
  set Tor := Submodule.torsionBy ℤ (W.baseChange k).toAffine.Point (ℓ : ℤ)
  haveI : Finite Tor := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hℓ.ne_zero)
  have hnt : Nontrivial Tor := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    exact Nat.one_lt_pow two_ne_zero hℓ.one_lt
  obtain ⟨⟨R, hR⟩, hR1⟩ := exists_ne (0 : Tor)
  refine ⟨R, fun h => hR1 (Subtype.ext h), ?_⟩
  exact (Submodule.mem_torsionBy_iff _ _).mp hR

theorem eq_zero_of_zsmul_eq_zero {W₁ W₂ : WeierstrassCurve k} [W₁.IsElliptic] [W₂.IsElliptic]
    {δ : W₁.toAffine.Point →+ W₂.toAffine.Point} (hδ : δ ∈ rationalHomSet k W₁ W₂)
    {N : ℤ} (hN : N ≠ 0) (h : N • δ = 0) : δ = 0 := by
  by_contra hδ0
  obtain ⟨ℓ, hℓ, hMℓ, hℓk⟩ := exists_prime_gt_natCast_ne_zero k N.natAbs
  obtain ⟨Q, hQ0, hQℓ⟩ := exists_ne_zero_nsmul_eq_zero W₂ hℓ hℓk
  obtain ⟨P, hP⟩ : ∃ P : W₁.toAffine.Point, δ P = Q :=
    WeierstrassCurve.surjective_of_mem_rationalHomSet k hδ hδ0 Q
  have hNQ : N • Q = 0 := by
    have := DFunLike.congr_fun h P
    rwa [AddMonoidHom.zsmul_apply, hP, AddMonoidHom.zero_apply] at this

  have hcop : IsCoprime (ℓ : ℤ) N := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h1 : Int.gcd (ℓ : ℤ) N ∣ ℓ := by
      have := Int.gcd_dvd_left (ℓ : ℤ) N
      exact_mod_cast this
    rcases (Nat.dvd_prime hℓ).mp h1 with h | h
    · exact h
    · exfalso
      have h2 : ((Int.gcd (ℓ : ℤ) N : ℕ) : ℤ) ∣ N := Int.gcd_dvd_right _ _
      rw [h] at h2
      have h3 : ℓ ∣ N.natAbs := Int.natCast_dvd.mp h2
      have := Nat.le_of_dvd (Int.natAbs_pos.mpr hN) h3
      omega
  obtain ⟨a, b, hab⟩ := hcop
  apply hQ0
  calc Q = (1 : ℤ) • Q := (one_zsmul Q).symm
    _ = (a * ℓ + b * N) • Q := by rw [hab]
    _ = 0 := by rw [add_zsmul, mul_zsmul, mul_zsmul, hQℓ, hNQ, zsmul_zero, zsmul_zero, add_zero]

theorem zsmul_id_ne_zero (W : WeierstrassCurve k) [W.IsElliptic] {N : ℤ} (hN : N ≠ 0) :
    (N • AddMonoidHom.id _ : W.toAffine.Point →+ W.toAffine.Point) ≠ 0 := by
  intro h
  have h' : N • (AddMonoidHom.id _ : W.toAffine.Point →+ W.toAffine.Point) = 0 := h
  have := eq_zero_of_zsmul_eq_zero (k := k) (W₁ := W) (W₂ := W) (id_mem_rationalHomSet k W) hN h'
  obtain ⟨ℓ, hℓ, -, hℓk⟩ := exists_prime_gt_natCast_ne_zero k 0
  obtain ⟨Q, hQ0, -⟩ := exists_ne_zero_nsmul_eq_zero W hℓ hℓk
  exact hQ0 (by first | simpa using DFunLike.congr_fun this Q | (have h_1 := DFunLike.congr_fun this Q; simp at h_1; exact h_1) | (have h_1 := DFunLike.congr_fun this Q; simp at h_1 ⊢; exact h_1) | exact (DFunLike.congr_fun this Q))

theorem exists_zsmul_eq (W : WeierstrassCurve k) [W.IsElliptic] {N : ℤ} (hN : N ≠ 0)
    (Q : W.toAffine.Point) : ∃ P : W.toAffine.Point, N • P = Q := by
  obtain ⟨P, hP⟩ : ∃ P : W.toAffine.Point, (N • AddMonoidHom.id _ : W.toAffine.Point →+ _) P = Q :=
    WeierstrassCurve.surjective_of_mem_rationalHomSet k
      (zsmul_id_mem_rationalHomSet (k := k) W N) (zsmul_id_ne_zero W hN) Q
  exact ⟨P, by first | simpa using hP | (have h_1 := hP; simp at h_1; exact h_1) | (have h_1 := hP; simp at h_1 ⊢; exact h_1) | exact (hP)⟩

theorem eq_zero_of_prime_zsmul_of_zsmul {G : Type*} [AddCommGroup G] {Q : G} {ℓ : ℕ}
    (hℓ : ℓ.Prime) {N : ℤ} (hN : N ≠ 0) (hlt : N.natAbs < ℓ) (h1 : (ℓ : ℤ) • Q = 0)
    (h2 : N • Q = 0) : Q = 0 := by
  have hcop : IsCoprime (ℓ : ℤ) N := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h1 : Int.gcd (ℓ : ℤ) N ∣ ℓ := by
      have := Int.gcd_dvd_left (ℓ : ℤ) N
      exact_mod_cast this
    rcases (Nat.dvd_prime hℓ).mp h1 with h | h
    · exact h
    · exfalso
      have h2 : ((Int.gcd (ℓ : ℤ) N : ℕ) : ℤ) ∣ N := Int.gcd_dvd_right _ _
      rw [h] at h2
      have h3 : ℓ ∣ N.natAbs := Int.natCast_dvd.mp h2
      have := Nat.le_of_dvd (Int.natAbs_pos.mpr hN) h3
      omega
  obtain ⟨a, b, hab⟩ := hcop
  calc Q = (1 : ℤ) • Q := (one_zsmul Q).symm
    _ = (a * ℓ + b * N) • Q := by rw [hab]
    _ = 0 := by rw [add_zsmul, mul_zsmul, mul_zsmul, h1, h2, zsmul_zero, zsmul_zero, add_zero]

end Torsion

section VarChange

variable {K : Type*} [Field K] [DecidableEq K]

def vcAddEquiv (C : VariableChange K) (E₀ : WeierstrassCurve K) :
    E₀.toAffine.Point ≃+ (C • E₀).toAffine.Point :=
  Classical.choose (WeierstrassCurve.exists_addEquiv_point_variableChange E₀ C)

theorem vcAddEquiv_some (C : VariableChange K) (E₀ : WeierstrassCurve K) (x y : K)
    (h : E₀.toAffine.Nonsingular x y) :
    ∃ h' : (C • E₀).toAffine.Nonsingular ((↑C.u⁻¹ : K) ^ 2 * (x - C.r))
        ((↑C.u⁻¹ : K) ^ 3 * (y - C.s * x + (C.s * C.r - C.t))),
      vcAddEquiv C E₀ (.some x y h) = .some ((↑C.u⁻¹ : K) ^ 2 * (x - C.r))
        ((↑C.u⁻¹ : K) ^ 3 * (y - C.s * x + (C.s * C.r - C.t))) h' :=
  Classical.choose_spec (WeierstrassCurve.exists_addEquiv_point_variableChange E₀ C) x y h

def vS {C : VariableChange K} {E₀ V : WeierstrassCurve K} (h : C • E₀ = V) :
    E₀.toAffine.Point ≃+ V.toAffine.Point :=
  (vcAddEquiv C E₀).trans (pointAddEquivOfEq h)

private theorem some_congr {R : Type*} [CommRing R] {V : Affine R} {x₁ x₂ y₁ y₂ : R}
    (hx : x₁ = x₂) (hy : y₁ = y₂) (h₁ : V.Nonsingular x₁ y₁) (h₂ : V.Nonsingular x₂ y₂) :
    Affine.Point.some x₁ y₁ h₁ = Affine.Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

theorem vS_apply {C : VariableChange K} {E₀ V : WeierstrassCurve K} (h : C • E₀ = V)
    (P : E₀.toAffine.Point) :
    vS h P = (Affine.Point.equivOfVariableChangeEq h).symm P := by
  subst h
  rcases P with _ | ⟨x, y, hP⟩
  · show vS _ 0 = _
    rw [map_zero]; rfl
  · obtain ⟨h', e⟩ := vcAddEquiv_some C E₀ x y hP
    simp only [vS, AddEquiv.trans_apply, pointAddEquivOfEq_refl, AddEquiv.refl_apply, e]
    show _ = Affine.Point.vcInvFun C E₀ (.some x y hP)
    simp only [Affine.Point.vcInvFun]
    exact some_congr rfl (by simp only [Affine.vcYInv]; ring) _ _

omit [DecidableEq K] in
private theorem exists_eq_some {W : WeierstrassCurve K}
    {P : W.toAffine.Point} {u v u' v' : K}
    {h₀ : W.toAffine.Nonsingular u v} (hP : P = .some u v h₀)
    (hu : u = u') (hv : v = v') :
    ∃ h'', P = .some u' v' h'' := by
  subst hu hv
  exact ⟨h₀, hP⟩

theorem vcAddEquiv_mem (C : VariableChange K) (E₀ : WeierstrassCurve K) :
    ((vcAddEquiv C E₀).toAddMonoidHom :
        (E₀.baseChange K).toAffine.Point →+ ((C • E₀).baseChange K).toAffine.Point) ∈
      rationalHomSet K E₀ (C • E₀) := by
  right
  refine ⟨Polynomial.C (Polynomial.C ((↑C.u⁻¹ : K) ^ 2) * (X - Polynomial.C C.r)), 1,
    Polynomial.C (Polynomial.C ((↑C.u⁻¹ : K) ^ 3)) *
      (X - Polynomial.C (Polynomial.C C.s * X) + Polynomial.C (Polynomial.C (C.s * C.r - C.t))), 1, ∅,
    Set.finite_empty, fun x y h _ => ?_⟩
  have e0 : evalEvalBC (F := K) K (1 : K[X][Y]) x y = 1 := by simp [evalEvalBC, Polynomial.evalEval]
  have e1 : evalEvalBC (F := K) K
      (Polynomial.C (Polynomial.C ((↑C.u⁻¹ : K) ^ 2) * (X - Polynomial.C C.r)) : K[X][Y]) x y =
      (↑C.u⁻¹ : K) ^ 2 * (x - C.r) := by
    simp [evalEvalBC, Polynomial.evalEval]
  have e2 : evalEvalBC (F := K) K
      (Polynomial.C (Polynomial.C ((↑C.u⁻¹ : K) ^ 3)) *
        (X - Polynomial.C (Polynomial.C C.s * X) +
          Polynomial.C (Polynomial.C (C.s * C.r - C.t))) : K[X][Y]) x y =
      (↑C.u⁻¹ : K) ^ 3 * (y - C.s * x + (C.s * C.r - C.t)) := by
    simp [evalEvalBC, Polynomial.evalEval]
  refine ⟨by rw [e0]; exact one_ne_zero, by rw [e0]; exact one_ne_zero, ?_⟩
  obtain ⟨h', hP⟩ := vcAddEquiv_some C E₀ x y h
  exact exists_eq_some hP (by rw [e0, e1, div_one]) (by rw [e0, e2, div_one])

theorem vcAddEquiv_symm_mem (C : VariableChange K) (E₀ : WeierstrassCurve K) :
    ((vcAddEquiv C E₀).symm.toAddMonoidHom :
        ((C • E₀).baseChange K).toAffine.Point →+ (E₀.baseChange K).toAffine.Point) ∈
      rationalHomSet K (C • E₀) E₀ := by
  right
  refine ⟨Polynomial.C (Polynomial.C ((C.u : K) ^ 2) * X + Polynomial.C C.r), 1,
    Polynomial.C (Polynomial.C ((C.u : K) ^ 3)) * X +
      Polynomial.C (Polynomial.C ((C.u : K) ^ 2 * C.s) * X + Polynomial.C C.t), 1, ∅,
    Set.finite_empty, fun x' y' h' _ => ?_⟩
  have e0 : evalEvalBC (F := K) K (1 : K[X][Y]) x' y' = 1 := by
    simp [evalEvalBC, Polynomial.evalEval]
  have e1 : evalEvalBC (F := K) K
      (Polynomial.C (Polynomial.C ((C.u : K) ^ 2) * X + Polynomial.C C.r) : K[X][Y]) x' y' =
      (C.u : K) ^ 2 * x' + C.r := by
    simp [evalEvalBC, Polynomial.evalEval]
  have e2 : evalEvalBC (F := K) K
      (Polynomial.C (Polynomial.C ((C.u : K) ^ 3)) * X +
        Polynomial.C (Polynomial.C ((C.u : K) ^ 2 * C.s) * X + Polynomial.C C.t) : K[X][Y]) x' y' =
      (C.u : K) ^ 3 * y' + ((C.u : K) ^ 2 * C.s * x' + C.t) := by
    simp [evalEvalBC, Polynomial.evalEval]
  refine ⟨by rw [e0]; exact one_ne_zero, by rw [e0]; exact one_ne_zero, ?_⟩
  set e := vcAddEquiv C E₀
  set P := e.symm (.some x' y' h') with hPdef
  have hP0 : P ≠ 0 := by
    intro h0
    have : e P = e 0 := by rw [h0]
    rw [hPdef, AddEquiv.apply_symm_apply, _root_.map_zero] at this
    exact Affine.Point.some_ne_zero _ this
  rcases hPxy : P with _ | ⟨x, y, h⟩
  · exact absurd hPxy hP0
  · obtain ⟨h'', hexy⟩ := vcAddEquiv_some C E₀ x y h
    have key : e (.some x y h) = .some x' y' h' := by
      rw [← hPxy, hPdef, AddEquiv.apply_symm_apply]
    rw [hexy] at key
    obtain ⟨hx, hy⟩ := Affine.Point.some.inj key
    have hw : (↑C.u⁻¹ : K) = (C.u : K)⁻¹ := Units.val_inv_eq_inv_val C.u
    have hu0 : (C.u : K) ≠ 0 := C.u.ne_zero
    have hPe : e.symm.toAddMonoidHom (.some x' y' h') = .some x y h := by
      show e.symm (.some x' y' h') = .some x y h
      rw [← hPdef]; exact hPxy
    refine exists_eq_some hPe ?_ ?_
    · rw [e0, e1, div_one, ← hx, hw]
      field_simp
      ring
    · rw [e0, e2, div_one, ← hx, ← hy, hw]
      field_simp
      ring

theorem vS_mem {C : VariableChange K} {E₀ V : WeierstrassCurve K} (h : C • E₀ = V) :
    ((vS h).toAddMonoidHom : (E₀.baseChange K).toAffine.Point →+ (V.baseChange K).toAffine.Point) ∈
      rationalHomSet K E₀ V := by
  subst h
  have : (vS (rfl : C • E₀ = C • E₀)).toAddMonoidHom = (vcAddEquiv C E₀).toAddMonoidHom := by
    ext P; rfl
  rw [this]
  exact vcAddEquiv_mem C E₀

theorem vS_symm_mem {C : VariableChange K} {E₀ V : WeierstrassCurve K} (h : C • E₀ = V) :
    ((vS h).symm.toAddMonoidHom :
        (V.baseChange K).toAffine.Point →+ (E₀.baseChange K).toAffine.Point) ∈
      rationalHomSet K V E₀ := by
  subst h
  have : (vS (rfl : C • E₀ = C • E₀)).symm.toAddMonoidHom = (vcAddEquiv C E₀).symm.toAddMonoidHom := by
    ext P; rfl
  rw [this]
  exact vcAddEquiv_symm_mem C E₀

theorem conj_vS_mem {C : VariableChange K} {E₀ V : WeierstrassCurve K} (h : C • E₀ = V)
    {β : E₀.toAffine.Point →+ E₀.toAffine.Point} (hβ : β ∈ rationalHomSet K E₀ E₀) :
    ((vS h).toAddMonoidHom.comp (β.comp (vS h).symm.toAddMonoidHom) :
        V.toAffine.Point →+ V.toAffine.Point) ∈ rationalHomSet K V V :=
  WeierstrassCurve.comp_mem_rationalHomSet K V E₀ V
    (WeierstrassCurve.comp_mem_rationalHomSet K V E₀ E₀ (vS_symm_mem h) hβ) (vS_mem h)

end VarChange

section Place

local notation "ℚbar" => AlgebraicClosure ℚ

variable {A : ValuationSubring ℚbar} [DecidableEq ℚbar] [DecidableEq (ResidueField A)]

theorem isElliptic_map_subtype {L : Type*} [Field L] {B : ValuationSubring L}
    (E : WeierstrassCurve B) (hΔ : (E.map (residue B)).Δ ≠ 0) :
    (E.map B.subtype).IsElliptic := by
  have hu : IsUnit E.Δ := (map_residue_Δ_ne_zero_iff E).mp hΔ
  rw [WeierstrassCurve.isElliptic_iff, WeierstrassCurve.map_Δ]
  exact hu.map B.subtype

theorem isElliptic_map_residue {L : Type*} [Field L] {B : ValuationSubring L}
    (E : WeierstrassCurve B) (hΔ : (E.map (residue B)).Δ ≠ 0) :
    (E.map (residue B)).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]; exact isUnit_iff_ne_zero.mpr hΔ

def redW (E : WeierstrassCurve A) (hΔ : (E.map (residue A)).Δ ≠ 0)
    {X : WeierstrassCurve (ResidueField A)} {v : VariableChange (ResidueField A)}
    (hv : v • E.map (residue A) = X) :
    (E.map A.subtype).toAffine.Point →+ X.toAffine.Point :=
  (vS hv).toAddMonoidHom.comp (reduceHom hΔ)

theorem redW_apply (E : WeierstrassCurve A) (hΔ : (E.map (residue A)).Δ ≠ 0)
    {X : WeierstrassCurve (ResidueField A)} {v : VariableChange (ResidueField A)}
    (hv : v • E.map (residue A) = X) (P : (E.map A.subtype).toAffine.Point) :
    redW E hΔ hv P = (Affine.Point.equivOfVariableChangeEq hv).symm (reduceHom hΔ P) :=
  vS_apply hv _

theorem exists_reduce (E₁ E₂ : WeierstrassCurve A)
    (hΔ₁ : (E₁.map (residue A)).Δ ≠ 0) (hΔ₂ : (E₂.map (residue A)).Δ ≠ 0)
    {X₁ X₂ : WeierstrassCurve (ResidueField A)} {v₁ v₂ : VariableChange (ResidueField A)}
    (hv₁ : v₁ • E₁.map (residue A) = X₁) (hv₂ : v₂ • E₂.map (residue A) = X₂)
    {μ : (E₁.map A.subtype).toAffine.Point →+ (E₂.map A.subtype).toAffine.Point}
    (hμ : μ ∈ rationalHomSet ℚbar (E₁.map A.subtype) (E₂.map A.subtype)) :
    ∃ ν : X₁.toAffine.Point →+ X₂.toAffine.Point, ν ∈ rationalHomSet (ResidueField A) X₁ X₂ ∧
      (redW E₂ hΔ₂ hv₂).comp μ = ν.comp (redW E₁ hΔ₁ hv₁) ∧ (μ ≠ 0 → ν ≠ 0) := by
  obtain ⟨ν₀, hν₀, hcomm, hne⟩ :=
    WeierstrassCurve.exists_mem_rationalHomSet_reduceHom_comp_eq_comp_reduceHom E₁ E₂ hΔ₁ hΔ₂ hμ
  refine ⟨(vS hv₂).toAddMonoidHom.comp (ν₀.comp (vS hv₁).symm.toAddMonoidHom), ?_, ?_, ?_⟩
  · exact WeierstrassCurve.comp_mem_rationalHomSet (ResidueField A) X₁ (E₂.map (residue A)) X₂
      (WeierstrassCurve.comp_mem_rationalHomSet (ResidueField A) X₁ (E₁.map (residue A))
        (E₂.map (residue A)) (vS_symm_mem hv₁) hν₀) (vS_mem hv₂)
  · ext P
    have := DFunLike.congr_fun hcomm P
    simp only [AddMonoidHom.coe_comp, Function.comp_apply] at this
    show (vS hv₂) (reduceHom hΔ₂ (μ P)) =
      (vS hv₂) (ν₀ ((vS hv₁).symm ((vS hv₁) (reduceHom hΔ₁ P))))
    rw [this, AddEquiv.symm_apply_apply]
    rfl
  · intro hμ0 h0
    apply hne hμ0
    ext Q
    have h1 := DFunLike.congr_fun h0 (vS hv₁ Q)
    have h2 : (vS hv₂) (ν₀ ((vS hv₁).symm (vS hv₁ Q))) = 0 := h1
    rw [AddEquiv.symm_apply_apply] at h2
    have h3 : ν₀ Q = 0 := by
      have := congrArg (vS hv₂).symm h2
      rwa [AddEquiv.symm_apply_apply, map_zero] at this
    rw [AddMonoidHom.zero_apply]; exact h3

theorem eq_zero_of_comp_redW (E : WeierstrassCurve A) (hΔ : (E.map (residue A)).Δ ≠ 0)
    {X₁ X₂ : WeierstrassCurve (ResidueField A)} [X₁.IsElliptic] [X₂.IsElliptic]
    [IsAlgClosed (ResidueField A)]
    {v : VariableChange (ResidueField A)} (hv : v • E.map (residue A) = X₁)
    {δ : X₁.toAffine.Point →+ X₂.toAffine.Point} (hδ : δ ∈ rationalHomSet (ResidueField A) X₁ X₂)
    (h : δ.comp (redW E hΔ hv) = 0) : δ = 0 := by
  by_contra hδ0
  obtain ⟨σ, -, n, hn, hdual⟩ :
      ∃ σ ∈ rationalHomSet (ResidueField A) X₂ X₁, ∃ n : ℤ, 0 < n ∧ AddMonoidHom.IsDualPair δ σ n :=
    WeierstrassCurve.exists_isDualPair_of_mem_rationalHomSet (ResidueField A) X₁ X₂ hδ hδ0
  obtain ⟨ℓ, hℓ, hnℓ, hℓk⟩ := exists_prime_gt_natCast_ne_zero (ResidueField A) n.natAbs
  obtain ⟨Q₀, hQ₀0, hQ₀ℓ⟩ := exists_ne_zero_nsmul_eq_zero X₁ hℓ hℓk

  set Q₁ : (E.map (residue A)).toAffine.Point := (vS hv).symm Q₀ with hQ₁
  have hQ₁ℓ : ℓ • Q₁ = 0 := by
    rw [← natCast_zsmul, hQ₁, ← map_zsmul, hQ₀ℓ, map_zero]
  obtain ⟨Q, -, hQ⟩ :=
    WeierstrassCurve.exists_reduceHom_eq_of_nsmul_eq_zero_of_natCast_ne_zero A E hΔ hℓk Q₁ hQ₁ℓ
  have hδQ₀ : δ Q₀ = 0 := by
    have := DFunLike.congr_fun h Q
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, redW, AddEquiv.coe_toAddMonoidHom, hQ,
      hQ₁, AddEquiv.apply_symm_apply, AddMonoidHom.zero_apply] at this
    exact this
  have hnQ₀ : n • Q₀ = 0 := by rw [← hdual.comp_left Q₀, hδQ₀, map_zero]
  exact hQ₀0 (eq_zero_of_prime_zsmul_of_zsmul hℓ hn.ne' hnℓ hQ₀ℓ hnQ₀)

end Place

section Kronecker

local notation "ℚbar" => AlgebraicClosure ℚ

variable {A : ValuationSubring ℚbar}

theorem exists_residue_of_isRoot_fibrePoly [CharP (ResidueField A) 2]
    (data : ModularCurve.ModularPolynomialData 2) (a : A) {j' : ℚbar}
    (hroot : (ModularCurve.fibrePoly data.Φ (a : ℚbar)).IsRoot j') :
    ∃ b : A, (b : ℚbar) = j' ∧
      ((residue A a) ^ 2 = residue A b ∨ residue A a = (residue A b) ^ 2) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set fA : Polynomial A := data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom A) a) with hfA
  have hmonic : fA.Monic := data.monic.map _
  have hcomp : ∀ {S : Type} [CommRing S] (g : A →+* S),
      (g.comp (Polynomial.eval₂RingHom (Int.castRingHom A) a) : Polynomial ℤ →+* S) =
        Polynomial.eval₂RingHom (Int.castRingHom S) (g a) := by
    intro S _ g
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp
  have hmapL : fA.map A.subtype = ModularCurve.fibrePoly data.Φ (a : ℚbar) := by
    rw [hfA, Polynomial.map_map, ModularCurve.fibrePoly, hcomp]
    rfl
  have hint : _root_.IsIntegral A j' := by
    refine ⟨fA, hmonic, ?_⟩
    have : (algebraMap A ℚbar) = A.subtype := rfl
    rw [this, ← Polynomial.eval_map, hmapL]
    exact hroot
  obtain ⟨b, hb⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := ℚbar)).mp hint
  have hb' : (b : ℚbar) = j' := hb
  refine ⟨b, hb', ?_⟩
  have hevalA : fA.eval b = 0 := by
    have h1 : A.subtype (fA.eval b) = 0 := by
      rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, hmapL]
      show (ModularCurve.fibrePoly data.Φ (a : ℚbar)).eval (b : ℚbar) = 0
      rw [hb']
      exact hroot
    exact Subtype.ext h1
  have hκ : (fA.map (residue A)).IsRoot (residue A b) := by
    rw [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_at_apply, hevalA, map_zero]
  have hmapκ : fA.map (residue A) = ModularCurve.fibrePoly data.Φ (residue A a) := by
    rw [hfA, Polynomial.map_map, ModularCurve.fibrePoly, hcomp]
  have hK : ModularCurve.reduceModBivar 2 data.Φ =
      (Polynomial.C Polynomial.X ^ 2 - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ 2) :=
    ModularCurve.modularPolynomial_kronecker 2 data
  rw [hmapκ, ModularCurve.fibrePoly_eq_map_reduceModBivar (ℓ := 2), hK] at hκ
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C,
    Polynomial.map_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
    Polynomial.IsRoot, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow, mul_eq_zero, sub_eq_zero] at hκ
  rcases hκ with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem algebraRat_eq :
    (AlgebraicClosure.instAlgebra ℚ : Algebra ℚ ℚbar) = (inferInstance : Algebra ℚ ℚbar) :=
  Subsingleton.elim _ _

theorem isAlgebraic_rat : Algebra.IsAlgebraic ℚ ℚbar := by
  have h := AlgebraicClosure.isAlgebraic (k := ℚ)
  rwa [algebraRat_eq] at h

theorem isAlgebraic_int : @Algebra.IsAlgebraic ℤ ℚbar _ _ (Ring.toIntAlgebra ℚbar) := by
  haveI := isAlgebraic_rat
  have h : Algebra.IsAlgebraic ℤ ℚbar :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := ℚbar)).mpr inferInstance
  convert h <;> first | rfl | exact Subsingleton.elim _ _

end Kronecker

section Main

local notation "ℚbar" => AlgebraicClosure ℚ

variable (A : ValuationSubring ℚbar) [DecidableEq ℚbar] [DecidableEq (ResidueField A)]
  [CharP (ResidueField A) 2]

theorem conj_charPoly {G H : Type*} [AddCommGroup G] [AddCommGroup H] (e : G ≃+ H)
    {α : G →+ G} {t q : ℤ} (h : α.comp α + q • AddMonoidHom.id G = t • α) :
    (e.toAddMonoidHom.comp (α.comp e.symm.toAddMonoidHom)).comp
        (e.toAddMonoidHom.comp (α.comp e.symm.toAddMonoidHom)) + q • AddMonoidHom.id H =
      t • (e.toAddMonoidHom.comp (α.comp e.symm.toAddMonoidHom)) := by
  ext Q
  have h' := DFunLike.congr_fun h (e.symm Q)
  simp only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply, AddMonoidHom.zsmul_apply,
    AddMonoidHom.id_apply] at h' ⊢
  change e (α (e.symm (e (α (e.symm Q))))) + q • Q = t • e (α (e.symm Q))
  rw [e.symm_apply_apply, ← map_zsmul, ← h', map_add, map_zsmul, e.apply_symm_apply]

theorem main (W : WeierstrassCurve (ResidueField A)) [W.IsElliptic]
    {α₀ : W.toAffine.Point →+ W.toAffine.Point}
    (hα₀ : α₀ ∈ rationalHomSet (ResidueField A) W W) (t q : ℤ)
    (hchar : α₀.comp α₀ + q • AddMonoidHom.id _ = t • α₀) (hirr : ∀ m : ℤ, m ^ 2 - t * m + q ≠ 0)
    (ht : Odd t) (hq : Even q)
    (E : WeierstrassCurve A) (hΔ : (E.map (residue A)).Δ ≠ 0) (v : VariableChange (ResidueField A))
    (hv : v • E.map (residue A) = W)
    {γ : (E.map A.subtype).toAffine.Point →+ (E.map A.subtype).toAffine.Point}
    (hγ : γ ∈ rationalHomSet ℚbar (E.map A.subtype) (E.map A.subtype))
    (hγred : ∀ P : (E.map A.subtype).toAffine.Point,
      (Affine.Point.equivOfVariableChangeEq hv).symm (reduceHom hΔ (γ P)) =
        ((2 : ℤ) • α₀) ((Affine.Point.equivOfVariableChangeEq hv).symm (reduceHom hΔ P))) :
    ∃ (E₁ : WeierstrassCurve A) (hΔ₁ : (E₁.map (residue A)).Δ ≠ 0)
      (v₁ : VariableChange (ResidueField A)) (hv₁ : v₁ • E₁.map (residue A) = W),
      ∃ α ∈ rationalHomSet ℚbar (E₁.map A.subtype) (E₁.map A.subtype),
        ∀ P : (E₁.map A.subtype).toAffine.Point,
          (Affine.Point.equivOfVariableChangeEq hv₁).symm (reduceHom hΔ₁ (α P)) =
            α₀ ((Affine.Point.equivOfVariableChangeEq hv₁).symm (reduceHom hΔ₁ P)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsAlgClosed (ResidueField A) :=
    ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  haveI hEL : (E.map A.subtype).IsElliptic := isElliptic_map_subtype E hΔ
  haveI hEr : (E.map (residue A)).IsElliptic := isElliptic_map_residue E hΔ
  haveI hEA : E.IsElliptic := ⟨(map_residue_Δ_ne_zero_iff E).mp hΔ⟩
  have h2L : (2 : ℚbar) ≠ 0 := two_ne_zero

  have hred : ∀ P, redW E hΔ hv P = (Affine.Point.equivOfVariableChangeEq hv).symm (reduceHom hΔ P) :=
    redW_apply E hΔ hv
  have hγred' : ∀ P, redW E hΔ hv (γ P) = (2 : ℤ) • α₀ (redW E hΔ hv P) := fun P => by
    rw [hred, hred]; exact hγred P
  have hcharP : ∀ x : W.toAffine.Point, α₀ (α₀ x) = t • α₀ x - q • x := fun x => by
    have hc := DFunLike.congr_fun hchar x
    simp only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply, AddMonoidHom.zsmul_apply,
      AddMonoidHom.id_apply] at hc
    exact eq_sub_of_add_eq hc

  have hcharγ : γ.comp γ + (4 * q) • AddMonoidHom.id _ = (2 * t) • γ := by
    have hμmem : γ.comp γ + (4 * q) • AddMonoidHom.id _ - (2 * t) • γ ∈
        rationalHomSet ℚbar (E.map A.subtype) (E.map A.subtype) :=
      sub_mem_rationalHomSet
        (WeierstrassCurve.add_mem_rationalHomSet ℚbar _ _
          (WeierstrassCurve.comp_mem_rationalHomSet ℚbar _ _ _ hγ hγ)
          (zsmul_id_mem_rationalHomSet (k := ℚbar) (E.map A.subtype) _))
        (zsmul_mem_rationalHomSet hγ _)
    obtain ⟨ν, hν, hcomm, hne⟩ := exists_reduce E E hΔ hΔ hv hv hμmem
    have hν0 : ν.comp (redW E hΔ hv) = 0 := by
      rw [← hcomm]
      ext P
      have e1 := hγred' P
      have e2 := hγred' (γ P)
      rw [e1, map_zsmul] at e2
      show redW E hΔ hv (γ (γ P) + (4 * q) • P - (2 * t) • γ P) = 0
      rw [map_sub, map_add, map_zsmul, map_zsmul, e2, e1, hcharP]
      module
    have hν' : ν = 0 := eq_zero_of_comp_redW E hΔ hv hν hν0
    have hμ0 : γ.comp γ + (4 * q) • AddMonoidHom.id _ - (2 * t) • γ = 0 := by
      by_contra h; exact hne h hν'
    exact sub_eq_zero.mp hμ0

  by_cases hcase : ∀ P : (E.map A.subtype).toAffine.Point, (2 : ℤ) • P = 0 → γ P = 0
  ·
    obtain ⟨δ, hδ, hγδ⟩ : ∃ δ : (E.map A.subtype).toAffine.Point →+ (E.map A.subtype).toAffine.Point,
        δ ∈ rationalHomSet ℚbar (E.map A.subtype) (E.map A.subtype) ∧
        ∀ P : (E.map A.subtype).toAffine.Point, γ P = (2 : ℤ) • δ P := by
      obtain ⟨δ, hδ, h⟩ :=
        WeierstrassCurve.exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero ℚbar
          (E.map A.subtype) (E.map A.subtype) (N := 2) (by norm_num) hγ
          (fun P hP => hcase P hP)
      exact ⟨δ, hδ, fun P => h P⟩
    obtain ⟨δbar, hδbar, hcommδ, -⟩ := exists_reduce E E hΔ hΔ hv hv hδ
    have hcommδ' : ∀ P, redW E hΔ hv (δ P) = δbar (redW E hΔ hv P) := fun P =>
      DFunLike.congr_fun hcommδ P
    have hεmem : (2 : ℤ) • (δbar - α₀) ∈ rationalHomSet (ResidueField A) W W :=
      zsmul_mem_rationalHomSet (sub_mem_rationalHomSet hδbar hα₀) 2
    have hε : ((2 : ℤ) • (δbar - α₀)).comp (redW E hΔ hv) = 0 := by
      ext P
      have e1 : (2 : ℤ) • redW E hΔ hv (δ P) = redW E hΔ hv (γ P) := by
        rw [← map_zsmul, ← hγδ]
      show (2 : ℤ) • (δbar (redW E hΔ hv P) - α₀ (redW E hΔ hv P)) = 0
      rw [zsmul_sub, ← hcommδ', e1, hγred', sub_self]
    have h0 := eq_zero_of_comp_redW E hΔ hv hεmem hε
    have h1 : δbar - α₀ = 0 :=
      eq_zero_of_zsmul_eq_zero (sub_mem_rationalHomSet hδbar hα₀) two_ne_zero h0
    have h1x : ∀ x, δbar x = α₀ x := fun x => by
      have := DFunLike.congr_fun h1 x
      rwa [AddMonoidHom.sub_apply, AddMonoidHom.zero_apply, sub_eq_zero] at this
    refine ⟨E, hΔ, v, hv, δ, hδ, fun P => ?_⟩
    have goal' : redW E hΔ hv (δ P) = α₀ (redW E hΔ hv P) := by
      rw [hcommδ', h1x]
    rw [hred, hred] at goal'
    exact goal'

  push Not at hcase
  obtain ⟨P₁, hP₁, hγP₁⟩ := hcase
  obtain ⟨E', hE', π, π', α', hπ, hπ', hα', hπ'π, hππ', h2απ, hcharα', hΦ⟩ :=
    WeierstrassCurve.exists_mem_rationalHomSet_two_smul_comp_eq_comp_of_comp_self_add_smul_eq_smul
      h2L (E.map A.subtype) hγ t q hcharγ ⟨P₁, hP₁, hγP₁⟩
  haveI := hE'

  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData 2
  have hjEL : (E.map A.subtype).j = (E.j : ℚbar) := E.map_j A.subtype
  obtain ⟨jA, hjA, hres⟩ :=
    exists_residue_of_isRoot_fibrePoly data E.j (j' := E'.j) (by rw [← hjEL]; exact hΦ data)

  obtain ⟨n, hn⟩ : ∃ n : ℕ,
      iterateFrobenius (ResidueField A) 2 n (E.map (residue A)).j = residue A jA := by
    have hjr : (E.map (residue A)).j = residue A E.j := E.map_j (residue A)
    rw [hjr]
    rcases hres with h | h
    · exact ⟨1, by rw [iterateFrobenius_def, pow_one, h]⟩
    · haveI := isAlgebraic_int
      obtain ⟨N, hN, hpow⟩ :=
        ValuationSubring.exists_pow_prime_pow_eq_self_of_isAlgebraic A 2 (residue A jA)
      refine ⟨N - 1, ?_⟩
      rw [iterateFrobenius_def, h, ← pow_mul, ← pow_succ', Nat.sub_add_cancel hN, hpow]

  haveI hW₀ : ((E.map (residue A)).map (iterateFrobenius (ResidueField A) 2 n)).IsElliptic :=
    inferInstance
  have hjW₀ : residue A jA = ((E.map (residue A)).map (iterateFrobenius (ResidueField A) 2 n)).j := by
    rw [(E.map (residue A)).map_j, hn]
  obtain ⟨E'', hE''L, hE''r, hj''⟩ :=
    WeierstrassCurve.exists_map_residue_eq_and_map_subtype_j_eq A
      ((E.map (residue A)).map (iterateFrobenius (ResidueField A) 2 n)) jA hjW₀
  haveI := hE''L
  have hΔ'' : (E''.map (residue A)).Δ ≠ 0 := by rw [hE''r]; exact (WeierstrassCurve.isUnit_Δ _).ne_zero

  obtain ⟨u, hu⟩ := WeierstrassCurve.exists_variableChange_of_j_eq E' (E''.map A.subtype)
    (by rw [hj'', hjA])

  set π'' : (E.map A.subtype).toAffine.Point →+ (E''.map A.subtype).toAffine.Point :=
    (vS hu).toAddMonoidHom.comp π with hπ''def
  set α'' : (E''.map A.subtype).toAffine.Point →+ (E''.map A.subtype).toAffine.Point :=
    (vS hu).toAddMonoidHom.comp (α'.comp (vS hu).symm.toAddMonoidHom) with hα''def
  have hπ''mem : π'' ∈ rationalHomSet ℚbar (E.map A.subtype) (E''.map A.subtype) :=
    WeierstrassCurve.comp_mem_rationalHomSet ℚbar (E.map A.subtype) E' (E''.map A.subtype) hπ
      (vS_mem hu)
  have hα''mem : α'' ∈ rationalHomSet ℚbar (E''.map A.subtype) (E''.map A.subtype) :=
    conj_vS_mem hu hα'
  have hπ''ne : π'' ≠ 0 := by
    intro h0
    have hπ0 : π = 0 := by
      ext P
      have := DFunLike.congr_fun h0 P
      simp only [hπ''def, AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
        AddMonoidHom.zero_apply] at this
      have := congrArg (vS hu).symm this
      rwa [AddEquiv.symm_apply_apply, map_zero] at this
    have h2 : (2 • AddMonoidHom.id _ : (E.map A.subtype).toAffine.Point →+ _) = 0 := by
      rw [← hπ'π, hπ0, AddMonoidHom.comp_zero]
    have h2' : ((2 : ℤ) • AddMonoidHom.id _ : (E.map A.subtype).toAffine.Point →+ _) = 0 := by
      rw [← h2]; ext P; simp [two_nsmul, two_zsmul]
    exact zsmul_id_ne_zero (k := ℚbar) (E.map A.subtype) two_ne_zero h2'
  have h2απ'' : ∀ P, (2 : ℤ) • α'' (π'' P) = π'' (γ P) := fun P => by
    have := DFunLike.congr_fun h2απ P
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.zsmul_apply] at this
    simp only [hπ''def, hα''def, AddMonoidHom.coe_comp, Function.comp_apply,
      AddEquiv.coe_toAddMonoidHom, AddEquiv.symm_apply_apply, ← map_zsmul, this]
  have hcharα'' : α''.comp α'' + q • AddMonoidHom.id _ = t • α'' := conj_charPoly (vS hu) hcharα'
  have hcharα''P : ∀ Q, α'' (α'' Q) + q • Q - t • α'' Q = 0 := fun Q => by
    have := DFunLike.congr_fun hcharα'' Q
    simp only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply, AddMonoidHom.zsmul_apply,
      AddMonoidHom.id_apply] at this
    rw [this, sub_self]

  have hv'' : v.map (iterateFrobenius (ResidueField A) 2 n) • E''.map (residue A) =
      W.map (iterateFrobenius (ResidueField A) 2 n) := by
    rw [hE''r, WeierstrassCurve.map_variableChange, hv]

  obtain ⟨ρ, hρ, hρcomm, hρne⟩ := exists_reduce E E'' hΔ hΔ'' hv hv'' hπ''mem
  have hρ0 : ρ ≠ 0 := hρne hπ''ne
  obtain ⟨αbar, hαbar, hαcomm, -⟩ := exists_reduce E'' E'' hΔ'' hΔ'' hv'' hv'' hα''mem
  have hρcomm' : ∀ P, redW E'' hΔ'' hv'' (π'' P) = ρ (redW E hΔ hv P) := fun P =>
    DFunLike.congr_fun hρcomm P
  have hαcomm' : ∀ Q, redW E'' hΔ'' hv'' (α'' Q) = αbar (redW E'' hΔ'' hv'' Q) := fun Q =>
    DFunLike.congr_fun hαcomm Q

  have hi : αbar.comp ρ = ρ.comp α₀ := by
    have hδmem : αbar.comp ρ - ρ.comp α₀ ∈
        rationalHomSet (ResidueField A) W (W.map (iterateFrobenius (ResidueField A) 2 n)) :=
      sub_mem_rationalHomSet (WeierstrassCurve.comp_mem_rationalHomSet _ _ _ _ hρ hαbar)
        (WeierstrassCurve.comp_mem_rationalHomSet _ _ _ _ hα₀ hρ)
    have hz : ((2 : ℤ) • (αbar.comp ρ - ρ.comp α₀)).comp (redW E hΔ hv) = 0 := by
      ext P
      have e3 : ρ (redW E hΔ hv (γ P)) = redW E'' hΔ'' hv'' (π'' (γ P)) := (hρcomm' (γ P)).symm
      show (2 : ℤ) • (αbar (ρ (redW E hΔ hv P)) - ρ (α₀ (redW E hΔ hv P))) = 0
      rw [zsmul_sub, ← hρcomm', ← hαcomm', ← map_zsmul (redW E'' hΔ'' hv''), h2απ'', ← map_zsmul ρ,
        ← hγred', e3, sub_self]
    have h0 := eq_zero_of_comp_redW E hΔ hv (zsmul_mem_rationalHomSet hδmem 2) hz
    have h1 := eq_zero_of_zsmul_eq_zero hδmem two_ne_zero h0
    ext x
    have := DFunLike.congr_fun h1 x
    rwa [AddMonoidHom.sub_apply, AddMonoidHom.zero_apply, sub_eq_zero] at this

  have hii : αbar.comp αbar + q • AddMonoidHom.id _ = t • αbar := by
    have hδmem : αbar.comp αbar + q • AddMonoidHom.id _ - t • αbar ∈
        rationalHomSet (ResidueField A) (W.map (iterateFrobenius (ResidueField A) 2 n))
          (W.map (iterateFrobenius (ResidueField A) 2 n)) :=
      sub_mem_rationalHomSet
        (WeierstrassCurve.add_mem_rationalHomSet _ _ _
          (WeierstrassCurve.comp_mem_rationalHomSet _ _ _ _ hαbar hαbar)
          (zsmul_id_mem_rationalHomSet (k := ResidueField A) _ _))
        (zsmul_mem_rationalHomSet hαbar _)
    have hz : (αbar.comp αbar + q • AddMonoidHom.id _ - t • αbar).comp (redW E'' hΔ'' hv'') = 0 := by
      ext Q
      show αbar (αbar (redW E'' hΔ'' hv'' Q)) + q • redW E'' hΔ'' hv'' Q - t • αbar (redW E'' hΔ'' hv'' Q) = 0
      rw [← hαcomm', ← hαcomm', ← map_zsmul (redW E'' hΔ'' hv''), ← map_zsmul (redW E'' hΔ'' hv''),
        ← map_add, ← map_sub, hcharα''P, map_zero]
    have h1 := eq_zero_of_comp_redW E'' hΔ'' hv'' hδmem hz
    ext x
    have := DFunLike.congr_fun h1 x
    change αbar (αbar x) + q • x - t • αbar x = 0 at this
    change αbar (αbar x) + q • x = t • αbar x
    exact eq_of_sub_eq_zero this

  have hq2 : ((2 : ℕ) : ℤ) ∣ q := by exact_mod_cast even_iff_two_dvd.mp hq
  have ht2 : ¬ ((2 : ℕ) : ℤ) ∣ t := by
    have : ¬ (2 : ℤ) ∣ t := by rw [← even_iff_two_dvd]; exact Int.not_even_iff_odd.mpr ht
    exact_mod_cast this
  obtain ⟨T, hT, h2T⟩ :=
    WeierstrassCurve.exists_ne_zero_and_char_nsmul_eq_zero_of_comp_self_add_smul_eq_smul_of_dvd_of_not_dvd
      2 W hα₀ t q hchar hirr hq2 ht2
  have hFTW := WeierstrassCurve.comp_ratPointHom_iterateFrobenius_eq_of_comp_eq_comp 2 n W hT h2T
    hρ hρ0 hα₀ hαbar hi
  exact WeierstrassCurve.exists_reduceHom_comp_eq_of_exists_reduceHom_comp_eq_map_iterateFrobenius
    2 A n W α₀ hFTW ⟨E'', hΔ'', v.map (iterateFrobenius (ResidueField A) 2 n), hv'', α'', hα''mem,
      fun P => by rw [← redW_apply, ← redW_apply]; exact hαcomm' P⟩

end Main

end WeierstrassCurve.TwoDescentPlace

end

open IsLocalRing in
theorem solution (A : ValuationSubring (AlgebraicClosure ℚ)) [DecidableEq (AlgebraicClosure ℚ)] [DecidableEq (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) 2] (W : WeierstrassCurve (IsLocalRing.ResidueField A)) [W.IsElliptic] {α₀ : W.toAffine.Point →+ W.toAffine.Point} (hα₀ : α₀ ∈ WeierstrassCurve.rationalHomSet (IsLocalRing.ResidueField A) W W) (t q : ℤ) (hchar : α₀.comp α₀ + q • AddMonoidHom.id _ = t • α₀) (hirr : ∀ m : ℤ, m ^ 2 - t * m + q ≠ 0) (ht : Odd t) (hq : Even q) (hlift : ∃ (E : WeierstrassCurve A) (hΔ : (E.map (IsLocalRing.residue A)).Δ ≠ 0) (v : WeierstrassCurve.VariableChange (IsLocalRing.ResidueField A)) (hv : v • E.map (IsLocalRing.residue A) = W), ∃ γ ∈ WeierstrassCurve.rationalHomSet (AlgebraicClosure ℚ) (E.map A.subtype) (E.map A.subtype), ∀ P : (E.map A.subtype).toAffine.Point, (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv).symm (WeierstrassCurve.reduceHom hΔ (γ P)) = ((2 : ℤ) • α₀) ((WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv).symm (WeierstrassCurve.reduceHom hΔ P))) : ∃ (E : WeierstrassCurve A) (hΔ : (E.map (IsLocalRing.residue A)).Δ ≠ 0) (v : WeierstrassCurve.VariableChange (IsLocalRing.ResidueField A)) (hv : v • E.map (IsLocalRing.residue A) = W), ∃ α ∈ WeierstrassCurve.rationalHomSet (AlgebraicClosure ℚ) (E.map A.subtype) (E.map A.subtype), ∀ P : (E.map A.subtype).toAffine.Point, (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv).symm (WeierstrassCurve.reduceHom hΔ (α P)) = α₀ ((WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hv).symm (WeierstrassCurve.reduceHom hΔ P)) := by
  obtain ⟨E, hΔ, v, hv, γ, hγ, hγred⟩ := hlift
  exact WeierstrassCurve.TwoDescentPlace.main A W hα₀ t q hchar hirr ht hq E hΔ v hv hγ hγred

end S_WeierstrassCurve_exists_variableChange_smul_eq_and_reduceHom_comp_eq_of_exists_reduceHom_comp_eq_two_smul_of_charP_two
end P2MW
export P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_and_reduceHom_comp_eq_of_exists_reduceHom_comp_eq_two_smul_of_charP_two (solution)
