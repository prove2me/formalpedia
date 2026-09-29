-- Prove2me | solution 1 for WeierstrassCurve.exists_mem_rationalHomSet_two_smul_comp_eq_comp_of_comp_self_add_smul_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/04632da1-19a0-5248-87d8-05178a52d094

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_VeluPointMap2
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_FibrePoly
import Theorems.Thm_WeierstrassCurve_exists_coe_eq_veluPointMap2_and_mem_rationalHomSet_and_comp_eq_two_smul
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient2_j
import Theorems.Thm_WeierstrassCurve_exists_enum_twoTorsion_veluQuotient2_discriminant_ne_zero
import Theorems.Thm_WeierstrassCurve_veluQuotient2_Delta_ne_zero
import Theorems.Thm_WeierstrassCurve_isElliptic_veluQuotient2_of_isElliptic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_two_smul_comp_eq_comp_of_comp_self_add_smul_eq_smul
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.pointAddEquivOfEq_refl WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.veluX_empty"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_two_smul_comp_eq_comp_of_comp_self_add_smul_eq_smul.WeierstrassCurve Polynomial"
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine isUnit_Δ Affine.negY mk.injEq a₃ a₁ mk Affine.Point.some Affine.Point.some.injEq toAffine Affine.Point Affine.equation_iff_nonsingular Affine.Point.some_ne_zero Δ Affine.equation_iff Affine.Point.neg_some baseChange j evalEvalBC IsRationallyRepresented rationalHomSet zero_mem_rationalHomSet id_mem_rationalHomSet veluPointMap2_some_of_eq veluPointMap2_some_of_ne veluQuotient2 veluGy exists_coe_eq_veluPointMap2_and_mem_rationalHomSet_and_comp_eq_two_smul exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero card_torsion_of_isAlgClosed surjective_of_mem_rationalHomSet comp_mem_rationalHomSet add_mem_rationalHomSet exists_enum_twoTorsion_veluQuotient2_discriminant_ne_zero veluQuotient2_Delta_ne_zero isElliptic_veluQuotient2_of_isElliptic"
namespace AscendTwoIsogeny
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
    exact absurd (Nat.dvd_one.mp h1) (CharP.ringChar_ne_one)
  · exact ⟨ℓ₁, hp₁, by omega, hz₁⟩

variable {k} [DecidableEq k] [IsAlgClosed k]

theorem exists_ne_zero_zsmul_eq_zero (W : WeierstrassCurve k) [W.IsElliptic] {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hℓk : (ℓ : k) ≠ 0) : ∃ Q : W.toAffine.Point, Q ≠ 0 ∧ (ℓ : ℤ) • Q = 0 := by
  have hcard : Nat.card (Submodule.torsionBy ℤ (W.baseChange k).toAffine.Point (ℓ : ℤ)) = ℓ ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed (K := k) W hℓk
  set Tor := Submodule.torsionBy ℤ (W.baseChange k).toAffine.Point (ℓ : ℤ)
  haveI : Finite Tor := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hℓ.ne_zero)
  have hnt : Nontrivial Tor := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    exact Nat.one_lt_pow two_ne_zero hℓ.one_lt
  obtain ⟨⟨R, hR⟩, hR1⟩ := exists_ne (0 : Tor)
  exact ⟨R, fun h => hR1 (Subtype.ext h), (Submodule.mem_torsionBy_iff _ _).mp hR⟩

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

theorem zsmul_id_ne_zero (W : WeierstrassCurve k) [W.IsElliptic] {N : ℤ} (hN : N ≠ 0) :
    (N • AddMonoidHom.id _ : W.toAffine.Point →+ W.toAffine.Point) ≠ 0 := by
  intro h
  obtain ⟨ℓ, hℓ, hNℓ, hℓk⟩ := exists_prime_gt_natCast_ne_zero k N.natAbs
  obtain ⟨Q, hQ0, hQℓ⟩ := exists_ne_zero_zsmul_eq_zero W hℓ hℓk
  have hNQ : N • Q = 0 := by
    have := DFunLike.congr_fun h Q
    simpa using this
  exact hQ0 (eq_zero_of_prime_zsmul_of_zsmul hℓ hN hNℓ hQℓ hNQ)

theorem exists_zsmul_eq (W : WeierstrassCurve k) [W.IsElliptic] {N : ℤ} (hN : N ≠ 0)
    (Q : W.toAffine.Point) : ∃ P : W.toAffine.Point, N • P = Q := by
  obtain ⟨P, hP⟩ : ∃ P : W.toAffine.Point, (N • AddMonoidHom.id _ : W.toAffine.Point →+ _) P = Q :=
    WeierstrassCurve.surjective_of_mem_rationalHomSet k
      (zsmul_id_mem_rationalHomSet (k := k) W N) (zsmul_id_ne_zero W hN) Q
  exact ⟨P, by exact hP⟩

end Torsion

section TorsionImage

variable {k : Type*} [Field k] [DecidableEq k] [IsAlgClosed k]

theorem eq_zero_of_zsmul_eq_zero {W₁ W₂ : WeierstrassCurve k} [W₁.IsElliptic] [W₂.IsElliptic]
    {δ : W₁.toAffine.Point →+ W₂.toAffine.Point} (hδ : δ ∈ rationalHomSet k W₁ W₂)
    {N : ℤ} (hN : N ≠ 0) (h : N • δ = 0) : δ = 0 := by
  by_contra hδ0
  obtain ⟨ℓ, hℓ, hMℓ, hℓk⟩ := exists_prime_gt_natCast_ne_zero k N.natAbs
  obtain ⟨Q, hQ0, hQℓ⟩ := exists_ne_zero_zsmul_eq_zero W₂ hℓ hℓk
  obtain ⟨P, hP⟩ : ∃ P : W₁.toAffine.Point, δ P = Q :=
    WeierstrassCurve.surjective_of_mem_rationalHomSet k hδ hδ0 Q
  have hNQ : N • Q = 0 := by
    have := DFunLike.congr_fun h P
    rwa [AddMonoidHom.zsmul_apply, hP, AddMonoidHom.zero_apply] at this
  exact hQ0 (eq_zero_of_prime_zsmul_of_zsmul hℓ hN hMℓ hQℓ hNQ)

end TorsionImage

section TwoTorsion

theorem some_congr {R : Type*} [CommRing R] {V : Affine R} {x₁ x₂ y₁ y₂ : R}
    (hx : x₁ = x₂) (hy : y₁ = y₂) (h₁ : V.Nonsingular x₁ y₁) (h₂ : V.Nonsingular x₂ y₂) :
    Affine.Point.some x₁ y₁ h₁ = Affine.Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

variable {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] (h2 : (2 : K) ≠ 0)
  (E : WeierstrassCurve K) [E.IsElliptic]

include h2 in

theorem two_torsion_cases {Q₀ P₁ : E.toAffine.Point} (hQ₀ : (2 : ℤ) • Q₀ = 0) (hP₁ : (2 : ℤ) • P₁ = 0)
    (hQ₀0 : Q₀ ≠ 0) (hP₁0 : P₁ ≠ 0) (hne : P₁ ≠ Q₀) (T : E.toAffine.Point) (hT : (2 : ℤ) • T = 0) :
    T = 0 ∨ T = Q₀ ∨ T = P₁ ∨ T = P₁ + Q₀ := by
  set S := Submodule.torsionBy ℤ E.toAffine.Point ((2 : ℕ) : ℤ) with hS
  have hcard : Nat.card S = 2 ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed (K := K) E (n := 2) (by exact_mod_cast h2)
  haveI : Finite S := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Fintype S := Fintype.ofFinite S
  have hcard' : Fintype.card S = 4 := by rw [← Nat.card_eq_fintype_card, hcard]; norm_num
  have mem : ∀ {X : E.toAffine.Point}, (2 : ℤ) • X = 0 → X ∈ S :=
    fun {X} hX => (Submodule.mem_torsionBy_iff _ _).mpr (by exact_mod_cast hX)
  have hPQ : (2 : ℤ) • (P₁ + Q₀) = 0 := by rw [zsmul_add, hP₁, hQ₀, add_zero]
  let s0 : S := ⟨0, mem (by simp)⟩
  let sQ : S := ⟨Q₀, mem hQ₀⟩
  let sP : S := ⟨P₁, mem hP₁⟩
  let sPQ : S := ⟨P₁ + Q₀, mem hPQ⟩
  have hPQ0 : P₁ + Q₀ ≠ 0 := by
    intro h
    have h' : P₁ = -Q₀ := eq_neg_of_add_eq_zero_left h
    apply hne
    rw [h']

    have : Q₀ + Q₀ = 0 := by rw [← two_zsmul, hQ₀]
    exact (neg_eq_of_add_eq_zero_left this)
  have hPQQ : P₁ + Q₀ ≠ Q₀ := fun h => hP₁0 (by simpa using h)
  have hPQP : P₁ + Q₀ ≠ P₁ := fun h => hQ₀0 (by simpa using h)
  have huniv : (Finset.univ : Finset S) = {s0, sQ, sP, sPQ} := by
    symm
    apply Finset.eq_univ_of_card
    rw [hcard', Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton, sP, sPQ, Subtype.mk.injEq]
      exact fun h => hPQP h.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, sQ, sP, sPQ, Subtype.mk.injEq, not_or]
      exact ⟨fun h => hne h.symm, fun h => hPQQ h.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, s0, sQ, sP, sPQ, Subtype.mk.injEq, not_or]
      exact ⟨fun h => hQ₀0 h.symm, fun h => hP₁0 h.symm, fun h => hPQ0 h.symm⟩
  have hTmem : (⟨T, mem hT⟩ : S) ∈ (Finset.univ : Finset S) := Finset.mem_univ _
  rw [huniv] at hTmem
  simp only [Finset.mem_insert, Finset.mem_singleton, s0, sQ, sP, sPQ, Subtype.mk.injEq] at hTmem
  exact hTmem

omit [IsAlgClosed K] in

theorem y_eq_or_eq_negY {x y₁ y₂ : K} (h₁ : E.toAffine.Equation x y₁) (h₂ : E.toAffine.Equation x y₂) :
    y₁ = y₂ ∨ y₁ = E.toAffine.negY x y₂ := by
  have key : (y₁ - y₂) * (y₁ - E.toAffine.negY x y₂) = 0 := by
    rw [Affine.equation_iff] at h₁ h₂
    rw [Affine.negY]
    linear_combination h₁ - h₂
  rcases mul_eq_zero.mp key with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

omit [IsAlgClosed K] in

theorem veluGy_eq_zero_of_two_zsmul {x y : K} {h : E.toAffine.Nonsingular x y}
    (h2P : (2 : ℤ) • (Affine.Point.some x y h) = 0) : E.veluGy x y = 0 := by
  rw [two_zsmul, add_eq_zero_iff_eq_neg, Affine.Point.neg_some, Affine.Point.some.injEq] at h2P
  have hy := h2P.2
  show -(2 * y + E.a₁ * x + E.a₃) = 0
  rw [Affine.negY] at hy
  linear_combination -hy

end TwoTorsion

section Main

variable {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] (h2 : (2 : K) ≠ 0)
  (E : WeierstrassCurve K) [E.IsElliptic] {γ : E.toAffine.Point →+ E.toAffine.Point}
  (hγ : γ ∈ rationalHomSet K E E) (t q : ℤ)
  (hchar : γ.comp γ + (4 * q) • AddMonoidHom.id _ = (2 * t) • γ)
  (hne : ∃ P : E.toAffine.Point, (2 : ℤ) • P = 0 ∧ γ P ≠ 0)

include h2 hγ hchar hne in
theorem main : ∃ (E' : WeierstrassCurve K) (_ : E'.IsElliptic) (π : E.toAffine.Point →+ E'.toAffine.Point)
    (π' : E'.toAffine.Point →+ E.toAffine.Point) (α : E'.toAffine.Point →+ E'.toAffine.Point),
    π ∈ rationalHomSet K E E' ∧ π' ∈ rationalHomSet K E' E ∧ α ∈ rationalHomSet K E' E' ∧
    π'.comp π = 2 • AddMonoidHom.id _ ∧ π.comp π' = 2 • AddMonoidHom.id _ ∧
    ((2 : ℤ) • α).comp π = π.comp γ ∧ α.comp α + q • AddMonoidHom.id _ = t • α ∧
    ∀ data : ModularCurve.ModularPolynomialData 2, (ModularCurve.fibrePoly data.Φ E.j).IsRoot E'.j := by
  obtain ⟨P₁, hP₁, hγP₁⟩ := hne
  have hcharP : ∀ X, γ (γ X) = (2 * t) • γ X - (4 * q) • X := fun X => by
    have := DFunLike.congr_fun hchar X
    simp only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply, AddMonoidHom.zsmul_apply,
      AddMonoidHom.id_apply] at this
    exact eq_sub_of_add_eq this

  have hcharP' : ∀ X, γ (γ X) = t • γ ((2 : ℤ) • X) - q • ((2 : ℤ) • ((2 : ℤ) • X)) := fun X => by
    rw [hcharP, map_zsmul, smul_smul, smul_smul, smul_smul]
    module
  obtain ⟨Q₀, hQ₀def⟩ : ∃ Q₀, Q₀ = γ P₁ := ⟨_, rfl⟩
  have hQ₀2 : (2 : ℤ) • Q₀ = 0 := by rw [hQ₀def, ← map_zsmul, hP₁, map_zero]
  have hγQ₀ : γ Q₀ = 0 := by
    rw [hQ₀def, hcharP', hP₁, map_zero, smul_zero, smul_zero, smul_zero, sub_zero]
  have hQ₀0 : Q₀ ≠ 0 := by rw [hQ₀def]; exact hγP₁
  have hP₁0 : P₁ ≠ 0 := fun h => hγP₁ (by rw [h, map_zero])
  have hP₁Q₀ : P₁ ≠ Q₀ := fun h => hγP₁ (by rw [h, hγQ₀])

  obtain ⟨x₀, y₀, h₀, hQ₀xy⟩ : ∃ x₀ y₀ h₀, Q₀ = Affine.Point.some x₀ y₀ h₀ := by
    rcases hQ : Q₀ with _ | ⟨x₀, y₀, h₀⟩
    · exact absurd hQ hQ₀0
    · exact ⟨x₀, y₀, h₀, rfl⟩
  have hQeq : E.toAffine.Equation x₀ y₀ := h₀.1
  have hgy : E.veluGy x₀ y₀ = 0 := veluGy_eq_zero_of_two_zsmul E (by rw [← hQ₀xy]; exact hQ₀2)
  have hΔ' : (E.veluQuotient2 x₀ y₀).Δ ≠ 0 :=
    veluQuotient2_Delta_ne_zero (E.isUnit_Δ).ne_zero hQeq hgy
  haveI hE' : (E.veluQuotient2 x₀ y₀).IsElliptic := isElliptic_veluQuotient2_of_isElliptic hQeq hgy

  obtain ⟨π, hπcoe, hπ, ⟨π'₀, hπ'₀, hπ'π₀, hππ'₀⟩, hUP⟩ :=
    WeierstrassCurve.exists_coe_eq_veluPointMap2_and_mem_rationalHomSet_and_comp_eq_two_smul
      h2 E hQeq hgy hΔ'
  obtain ⟨π', hπ', hπ'π, hππ'⟩ :
      ∃ π' : (E.veluQuotient2 x₀ y₀).toAffine.Point →+ E.toAffine.Point,
        π' ∈ rationalHomSet K (E.veluQuotient2 x₀ y₀) E ∧
          π'.comp π = 2 • AddMonoidHom.id _ ∧ π.comp π' = 2 • AddMonoidHom.id _ :=
    ⟨π'₀, hπ'₀, hπ'π₀, hππ'₀⟩

  have hπQ₀ : π Q₀ = 0 := by
    rw [hQ₀xy, hπcoe]; exact veluPointMap2_some_of_eq h2 hQeq hgy hΔ' h₀ rfl

  have hker2 : ∀ P, π P = 0 → (2 : ℤ) • P = 0 := fun P hP => by
    have := DFunLike.congr_fun hπ'π P
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, hP, map_zero] at this
    have e : (2 • AddMonoidHom.id _ : E.toAffine.Point →+ E.toAffine.Point) P = (2 : ℤ) • P := by
      simp [two_nsmul, two_zsmul]
    rw [← e]
    exact this.symm

  have hcases := two_torsion_cases h2 E hQ₀2 hP₁ hQ₀0 hP₁0 hP₁Q₀
  have hγ2 : ∀ T, (2 : ℤ) • T = 0 → γ T = 0 ∨ γ T = Q₀ := fun T hT => by
    rcases hcases T hT with rfl | rfl | rfl | rfl
    · exact Or.inl (map_zero γ)
    · exact Or.inl hγQ₀
    · exact Or.inr hQ₀def.symm
    · right; rw [map_add, hγQ₀, add_zero, hQ₀def]
  have hπγ2 : ∀ T, (2 : ℤ) • T = 0 → π (γ T) = 0 := fun T hT => by
    rcases hγ2 T hT with h | h
    · rw [h, map_zero]
    · rw [h, hπQ₀]

  have hkerγ2 : ∀ T, (2 : ℤ) • T = 0 → γ T = 0 → T = 0 ∨ T = Q₀ := fun T hT hγT => by
    rcases hcases T hT with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hγT hγP₁
    · exfalso; apply hQ₀0
      rw [map_add, hγQ₀, add_zero] at hγT
      rw [hQ₀def]; exact hγT

  have hπP₁ : π P₁ ≠ 0 := by
    rcases hP : P₁ with _ | ⟨x₁, y₁, h₁⟩
    · exact absurd hP hP₁0
    · have hx₁ : x₁ ≠ x₀ := by
        intro hx
        subst hx
        apply hP₁Q₀
        rw [hP, hQ₀xy]
        rcases y_eq_or_eq_negY E h₁.1 hQeq with hy | hy
        · subst hy; rfl
        ·
          have hgy' : E.toAffine.negY x₁ y₀ = y₀ := by
            have e : E.veluGy x₁ y₀ = -(2 * y₀ + E.a₁ * x₁ + E.a₃) := rfl
            rw [Affine.negY]; linear_combination hgy - e
          rw [hgy'] at hy; subst hy; rfl
      rw [hπcoe, veluPointMap2_some_of_ne h2 hQeq hgy hΔ' h₁ hx₁]
      exact Affine.Point.some_ne_zero _
  have hkerπ : ∀ P, π P = 0 → P = 0 ∨ P = Q₀ := fun P hP => by
    rcases hcases P (hker2 P hP) with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hP hπP₁
    · exfalso; apply hπP₁; rwa [map_add, hπQ₀, add_zero] at hP

  obtain ⟨β', hβ', hfac⟩ := hUP (E.veluQuotient2 x₀ y₀) hE' (π.comp γ)
    (WeierstrassCurve.comp_mem_rationalHomSet K E E (E.veluQuotient2 x₀ y₀) hγ hπ)
    (fun T hT => by
      show π (γ T) = 0
      exact hπγ2 T (hker2 T hT))
  have hfac' : ∀ P, β' (π P) = π (γ P) := fun P => (DFunLike.congr_fun hfac P).symm

  have hπ0 : π ≠ 0 := fun h => hπP₁ (by rw [h]; rfl)
  have hsurj : Function.Surjective π := WeierstrassCurve.surjective_of_mem_rationalHomSet K hπ hπ0

  have hβ'2 : ∀ Q : (E.veluQuotient2 x₀ y₀).toAffine.Point, ((2 : ℕ) : ℤ) • Q = 0 → β' Q = 0 := by
    intro Q hQ
    obtain ⟨P, rfl⟩ := hsurj Q
    have hQ' : π ((2 : ℤ) • P) = 0 := by rw [map_zsmul]; exact_mod_cast hQ
    rw [hfac']
    rcases hkerπ _ hQ' with h | h
    · exact hπγ2 P h
    ·
      have hγP2 : (2 : ℤ) • γ P = 0 := by rw [← map_zsmul, h, hγQ₀]
      have hγγP : γ (γ P) = 0 := by
        rw [hcharP', h, hγQ₀, hQ₀2, smul_zero, smul_zero, sub_zero]
      rcases hkerγ2 (γ P) hγP2 hγγP with h' | h'
      · rw [h']; exact map_zero π
      · rw [h']; exact hπQ₀
  obtain ⟨α', hα', hβα⟩ :
      ∃ α' : (E.veluQuotient2 x₀ y₀).toAffine.Point →+ (E.veluQuotient2 x₀ y₀).toAffine.Point,
        α' ∈ rationalHomSet K (E.veluQuotient2 x₀ y₀) (E.veluQuotient2 x₀ y₀) ∧
          ∀ Q, β' Q = (2 : ℤ) • α' Q := by
    obtain ⟨α', h₁, h₂⟩ :=
      WeierstrassCurve.exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero K
        (E.veluQuotient2 x₀ y₀) (E.veluQuotient2 x₀ y₀) (N := 2) h2 hβ' hβ'2
    exact ⟨α', h₁, fun Q => h₂ Q⟩

  have hβ'char : ∀ Q, β' (β' Q) = (2 * t) • β' Q - (4 * q) • Q := by
    intro Q
    obtain ⟨P, rfl⟩ := hsurj Q
    rw [hfac', hfac', hcharP, map_sub, map_zsmul, map_zsmul]
    rfl
  have hα'char : α'.comp α' + q • AddMonoidHom.id _ = t • α' := by
    have hδmem : α'.comp α' + q • AddMonoidHom.id _ - t • α' ∈
        rationalHomSet K (E.veluQuotient2 x₀ y₀) (E.veluQuotient2 x₀ y₀) :=
      sub_mem_rationalHomSet
        (WeierstrassCurve.add_mem_rationalHomSet K _ _
          (WeierstrassCurve.comp_mem_rationalHomSet K _ _ _ hα' hα')
          (zsmul_id_mem_rationalHomSet (k := K) _ _))
        (zsmul_mem_rationalHomSet hα' _)
    have h4 : (4 : ℤ) • (α'.comp α' + q • AddMonoidHom.id _ - t • α') = 0 := by
      ext Q
      have e : (2 : ℤ) • ((2 : ℤ) • α' (α' Q)) = (2 * t) • ((2 : ℤ) • α' Q) - (4 * q) • Q := by
        have h := hβ'char Q
        rw [hβα (β' Q), hβα Q, map_zsmul] at h
        exact h
      show (4 : ℤ) • (α' (α' Q) + q • Q - t • α' Q) = 0
      linear_combination (norm := module) e
    have h0 := eq_zero_of_zsmul_eq_zero hδmem (by norm_num : (4 : ℤ) ≠ 0) h4
    ext Q
    have := DFunLike.congr_fun h0 Q
    change α' (α' Q) + q • Q - t • α' Q = 0 at this
    change α' (α' Q) + q • Q = t • α' Q
    exact eq_of_sub_eq_zero this

  have hΦ : ∀ data : ModularCurve.ModularPolynomialData 2,
      (ModularCurve.fibrePoly data.Φ E.j).IsRoot (E.veluQuotient2 x₀ y₀).j := by
    intro data
    obtain ⟨ι, hι, hcard, Pt, hinj, heq, hgys, hΔs⟩ :=
      WeierstrassCurve.exists_enum_twoTorsion_veluQuotient2_discriminant_ne_zero h2 E
    letI := hι
    rw [ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient2_j h2 data E hcard Pt hinj
      heq hgys hΔs]

    have hpt2 : ∀ i, (2 : ℤ) • (Affine.Point.some (Pt i).1 (Pt i).2
        ((Affine.equation_iff_nonsingular).mp (heq i)) : E.toAffine.Point) = 0 := by
      intro i
      rw [two_zsmul, add_eq_zero_iff_eq_neg, Affine.Point.neg_some]
      have hy : (Pt i).2 = E.toAffine.negY (Pt i).1 (Pt i).2 := by
        have e : E.veluGy (Pt i).1 (Pt i).2 = -(2 * (Pt i).2 + E.a₁ * (Pt i).1 + E.a₃) := rfl
        rw [Affine.negY]; linear_combination e - hgys i
      exact some_congr rfl hy _ _
    have hex : ∃ i, Pt i = (x₀, y₀) := by
      by_contra hcon
      push Not at hcon

      have hval : ∀ i, (Affine.Point.some (Pt i).1 (Pt i).2
          ((Affine.equation_iff_nonsingular).mp (heq i)) : E.toAffine.Point) = P₁ ∨
          (Affine.Point.some (Pt i).1 (Pt i).2
            ((Affine.equation_iff_nonsingular).mp (heq i)) : E.toAffine.Point) = P₁ + Q₀ := by
        intro i
        rcases hcases _ (hpt2 i) with h | h | h | h
        · exact absurd h (Affine.Point.some_ne_zero _)
        · exfalso; apply hcon i
          rw [hQ₀xy, Affine.Point.some.injEq] at h
          exact Prod.ext h.1 h.2
        · exact Or.inl h
        · exact Or.inr h

      let f : ι → Bool := fun i => decide ((Affine.Point.some (Pt i).1 (Pt i).2
          ((Affine.equation_iff_nonsingular).mp (heq i)) : E.toAffine.Point) = P₁)
      have hfinj : Function.Injective f := by
        intro i j hij
        apply hinj
        have key : (Affine.Point.some (Pt i).1 (Pt i).2 ((Affine.equation_iff_nonsingular).mp (heq i)) :
            E.toAffine.Point) =
            Affine.Point.some (Pt j).1 (Pt j).2 ((Affine.equation_iff_nonsingular).mp (heq j)) := by
          rcases hval i with hi | hi <;> rcases hval j with hj | hj
          · rw [hi, hj]
          · exfalso
            have h1 : f i = true := by simp [f, hi]
            have h2 : f j = false := by
              simp only [f, decide_eq_false_iff_not]
              rw [hj]; exact fun h => hQ₀0 (by simpa using h)
            rw [h1, h2] at hij; exact Bool.noConfusion hij
          · exfalso
            have h1 : f j = true := by simp [f, hj]
            have h2 : f i = false := by
              simp only [f, decide_eq_false_iff_not]
              rw [hi]; exact fun h => hQ₀0 (by simpa using h)
            rw [h1, h2] at hij; exact Bool.noConfusion hij.symm
          · rw [hi, hj]
        rw [Affine.Point.some.injEq] at key
        exact Prod.ext key.1 key.2
      have := Fintype.card_le_of_injective f hfinj
      rw [hcard, Fintype.card_bool] at this
      omega
    obtain ⟨i, hi⟩ := hex
    rw [Polynomial.IsRoot, Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero]
    have h1 : (Pt i).1 = x₀ := by rw [hi]
    have h2' : (Pt i).2 = y₀ := by rw [hi]
    congr 1
    · exact WeierstrassCurve.ext rfl rfl rfl (by rw [h1, h2']) (by rw [h1, h2'])

  refine ⟨E.veluQuotient2 x₀ y₀, hE', π, π', α', hπ, hπ', hα', hπ'π, hππ', ?_, hα'char, hΦ⟩
  ext P
  show (2 : ℤ) • α' (π P) = π (γ P)
  rw [← hβα, hfac']

end Main

end WeierstrassCurve.AscendTwoIsogeny

end

theorem solution {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] (h2 : (2 : K) ≠ 0) (E : WeierstrassCurve K) [E.IsElliptic] {γ : E.toAffine.Point →+ E.toAffine.Point} (hγ : γ ∈ WeierstrassCurve.rationalHomSet K E E) (t q : ℤ) (hchar : γ.comp γ + (4 * q) • AddMonoidHom.id _ = (2 * t) • γ) (hne : ∃ P : E.toAffine.Point, (2 : ℤ) • P = 0 ∧ γ P ≠ 0) : ∃ (E' : WeierstrassCurve K) (_ : E'.IsElliptic) (π : E.toAffine.Point →+ E'.toAffine.Point) (π' : E'.toAffine.Point →+ E.toAffine.Point) (α : E'.toAffine.Point →+ E'.toAffine.Point), π ∈ WeierstrassCurve.rationalHomSet K E E' ∧ π' ∈ WeierstrassCurve.rationalHomSet K E' E ∧ α ∈ WeierstrassCurve.rationalHomSet K E' E' ∧ π'.comp π = 2 • AddMonoidHom.id _ ∧ π.comp π' = 2 • AddMonoidHom.id _ ∧ ((2 : ℤ) • α).comp π = π.comp γ ∧ α.comp α + q • AddMonoidHom.id _ = t • α ∧ ∀ data : ModularCurve.ModularPolynomialData 2, (ModularCurve.fibrePoly data.Φ E.j).IsRoot E'.j :=
  WeierstrassCurve.AscendTwoIsogeny.main h2 E hγ t q hchar hne

end S_WeierstrassCurve_exists_mem_rationalHomSet_two_smul_comp_eq_comp_of_comp_self_add_smul_eq_smul
end P2MW
export P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_two_smul_comp_eq_comp_of_comp_self_add_smul_eq_smul (solution)
