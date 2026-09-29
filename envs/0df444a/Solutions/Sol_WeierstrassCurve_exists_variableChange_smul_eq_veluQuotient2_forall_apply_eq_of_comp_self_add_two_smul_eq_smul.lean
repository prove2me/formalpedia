-- Prove2me | solution 1 for WeierstrassCurve.exists_variableChange_smul_eq_veluQuotient2_forall_apply_eq_of_comp_self_add_two_smul_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/e41a9a03-78ae-504d-bc6c-24581f08ed6b

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_VeluPointMap2
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_WeierstrassCurve_isAddCyclic_ker_and_card_ker_eq_of_comp_self_add_smul_eq_smul
import Theorems.Thm_WeierstrassCurve_exists_coe_eq_veluPointMap2_and_mem_rationalHomSet_and_comp_eq_two_smul
import Theorems.Thm_WeierstrassCurve_veluPointMap2_surjective_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_isElliptic_veluQuotient2_of_isElliptic
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_exists_variableChange_forall_eq_equivOfVariableChangeEq_of_comp_eq_id
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_veluQuotient2_forall_apply_eq_of_comp_self_add_two_smul_eq_smul
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.pointAddEquivOfEq_refl WeierstrassCurve.vcInvEmbedding_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_veluQuotient2_forall_apply_eq_of_comp_self_add_two_smul_eq_smul.WeierstrassCurve Polynomial"
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY a₃ a₁ map Affine.Point.some Affine.Point.some.inj toAffine Affine.Point Affine.Point.some_ne_zero Δ VariableChange Affine.equation_iff Affine.Point.neg_some baseChange evalEvalBC IsRationallyRepresented rationalHomSet zero_mem_rationalHomSet id_mem_rationalHomSet veluPointMap2 veluPointMap2_some_of_eq veluPointMap2_some_of_ne veluQuotient2 veluGy Affine.Point.equivOfVariableChangeEq isAddCyclic_ker_and_card_ker_eq_of_comp_self_add_smul_eq_smul exists_coe_eq_veluPointMap2_and_mem_rationalHomSet_and_comp_eq_two_smul veluPointMap2_surjective_of_isAlgClosed isElliptic_veluQuotient2_of_isElliptic exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero surjective_of_mem_rationalHomSet comp_mem_rationalHomSet add_mem_rationalHomSet card_torsion_of_isAlgClosed exists_variableChange_forall_eq_equivOfVariableChangeEq_of_comp_eq_id"
namespace KernelIsoVC2
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

section NonTorsion

variable {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k] (W : WeierstrassCurve k) [W.IsElliptic]

omit [IsAlgClosed k] [DecidableEq k] in
theorem natCast_ne_zero_of_prime_of_lt {ℓ : ℕ} (hℓ : ℓ.Prime) (hlt : ringChar k < ℓ) :
    (ℓ : k) ≠ 0 := by
  intro h
  have hdvd : ringChar k ∣ ℓ := (ringChar.spec k ℓ).mp h
  rcases (Nat.dvd_prime hℓ).mp hdvd with h1 | h1
  · exact CharP.ringChar_ne_one h1
  · omega

theorem finite_torsionBy {n : ℕ} (hn : (n : k) ≠ 0) :
    Finite (Submodule.torsionBy ℤ (W.baseChange k).toAffine.Point n) := by
  have hcard := WeierstrassCurve.card_torsion_of_isAlgClosed (K := k) W hn
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (by simp)
  exact Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hn0)

theorem exists_zsmul_ne_zero {M : ℤ} (hM : M ≠ 0) : ∃ P : W.toAffine.Point, M • P ≠ 0 := by
  obtain ⟨ℓ, hℓge, hℓ⟩ := Nat.exists_infinite_primes (M.natAbs + ringChar k + 1)
  have hℓM : ¬ (ℓ : ℤ) ∣ M := by
    intro h
    have h1 : ℓ ≤ M.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hM) (Int.natCast_dvd.mp h)
    omega
  have hℓk : (ℓ : k) ≠ 0 := natCast_ne_zero_of_prime_of_lt hℓ (by omega)
  have hcard : Nat.card (Submodule.torsionBy ℤ (W.baseChange k).toAffine.Point ℓ) = ℓ ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed W hℓk
  have hgt : 1 < Nat.card (Submodule.torsionBy ℤ (W.baseChange k).toAffine.Point ℓ) := by
    rw [hcard]; nlinarith [hℓ.one_lt]
  haveI : Finite (Submodule.torsionBy ℤ (W.baseChange k).toAffine.Point ℓ) := finite_torsionBy W hℓk
  haveI : Nontrivial (Submodule.torsionBy ℤ (W.baseChange k).toAffine.Point ℓ) :=
    Finite.one_lt_card_iff_nontrivial.mp hgt
  obtain ⟨⟨P, hP⟩, hP0⟩ := exists_ne (0 : Submodule.torsionBy ℤ (W.baseChange k).toAffine.Point ℓ)
  have hPℓ : (ℓ : ℤ) • P = 0 := by simpa using hP
  have hP0' : P ≠ 0 := fun h => hP0 (by ext; simpa using h)
  refine ⟨P, fun hMP => hP0' ?_⟩
  have hcop : IsCoprime (ℓ : ℤ) M := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h1 : Int.gcd (ℓ : ℤ) M ∣ ℓ := by
      have := Int.gcd_dvd_left (ℓ : ℤ) M
      exact_mod_cast this
    rcases (Nat.dvd_prime hℓ).mp h1 with h | h
    · exact h
    · exfalso
      apply hℓM
      have := Int.gcd_dvd_right (ℓ : ℤ) M
      rwa [h] at this
  obtain ⟨a, b, hab⟩ := hcop
  have hMP' : M • P = 0 := hMP
  calc P = (a * ℓ + b * M) • P := by rw [hab, one_zsmul]
    _ = 0 := by rw [add_zsmul, mul_zsmul, mul_zsmul, hPℓ, hMP', zsmul_zero, zsmul_zero, add_zero]

theorem exists_zsmul_eq {M : ℤ} (hM : M ≠ 0) (P : W.toAffine.Point) :
    ∃ P' : W.toAffine.Point, M • P' = P := by
  have hmem : (M • AddMonoidHom.id _ : (W.baseChange k).toAffine.Point →+ _) ∈ rationalHomSet k W W :=
    zsmul_id_mem_rationalHomSet W M
  have hne : (M • AddMonoidHom.id _ : (W.baseChange k).toAffine.Point →+ _) ≠ 0 := by
    intro h0
    obtain ⟨R, hR⟩ := exists_zsmul_ne_zero W hM
    exact hR (by exact DFunLike.congr_fun h0 R)
  obtain ⟨P', hP'⟩ := WeierstrassCurve.surjective_of_mem_rationalHomSet k hmem hne P
  exact ⟨P', by simp at hP'; exact hP'⟩

theorem eq_zero_of_zsmul_apply_eq_zero {G : Type*} [AddCommGroup G] {M : ℤ} (hM : M ≠ 0)
    (δ : W.toAffine.Point →+ G) (h : ∀ P, M • δ P = 0) : δ = 0 := by
  ext P
  obtain ⟨P', rfl⟩ := exists_zsmul_eq W hM P
  rw [map_zsmul, h P', AddMonoidHom.zero_apply]

theorem charPoly_apply {G : Type*} [AddCommGroup G] {β : G →+ G} {s m : ℤ}
    (h : β.comp β + m • AddMonoidHom.id _ = s • β) (P : G) : β (β P) + m • P = s • β P := by
  have := DFunLike.congr_fun h P
  simpa using this

theorem comp_conj_apply {G : Type*} [AddCommGroup G] {β : G →+ G} {s m : ℤ}
    (hchar : β.comp β + m • AddMonoidHom.id _ = s • β) (P : G) :
    β ((s • AddMonoidHom.id G - β) P) = m • P := by
  have e1 := charPoly_apply hchar P
  have e3 : β (β P) = s • β P - m • P := eq_sub_of_add_eq e1
  have e4 : (s • AddMonoidHom.id G - β) P = s • P - β P := by
    simp only [AddMonoidHom.sub_apply, AddMonoidHom.smul_apply, AddMonoidHom.id_apply]
  rw [e4, map_sub, map_zsmul, e3]
  module

end NonTorsion

section Units

variable {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k] (W : WeierstrassCurve k) [W.IsElliptic]
variable {V : WeierstrassCurve k} [V.IsElliptic]
variable {φ₀ : W.toAffine.Point →+ V.toAffine.Point} (hφ₀ : φ₀ ∈ rationalHomSet k W V)
variable {m : ℕ} (hm : (m : k) ≠ 0)

include hφ₀ hm in

theorem exists_inverse {ι : V.toAffine.Point →+ W.toAffine.Point} (hι : ι ∈ rationalHomSet k V W)
    (hinj : Function.Injective ι)
    {γ' : W.toAffine.Point →+ W.toAffine.Point} (hγ' : γ' ∈ rationalHomSet k W W)
    (hγγ' : ∀ P, ι (φ₀ (γ' P)) = (m : ℤ) • P)
    (hkill : ∀ T : W.toAffine.Point, (m : ℤ) • T = 0 → φ₀ (γ' T) = 0) :
    ∃ τ : W.toAffine.Point →+ V.toAffine.Point, τ ∈ rationalHomSet k W V ∧
      ι.comp τ = AddMonoidHom.id W.toAffine.Point ∧ τ.comp ι = AddMonoidHom.id V.toAffine.Point := by
  have hm0 : (m : ℤ) ≠ 0 := by
    have : m ≠ 0 := by rintro rfl; exact hm (by simp)
    exact_mod_cast this

  have hθ : φ₀.comp γ' ∈ rationalHomSet k W V :=
    WeierstrassCurve.comp_mem_rationalHomSet k W W V hγ' hφ₀
  have hkill' : ∀ P : (W.baseChange k).toAffine.Point, (m : ℤ) • P = 0 → (φ₀.comp γ') P = 0 :=
    fun T hT => hkill T hT
  obtain ⟨τ, hτ, hθτ⟩ := WeierstrassCurve.exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero
    k W V hm hθ hkill'
  let τ₀ : W.toAffine.Point →+ V.toAffine.Point := τ
  have hθτ' : ∀ P : W.toAffine.Point, φ₀ (γ' P) = (m : ℤ) • τ₀ P := fun P => hθτ P

  have hιτ : ι.comp τ₀ = AddMonoidHom.id _ := by
    have hδ := eq_zero_of_zsmul_apply_eq_zero W hm0 (ι.comp τ₀ - AddMonoidHom.id _) (fun P => by
      show (m : ℤ) • (ι (τ₀ P) - P) = 0
      rw [smul_sub, ← map_zsmul, ← hθτ' P, hγγ', sub_self])
    exact sub_eq_zero.mp hδ
  refine ⟨τ₀, hτ, hιτ, ?_⟩
  ext P
  apply hinj
  exact DFunLike.congr_fun hιτ (ι P)

end Units

section TwoTorsion

variable {k : Type*} [Field k] [DecidableEq k] (W : WeierstrassCurve k)

omit [DecidableEq k] in

theorem eq_of_equation_of_veluGy_eq_zero {x₀ y₀ y : k} (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) (hy : W.toAffine.Equation x₀ y) : y = y₀ := by
  rw [Affine.equation_iff] at hQ hy
  have hgy' : -(2 * y₀ + W.a₁ * x₀ + W.a₃) = 0 := hgy
  have hsq : (y - y₀) ^ 2 = 0 := by linear_combination hy - hQ + (y - y₀) * hgy'
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq)

theorem veluPointMap2_eq_zero_iff (h2 : (2 : k) ≠ 0) {x₀ y₀ : k} (h₀ : W.toAffine.Nonsingular x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0) (T : W.toAffine.Point) :
    veluPointMap2 h2 h₀.1 hgy hΔ T = 0 ↔ T = 0 ∨ T = .some x₀ y₀ h₀ := by
  rcases T with _ | ⟨x, y, h⟩
  · exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
  · by_cases hx : x = x₀
    · refine ⟨fun _ => Or.inr ?_, fun _ => veluPointMap2_some_of_eq h2 h₀.1 hgy hΔ h hx⟩
      subst hx
      have hy : y = y₀ := eq_of_equation_of_veluGy_eq_zero W h₀.1 hgy h.1
      subst hy
      rfl
    · refine ⟨fun h0 => ?_, fun h0 => ?_⟩
      · rw [veluPointMap2_some_of_ne h2 h₀.1 hgy hΔ h hx] at h0
        exact absurd h0 (Affine.Point.some_ne_zero _)
      · rcases h0 with h0 | h0
        · exact absurd h0 (Affine.Point.some_ne_zero _)
        · exact absurd (Affine.Point.some.inj h0).1 hx

end TwoTorsion

section Main

variable {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k] (W : WeierstrassCurve k) [W.IsElliptic]

theorem main {β : W.toAffine.Point →+ W.toAffine.Point} (hβ : β ∈ rationalHomSet k W W)
    (s : ℤ) (hchar : β.comp β + (2 : ℤ) • AddMonoidHom.id _ = s • β)
    (hirr : ∀ x : ℤ, x ^ 2 - s * x + 2 ≠ 0)
    (h2 : (2 : k) ≠ 0)
    {x₀ y₀ : k} (h₀ : W.toAffine.Nonsingular x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0)
    (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0)
    (hQ₀β : β (.some x₀ y₀ h₀) = 0) :
    ∃ (γ₀ : VariableChange k) (hγ₀ : γ₀ • W = W.veluQuotient2 x₀ y₀),
      ∀ P, β P = Affine.Point.equivOfVariableChangeEq hγ₀ (veluPointMap2 h2 h₀.1 hgy hΔ P) := by
  have e2 : ((2 : ℕ) : ℤ) = 2 := rfl
  have hm : ((2 : ℕ) : k) ≠ 0 := by exact_mod_cast h2
  have hm0 : ((2 : ℕ) : ℤ) ≠ 0 := by decide
  set Q₀ : W.toAffine.Point := .some x₀ y₀ h₀ with hQ₀def
  have hQ₀ne : Q₀ ≠ 0 := Affine.Point.some_ne_zero _

  have hchar' : β.comp β + ((2 : ℕ) : ℤ) • AddMonoidHom.id _ = s • β := by rw [e2]; exact hchar
  have hirr' : ∀ x : ℤ, x ^ 2 - s * x + ((2 : ℕ) : ℤ) ≠ 0 := fun x => by rw [e2]; exact hirr x
  have hprim : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ s → ¬ (ℓ : ℤ) ^ 2 ∣ ((2 : ℕ) : ℤ) := by
    intro ℓ hℓ _ hdvd
    have hle : (ℓ : ℤ) ^ 2 ≤ 2 := Int.le_of_dvd (by decide) hdvd
    have h2ℓ : (2 : ℤ) ≤ ℓ := by exact_mod_cast hℓ.two_le
    nlinarith
  obtain ⟨-, hcardβ⟩ :=
    W.isAddCyclic_ker_and_card_ker_eq_of_comp_self_add_smul_eq_smul hβ s 2 hchar' hm hirr' hprim
  have hkerβ : ∀ T, β T = 0 ↔ T = 0 ∨ T = Q₀ := by
    intro T
    refine ⟨fun hT => ?_, ?_⟩
    · by_cases hT0 : T = 0
      · exact Or.inl hT0
      · right
        obtain ⟨y, -, huniq⟩ :=
          (Nat.card_eq_two_iff' (⟨0, AddMonoidHom.mem_ker.mpr (map_zero β)⟩ : β.ker)).mp hcardβ
        have e1 := huniq ⟨T, AddMonoidHom.mem_ker.mpr hT⟩ (fun h => hT0 (congrArg Subtype.val h))
        have e2 := huniq ⟨Q₀, AddMonoidHom.mem_ker.mpr hQ₀β⟩
          (fun h => hQ₀ne (congrArg Subtype.val h))
        exact congrArg Subtype.val (e1.trans e2.symm)
    · rintro (rfl | rfl)
      · exact map_zero β
      · exact hQ₀β

  haveI : (W.veluQuotient2 x₀ y₀).IsElliptic := isElliptic_veluQuotient2_of_isElliptic h₀.1 hgy
  obtain ⟨φ₀, hφ₀, hφ₀rat, -, hUP⟩ :=
    W.exists_coe_eq_veluPointMap2_and_mem_rationalHomSet_and_comp_eq_two_smul h2 h₀.1 hgy hΔ
  have hkerφ₀ : ∀ T, φ₀ T = 0 ↔ β T = 0 := fun T => by
    rw [hkerβ, hφ₀]; exact veluPointMap2_eq_zero_iff W h2 h₀ hgy hΔ T
  obtain ⟨ι₀', hι₀, hβfac'⟩ := hUP W inferInstance β hβ (fun T hT => (hkerφ₀ T).mp hT)
  let ι₀ : (W.veluQuotient2 x₀ y₀).toAffine.Point →+ W.toAffine.Point := ι₀'
  have hβfac : β = ι₀.comp φ₀ := hβfac'
  have hφ₀surj : Function.Surjective φ₀ := by
    rw [hφ₀]; exact veluPointMap2_surjective_of_isAlgClosed W h2 h₀.1 hgy hΔ
  have hι₀inj : Function.Injective ι₀ := by
    intro P₁ P₂ h12
    obtain ⟨P, rfl⟩ := hφ₀surj P₁
    obtain ⟨R, rfl⟩ := hφ₀surj P₂
    have h1 : β (P - R) = 0 := by rw [hβfac, map_sub]; exact sub_eq_zero.mpr h12
    have h2' : φ₀ (P - R) = 0 := (hkerφ₀ _).mpr h1
    rw [map_sub, sub_eq_zero] at h2'
    rw [h2']

  let β' : W.toAffine.Point →+ W.toAffine.Point := s • AddMonoidHom.id _ - β
  have hβ'rat : β' ∈ rationalHomSet k W W :=
    sub_mem_rationalHomSet (zsmul_id_mem_rationalHomSet W s) hβ
  have hββ' : ∀ P, ι₀ (φ₀ (β' P)) = ((2 : ℕ) : ℤ) • P := fun P => by
    rw [e2, ← comp_conj_apply hchar P]
    exact (DFunLike.congr_fun hβfac (β' P)).symm
  have hkill₀ : ∀ T : W.toAffine.Point, ((2 : ℕ) : ℤ) • T = 0 → φ₀ (β' T) = 0 := by
    intro T hT
    rw [e2] at hT
    exact (hkerφ₀ _).mpr ((comp_conj_apply hchar T).trans (by rw [hT]))
  obtain ⟨τ, hτ, hι₀τ, hτι₀⟩ := exists_inverse W hφ₀rat hm hι₀ hι₀inj hβ'rat hββ' hkill₀

  obtain ⟨γ₀, hγ₀, hpt⟩ :=
    WeierstrassCurve.exists_variableChange_forall_eq_equivOfVariableChangeEq_of_comp_eq_id
      (W.veluQuotient2 x₀ y₀) W ι₀ hι₀ τ hτ hτι₀ hι₀τ
  refine ⟨γ₀, hγ₀, fun P => ?_⟩
  rw [show veluPointMap2 h2 h₀.1 hgy hΔ P = φ₀ P from (congrFun hφ₀ P).symm, ← hpt (φ₀ P)]
  exact DFunLike.congr_fun hβfac P

end Main

end WeierstrassCurve.KernelIsoVC2

theorem solution
    {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k] (W : WeierstrassCurve k) [W.IsElliptic]
    {β : W.toAffine.Point →+ W.toAffine.Point} (hβ : β ∈ WeierstrassCurve.rationalHomSet k W W)
    (s : ℤ) (hchar : β.comp β + (2 : ℤ) • AddMonoidHom.id _ = s • β)
    (hirr : ∀ x : ℤ, x ^ 2 - s * x + 2 ≠ 0)
    (h2 : (2 : k) ≠ 0)
    {x₀ y₀ : k} (h₀ : W.toAffine.Nonsingular x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0)
    (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0)
    (hQ₀β : β (.some x₀ y₀ h₀) = 0) :
    ∃ (γ₀ : WeierstrassCurve.VariableChange k) (hγ₀ : γ₀ • W = W.veluQuotient2 x₀ y₀),
      ∀ P, β P = WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hγ₀
        (WeierstrassCurve.veluPointMap2 h2 h₀.1 hgy hΔ P) :=
  WeierstrassCurve.KernelIsoVC2.main W hβ s hchar hirr h2 h₀ hgy hΔ hQ₀β

end S_WeierstrassCurve_exists_variableChange_smul_eq_veluQuotient2_forall_apply_eq_of_comp_self_add_two_smul_eq_smul
end P2MW
export P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_veluQuotient2_forall_apply_eq_of_comp_self_add_two_smul_eq_smul (solution)
