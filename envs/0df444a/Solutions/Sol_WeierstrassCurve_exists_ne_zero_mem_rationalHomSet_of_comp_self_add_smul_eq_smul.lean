-- Prove2me | solution 1 for WeierstrassCurve.exists_ne_zero_mem_rationalHomSet_of_comp_self_add_smul_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/0347c7f4-4577-557c-bda4-b35d6af975f3

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_PeriodPair_Uniformization
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_exists_isDualPair_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_apply_map_eq_map_apply
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Theorems.Thm_PeriodPair_isUniformization_toPoint
import Theorems.Thm_PeriodPair_discriminant_ne_zero
import Theorems.Thm_PeriodPair_exists_variableChange_smul_weierstrassCurve_eq
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_apply_map_eq_map_apply_of_mem_rationalHomSet_baseChange
import Theorems.Thm_PeriodPair_exists_forall_apply_toPoint_eq_toPoint_mul_of_mem_rationalHomSet
import Theorems.Thm_PeriodPair_exists_mem_rationalHomSet_forall_apply_toPoint_eq_toPoint_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_ne_zero_mem_rationalHomSet_of_comp_self_add_smul_eq_smul
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Polynomial
open scoped Polynomial.Bivariate
p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_exists_ne_zero_mem_rationalHomSet_of_comp_self_add_smul_eq_smul.WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY a₃ a₁ map isElliptic_iff a₄ a₂ a₆ Affine.Point.some Affine.degree_polynomial Affine.Point.some.inj reduction map_id toAffine Affine.Point map_injective map_Δ Affine.monic_polynomial Δ VariableChange Affine.Point.neg_some minimal baseChange evalEvalBC IsRationallyRepresented rationalHomSet zero_mem_rationalHomSet id_mem_rationalHomSet Affine.Point.vcFun Affine.Point.vcInvFun Affine.Point.vcFun_leftInverse Affine.Point.vcFun_rightInverse comp_mem_rationalHomSet add_mem_rationalHomSet exists_isDualPair_of_mem_rationalHomSet card_torsion_of_isAlgClosed exists_mem_rationalHomSet_apply_map_eq_map_apply Affine.Point.vcInvFun_add exists_mem_rationalHomSet_apply_map_eq_map_apply_of_mem_rationalHomSet_baseChange"
namespace CMIsog
p2m_open "WeierstrassCurve"

section Generalities

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k]

abbrev Pt (k : Type*) [Field k] [Algebra F k] (W : WeierstrassCurve F) :=
  (W.baseChange k).toAffine.Point

noncomputable def bc (x y : k) : F[X][Y] →+* k :=
  (evalEvalRingHom x y).comp (mapRingHom (mapRingHom (algebraMap F k)))

theorem evalEvalBC_eq (p : F[X][Y]) (x y : k) :
    WeierstrassCurve.evalEvalBC k p x y = bc x y p := rfl

@[scoped simp] theorem bc_CC (x y : k) (a : F) : bc x y (C (C a)) = algebraMap F k a := by
  simp [bc]

@[scoped simp] theorem bc_CX (x y : k) : bc x y (C X : F[X][Y]) = x := by
  simp [bc]

@[scoped simp] theorem bc_Y (x y : k) : bc x y (Y : F[X][Y]) = y := by
  simp [bc]

variable [DecidableEq k]

section IsRat

variable (W : WeierstrassCurve F)

def IsRat (f : k → k → k) : Prop :=
  ∃ (n d : F[X][Y]) (B : Set k), B.Finite ∧
    ∀ x y : k, (W.baseChange k).toAffine.Nonsingular x y → x ∉ B →
      bc x y d ≠ 0 ∧ f x y = bc x y n / bc x y d

namespace IsRat

variable {W}
variable {f g : k → k → k}

omit [DecidableEq k] in
theorem of_eq (hf : IsRat W f) (hfg : ∀ x y, g x y = f x y) : IsRat W g := by
  obtain ⟨n, d, B, hB, h⟩ := hf
  exact ⟨n, d, B, hB, fun x y hxy hx => by rw [hfg]; exact h x y hxy hx⟩

omit [DecidableEq k] in
theorem poly (p : F[X][Y]) : IsRat W (fun (x y : k) => bc x y p) :=
  ⟨p, 1, ∅, Set.finite_empty, fun x y _ _ => by simp⟩

omit [DecidableEq k] in
theorem const (a : F) : IsRat W (fun _ _ => algebraMap F k a) :=
  (poly (C (C a))).of_eq fun x y => by simp

omit [DecidableEq k] in
theorem fst : IsRat W (fun (x : k) (_ : k) => x) :=
  (poly (C X)).of_eq fun x y => by simp

omit [DecidableEq k] in
theorem snd : IsRat W (fun (_ : k) (y : k) => y) :=
  (poly Y).of_eq fun x y => by simp

omit [DecidableEq k] in
theorem add (hf : IsRat W f) (hg : IsRat W g) : IsRat W (fun x y => f x y + g x y) := by
  obtain ⟨n₁, d₁, B₁, hB₁, h₁⟩ := hf
  obtain ⟨n₂, d₂, B₂, hB₂, h₂⟩ := hg
  refine ⟨n₁ * d₂ + n₂ * d₁, d₁ * d₂, B₁ ∪ B₂, hB₁.union hB₂, fun x y hxy hx => ?_⟩
  simp only [Set.mem_union, not_or] at hx
  obtain ⟨hd₁, hf₁⟩ := h₁ x y hxy hx.1
  obtain ⟨hd₂, hf₂⟩ := h₂ x y hxy hx.2
  refine ⟨by rw [map_mul]; exact mul_ne_zero hd₁ hd₂, ?_⟩
  beta_reduce
  rw [hf₁, hf₂, map_add, map_mul, map_mul, map_mul, div_add_div _ _ hd₁ hd₂]
  ring

omit [DecidableEq k] in
theorem neg (hf : IsRat W f) : IsRat W (fun x y => -f x y) := by
  obtain ⟨n, d, B, hB, h⟩ := hf
  refine ⟨-n, d, B, hB, fun x y hxy hx => ?_⟩
  obtain ⟨hd, hf⟩ := h x y hxy hx
  exact ⟨hd, by beta_reduce; rw [hf, map_neg, neg_div]⟩

omit [DecidableEq k] in
theorem sub (hf : IsRat W f) (hg : IsRat W g) : IsRat W (fun x y => f x y - g x y) :=
  (hf.add hg.neg).of_eq fun x y => by ring

omit [DecidableEq k] in
theorem mul (hf : IsRat W f) (hg : IsRat W g) : IsRat W (fun x y => f x y * g x y) := by
  obtain ⟨n₁, d₁, B₁, hB₁, h₁⟩ := hf
  obtain ⟨n₂, d₂, B₂, hB₂, h₂⟩ := hg
  refine ⟨n₁ * n₂, d₁ * d₂, B₁ ∪ B₂, hB₁.union hB₂, fun x y hxy hx => ?_⟩
  simp only [Set.mem_union, not_or] at hx
  obtain ⟨hd₁, hf₁⟩ := h₁ x y hxy hx.1
  obtain ⟨hd₂, hf₂⟩ := h₂ x y hxy hx.2
  refine ⟨by rw [map_mul]; exact mul_ne_zero hd₁ hd₂, ?_⟩
  beta_reduce
  rw [hf₁, hf₂, map_mul, map_mul, div_mul_div_comm]

end IsRat

variable {W}

omit [DecidableEq k] in
theorem exists_some_of_eq {W₂ : WeierstrassCurve F} {Q : Pt k W₂} {x₁ y₁ : k}
    {h₁ : (W₂.baseChange k).toAffine.Nonsingular x₁ y₁}
    (hQ : Q = .some x₁ y₁ h₁) {x₂ y₂ : k} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    ∃ h₂, Q = .some x₂ y₂ h₂ := by
  subst hx hy; exact ⟨h₁, hQ⟩

theorem isRationallyRepresented_of_isRat {W₁ W₂ : WeierstrassCurve F}
    (γ : Pt k W₁ →+ Pt k W₂) {fX fY : k → k → k} (hX : IsRat W₁ fX) (hY : IsRat W₁ fY)
    {B₀ : Set k} (hB₀ : B₀.Finite)
    (hγ : ∀ (x y : k) (h : (W₁.baseChange k).toAffine.Nonsingular x y), x ∉ B₀ →
      ∃ h', γ (.some x y h) = .some (fX x y) (fY x y) h') :
    IsRationallyRepresented k W₁ W₂ γ := by
  obtain ⟨nX, dX, BX, hBX, hX⟩ := hX
  obtain ⟨nY, dY, BY, hBY, hY⟩ := hY
  refine ⟨nX, dX, nY, dY, B₀ ∪ BX ∪ BY, (hB₀.union hBX).union hBY, fun x y h hx => ?_⟩
  simp only [Set.mem_union, not_or] at hx
  obtain ⟨hdX, hfX⟩ := hX x y h hx.1.2
  obtain ⟨hdY, hfY⟩ := hY x y h hx.2
  obtain ⟨h', hγ'⟩ := hγ x y h hx.1.1
  refine ⟨hdX, hdY, ?_⟩
  simp only [evalEvalBC_eq]
  exact exists_some_of_eq hγ' hfX hfY

theorem exists_isRat_of_isRationallyRepresented {W₁ W₂ : WeierstrassCurve F}
    {α : Pt k W₁ →+ Pt k W₂} (hα : IsRationallyRepresented k W₁ W₂ α) :
    ∃ (fX fY : k → k → k) (B : Set k), IsRat W₁ fX ∧ IsRat W₁ fY ∧ B.Finite ∧
      ∀ (x y : k) (h : (W₁.baseChange k).toAffine.Nonsingular x y), x ∉ B →
        ∃ h', α (.some x y h) = .some (fX x y) (fY x y) h' := by
  obtain ⟨nX, dX, nY, dY, B, hB, hrep⟩ := hα
  refine ⟨fun x y => bc x y nX / bc x y dX, fun x y => bc x y nY / bc x y dY, B,
    ⟨nX, dX, B, hB, fun x y h hx => ⟨(hrep x y h hx).1, rfl⟩⟩,
    ⟨nY, dY, B, hB, fun x y h hx => ⟨(hrep x y h hx).2.1, rfl⟩⟩, hB, fun x y h hx => ?_⟩
  obtain ⟨-, -, h', hP⟩ := hrep x y h hx
  exact ⟨h', hP⟩

end IsRat

theorem neg_mem_rationalHomSet {W₁ W₂ : WeierstrassCurve F} {α : Pt k W₁ →+ Pt k W₂}
    (hα : α ∈ rationalHomSet k W₁ W₂) : -α ∈ rationalHomSet k W₁ W₂ := by
  rcases hα with rfl | hα
  · exact Or.inl (neg_zero)
  right
  obtain ⟨fX, fY, B, hfX, hfY, hB, hrep⟩ := exists_isRat_of_isRationallyRepresented hα
  refine isRationallyRepresented_of_isRat (-α) hfX
    (((hfY.neg).sub ((IsRat.const W₂.a₁).mul hfX)).sub (IsRat.const W₂.a₃)) hB ?_
  intro x y h hx
  obtain ⟨h', hP⟩ := hrep x y h hx
  refine ⟨?_, ?_⟩
  · have := ((W₂.baseChange k).toAffine.nonsingular_neg _ _).mpr h'
    simpa [Affine.negY] using this
  · rw [AddMonoidHom.neg_apply, hP, Affine.Point.neg_some]
    congr 1

theorem zsmul_mem_rationalHomSet [IsAlgClosed k] {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic]
    [W₂.IsElliptic] {α : Pt k W₁ →+ Pt k W₂} (hα : α ∈ rationalHomSet k W₁ W₂) (n : ℤ) :
    n • α ∈ rationalHomSet k W₁ W₂ := by
  induction n using Int.induction_on with
  | zero => rw [zero_zsmul]; exact zero_mem_rationalHomSet k W₁ W₂
  | succ n ih =>
    rw [add_zsmul, one_zsmul]
    exact WeierstrassCurve.add_mem_rationalHomSet k W₁ W₂ ih hα
  | pred n ih =>
    rw [sub_zsmul, one_zsmul]
    exact WeierstrassCurve.add_mem_rationalHomSet k W₁ W₂ ih (neg_mem_rationalHomSet hα)

theorem sub_mem_rationalHomSet [IsAlgClosed k] {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic]
    [W₂.IsElliptic] {α β : Pt k W₁ →+ Pt k W₂} (hα : α ∈ rationalHomSet k W₁ W₂)
    (hβ : β ∈ rationalHomSet k W₁ W₂) : α - β ∈ rationalHomSet k W₁ W₂ := by
  rw [sub_eq_add_neg]
  exact WeierstrassCurve.add_mem_rationalHomSet k W₁ W₂ hα (neg_mem_rationalHomSet hβ)

theorem quad_mem_rationalHomSet [IsAlgClosed k] {W : WeierstrassCurve F} [W.IsElliptic]
    {α : Pt k W →+ Pt k W} (hα : α ∈ rationalHomSet k W W) (t q : ℤ) :
    α.comp α + q • AddMonoidHom.id _ - t • α ∈ rationalHomSet k W W :=
  sub_mem_rationalHomSet
    (WeierstrassCurve.add_mem_rationalHomSet k W W (WeierstrassCurve.comp_mem_rationalHomSet k W W W hα hα)
      (zsmul_mem_rationalHomSet (id_mem_rationalHomSet k W) q))
    (zsmul_mem_rationalHomSet hα t)

theorem finite_zeros_of_ne_zero [IsAlgClosed k] [CharZero k] {W₁ W₂ : WeierstrassCurve F}
    [W₁.IsElliptic] [W₂.IsElliptic] {ρ : Pt k W₁ →+ Pt k W₂} (hρ : ρ ∈ rationalHomSet k W₁ W₂)
    (hρ0 : ρ ≠ 0) : {P : Pt k W₁ | ρ P = 0}.Finite := by
  obtain ⟨σ, -, n, hn, hdual⟩ :=
    WeierstrassCurve.exists_isDualPair_of_mem_rationalHomSet k W₁ W₂ hρ hρ0
  have hsub : {P : Pt k W₁ | ρ P = 0} ⊆
      (Submodule.torsionBy ℤ (Pt k W₁) (n.toNat : ℤ) : Set (Pt k W₁)) := by
    intro P hP
    simp only [Set.mem_setOf_eq] at hP
    simp only [SetLike.mem_coe, Submodule.mem_torsionBy_iff]
    rw [Int.toNat_of_nonneg hn.le]
    have := hdual.comp_left P
    rw [hP, _root_.map_zero] at this
    simpa using this.symm
  refine Set.Finite.subset ?_ hsub
  have hn0 : ((n.toNat : ℕ) : k) ≠ 0 := by
    have : n.toNat ≠ 0 := by omega
    exact_mod_cast this
  have hcard := WeierstrassCurve.card_torsion_of_isAlgClosed (K := k) W₁ hn0
  have hfin : Finite (Submodule.torsionBy ℤ (Pt k W₁) (n.toNat : ℕ)) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcard]
    have : n.toNat ≠ 0 := by omega
    positivity
  exact Set.toFinite _

theorem eq_zero_of_infinite_zeros [IsAlgClosed k] [CharZero k] {W₁ W₂ : WeierstrassCurve F}
    [W₁.IsElliptic] [W₂.IsElliptic] {ρ : Pt k W₁ →+ Pt k W₂} (hρ : ρ ∈ rationalHomSet k W₁ W₂)
    {S : Set (Pt k W₁)} (hS : S.Infinite) (h0 : ∀ P ∈ S, ρ P = 0) : ρ = 0 := by
  by_contra hne
  exact hS ((finite_zeros_of_ne_zero hρ hne).subset fun P hP => h0 P hP)

omit [DecidableEq k] in

theorem infinite_point [DecidableEq k] [IsAlgClosed k] {W : WeierstrassCurve F} [W.IsElliptic] :
    Infinite (Pt k W) := by
  haveI : (W.baseChange k).IsElliptic :=
    (inferInstance : (W.map (algebraMap F k)).IsElliptic)
  have hy : ∀ x : k, ∃ y : k, (W.baseChange k).toAffine.Nonsingular x y := by
    intro x
    have hdeg : ((W.baseChange k).toAffine.polynomial.map (evalRingHom x)).degree ≠ 0 := by
      rw [WeierstrassCurve.Affine.monic_polynomial.degree_map,
        WeierstrassCurve.Affine.degree_polynomial]
      norm_num
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hdeg
    refine ⟨y, ((W.baseChange k).toAffine.equation_iff_nonsingular).mp ?_⟩
    rw [IsRoot.def, map_evalRingHom_eval] at hy
    exact hy
  choose f hf using hy
  refine Infinite.of_injective (fun x : k => (Affine.Point.some x (f x) (hf x) : Pt k W)) ?_
  intro x x' hxx'
  exact (WeierstrassCurve.Affine.Point.some.inj hxx').left

theorem mem_rationalHomSet_baseChange_of_mem {W₁ W₂ : WeierstrassCurve F} {α : Pt k W₁ →+ Pt k W₂}
    (hα : α ∈ rationalHomSet k W₁ W₂) :
    α ∈ rationalHomSet k (W₁.baseChange k) (W₂.baseChange k) := by
  rcases hα with rfl | ⟨nX, dX, nY, dY, B, hB, hrep⟩
  · exact Or.inl rfl
  right
  refine ⟨nX.map (mapRingHom (algebraMap F k)), dX.map (mapRingHom (algebraMap F k)),
    nY.map (mapRingHom (algebraMap F k)), dY.map (mapRingHom (algebraMap F k)), B, hB, ?_⟩
  intro x y h hx
  have key : ∀ p : F[X][Y], evalEvalBC k (F := k) (p.map (mapRingHom (algebraMap F k))) x y =
      evalEvalBC k p x y := by
    intro p
    simp only [evalEvalBC, Algebra.algebraMap_self, Polynomial.mapRingHom_id, Polynomial.map_id]
  simp only [key]
  exact hrep x y h hx

end Generalities

section LatticeCurves

noncomputable def T (L : PeriodPair) (hL : L.DiscriminantNeZero) :
    ℂ →+ L.weierstrassCurve.toAffine.Point :=
  AddMonoidHom.mk' (L.toPoint hL) (PeriodPair.isUniformization_toPoint L hL).1

theorem T_apply (L : PeriodPair) (hL : L.DiscriminantNeZero) (z : ℂ) : T L hL z = L.toPoint hL z :=
  rfl

theorem T_surjective (L : PeriodPair) (hL : L.DiscriminantNeZero) : Function.Surjective (T L hL) :=
  (PeriodPair.isUniformization_toPoint L hL).2.1

theorem T_eq_zero_iff (L : PeriodPair) (hL : L.DiscriminantNeZero) {z : ℂ} :
    T L hL z = 0 ↔ z ∈ L.lattice :=
  ⟨(PeriodPair.isUniformization_toPoint L hL).2.2 z, fun h => L.toPoint_of_mem hL h⟩

theorem T_intCast_mul (L : PeriodPair) (hL : L.DiscriminantNeZero) (n : ℤ) (z : ℂ) :
    T L hL (n * z) = n • T L hL z := by
  rw [← zsmul_eq_mul, map_zsmul]

theorem omega1_ne_zero (L : PeriodPair) : L.ω₁ ≠ 0 := by
  have := L.indep.ne_zero 0
  simpa using this

theorem eq_zero_of_forall_mul_mem_lattice (L : PeriodPair) {c : ℂ}
    (h : ∀ z : ℂ, c * z ∈ L.lattice) : c = 0 := by
  by_contra hc
  have hmem := h (L.ω₁ / (2 * c))
  have : c * (L.ω₁ / (2 * c)) = L.ω₁ / 2 := by field_simp
  rw [this] at hmem
  exact L.ω₁_div_two_notMem_lattice hmem

theorem intCast_mul_mem_lattice (L : PeriodPair) (n : ℤ) {z : ℂ} (hz : z ∈ L.lattice) :
    (n : ℂ) * z ∈ L.lattice := by
  rw [← zsmul_eq_mul]; exact L.lattice.smul_mem n hz

theorem exists_transporter (L₁ L₂ : PeriodPair) (t q : ℤ)
    (hirr : ∀ m : ℤ, m ^ 2 - t * m + q ≠ 0) (a₁ a₂ : ℂ)
    (hs₁ : ∀ l ∈ L₁.lattice, a₁ * l ∈ L₁.lattice) (hs₂ : ∀ l ∈ L₂.lattice, a₂ * l ∈ L₂.lattice)
    (hq₁ : a₁ ^ 2 - t * a₁ + q = 0) (hq₂ : a₂ ^ 2 - t * a₂ + q = 0) :
    ∃ γ : ℂ, γ ≠ 0 ∧ ∀ l ∈ L₁.lattice, γ * l ∈ L₂.lattice := by

  obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.mp (hs₁ _ L₁.ω₁_mem_lattice)
  have hω₁ := omega1_ne_zero L₁
  have hω₁' := omega1_ne_zero L₂
  have hn : n ≠ 0 := by
    rintro rfl
    have ha : a₁ = m := by
      have : ((m : ℂ) - a₁) * L₁.ω₁ = 0 := by
        push_cast at hmn; linear_combination hmn
      rcases mul_eq_zero.mp this with h | h
      · linear_combination -h
      · exact absurd h hω₁
    apply hirr m
    have : ((m ^ 2 - t * m + q : ℤ) : ℂ) = 0 := by push_cast; rw [← ha]; exact hq₁
    exact_mod_cast this

  have ha₁₂ : a₁ = a₂ ∨ a₁ = t - a₂ := by
    have : (a₁ - a₂) * (a₁ - (t - a₂)) = 0 := by linear_combination hq₁ - hq₂
    rcases mul_eq_zero.mp this with h | h
    · left; linear_combination h
    · right; linear_combination h
  have hs₁₂ : ∀ l ∈ L₂.lattice, a₁ * l ∈ L₂.lattice := by
    intro l hl
    rcases ha₁₂ with rfl | rfl
    · exact hs₂ l hl
    · rw [sub_mul]
      exact L₂.lattice.sub_mem (intCast_mul_mem_lattice L₂ t hl) (hs₂ l hl)
  refine ⟨n * L₂.ω₁ / L₁.ω₁, ?_, ?_⟩
  · have : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    exact div_ne_zero (mul_ne_zero this hω₁') hω₁
  intro l hl
  obtain ⟨p, r, rfl⟩ := PeriodPair.mem_lattice.mp hl
  have hω₂ : L₁.ω₂ = (a₁ - m) * L₁.ω₁ / n := by
    have : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    field_simp
    linear_combination hmn
  have key : (n : ℂ) * L₂.ω₁ / L₁.ω₁ * (p * L₁.ω₁ + r * L₁.ω₂) =
      ((n * p - r * m : ℤ) : ℂ) * L₂.ω₁ + (r : ℂ) * (a₁ * L₂.ω₁) := by
    rw [hω₂]
    have : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    field_simp
    push_cast
    ring
  rw [key]
  exact L₂.lattice.add_mem (intCast_mul_mem_lattice L₂ _ L₂.ω₁_mem_lattice)
    (intCast_mul_mem_lattice L₂ r (hs₁₂ _ L₂.ω₁_mem_lattice))

theorem latticeCurve_case (L₁ L₂ : PeriodPair) (h₁Δ : L₁.DiscriminantNeZero)
    (h₂Δ : L₂.DiscriminantNeZero) (t q : ℤ) (hirr : ∀ m : ℤ, m ^ 2 - t * m + q ≠ 0)
    {α₁ : L₁.weierstrassCurve.toAffine.Point →+ L₁.weierstrassCurve.toAffine.Point}
    {α₂ : L₂.weierstrassCurve.toAffine.Point →+ L₂.weierstrassCurve.toAffine.Point}
    (hα₁ : α₁ ∈ rationalHomSet ℂ L₁.weierstrassCurve L₁.weierstrassCurve)
    (hα₂ : α₂ ∈ rationalHomSet ℂ L₂.weierstrassCurve L₂.weierstrassCurve)
    (h₁ : α₁.comp α₁ + q • AddMonoidHom.id _ = t • α₁)
    (h₂ : α₂.comp α₂ + q • AddMonoidHom.id _ = t • α₂) :
    ∃ β ∈ rationalHomSet ℂ L₁.weierstrassCurve L₂.weierstrassCurve, β ≠ 0 := by

  obtain ⟨a₁, ha₁⟩ := PeriodPair.exists_forall_apply_toPoint_eq_toPoint_mul_of_mem_rationalHomSet
    L₁ L₁ h₁Δ h₁Δ hα₁
  obtain ⟨a₂, ha₂⟩ := PeriodPair.exists_forall_apply_toPoint_eq_toPoint_mul_of_mem_rationalHomSet
    L₂ L₂ h₂Δ h₂Δ hα₂

  have stab : ∀ (L : PeriodPair) (hL : L.DiscriminantNeZero)
      (α : L.weierstrassCurve.toAffine.Point →+ L.weierstrassCurve.toAffine.Point) (a : ℂ),
      (∀ z, α (L.toPoint hL z) = L.toPoint hL (a * z)) → ∀ l ∈ L.lattice, a * l ∈ L.lattice := by
    intro L hL α a ha l hl
    rw [← T_eq_zero_iff L hL, T_apply, ← ha, L.toPoint_of_mem hL hl, _root_.map_zero]
  have quad : ∀ (L : PeriodPair) (hL : L.DiscriminantNeZero)
      (α : L.weierstrassCurve.toAffine.Point →+ L.weierstrassCurve.toAffine.Point) (a : ℂ),
      (∀ z, α (L.toPoint hL z) = L.toPoint hL (a * z)) →
      α.comp α + q • AddMonoidHom.id _ = t • α → a ^ 2 - t * a + q = 0 := by
    intro L hL α a ha hrel
    apply eq_zero_of_forall_mul_mem_lattice L
    intro z
    rw [← T_eq_zero_iff L hL]
    have hz : α (α (T L hL z)) + q • T L hL z = t • α (T L hL z) := by
      have := congrArg (fun φ : L.weierstrassCurve.toAffine.Point →+ _ => φ (T L hL z)) hrel
      simpa using this
    rw [T_apply, ha, ha] at hz
    have e : (a ^ 2 - t * a + q) * z = a * (a * z) + q * z - t * (a * z) := by ring
    rw [e, map_sub, map_add, T_intCast_mul, T_intCast_mul]
    simp only [T_apply]
    rw [hz, sub_self]
  obtain ⟨γ, hγ0, hγ⟩ := exists_transporter L₁ L₂ t q hirr a₁ a₂ (stab L₁ h₁Δ α₁ a₁ ha₁)
    (stab L₂ h₂Δ α₂ a₂ ha₂) (quad L₁ h₁Δ α₁ a₁ ha₁ h₁) (quad L₂ h₂Δ α₂ a₂ ha₂ h₂)

  obtain ⟨β, hβ, hβγ⟩ :=
    PeriodPair.exists_mem_rationalHomSet_forall_apply_toPoint_eq_toPoint_mul L₁ L₂ h₁Δ h₂Δ γ hγ
  refine ⟨β, hβ, fun hβ0 => ?_⟩
  have hz : γ * (L₂.ω₁ / (2 * γ)) = L₂.ω₁ / 2 := by field_simp
  have := hβγ (L₂.ω₁ / (2 * γ))
  rw [hβ0, AddMonoidHom.zero_apply, hz] at this
  exact L₂.ω₁_div_two_notMem_lattice ((T_eq_zero_iff L₂ h₂Δ).mp this.symm)

end LatticeCurves

section VariableChange

variable {K : Type*} [Field K] [DecidableEq K] (C : VariableChange K) (E : WeierstrassCurve K)

noncomputable def vcTo : E.toAffine.Point →+ (C • E).toAffine.Point :=
  AddMonoidHom.mk' (Affine.Point.vcInvFun C E.toAffine) (Affine.Point.vcInvFun_add C E.toAffine)

noncomputable def vcFrom : (C • E).toAffine.Point →+ E.toAffine.Point :=
  AddMonoidHom.mk' (Affine.Point.vcFun C E.toAffine) (by
    intro P Q
    have hs : ∀ R : (C • E).toAffine.Point, ∃ R₀ : E.toAffine.Point,
        R = Affine.Point.vcInvFun C E.toAffine R₀ :=
      fun R => ⟨_, (Affine.Point.vcFun_leftInverse (C := C) (W := E.toAffine) R).symm⟩
    obtain ⟨P₀, rfl⟩ := hs P
    obtain ⟨Q₀, rfl⟩ := hs Q
    rw [← Affine.Point.vcInvFun_add]
    simp only [Affine.Point.vcFun_rightInverse (C := C) (W := E.toAffine) _])

theorem vcFrom_vcTo (P : E.toAffine.Point) : vcFrom C E (vcTo C E P) = P :=
  Affine.Point.vcFun_rightInverse (C := C) (W := E.toAffine) P

theorem vcTo_vcFrom (P : (C • E).toAffine.Point) : vcTo C E (vcFrom C E P) = P :=
  Affine.Point.vcFun_leftInverse (C := C) (W := E.toAffine) P

theorem vcTo_injective : Function.Injective (vcTo C E) :=
  Function.LeftInverse.injective (vcFrom_vcTo C E)

theorem vcFrom_surjective : Function.Surjective (vcFrom C E) :=
  Function.RightInverse.surjective (vcFrom_vcTo C E)

theorem vcTo_mem_rationalHomSet : vcTo C E ∈ rationalHomSet K E (C • E) := by
  right
  refine isRationallyRepresented_of_isRat (F := K) (k := K) (W₁ := E) (W₂ := C • E) (vcTo C E)
    (fX := fun x y => ((C.u⁻¹ : Kˣ) : K) ^ 2 * (x - C.r))
    (fY := fun x y => ((C.u⁻¹ : Kˣ) : K) ^ 3 * (y - C.t - C.s * (x - C.r))) ?_ ?_
    Set.finite_empty ?_
  · exact ((IsRat.const (((C.u⁻¹ : Kˣ) : K) ^ 2)).mul (IsRat.fst.sub (IsRat.const C.r))).of_eq
      fun x y => by simp only [Algebra.algebraMap_self, RingHom.id_apply]
  · exact ((IsRat.const (((C.u⁻¹ : Kˣ) : K) ^ 3)).mul ((IsRat.snd.sub (IsRat.const C.t)).sub
      ((IsRat.const C.s).mul (IsRat.fst.sub (IsRat.const C.r))))).of_eq
      fun x y => by simp only [Algebra.algebraMap_self, RingHom.id_apply]
  · intro x y h _
    exact ⟨_, rfl⟩

theorem vcFrom_mem_rationalHomSet : vcFrom C E ∈ rationalHomSet K (C • E) E := by
  right
  refine isRationallyRepresented_of_isRat (F := K) (k := K) (W₁ := C • E) (W₂ := E) (vcFrom C E)
    (fX := fun x y => (C.u : K) ^ 2 * x + C.r)
    (fY := fun x y => (C.u : K) ^ 3 * y + (C.u : K) ^ 2 * C.s * x + C.t) ?_ ?_
    Set.finite_empty ?_
  · exact (((IsRat.const ((C.u : K) ^ 2)).mul IsRat.fst).add (IsRat.const C.r)).of_eq
      fun x y => by simp only [Algebra.algebraMap_self, RingHom.id_apply]
  · exact ((((IsRat.const ((C.u : K) ^ 3)).mul IsRat.snd).add
      ((IsRat.const ((C.u : K) ^ 2 * C.s)).mul IsRat.fst)).add (IsRat.const C.t)).of_eq
      fun x y => by simp only [Algebra.algebraMap_self, RingHom.id_apply]
  · intro x y h _
    exact ⟨_, rfl⟩

end VariableChange

section ComplexCase

theorem complex_case (X₁ X₂ : WeierstrassCurve ℂ) [X₁.IsElliptic] [X₂.IsElliptic] (t q : ℤ)
    (hirr : ∀ m : ℤ, m ^ 2 - t * m + q ≠ 0)
    {α₁ : X₁.toAffine.Point →+ X₁.toAffine.Point} {α₂ : X₂.toAffine.Point →+ X₂.toAffine.Point}
    (hα₁ : α₁ ∈ rationalHomSet ℂ X₁ X₁) (hα₂ : α₂ ∈ rationalHomSet ℂ X₂ X₂)
    (h₁ : α₁.comp α₁ + q • AddMonoidHom.id _ = t • α₁)
    (h₂ : α₂.comp α₂ + q • AddMonoidHom.id _ = t • α₂) :
    ∃ β ∈ rationalHomSet ℂ X₁ X₂, β ≠ 0 := by
  obtain ⟨L₁, C₁, hC₁⟩ := PeriodPair.exists_variableChange_smul_weierstrassCurve_eq X₁
  obtain ⟨L₂, C₂, hC₂⟩ := PeriodPair.exists_variableChange_smul_weierstrassCurve_eq X₂
  subst hC₁ hC₂

  have transport : ∀ (L : PeriodPair) (C : VariableChange ℂ)
      (α : (C • L.weierstrassCurve).toAffine.Point →+ (C • L.weierstrassCurve).toAffine.Point),
      α ∈ rationalHomSet ℂ (C • L.weierstrassCurve) (C • L.weierstrassCurve) →
      α.comp α + q • AddMonoidHom.id _ = t • α →
      let α' := (vcFrom C L.weierstrassCurve).comp (α.comp (vcTo C L.weierstrassCurve))
      α' ∈ rationalHomSet ℂ L.weierstrassCurve L.weierstrassCurve ∧
        α'.comp α' + q • AddMonoidHom.id _ = t • α' := by
    intro L C α hα hrel
    refine ⟨?_, ?_⟩
    · exact WeierstrassCurve.comp_mem_rationalHomSet ℂ _ _ _
        (WeierstrassCurve.comp_mem_rationalHomSet ℂ _ _ _ (vcTo_mem_rationalHomSet C _) hα)
        (vcFrom_mem_rationalHomSet C _)
    · have key : ∀ P, α (α P) + q • P = t • α P := fun P => by
        have := congrArg (fun φ : (C • L.weierstrassCurve).toAffine.Point →+ _ => φ P) hrel
        simpa using this
      ext P
      have hk := congrArg (vcFrom C L.weierstrassCurve) (key (vcTo C L.weierstrassCurve P))
      rw [map_add, map_zsmul, map_zsmul, vcFrom_vcTo] at hk
      simpa [vcTo_vcFrom] using hk
  obtain ⟨hα₁', h₁'⟩ := transport L₁ C₁ α₁ hα₁ h₁
  obtain ⟨hα₂', h₂'⟩ := transport L₂ C₂ α₂ hα₂ h₂
  obtain ⟨β', hβ', hβ'0⟩ := latticeCurve_case L₁ L₂ (PeriodPair.discriminant_ne_zero L₁)
    (PeriodPair.discriminant_ne_zero L₂) t q hirr hα₁' hα₂' h₁' h₂'
  refine ⟨(vcTo C₂ L₂.weierstrassCurve).comp (β'.comp (vcFrom C₁ L₁.weierstrassCurve)), ?_, ?_⟩
  · exact WeierstrassCurve.comp_mem_rationalHomSet ℂ _ _ _
      (WeierstrassCurve.comp_mem_rationalHomSet ℂ _ _ _ (vcFrom_mem_rationalHomSet C₁ _) hβ')
      (vcTo_mem_rationalHomSet C₂ _)
  · intro h0
    apply hβ'0
    ext Q
    obtain ⟨P, rfl⟩ := vcFrom_surjective C₁ L₁.weierstrassCurve Q
    have h0P : vcTo C₂ L₂.weierstrassCurve (β' (vcFrom C₁ L₁.weierstrassCurve P)) = 0 :=
      congrArg (fun φ : (C₁ • L₁.weierstrassCurve).toAffine.Point →+ _ => φ P) h0
    rw [AddMonoidHom.zero_apply]
    exact vcTo_injective C₂ L₂.weierstrassCurve (h0P.trans (_root_.map_zero _).symm)

end ComplexCase

section RingHomToComplex

variable {k : Type*} [Field k] [IsAlgClosed k] [CharZero k] [DecidableEq k]

theorem push_quadratic {K : Type*} [Field K] [Algebra k K] [IsAlgClosed K] [CharZero K]
    [DecidableEq K] (X : WeierstrassCurve k) [X.IsElliptic] (t q : ℤ)
    {α : Pt k X →+ Pt k X} {α' : Pt K X →+ Pt K X} (hα' : α' ∈ rationalHomSet K X X)
    (hc : ∀ P : Pt k X, α' (Point.map (IsScalarTower.toAlgHom k k K) P) =
      Point.map (IsScalarTower.toAlgHom k k K) (α P))
    (hrel : α.comp α + q • AddMonoidHom.id _ = t • α) :
    α'.comp α' + q • AddMonoidHom.id _ = t • α' := by
  set ι := IsScalarTower.toAlgHom k k K
  have hδ : α'.comp α' + q • AddMonoidHom.id _ - t • α' ∈ rationalHomSet K X X :=
    quad_mem_rationalHomSet hα' t q
  have key : ∀ P : Pt k X, α (α P) + q • P - t • α P = 0 := fun P => by
    have := congrArg (fun φ : Pt k X →+ Pt k X => φ P) hrel
    simp only [AddMonoidHom.add_apply, AddMonoidHom.coe_comp, Function.comp_apply,
      AddMonoidHom.smul_apply, AddMonoidHom.id_apply] at this
    rw [this, sub_self]
  have hinf : (Set.range (Point.map (W' := X) ι)).Infinite := by
    haveI : Infinite (Pt k X) := infinite_point
    exact Set.infinite_range_of_injective (Point.map_injective ι)
  have hzero := eq_zero_of_infinite_zeros hδ hinf (by
    rintro _ ⟨P, rfl⟩
    simp only [AddMonoidHom.sub_apply, AddMonoidHom.add_apply, AddMonoidHom.coe_comp,
      Function.comp_apply, AddMonoidHom.smul_apply, AddMonoidHom.id_apply]
    rw [hc, hc, ← map_zsmul, ← map_zsmul, ← map_add, ← map_sub, key P, _root_.map_zero])
  exact sub_eq_zero.mp hzero

theorem of_ringHom_complex (f : k →+* ℂ) (X₁ X₂ : WeierstrassCurve k) [X₁.IsElliptic]
    [X₂.IsElliptic] (t q : ℤ) (hirr : ∀ m : ℤ, m ^ 2 - t * m + q ≠ 0)
    {α₁ : Pt k X₁ →+ Pt k X₁} {α₂ : Pt k X₂ →+ Pt k X₂}
    (hα₁ : α₁ ∈ rationalHomSet k X₁ X₁) (hα₂ : α₂ ∈ rationalHomSet k X₂ X₂)
    (h₁ : α₁.comp α₁ + q • AddMonoidHom.id _ = t • α₁)
    (h₂ : α₂.comp α₂ + q • AddMonoidHom.id _ = t • α₂) :
    ∃ β ∈ rationalHomSet k X₁ X₂, β ≠ 0 := by
  letI : Algebra k ℂ := f.toAlgebra

  obtain ⟨α₁', hα₁', hc₁⟩ :=
    WeierstrassCurve.exists_mem_rationalHomSet_apply_map_eq_map_apply k ℂ X₁ X₁ hα₁
  obtain ⟨α₂', hα₂', hc₂⟩ :=
    WeierstrassCurve.exists_mem_rationalHomSet_apply_map_eq_map_apply k ℂ X₂ X₂ hα₂
  have h₁' := push_quadratic X₁ t q hα₁' hc₁ h₁
  have h₂' := push_quadratic X₂ t q hα₂' hc₂ h₂
  haveI i₁ : (X₁.baseChange ℂ).IsElliptic := (inferInstance : (X₁.map (algebraMap k ℂ)).IsElliptic)
  haveI i₂ : (X₂.baseChange ℂ).IsElliptic := (inferInstance : (X₂.map (algebraMap k ℂ)).IsElliptic)

  obtain ⟨βC, hβC, hβC0⟩ := complex_case (X₁.baseChange ℂ) (X₂.baseChange ℂ) t q hirr
    (mem_rationalHomSet_baseChange_of_mem hα₁') (mem_rationalHomSet_baseChange_of_mem hα₂') h₁' h₂'

  obtain ⟨β₀, hβ₀, hcβ⟩ := WeierstrassCurve.exists_mem_rationalHomSet_apply_map_eq_map_apply_of_mem_rationalHomSet_baseChange
    ℂ X₁ X₂ hβC
  refine ⟨β₀, hβ₀, fun h0 => hβC0 ?_⟩
  have hinf : (Set.range (Point.map (W' := X₁) (IsScalarTower.toAlgHom k k ℂ))).Infinite := by
    haveI : Infinite (Pt k X₁) := infinite_point
    exact Set.infinite_range_of_injective (Point.map_injective _)
  refine eq_zero_of_infinite_zeros (F := ℂ) (k := ℂ) (W₁ := X₁.baseChange ℂ)
    (W₂ := X₂.baseChange ℂ) hβC hinf ?_
  rintro _ ⟨P, rfl⟩
  refine (hcβ P).trans ?_
  rw [h0, AddMonoidHom.zero_apply, _root_.map_zero]
  rfl

end RingHomToComplex

section Embedding

open Cardinal

universe u

theorem exists_ringHom_complex (k : Type u) [Field k] [CharZero k] (hk : #k ≤ 𝔠) :
    Nonempty (k →+* ℂ) := by
  let R := MvPolynomial ℝ k
  let K := AlgebraicClosure (FractionRing R)

  let g₁ : k →+* R := MvPolynomial.C
  let g₂ : R →+* FractionRing R := algebraMap R (FractionRing R)
  let g₃ : FractionRing R →+* K := algebraMap (FractionRing R) K
  have hg₂ : Function.Injective g₂ := IsFractionRing.injective R (FractionRing R)
  have hg₃ : Function.Injective g₃ := (algebraMap (FractionRing R) K).injective

  have hR : #R = 𝔠 := by
    have h := MvPolynomial.cardinalMk_eq_max_lift (σ := ℝ) (R := k)
    rw [h]
    simp only [Cardinal.lift_uzero, Cardinal.mk_real, Cardinal.lift_continuum]
    apply le_antisymm
    · exact max_le (max_le hk le_rfl) Cardinal.aleph0_le_continuum
    · exact le_max_of_le_left (le_max_right _ _)
  have hF : #(FractionRing R) = 𝔠 := by
    rw [← hR]; exact Localization.cardinalMk le_rfl
  have hKle : #K ≤ 𝔠 := by
    have := Algebra.IsAlgebraic.cardinalMk_le_max (FractionRing R) K
    rw [hF] at this
    exact this.trans (max_le le_rfl Cardinal.aleph0_le_continuum)
  have hKge : 𝔠 ≤ #K := by
    have hinj : Function.Injective (fun r : ℝ => g₃ (g₂ (MvPolynomial.X r))) :=
      fun r r' h => MvPolynomial.X_injective (hg₂ (hg₃ h))
    have := Cardinal.lift_mk_le_lift_mk_of_injective hinj
    simpa [Cardinal.mk_real] using this
  have hK : #K = 𝔠 := le_antisymm hKle hKge
  have hequiv : Nonempty (K ≃ ℂ) := by
    rw [← Cardinal.lift_mk_eq'.{u, 0}]
    simp [hK]
  haveI : CharZero K := by
    have hinj : Function.Injective ((g₃.comp g₂).comp g₁) := hg₃.comp (hg₂.comp g₁.injective)
    exact charZero_of_injective_ringHom hinj
  obtain ⟨e⟩ := IsAlgClosed.ringEquiv_of_equiv_of_charZero (K := K) (L := ℂ)
    (by rw [hK]; exact Cardinal.aleph0_lt_continuum) hequiv
  exact ⟨e.toRingHom.comp ((g₃.comp g₂).comp g₁)⟩

end Embedding

end WeierstrassCurve.CMIsog
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_ne_zero_mem_rationalHomSet_of_comp_self_add_smul_eq_smul.WeierstrassCurve P2MW.S_WeierstrassCurve_exists_ne_zero_mem_rationalHomSet_of_comp_self_add_smul_eq_smul.WeierstrassCurve.CMIsog"
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_ne_zero_mem_rationalHomSet_of_comp_self_add_smul_eq_smul.WeierstrassCurve"

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
open WeierstrassCurve.CMIsog Cardinal in
theorem solution {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [DecidableEq Ω] (X₁ X₂ : WeierstrassCurve Ω) [X₁.IsElliptic] [X₂.IsElliptic] (t q : ℤ) (hirr : ∀ m : ℤ, m ^ 2 - t * m + q ≠ 0) {α₁ : X₁.toAffine.Point →+ X₁.toAffine.Point} {α₂ : X₂.toAffine.Point →+ X₂.toAffine.Point} (hα₁ : α₁ ∈ WeierstrassCurve.rationalHomSet Ω X₁ X₁) (hα₂ : α₂ ∈ WeierstrassCurve.rationalHomSet Ω X₂ X₂) (h₁ : α₁.comp α₁ + q • AddMonoidHom.id _ = t • α₁) (h₂ : α₂.comp α₂ + q • AddMonoidHom.id _ = t • α₂) : ∃ β ∈ WeierstrassCurve.rationalHomSet Ω X₁ X₂, β ≠ 0 := by
  classical

  let S : Set Ω := {X₁.a₁, X₁.a₂, X₁.a₃, X₁.a₄, X₁.a₆, X₂.a₁, X₂.a₂, X₂.a₃, X₂.a₄, X₂.a₆}
  let F₀ : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ S
  let k : IntermediateField F₀ Ω := algebraicClosure F₀ Ω
  haveI : IsAlgClosed k := IsAlgClosure.isAlgClosed F₀
  have hS : ∀ s ∈ S, s ∈ k := fun s hs => by
    have h1 : s ∈ F₀ := IntermediateField.subset_adjoin ℚ S hs
    have : (algebraMap F₀ Ω) ⟨s, h1⟩ ∈ k := IntermediateField.algebraMap_mem k _
    exact this

  have hk : #k ≤ 𝔠 := by
    have hF₀ : #F₀ ≤ ℵ₀ := by
      have h := IntermediateField.lift_cardinalMk_adjoin_le ℚ S
      have hSfin : Finite S := by
        simp only [S]
        exact Set.toFinite _
      have hSc : Cardinal.lift.{0} #S ≤ ℵ₀ := by
        rw [Cardinal.lift_le_aleph0]; exact (Cardinal.lt_aleph0_of_finite _).le
      have hQ : Cardinal.lift.{u_1, 0} #ℚ ≤ ℵ₀ := by
        rw [Cardinal.mkRat]; simp
      have h' : Cardinal.lift.{0} #F₀ ≤ ℵ₀ := h.trans (max_le (max_le hQ hSc) le_rfl)
      simpa using h'
    haveI : Module.IsTorsionFree F₀ k := inferInstance
    have := Algebra.IsAlgebraic.cardinalMk_le_max F₀ k
    exact this.trans ((max_le hF₀ le_rfl).trans Cardinal.aleph0_le_continuum)
  obtain ⟨f⟩ := exists_ringHom_complex k hk

  obtain ⟨Y₁, hY₁⟩ : ∃ V : WeierstrassCurve k, V.baseChange Ω = X₁ :=
    ⟨⟨⟨X₁.a₁, hS _ (by simp [S])⟩, ⟨X₁.a₂, hS _ (by simp [S])⟩, ⟨X₁.a₃, hS _ (by simp [S])⟩,
      ⟨X₁.a₄, hS _ (by simp [S])⟩, ⟨X₁.a₆, hS _ (by simp [S])⟩⟩, rfl⟩
  obtain ⟨Y₂, hY₂⟩ : ∃ V : WeierstrassCurve k, V.baseChange Ω = X₂ :=
    ⟨⟨⟨X₂.a₁, hS _ (by simp [S])⟩, ⟨X₂.a₂, hS _ (by simp [S])⟩, ⟨X₂.a₃, hS _ (by simp [S])⟩,
      ⟨X₂.a₄, hS _ (by simp [S])⟩, ⟨X₂.a₆, hS _ (by simp [S])⟩⟩, rfl⟩

  have pack : ∀ (V : WeierstrassCurve Ω), V = X₁ ∨ V = X₂ → V.IsElliptic ∧
      ∃ α : V.toAffine.Point →+ V.toAffine.Point, α ∈ WeierstrassCurve.rationalHomSet Ω V V ∧
        α.comp α + q • AddMonoidHom.id _ = t • α := by
    rintro V (rfl | rfl)
    · exact ⟨inferInstance, α₁, hα₁, h₁⟩
    · exact ⟨inferInstance, α₂, hα₂, h₂⟩
  obtain ⟨e₁, α₁', hα₁', h₁'⟩ := pack (Y₁.baseChange Ω) (Or.inl hY₁)
  obtain ⟨e₂, α₂', hα₂', h₂'⟩ := pack (Y₂.baseChange Ω) (Or.inr hY₂)
  suffices H : ∃ β ∈ WeierstrassCurve.rationalHomSet Ω (Y₁.baseChange Ω) (Y₂.baseChange Ω), β ≠ 0 by
    have unpack : ∀ (V₁ V₂ : WeierstrassCurve Ω), V₁ = X₁ → V₂ = X₂ →
        (∃ β ∈ WeierstrassCurve.rationalHomSet Ω V₁ V₂, β ≠ 0) →
        ∃ β ∈ WeierstrassCurve.rationalHomSet Ω X₁ X₂, β ≠ 0 := by
      rintro V₁ V₂ rfl rfl h; exact h
    exact unpack _ _ hY₁ hY₂ H
  haveI := e₁
  haveI := e₂
  have ell : ∀ (V : WeierstrassCurve k), (V.baseChange Ω).IsElliptic → V.IsElliptic := by
    intro V hV
    rw [WeierstrassCurve.isElliptic_iff] at hV ⊢
    rw [show (V.baseChange Ω).Δ = algebraMap k Ω V.Δ from V.map_Δ _] at hV
    by_contra hΔ
    have hz : V.Δ = 0 := not_not.mp (fun h' => hΔ (Ne.isUnit h'))
    rw [hz, _root_.map_zero] at hV
    exact hV.ne_zero rfl
  haveI hY₁e : Y₁.IsElliptic := ell Y₁ e₁
  haveI hY₂e : Y₂.IsElliptic := ell Y₂ e₂

  obtain ⟨γ₁, hγ₁, hcγ₁⟩ := WeierstrassCurve.exists_mem_rationalHomSet_apply_map_eq_map_apply_of_mem_rationalHomSet_baseChange
    Ω Y₁ Y₁ hα₁'
  obtain ⟨γ₂, hγ₂, hcγ₂⟩ := WeierstrassCurve.exists_mem_rationalHomSet_apply_map_eq_map_apply_of_mem_rationalHomSet_baseChange
    Ω Y₂ Y₂ hα₂'
  have descend : ∀ (V : WeierstrassCurve k)
      (α : (V.baseChange Ω).toAffine.Point →+ (V.baseChange Ω).toAffine.Point) (γ : Pt k V →+ Pt k V),
      (∀ P, α (Point.map (IsScalarTower.toAlgHom k k Ω) P) =
        Point.map (IsScalarTower.toAlgHom k k Ω) (γ P)) →
      α.comp α + q • AddMonoidHom.id _ = t • α → γ.comp γ + q • AddMonoidHom.id _ = t • γ := by
    intro V α γ hc hrel
    ext P
    apply Point.map_injective (IsScalarTower.toAlgHom k k Ω)
    have := congrArg (fun φ : (V.baseChange Ω).toAffine.Point →+ _ =>
      φ (Point.map (IsScalarTower.toAlgHom k k Ω) P)) hrel
    simp only [AddMonoidHom.add_apply, AddMonoidHom.coe_comp, Function.comp_apply,
      AddMonoidHom.smul_apply, AddMonoidHom.id_apply] at this ⊢
    rw [hc, hc, ← map_zsmul, ← map_zsmul, ← map_add] at this
    exact this
  have hq₁ := descend Y₁ α₁' γ₁ hcγ₁ h₁'
  have hq₂ := descend Y₂ α₂' γ₂ hcγ₂ h₂'

  obtain ⟨β₀, hβ₀, hβ₀0⟩ := of_ringHom_complex f Y₁ Y₂ t q hirr hγ₁ hγ₂ hq₁ hq₂

  obtain ⟨β, hβ, hcβ⟩ :=
    WeierstrassCurve.exists_mem_rationalHomSet_apply_map_eq_map_apply k Ω Y₁ Y₂ hβ₀
  refine ⟨β, mem_rationalHomSet_baseChange_of_mem hβ, fun h0 => hβ₀0 ?_⟩
  ext P
  have hP := hcβ P
  rw [h0] at hP
  have hP' : Point.map (IsScalarTower.toAlgHom k k Ω) (β₀ P) = 0 := hP.symm.trans rfl
  rw [AddMonoidHom.zero_apply]
  exact Point.map_injective _ (hP'.trans (_root_.map_zero _).symm)

end S_WeierstrassCurve_exists_ne_zero_mem_rationalHomSet_of_comp_self_add_smul_eq_smul
end P2MW
export P2MW.S_WeierstrassCurve_exists_ne_zero_mem_rationalHomSet_of_comp_self_add_smul_eq_smul (solution)
