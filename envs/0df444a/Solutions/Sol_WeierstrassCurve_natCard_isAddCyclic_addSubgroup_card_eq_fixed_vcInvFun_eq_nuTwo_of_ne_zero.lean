-- Prove2me | solution 1 for WeierstrassCurve.natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuTwo_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/f0937dc8-fe31-5238-bd74-181949294dbc

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_ModularCurve_GenusNumerics
import Theorems.Thm_AddCommGroup_natCard_isAddCyclic_addSubgroup_map_eq_of_sq_eq_neg_one_eq_nuTwo
import Theorems.Thm_WeierstrassCurve_variableChange_mk_smul_eq_self_of_sq_eq_neg_one
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_some_eq_some_div
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Theorems.Thm_WeierstrassCurve_Affine_evalEval_psi_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuTwo_of_ne_zero
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 6400000

open WeierstrassCurve WeierstrassCurve.Affine ModularCurve Polynomial

namespace P2MKcA
namespace FC1728

variable {L : Type*} [Field L] [DecidableEq L]

def xy {W : WeierstrassCurve L} : W.toAffine.Point → Option (L × L)
  | 0 => none
  | .some x y _ => some (x, y)

theorem xy_injective {W : WeierstrassCurve L} : Function.Injective (xy (W := W)) := by
  rintro (_ | ⟨x, y, h⟩) (_ | ⟨x', y', h'⟩) hh
  · rfl
  · exact absurd hh (by simp [xy])
  · exact absurd hh (by simp [xy])
  · simp only [xy, Option.some.injEq, Prod.mk.injEq] at hh
    obtain ⟨rfl, rfl⟩ := hh
    rfl

theorem xy_vcInvFun (γ : VariableChange L) {W : WeierstrassCurve L} (P : W.toAffine.Point) :
    xy (Point.vcInvFun γ W.toAffine P) = (xy P).map (fun q => (vcXInv γ q.1, vcYInv γ q.1 q.2)) := by
  rcases P with _ | ⟨x, y, h⟩ <;> rfl

def xco {W : WeierstrassCurve L} : W.toAffine.Point → Option L
  | 0 => none
  | .some x _ _ => some x

@[scoped simp] theorem xco_zero {W : WeierstrassCurve L} : xco (0 : W.toAffine.Point) = none := rfl
@[scoped simp] theorem xco_some {W : WeierstrassCurve L} {x y : L} (h : W.toAffine.Nonsingular x y) :
    xco (Point.some x y h) = some x := rfl

theorem xco_neg {W : WeierstrassCurve L} (P : W.toAffine.Point) : xco (-P) = xco P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [Point.neg_some]; rfl

theorem eq_or_eq_neg_of_xco_eq {W : WeierstrassCurve L} {P Q : W.toAffine.Point} (hPQ : xco P = xco Q) :
    P = Q ∨ P = -Q := by
  rcases P with _ | ⟨x, y, h⟩ <;> rcases Q with _ | ⟨x', y', h'⟩
  · exact Or.inl rfl
  · simp [xco] at hPQ
  · simp [xco] at hPQ
  · simp only [xco_some, Option.some.injEq] at hPQ
    subst hPQ
    have hy : y = y' ∨ y = W.toAffine.negY x y' := by
      have h1 := h.1; have h2 := h'.1
      rw [WeierstrassCurve.Affine.equation_iff] at h1 h2
      have : (y - y') * (y - W.toAffine.negY x y') = 0 := by
        rw [WeierstrassCurve.Affine.negY]; linear_combination h1 - h2
      rcases mul_eq_zero.mp this with h0 | h0
      · exact Or.inl (sub_eq_zero.mp h0)
      · exact Or.inr (sub_eq_zero.mp h0)
    rcases hy with rfl | rfl
    · exact Or.inl rfl
    · right; rw [Point.neg_some]

def castPt {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) : W₁.toAffine.Point ≃+ W₂.toAffine.Point := by
  subst e; exact AddEquiv.refl _

theorem heq_castPt {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) (P : W₁.toAffine.Point) :
    HEq P (castPt e P) := by subst e; exact HEq.rfl

theorem xy_castPt {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) (P : W₁.toAffine.Point) :
    xy (castPt e P) = xy P := by subst e; rfl

noncomputable def vcHom (γ : VariableChange L) (W : WeierstrassCurve L) (hW : γ • W = W) :
    W.toAffine.Point →+ W.toAffine.Point :=
  (castPt hW).toAddMonoidHom.comp
    { toFun := Point.vcInvFun γ W.toAffine
      map_zero' := Point.vcInvFun_zero
      map_add' := Point.vcInvFun_add γ W.toAffine }

theorem vcHom_apply (γ : VariableChange L) (W : WeierstrassCurve L) (hW : γ • W = W) (P : W.toAffine.Point) :
    vcHom γ W hW P = castPt hW (Point.vcInvFun γ W.toAffine P) := rfl

theorem heq_vcHom (γ : VariableChange L) (W : WeierstrassCurve L) (hW : γ • W = W) (P : W.toAffine.Point) :
    HEq (Point.vcInvFun γ W.toAffine P) (vcHom γ W hW P) := heq_castPt hW _

theorem xy_vcHom (γ : VariableChange L) (W : WeierstrassCurve L) (hW : γ • W = W) (P : W.toAffine.Point) :
    xy (vcHom γ W hW P) = (xy P).map (fun q => (vcXInv γ q.1, vcYInv γ q.1 q.2)) := by
  rw [vcHom_apply, xy_castPt, xy_vcInvFun]

theorem forall_exists_heq_iff_map_eq (γ : VariableChange L) (W : WeierstrassCurve L) (hW : γ • W = W)
    (hinj : Function.Injective (vcHom γ W hW)) (H : AddSubgroup W.toAffine.Point) [Finite H] :
    (∀ T ∈ H, ∃ T' ∈ H, HEq (Point.vcInvFun γ W.toAffine T) T') ↔ H.map (vcHom γ W hW) = H := by
  constructor
  · intro hH
    have hle : H.map (vcHom γ W hW) ≤ H := by
      intro y hy
      rw [AddSubgroup.mem_map] at hy
      obtain ⟨T, hT, rfl⟩ := hy
      obtain ⟨T', hT', hheq⟩ := hH T hT
      rwa [eq_of_heq ((heq_vcHom γ W hW T).symm.trans hheq)]
    exact AddSubgroup.eq_of_le_of_card_ge hle
      (Nat.card_congr (H.equivMapOfInjective _ hinj).toEquiv).le
  · intro hH T hT
    exact ⟨vcHom γ W hW T, by rw [← hH]; exact AddSubgroup.mem_map_of_mem _ hT, heq_vcHom γ W hW T⟩

theorem exists_eq_some_of_xy_eq {W : WeierstrassCurve L} {Q : W.toAffine.Point} {x y : L}
    (h : xy Q = some (x, y)) : ∃ h', Q = Point.some x y h' := by
  rcases Q with _ | ⟨x', y', h'⟩
  · exact absurd h (by simp [xy])
  · simp only [xy, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨h', rfl⟩

section Scalar

variable {V : Type*} [AddCommGroup V]

theorem exists_common_scalar {p : ℕ} [Fact p.Prime] (e : ZMod p × ZMod p ≃+ V) (σ : V →+ V)
    (heig : ∀ v : V, ∃ a : ℤ, σ v = a • v) : ∃ c : ℤ, ∀ v : V, σ v = c • v := by
  obtain ⟨a, ha⟩ := heig (e (1, 0))
  obtain ⟨b, hb⟩ := heig (e (0, 1))
  obtain ⟨c, hc⟩ := heig (e (1, 1))
  have hsum : e (1, 1) = e (1, 0) + e (0, 1) := by
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
  have key : c • e (1, 0) + c • e (0, 1) = a • e (1, 0) + b • e (0, 1) := by
    rw [← smul_add, ← hsum, ← hc, hsum, map_add, ha, hb]
  have key' : ((c : ZMod p), (c : ZMod p)) = ((a : ZMod p), (b : ZMod p)) := by
    apply e.injective
    have h1 : e ((c : ZMod p), (c : ZMod p)) = c • e (1, 0) + c • e (0, 1) := by
      rw [← map_zsmul, ← map_zsmul, ← map_add]; congr 1; ext <;> simp
    have h2 : e ((a : ZMod p), (b : ZMod p)) = a • e (1, 0) + b • e (0, 1) := by
      rw [← map_zsmul, ← map_zsmul, ← map_add]; congr 1; ext <;> simp
    rw [h1, h2, key]
  have hca : (c : ZMod p) = a := congrArg Prod.fst key'
  have hcb : (c : ZMod p) = b := congrArg Prod.snd key'
  have hpV : ∀ v : V, (p : ℤ) • v = 0 := by
    intro v
    obtain ⟨w, rfl⟩ := e.surjective v
    rw [← map_zsmul, show (p : ℤ) • w = 0 from ?_, map_zero]
    ext <;> simp [zsmul_eq_mul]
  have hzs : ∀ (m n : ℤ) (v : V), (m : ZMod p) = n → m • v = n • v := by
    intro m n v hmn
    obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub n m p).mp hmn.symm
    have : m = n + p * k := by linarith
    rw [this, add_zsmul, mul_comm, mul_zsmul, hpV, zsmul_zero, add_zero]
  refine ⟨c, fun v => ?_⟩
  obtain ⟨⟨s, t⟩, rfl⟩ := e.surjective v
  have hv : e (s, t) = (s.val : ℤ) • e (1, 0) + (t.val : ℤ) • e (0, 1) := by
    rw [← map_zsmul, ← map_zsmul, ← map_add]; congr 1; ext <;> simp
  rw [hv, map_add, map_zsmul, map_zsmul, ha, hb, smul_add, smul_comm c (s.val : ℤ), smul_comm c (t.val : ℤ),
    hzs a c _ hca.symm, hzs b c _ hcb.symm]

end Scalar

theorem xy_neg {W : WeierstrassCurve L} (P : W.toAffine.Point) :
    xy (-P) = (xy P).map (fun q => (q.1, W.toAffine.negY q.1 q.2)) := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [Affine.Point.neg_some]; rfl

theorem xco_eq_map_xy {W : WeierstrassCurve L} (P : W.toAffine.Point) : xco P = (xy P).map Prod.fst := by
  rcases P with _ | ⟨x, y, h⟩ <;> rfl

theorem natDegree_Phi_add_X_mul_PsiSq_le (W : WeierstrassCurve L) (m : ℕ) (hm : 1 ≤ m) :
    (W.Φ (m : ℤ) + X * W.ΨSq (m : ℤ)).natDegree ≤ m ^ 2 := by
  have hm2 : 1 ≤ m ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (by omega))
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · have hΦ := W.natDegree_Φ_le (m : ℤ)
    simp only [Int.natAbs_natCast] at hΦ
    exact hΦ
  · refine (natDegree_mul_le).trans ?_
    have hΨ := W.natDegree_ΨSq_le (m : ℤ)
    simp only [Int.natAbs_natCast] at hΨ
    have hX : (X : L[X]).natDegree ≤ 1 := natDegree_X_le
    omega

abbrev EA (A : L) : WeierstrassCurve L := ⟨0, 0, 0, A, 0⟩

theorem EA_Δ (A : L) : (EA A).Δ = -64 * A ^ 3 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]; ring

theorem isElliptic_EA (A : L) (hA : A ≠ 0) (h2 : (2 : L) ≠ 0) : (EA A).IsElliptic := by
  refine ⟨?_⟩
  rw [EA_Δ, isUnit_iff_ne_zero]
  have h64 : (64 : L) ≠ 0 := by
    rw [show (64 : L) = 2 ^ 6 by norm_num]
    exact pow_ne_zero _ h2
  exact mul_ne_zero (neg_ne_zero.mpr h64) (pow_ne_zero 3 hA)

theorem baseChange_self (W : WeierstrassCurve L) : (W⁄L) = W.toAffine := by
  show (W.baseChange L).toAffine = W.toAffine
  rw [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]

theorem exists_addOrderOf_eq_and_ne_nsmul [IsAlgClosed L] (A : L) (hA : A ≠ 0) (h2 : (2 : L) ≠ 0)
    (σ : (EA A).toAffine.Point →+ (EA A).toAffine.Point)
    (hσx : ∀ (x y : L) (h : (EA A).toAffine.Nonsingular x y), xco (σ (Point.some x y h)) = some (-x))
    (hσ : ∀ P : (EA A).toAffine.Point, σ (σ P) = -P)
    (p : ℕ) (hp : p.Prime) (hpL : (p : L) ≠ 0) :
    ∃ T : (EA A).toAffine.Point, addOrderOf T = p ∧ ∀ k : ℕ, σ T ≠ k • T := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hE : (EA A).IsElliptic := isElliptic_EA A hA h2
  have hσ0 : ∀ P : (EA A).toAffine.Point, σ P = 0 ↔ P = 0 := fun P =>
    ⟨fun h0 => by have := hσ P; rw [h0, map_zero] at this; exact neg_eq_zero.mp this.symm,
     fun h0 => by rw [h0, map_zero]⟩

  suffices core : ∃ (x y : L) (h : (EA A).toAffine.Nonsingular x y), addOrderOf (Point.some x y h) = p ∧
      ∀ k : ℕ, xco (k • Point.some x y h) ≠ some (-x) by
    obtain ⟨x, y, h, hord, hk⟩ := core
    refine ⟨Point.some x y h, hord, fun k hk' => hk k ?_⟩
    rw [← hk', hσx]
  rcases hp.eq_two_or_odd' with rfl | hpodd
  ·
    obtain ⟨a, ha⟩ : ∃ a : L, a ^ 2 = -A := by
      obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (-A) (n := 2) (by norm_num)
      exact ⟨a, ha⟩
    have ha0 : a ≠ 0 := by rintro rfl; apply hA; simpa using ha.symm
    have heq : (EA A).toAffine.Equation a 0 := by
      rw [WeierstrassCurve.Affine.equation_iff]; simp; linear_combination -a * ha
    have hns : (EA A).toAffine.Nonsingular a 0 := by
      rw [WeierstrassCurve.Affine.nonsingular_iff']
      refine ⟨heq, Or.inl ?_⟩
      show (0 : L) * 0 - (3 * a ^ 2 + 2 * 0 * a + A) ≠ 0
      intro h3a
      apply ha0
      have : (2 : L) * a ^ 2 = 0 := by linear_combination -h3a - ha
      simpa [h2] using this
    have hneg : -Point.some a 0 hns = Point.some a 0 hns := by
      rw [Point.neg_some]; congr 1; simp [WeierstrassCurve.Affine.negY]
    have h2T : (2 : ℕ) • Point.some a 0 hns = 0 := by
      rw [two_nsmul]; nth_rewrite 1 [← hneg]; rw [neg_add_cancel]
    have hord : addOrderOf (Point.some a 0 hns) = 2 :=
      addOrderOf_eq_prime_iff.mpr ⟨h2T, Point.some_ne_zero hns⟩
    refine ⟨a, 0, hns, hord, fun k => ?_⟩
    have hkT : k • Point.some a 0 hns = 0 ∨ k • Point.some a 0 hns = Point.some a 0 hns := by
      rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · left; rw [← two_mul, mul_nsmul, h2T, nsmul_zero]
      · right; rw [add_nsmul, mul_nsmul, h2T, nsmul_zero, zero_add, one_nsmul]
    rcases hkT with h0 | h1
    · rw [h0, xco_zero]; simp
    · rw [h1, xco_some]; simp only [ne_eq, Option.some.injEq]
      intro h; apply ha0
      have : (2 : L) * a = 0 := by linear_combination h
      simpa [h2] using this
  ·
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      rcases this.eq_or_lt with h | h
      · exact absurd hpodd (by rw [← h]; decide)
      · omega
    have hcard : Nat.card (Submodule.torsionBy ℤ (EA A).toAffine.Point p) = p ^ 2 := by
      have h := (EA A).card_torsion_of_isAlgClosed (K := L) hpL
      rwa [baseChange_self] at h
    by_contra hcon
    push Not at hcon

    have heig : ∀ T : (EA A).toAffine.Point, (p : ℤ) • T = 0 → ∃ a : ℤ, σ T = a • T := by
      intro T hpT
      rcases T with _ | ⟨x, y, h⟩
      · exact ⟨0, by rw [zero_smul]; exact map_zero σ⟩
      · have hord : addOrderOf (Point.some x y h) = p := by
          refine addOrderOf_eq_prime_iff.mpr ⟨?_, Point.some_ne_zero h⟩
          rw [← natCast_zsmul]; exact hpT
        obtain ⟨k, hk⟩ := hcon x y h hord
        have hx : xco (σ (Point.some x y h)) = xco (k • Point.some x y h) := by rw [hσx, hk]
        rcases eq_or_eq_neg_of_xco_eq hx with h1 | h1
        · exact ⟨k, by rw [h1, natCast_zsmul]⟩
        · exact ⟨-k, by rw [h1, neg_smul, natCast_zsmul]⟩

    let Ep := (Submodule.torsionBy ℤ (EA A).toAffine.Point p).toAddSubgroup
    have hEp_mem : ∀ T : (EA A).toAffine.Point, T ∈ Ep ↔ (p : ℤ) • T = 0 := fun T => Submodule.mem_torsionBy_iff _ _
    have hσEp : ∀ T ∈ Ep, σ T ∈ Ep := by
      intro T hT
      rw [hEp_mem] at hT ⊢
      rw [← map_zsmul, hT, map_zero]
    let σ' : Ep →+ Ep := (σ.domRestrict Ep).codRestrict Ep (fun T => hσEp T T.2)
    obtain ⟨eb⟩ : Nonempty (ZMod p × ZMod p ≃+ Ep) := by
      have h := (EA A).nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := L) hpL
      rwa [baseChange_self] at h
    have heig' : ∀ v : Ep, ∃ a : ℤ, σ' v = a • v := by
      rintro ⟨T, hT⟩
      obtain ⟨a, ha⟩ := heig T ((hEp_mem T).mp hT)
      exact ⟨a, Subtype.ext ha⟩
    obtain ⟨c, hc⟩ := exists_common_scalar eb σ' heig'

    obtain ⟨m, hm1, hmle, hmx⟩ : ∃ m : ℕ, 1 ≤ m ∧ 2 * m ≤ p - 1 ∧
        ∀ (x y : L) (h : (EA A).toAffine.Nonsingular x y), (p : ℤ) • Point.some x y h = 0 →
          xco ((m : ℤ) • Point.some x y h) = some (-x) := by
      let r : ℕ := ((c : ZMod p)).val
      have hr : (r : ZMod p) = c := by simp [r]
      have hrp : r < p := ZMod.val_lt _
      have hσc : ∀ (x y : L) (h : (EA A).toAffine.Nonsingular x y), (p : ℤ) • Point.some x y h = 0 →
          σ (Point.some x y h) = (r : ℤ) • Point.some x y h := by
        intro x y h hpT
        have hT : Point.some x y h ∈ Ep := (hEp_mem _).mpr hpT
        have := hc ⟨_, hT⟩
        have hval : σ (Point.some x y h) = c • Point.some x y h := congrArg Subtype.val this
        rw [hval]
        obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub (r : ℤ) c p).mp (by exact_mod_cast hr)
        have : c = r + p * k := by linarith
        rw [this, add_zsmul, mul_comm, mul_zsmul, hpT, zsmul_zero, add_zero]
      obtain ⟨x₀, y₀, h₀, hp₀⟩ : ∃ (x y : L) (h : (EA A).toAffine.Nonsingular x y), (p : ℤ) • Point.some x y h = 0 := by
        have h1 : 1 < Nat.card Ep := by rw [show Nat.card Ep = p ^ 2 from hcard]; nlinarith
        haveI : Finite Ep := Nat.finite_of_card_ne_zero (by rw [show Nat.card Ep = p ^ 2 from hcard]; positivity)
        haveI : Nontrivial Ep := Finite.one_lt_card_iff_nontrivial.mp h1
        obtain ⟨⟨T, hT⟩, hT0⟩ := exists_ne (0 : Ep)
        rcases T with _ | ⟨x, y, h⟩
        · exact absurd rfl (fun h => hT0 (Subtype.ext h))
        · exact ⟨x, y, h, (hEp_mem _).mp hT⟩
      have hr0 : r ≠ 0 := by
        intro hr0
        have := hσc x₀ y₀ h₀ hp₀
        rw [hr0, Nat.cast_zero, zero_smul, hσ0] at this
        exact Point.some_ne_zero h₀ this
      by_cases hle : 2 * r ≤ p - 1
      · refine ⟨r, Nat.one_le_iff_ne_zero.mpr hr0, hle, fun x y h hpT => ?_⟩
        rw [← hσc x y h hpT, hσx]
      · obtain ⟨k0, hk0⟩ := hpodd
        refine ⟨p - r, by omega, by omega, fun x y h hpT => ?_⟩
        have : ((p - r : ℕ) : ℤ) • Point.some x y h = -((r : ℤ) • Point.some x y h) := by
          rw [Nat.cast_sub hrp.le, sub_zsmul, hpT]; simp
        rw [this, xco_neg, ← hσc x y h hpT, hσx]

    set F : L[X] := (EA A).Φ (m : ℤ) + X * (EA A).ΨSq (m : ℤ) with hFdef
    have hFdeg : F.natDegree ≤ m ^ 2 := natDegree_Phi_add_X_mul_PsiSq_le (EA A) m hm1

    have hxm : ∀ (q : ℕ), q.Prime → m < q → ∀ (x y : L) (h : (EA A).toAffine.Nonsingular x y),
        (q : ℤ) • Point.some x y h = 0 →
        ((EA A).ΨSq (m : ℤ)).eval x ≠ 0 ∧
          xco ((m : ℤ) • Point.some x y h) = some (((EA A).Φ (m : ℤ)).eval x / ((EA A).ΨSq (m : ℤ)).eval x) := by
      intro q hq hmq x y h hqT
      haveI : Fact q.Prime := ⟨hq⟩
      have hord : addOrderOf (Point.some x y h) = q :=
        addOrderOf_eq_prime_iff.mpr ⟨by rw [← natCast_zsmul]; exact hqT, Point.some_ne_zero h⟩
      have hmT : (m : ℤ) • Point.some x y h ≠ 0 := by
        rw [natCast_zsmul]
        intro h0
        have hdvd := addOrderOf_dvd_of_nsmul_eq_zero h0
        rw [hord] at hdvd
        have := Nat.le_of_dvd (by omega) hdvd
        omega
      have hψ : ((EA A).ψ (m : ℤ)).evalEval x y ≠ 0 := fun h0 =>
        hmT ((WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff (EA A) h (m : ℤ)).mpr h0)
      obtain ⟨y', h', hmul⟩ := WeierstrassCurve.Affine.Point.zsmul_some_eq_some_div (EA A) h hψ
      refine ⟨?_, by rw [hmul, xco_some]⟩
      rw [← WeierstrassCurve.Affine.evalEval_psi_sq (EA A) h.1 (m : ℤ)]; exact pow_ne_zero 2 hψ

    have hF0 : F ≠ 0 := by
      intro hF

      obtain ⟨q, hqge, hq⟩ := Nat.exists_infinite_primes (max (m ^ 2 + 2) (ringChar L + 1))
      have hqm : m ^ 2 + 1 < q := by have := le_max_left (m ^ 2 + 2) (ringChar L + 1); omega
      have hqc : ringChar L < q := by have := le_max_right (m ^ 2 + 2) (ringChar L + 1); omega
      have hqL : (q : L) ≠ 0 := by
        intro h0
        have hdvd : ringChar L ∣ q := (ringChar.spec L q).mp h0
        rcases (Nat.dvd_prime hq).mp hdvd with h1 | h1
        · exact CharP.ringChar_ne_one h1
        · omega
      haveI : Fact q.Prime := ⟨hq⟩

      have hcardq : Nat.card (Submodule.torsionBy ℤ (EA A).toAffine.Point q) = q ^ 2 := by
        have h := (EA A).card_torsion_of_isAlgClosed (K := L) hqL
        rwa [baseChange_self] at h
      obtain ⟨x₀, y₀, h₀, hq₀⟩ : ∃ (x y : L) (h : (EA A).toAffine.Nonsingular x y), (q : ℤ) • Point.some x y h = 0 := by
        let Eq' := (Submodule.torsionBy ℤ (EA A).toAffine.Point q).toAddSubgroup
        have hq1 : 1 < q := hq.one_lt
        have h1 : 1 < Nat.card Eq' := by rw [show Nat.card Eq' = q ^ 2 from hcardq]; nlinarith
        haveI : Finite Eq' := Nat.finite_of_card_ne_zero (by rw [show Nat.card Eq' = q ^ 2 from hcardq]; positivity)
        haveI : Nontrivial Eq' := Finite.one_lt_card_iff_nontrivial.mp h1
        obtain ⟨⟨T, hT⟩, hT0⟩ := exists_ne (0 : Eq')
        rcases T with _ | ⟨x, y, h⟩
        · exact absurd rfl (fun h => hT0 (Subtype.ext h))
        · exact ⟨x, y, h, (Submodule.mem_torsionBy_iff _ _).mp hT⟩
      have hordq : addOrderOf (Point.some x₀ y₀ h₀) = q :=
        addOrderOf_eq_prime_iff.mpr ⟨by rw [← natCast_zsmul]; exact hq₀, Point.some_ne_zero h₀⟩

      have hm2q : m < q := by nlinarith
      obtain ⟨hΨ, hxq⟩ := hxm q hq hm2q x₀ y₀ h₀ hq₀
      have hΦ : ((EA A).Φ (m : ℤ)).eval x₀ = -x₀ * ((EA A).ΨSq (m : ℤ)).eval x₀ := by
        have := congrArg (Polynomial.eval x₀) hF
        rw [hFdef, eval_zero, eval_add, eval_mul, eval_X] at this
        linear_combination this
      have hx : xco (σ (Point.some x₀ y₀ h₀)) = xco ((m : ℤ) • Point.some x₀ y₀ h₀) := by
        rw [hσx, hxq, hΦ, mul_div_assoc, div_self hΨ, mul_one]

      obtain ⟨a, ha, haT⟩ : ∃ a : ℤ, (a = m ∨ a = -m) ∧ σ (Point.some x₀ y₀ h₀) = a • Point.some x₀ y₀ h₀ := by
        rcases eq_or_eq_neg_of_xco_eq hx with h1 | h1
        · exact ⟨m, Or.inl rfl, h1⟩
        · exact ⟨-m, Or.inr rfl, by rw [h1, neg_smul]⟩

      have hkill : (a * a + 1) • Point.some x₀ y₀ h₀ = 0 := by
        have := hσ (Point.some x₀ y₀ h₀)
        rw [haT, map_zsmul, haT, smul_smul] at this
        rw [add_smul, one_smul, this, neg_add_cancel]
      have hdvd : ((q : ℕ) : ℤ) ∣ a * a + 1 := by
        rw [← hordq]; exact addOrderOf_dvd_iff_zsmul_eq_zero.mpr hkill
      have hpos : 0 < a * a + 1 := by nlinarith
      have hle := Int.le_of_dvd hpos hdvd
      have hqm' : ((m : ℤ)) ^ 2 + 1 < q := by exact_mod_cast hqm
      rcases ha with rfl | rfl <;> nlinarith
    have hroot : ∀ (x y : L) (h : (EA A).toAffine.Nonsingular x y), (p : ℤ) • Point.some x y h = 0 → F.IsRoot x := by
      intro x y h hpT
      obtain ⟨hΨ, hxp⟩ := hxm p hp (by omega) x y h hpT
      have hx : xco ((m : ℤ) • Point.some x y h) = some (-x) := hmx x y h hpT
      rw [hxp, Option.some.injEq, div_eq_iff hΨ] at hx
      show F.eval x = 0
      rw [hFdef, eval_add, eval_mul, eval_X]
      linear_combination hx

    haveI hfinEp : Finite Ep := Nat.finite_of_card_ne_zero (by rw [show Nat.card Ep = p ^ 2 from hcard]; positivity)
    haveI : Fintype Ep := Fintype.ofFinite Ep
    classical
    let g : Ep → Option L := fun T => xco (T.1 : (EA A).toAffine.Point)
    let s : Finset Ep := Finset.univ.filter (fun T => T ≠ 0)
    have hs_card : s.card = p ^ 2 - 1 := by
      have : s.card + 1 = p ^ 2 := by
        rw [show s = Finset.univ.erase 0 by ext T; simp [s], Finset.card_erase_of_mem (Finset.mem_univ _),
          Finset.card_univ, ← Nat.card_eq_fintype_card, show Nat.card Ep = p ^ 2 from hcard]
        have : 1 ≤ p ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity); omega
      omega
    have hfib : ∀ b ∈ s.image g, (s.filter (fun T => g T = b)).card ≤ 2 := by
      intro b hb
      obtain ⟨T₁, hT₁, rfl⟩ := Finset.mem_image.mp hb
      have hsub : s.filter (fun T => g T = g T₁) ⊆ {T₁, -T₁} := by
        intro T hT
        rw [Finset.mem_filter] at hT
        have hx : xco (T.1 : (EA A).toAffine.Point) = xco (T₁.1 : (EA A).toAffine.Point) := hT.2
        rcases eq_or_eq_neg_of_xco_eq hx with h1 | h1
        · rw [Finset.mem_insert]; left; exact Subtype.ext h1
        · rw [Finset.mem_insert, Finset.mem_singleton]; right
          exact Subtype.ext (by rw [h1]; rfl)
      exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _ |>.trans (by simp))
    have hle : s.card ≤ 2 * (s.image g).card := Finset.card_le_mul_card_image s 2 hfib
    have himg : s.image g ⊆ (F.roots.toFinset).image some := by
      intro b hb
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hb
      rw [Finset.mem_filter] at hT
      obtain ⟨⟨T, hTp⟩, hT0⟩ := T, hT.2
      rcases T with _ | ⟨x, y, h⟩
      · exact absurd rfl (fun h => hT0 (Subtype.ext h))
      · refine Finset.mem_image.mpr ⟨x, ?_, rfl⟩
        rw [Multiset.mem_toFinset, mem_roots hF0]
        exact hroot x y h ((hEp_mem _).mp hTp)
    have hR : ((F.roots.toFinset).image some).card ≤ m ^ 2 := by
      refine Finset.card_image_le.trans ((Multiset.toFinset_card_le _).trans ?_)
      exact (Polynomial.card_roots' F).trans hFdeg
    have hfinal : p ^ 2 - 1 ≤ 2 * m ^ 2 := by
      rw [← hs_card]; exact hle.trans (Nat.mul_le_mul_left 2 ((Finset.card_le_card himg).trans hR))
    have h4 : 4 * m ^ 2 ≤ (p - 1) ^ 2 := by nlinarith
    have hp1 : 1 ≤ p := hp.one_lt.le
    zify [hp1, Nat.one_le_iff_ne_zero.mpr (show p ^ 2 ≠ 0 by positivity)] at hfinal h4 hmle
    nlinarith

end P2MKcA.FC1728
p2m_reactivate "P2MW.S_WeierstrassCurve_natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuTwo_of_ne_zero.P2MKcA P2MW.S_WeierstrassCurve_natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuTwo_of_ne_zero.P2MKcA.FC1728"
p2m_reactivate "P2MW.S_WeierstrassCurve_natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuTwo_of_ne_zero.P2MKcA"

open P2MKcA.FC1728 in
theorem solution
    {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L]
    (A : L) (hA : A ≠ 0) (u : Lˣ) (hu : (u : L) ^ 2 = -1)
    (h2 : (2 : L) ≠ 0) (N : ℕ) (hN : (N : L) ≠ 0) :
    Nat.card {H : AddSubgroup (⟨0, 0, 0, A, 0⟩ : WeierstrassCurve L).toAffine.Point //
        IsAddCyclic H ∧ Nat.card H = N ∧
        ∀ T ∈ H, ∃ T' ∈ H, HEq (Point.vcInvFun (⟨u, 0, 0, 0⟩ : VariableChange L)
          (⟨0, 0, 0, A, 0⟩ : WeierstrassCurve L).toAffine T) T'}
      = nuTwo N := by
  have hN0 : N ≠ 0 := by rintro rfl; exact hN Nat.cast_zero
  haveI : NeZero N := ⟨hN0⟩
  set W : WeierstrassCurve L := ⟨0, 0, 0, A, 0⟩ with hWdef
  set γ : VariableChange L := ⟨u, 0, 0, 0⟩ with hγdef
  haveI hE : W.IsElliptic := isElliptic_EA A hA h2

  have hW : γ • W = W := WeierstrassCurve.variableChange_mk_smul_eq_self_of_sq_eq_neg_one u hu A
  let σ : W.toAffine.Point →+ W.toAffine.Point := vcHom γ W hW
  have hi2 : ((u⁻¹ : Lˣ) : L) ^ 2 = -1 := by
    rw [Units.val_inv_eq_inv_val, inv_pow, hu, inv_neg, inv_one]

  have hσ : ∀ P : W.toAffine.Point, σ (σ P) = -P := by
    intro P
    apply xy_injective
    rw [xy_vcHom, xy_vcHom, xy_neg]
    rcases xy P with _ | ⟨x, y⟩
    · rfl
    · simp only [Option.map_some, hγdef, hWdef, vcXInv, vcYInv, Affine.negY, sub_zero, zero_mul,
        Option.some.injEq, Prod.mk.injEq]
      constructor
      · linear_combination (((u⁻¹ : Lˣ) : L) ^ 2 * x - x) * hi2
      · linear_combination (((u⁻¹ : Lˣ) : L) ^ 4 * y - ((u⁻¹ : Lˣ) : L) ^ 2 * y + y) * hi2

  have hσx : ∀ (x y : L) (h : W.toAffine.Nonsingular x y), xco (σ (Point.some x y h)) = some (-x) := by
    intro x y h
    rw [xco_eq_map_xy, xy_vcHom]
    simp only [xy, Option.map_some, hγdef, vcXInv, sub_zero, hi2, Option.some.injEq]
    ring
  have σinj : Function.Injective σ := fun a b h => by
    have h' := congrArg σ h; rwa [hσ, hσ, neg_inj] at h'

  have hns : ∀ p : ℕ, p.Prime → p ∣ N → ∃ a : W.toAffine.Point, addOrderOf a = p ∧ ∀ k : ℕ, σ a ≠ k • a := by
    intro p hp hpN
    have hpL : (p : L) ≠ 0 := by
      obtain ⟨c, rfl⟩ := hpN
      intro h0; apply hN; push_cast; rw [h0, zero_mul]
    exact exists_addOrderOf_eq_and_ne_nsmul A hA h2 σ hσx hσ p hp hpL

  obtain ⟨e⟩ : Nonempty (ZMod N × ZMod N ≃+ Submodule.torsionBy ℤ W.toAffine.Point N) := by
    have h := W.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := L) hN
    rwa [baseChange_self] at h

  rw [← AddCommGroup.natCard_isAddCyclic_addSubgroup_map_eq_of_sq_eq_neg_one_eq_nuTwo N e σ hσ hns]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun H => ?_)
  refine ⟨fun ⟨hc, hcard, hst⟩ => ⟨hc, hcard, ?_⟩, fun ⟨hc, hcard, hst⟩ => ⟨hc, hcard, ?_⟩⟩
  · haveI : Finite H := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hN0)
    exact (forall_exists_heq_iff_map_eq γ W hW σinj H).mp hst
  · haveI : Finite H := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hN0)
    exact (forall_exists_heq_iff_map_eq γ W hW σinj H).mpr hst

end S_WeierstrassCurve_natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuTwo_of_ne_zero
end P2MW
export P2MW.S_WeierstrassCurve_natCard_isAddCyclic_addSubgroup_card_eq_fixed_vcInvFun_eq_nuTwo_of_ne_zero (solution)
