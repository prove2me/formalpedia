-- Prove2me | solution 1 for WeierstrassCurve.exists_algEquiv_map_eq_smul_and_map_eq_smul_add_of_transcendental_j
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/00766ce4-9b2c-5aee-9d8f-24c3271c1929

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_ModularCurve_exists_point_tateBase_qTwist_eq_add_of_isPrimitiveRoot
import Theorems.Thm_ModularCurve_j_tateLaurent
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_algEquiv_map_eq_smul_and_map_eq_smul_add_of_transcendental_j
p2m_attr_erase "instance" "ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero"
p2m_attr_erase "simp" "Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "ModularCurve WeierstrassCurve~cusp WeierstrassCurve.Affine Polynomial"

noncomputable section

namespace P2MKcCuspMonodromy

universe u v w

theorem u_sq_eq_one_and_r_eq_zero_of_smul_eq {F : Type u} [Field F] (A : VariableChange F)
    (W : WeierstrassCurve F) (h : A • W = W) (hc₄ : W.c₄ ≠ 0) (hc₆ : W.c₆ ≠ 0) :
    ((A.u : F)) ^ 2 = 1 ∧ A.r = 0 := by
  have h4 : (A • W).c₄ = W.c₄ := by rw [h]
  have h6 : (A • W).c₆ = W.c₆ := by rw [h]
  rw [variableChange_c₄] at h4
  rw [variableChange_c₆] at h6
  have hu4 : ((A.u⁻¹ : Fˣ) : F) ^ 4 = 1 := by
    have := mul_right_cancel₀ hc₄ (h4.trans (one_mul _).symm)
    exact this
  have hu6 : ((A.u⁻¹ : Fˣ) : F) ^ 6 = 1 := by
    have := mul_right_cancel₀ hc₆ (h6.trans (one_mul _).symm)
    exact this
  have hv2 : ((A.u⁻¹ : Fˣ) : F) ^ 2 = 1 := by
    have hne : ((A.u⁻¹ : Fˣ) : F) ^ 4 ≠ 0 := by rw [hu4]; exact one_ne_zero
    have : ((A.u⁻¹ : Fˣ) : F) ^ 4 * ((A.u⁻¹ : Fˣ) : F) ^ 2 = ((A.u⁻¹ : Fˣ) : F) ^ 4 * 1 := by
      rw [← pow_add, mul_one]; exact hu6.trans hu4.symm
    exact mul_left_cancel₀ hne this
  have hu2 : ((A.u : F)) ^ 2 = 1 := by
    have hmul : ((A.u : F)) * ((A.u⁻¹ : Fˣ) : F) = 1 := by
      rw [Units.val_inv_eq_inv_val]; exact mul_inv_cancel₀ A.u.ne_zero
    calc ((A.u : F)) ^ 2 = ((A.u : F)) ^ 2 * (((A.u⁻¹ : Fˣ) : F) ^ 2) := by rw [hv2, mul_one]
      _ = (((A.u : F)) * ((A.u⁻¹ : Fˣ) : F)) ^ 2 := by ring
      _ = 1 := by rw [hmul, one_pow]
  refine ⟨hu2, ?_⟩
  have h2 : (A • W).b₂ = W.b₂ := by rw [h]
  have h4' : (A • W).b₄ = W.b₄ := by rw [h]
  rw [variableChange_b₂, hv2, one_mul] at h2
  rw [variableChange_b₄] at h4'
  have hv4 : ((A.u⁻¹ : Fˣ) : F) ^ 4 = 1 := hu4
  rw [hv4, one_mul] at h4'
  have e1 : 12 * A.r = 0 := by linear_combination h2
  have e2 : A.r * W.b₂ + 6 * A.r ^ 2 = 0 := by linear_combination h4'
  have e3 : A.r * W.c₄ = 0 := by
    have hc : W.c₄ = W.b₂ ^ 2 - 24 * W.b₄ := rfl
    rw [hc]
    linear_combination (W.b₂ - 6 * A.r) * e2 + (3 * A.r ^ 2 - 2 * W.b₄) * e1
  rcases mul_eq_zero.1 e3 with h0 | h0
  · exact h0
  · exact absurd h0 hc₄

theorem exists_pointEquiv_of_smul_eq {F : Type u} [Field F] [DecidableEq F] (C : VariableChange F)
    (W V : WeierstrassCurve F) (h : C • W = V) :
    ∃ e : V.toAffine.Point ≃+ W.toAffine.Point,
      ∀ (x y : F) (hxy : V.toAffine.Nonsingular x y),
        ∃ h' : W.toAffine.Nonsingular ((C.u : F) ^ 2 * x + C.r)
            ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t),
          e (.some x y hxy) = .some ((C.u : F) ^ 2 * x + C.r)
            ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t) h' := by
  subst h
  let e₀ : (C • W).toAffine.Point ≃ W.toAffine.Point := Point.variableChangeEquiv C W
  have hinv : ∀ P Q : W.toAffine.Point, e₀.symm (P + Q) = e₀.symm P + e₀.symm Q :=
    fun P Q => Point.vcInvFun_add C W P Q
  let eI : W.toAffine.Point ≃+ (C • W).toAffine.Point := AddEquiv.mk' e₀.symm hinv
  refine ⟨eI.symm, fun x y hxy => ?_⟩
  refine ⟨(nonsingular_variableChange_iff x y).mp hxy, ?_⟩
  show e₀ (.some x y hxy) = _
  rfl

theorem exists_eq_of_nsmul_eq_zero {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    (hf : Function.Injective f) (N : ℕ) [NeZero N]
    (hA : Nat.card {P : A // N • P = 0} = N ^ 2) (hB : Nat.card {Q : B // N • Q = 0} = N ^ 2)
    (Q : B) (hQ : N • Q = 0) : ∃ P : A, N • P = 0 ∧ f P = Q := by
  haveI : Finite {Q : B // N • Q = 0} :=
    Nat.finite_of_card_ne_zero (by rw [hB]; exact pow_ne_zero 2 (NeZero.ne N))
  let g : {P : A // N • P = 0} → {Q : B // N • Q = 0} := fun P =>
    ⟨f P.1, by rw [← map_nsmul, P.2, map_zero]⟩
  have hg : Function.Injective g := fun P P' h => Subtype.ext (hf (congrArg Subtype.val h))
  have hbij := hg.bijective_of_nat_card_le (by rw [hA, hB])
  obtain ⟨P, hP⟩ := hbij.2 ⟨Q, hQ⟩
  exact ⟨P.1, P.2, congrArg Subtype.val hP⟩

theorem natCard_torsion_of_isAlgClosed {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    [IsAlgClosed Ω] [DecidableEq Ω] (E : WeierstrassCurve k) [E.IsElliptic] (N : ℕ) [NeZero N]
    (hN : (N : Ω) ≠ 0) :
    Nat.card {Q : (E.baseChange Ω).toAffine.Point // N • Q = 0} = N ^ 2 := by
  obtain ⟨e⟩ := E.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := Ω) hN
  have h1 : Nat.card (Submodule.torsionBy ℤ (E.baseChange Ω).toAffine.Point N) = N ^ 2 := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zmod, sq]
  rw [← h1]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun Q => ?_)
  rw [Submodule.mem_torsionBy_iff]
  change N • Q = 0 ↔ ((N : ℤ)) • Q = 0
  rw [natCast_zsmul]

theorem forall_eq_or_forall_eq_neg {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f g : A →+ B) (h : ∀ a, f a = g a ∨ f a = -g a) :
    (∀ a, f a = g a) ∨ (∀ a, f a = -g a) := by
  by_contra hcon
  rw [not_or, not_forall, not_forall] at hcon
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hcon
  have ha' : f a = -g a := (h a).resolve_left ha
  have hb' : f b = g b := (h b).resolve_right hb
  rcases h (a + b) with hab | hab
  · apply ha
    have : f a = f (a + b) - f b := by rw [map_add, add_sub_cancel_right]
    rw [this, hab, hb', map_add, add_sub_cancel_right]
  · apply hb
    have : f b = f (a + b) - f a := by rw [map_add, add_sub_cancel_left]
    rw [this, hab, ha', map_add, neg_add, sub_neg_eq_add, neg_add_cancel_comm]

section MapPt

variable {R : Type u} {S : Type v} [Field R] [Field S] [DecidableEq R] [DecidableEq S]

def mapPtFun (W₀ : WeierstrassCurve R) (W₁ : WeierstrassCurve S) (f : R →+* S)
    (hf : Function.Injective f) (hW : W₀.map f = W₁) :
    W₀.toAffine.Point → W₁.toAffine.Point
  | 0 => 0
  | .some x y h => .some (f x) (f y) (hW ▸ (Affine.map_nonsingular _ hf x y).mpr h)

theorem mapPtFun_add (W₀ : WeierstrassCurve R) (W₁ : WeierstrassCurve S) (f : R →+* S)
    (hf : Function.Injective f) (hW : W₀.map f = W₁) (P Q : W₀.toAffine.Point) :
    mapPtFun W₀ W₁ f hf hW (P + Q) = mapPtFun W₀ W₁ f hf hW P + mapPtFun W₀ W₁ f hf hW Q := by
  subst hW
  rcases P with (_ | ⟨x₁, y₁, h₁⟩) <;> rcases Q with (_ | ⟨x₂, y₂, h₂⟩)
  any_goals rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = W₀.toAffine.negY x₂ y₂
  · rw [Point.add_of_Y_eq hxy.left hxy.right]
    show (0 : (W₀.map f).toAffine.Point) = .some (f x₁) (f y₁) _ + .some (f x₂) (f y₂) _
    rw [Point.add_of_Y_eq (congr_arg _ hxy.left) (by rw [hxy.right, Affine.map_negY])]
  · have hxy' : ¬((f x₁) = (f x₂) ∧ f y₁ = (W₀.map f).toAffine.negY (f x₂) (f y₂)) := by
      rintro ⟨h1, h2⟩
      exact hxy ⟨hf h1, hf (by rw [Affine.map_negY] at h2; exact h2)⟩
    rw [Point.add_some hxy]
    show Point.some (f _) (f _) _ = .some (f x₁) (f y₁) _ + .some (f x₂) (f y₂) _
    simp only [Point.add_some hxy', Affine.map_slope, Affine.map_addX, Affine.map_addY]

def mapPt (W₀ : WeierstrassCurve R) (W₁ : WeierstrassCurve S) (f : R →+* S)
    (hf : Function.Injective f) (hW : W₀.map f = W₁) :
    W₀.toAffine.Point →+ W₁.toAffine.Point where
  toFun := mapPtFun W₀ W₁ f hf hW
  map_zero' := rfl
  map_add' := mapPtFun_add W₀ W₁ f hf hW

theorem mapPt_zero (W₀ : WeierstrassCurve R) (W₁ : WeierstrassCurve S) (f : R →+* S)
    (hf : Function.Injective f) (hW : W₀.map f = W₁) : mapPt W₀ W₁ f hf hW 0 = 0 := rfl

theorem mapPt_some (W₀ : WeierstrassCurve R) (W₁ : WeierstrassCurve S) (f : R →+* S)
    (hf : Function.Injective f) (hW : W₀.map f = W₁) (x y : R) (h : W₀.toAffine.Nonsingular x y) :
    ∃ h', mapPt W₀ W₁ f hf hW (.some x y h) = .some (f x) (f y) h' := ⟨_, rfl⟩

theorem mapPt_injective (W₀ : WeierstrassCurve R) (W₁ : WeierstrassCurve S) (f : R →+* S)
    (hf : Function.Injective f) (hW : W₀.map f = W₁) : Function.Injective (mapPt W₀ W₁ f hf hW) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · exact absurd h.symm (Point.some_ne_zero _)
  · exact absurd h (Point.some_ne_zero _)
  · obtain ⟨hx, hy⟩ := Point.some.inj h
    have hx' := hf hx
    have hy' := hf hy
    subst hx' hy'
    rfl

end MapPt

theorem ne_of_transcendental {R A : Type*} [Field R] [Field A] [Algebra R A] {a : A}
    (ha : Transcendental R a) (n : ℕ) : a ≠ (n : A) := by
  intro h
  apply ha
  rw [h, show ((n : A)) = algebraMap R A n by simp]
  exact isAlgebraic_algebraMap _

theorem c₄_ne_zero_of_transcendental_j {A : Type*} [Field A] {R : Type*} [Field R] [Algebra R A]
    (W : WeierstrassCurve A) [W.IsElliptic] (hW : Transcendental R W.j) : W.c₄ ≠ 0 := by
  intro h
  have : W.j = 0 := W.j_eq_zero h
  exact ne_of_transcendental hW 0 (by rw [this, Nat.cast_zero])

theorem c₆_ne_zero_of_transcendental_j {A : Type*} [Field A] {R : Type*} [Field R] [Algebra R A]
    (W : WeierstrassCurve A) [W.IsElliptic] (hW : Transcendental R W.j) : W.c₆ ≠ 0 := by
  intro h
  have hrel := W.c_relation
  rw [h, zero_pow two_ne_zero, sub_zero] at hrel
  have : W.j = 1728 := by
    rw [WeierstrassCurve.j, ← hrel, ← W.coe_Δ', mul_left_comm, Units.inv_mul, mul_one]
  exact ne_of_transcendental hW 1728 (by rw [this]; norm_num)

theorem transcendental_of_algHom {K A B : Type*} [Field K] [Ring A] [Ring B] [Algebra K A]
    [Algebra K B] (f : A →ₐ[K] B) (hf : Function.Injective f) {x : A} (hx : Transcendental K x) :
    Transcendental K (f x) := by
  intro halg
  apply hx
  obtain ⟨p, hp0, hp⟩ := halg
  refine ⟨p, hp0, hf ?_⟩
  rw [← Polynomial.aeval_algHom_apply, hp, map_zero]

section Main

variable (K : Type u) [Field K] [IsAlgClosed K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0)
    (k Ω : Type v) [Field k] [Field Ω] [DecidableEq Ω] [Algebra K k] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower K k Ω] [IsAlgClosure k Ω] (E : WeierstrassCurve k) [E.IsElliptic]
    (hE : Transcendental K E.j) (hgen : IntermediateField.adjoin K ({E.j} : Set k) = ⊤)

theorem exists_algEquiv_ratFunc {x : k} (hx : Transcendental K x)
    (hgen : IntermediateField.adjoin K ({x} : Set k) = ⊤) :
    ∃ φ : RatFunc K ≃ₐ[K] k, φ (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) = x := by
  have hinj : Function.Injective (Polynomial.aeval (R := K) x) := transcendental_iff_injective.mp hx
  have hφ : nonZeroDivisors (Polynomial K) ≤
      Submonoid.comap (Polynomial.aeval (R := K) x) (nonZeroDivisors k) := by
    intro p hp
    rw [Submonoid.mem_comap]
    apply mem_nonZeroDivisors_of_ne_zero
    intro h0
    have : p = 0 := hinj (by rw [h0, map_zero])
    exact nonZeroDivisors.ne_zero hp this
  set ψ : RatFunc K →ₐ[K] k := RatFunc.liftAlgHom (Polynomial.aeval x) hφ with hψ
  have hψX : ψ (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) = x := by
    have h := RatFunc.liftAlgHom_apply_div (Polynomial.aeval (R := K) x) hφ Polynomial.X 1
    rw [map_one, div_one, map_one, div_one, Polynomial.aeval_X] at h
    exact h
  have hsurj : Function.Surjective ψ := by
    intro y
    have hy : y ∈ (⊤ : IntermediateField K k) := IntermediateField.mem_top
    rw [← hgen] at hy
    have hle : IntermediateField.adjoin K ({x} : Set k) ≤ ψ.fieldRange := by
      rw [IntermediateField.adjoin_le_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact AlgHom.mem_fieldRange.mpr ⟨_, hψX⟩
    exact AlgHom.mem_fieldRange.mp (hle hy)
  exact ⟨AlgEquiv.ofBijective ψ ⟨ψ.toRingHom.injective, hsurj⟩, hψX⟩

theorem exists_algHom_ratFunc {F : Type*} [Field F] [Algebra K F] {y : F} (hy : Transcendental K y) :
    ∃ ψ : RatFunc K →ₐ[K] F, ψ (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) = y := by
  have hinj : Function.Injective (Polynomial.aeval (R := K) y) := transcendental_iff_injective.mp hy
  have hφ : nonZeroDivisors (Polynomial K) ≤
      Submonoid.comap (Polynomial.aeval (R := K) y) (nonZeroDivisors F) := by
    intro p hp
    rw [Submonoid.mem_comap]
    apply mem_nonZeroDivisors_of_ne_zero
    intro h0
    have : p = 0 := hinj (by rw [h0, map_zero])
    exact nonZeroDivisors.ne_zero hp this
  refine ⟨RatFunc.liftAlgHom (Polynomial.aeval y) hφ, ?_⟩
  have h := RatFunc.liftAlgHom_apply_div (Polynomial.aeval (R := K) y) hφ Polynomial.X 1
  rw [map_one, div_one, map_one, div_one, Polynomial.aeval_X] at h
  exact h

theorem algHom_ext_of_adjoin_eq_top {F : Type*} [Field F] [Algebra K F] {x : k}
    (hgen : IntermediateField.adjoin K ({x} : Set k) = ⊤) (f g : k →ₐ[K] F) (h : f x = g x) :
    f = g := by
  have hsub : ∀ z ∈ AlgHom.equalizer f g, z⁻¹ ∈ AlgHom.equalizer f g := by
    intro z hz
    rw [AlgHom.mem_equalizer] at hz ⊢
    rw [map_inv₀, map_inv₀, hz]
  let S : IntermediateField K k := (AlgHom.equalizer f g).toIntermediateField hsub
  have hx : x ∈ S := by
    show x ∈ AlgHom.equalizer f g
    rw [AlgHom.mem_equalizer]; exact h
  have hle : IntermediateField.adjoin K ({x} : Set k) ≤ S := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]; exact hx
  rw [hgen, top_le_iff] at hle
  apply AlgHom.ext
  intro z
  have hz : z ∈ S := by rw [hle]; exact IntermediateField.mem_top
  exact (AlgHom.mem_equalizer f g z).mp hz

include hM hE hgen in
theorem main : ∃ (P₁ P₂ : (E.baseChange Ω).toAffine.Point) (σ : Ω ≃ₐ[k] Ω) (ε : ℤ),
      M • P₁ = 0 ∧ M • P₂ = 0 ∧
      (∀ a b : ℤ, a • P₁ + b • P₂ = 0 → (M : ℤ) ∣ a ∧ (M : ℤ) ∣ b) ∧
      (ε = 1 ∨ ε = -1) ∧
      WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P₁ = ε • P₁ ∧
      WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P₂ = ε • (P₁ + P₂) := by
  classical

  by_cases hM1 : M = 1
  · subst hM1
    refine ⟨0, 0, AlgEquiv.refl, 1, by simp, by simp, fun a b _ => ⟨one_dvd a, one_dvd b⟩,
      Or.inl rfl, by simp, by simp⟩
  have hM2 : 2 ≤ M := by
    have := NeZero.ne M
    omega

  haveI : NeZero (M : K) := ⟨hM⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.prim (M := K) (n := M)
  have hζ₀0 : ζ₀ ≠ 0 := hζ₀.ne_zero (NeZero.ne M)
  set ζ : Kˣ := Units.mk0 ζ₀ hζ₀0 with hζdef
  have hζ : IsPrimitiveRoot (ζ : K) M := hζ₀
  have hζM : ζ ^ M = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hζ.pow_eq_one, Units.val_one]
  let F : Type u := LaurentSeries K
  letI : DecidableEq F := Classical.decEq F
  obtain ⟨xA, yA, xB, yB, hA, hB, hB', hMA, hMB, hind, hτxA, hτyA, hAB⟩ :=
    ModularCurve.exists_point_tateBase_qTwist_eq_add_of_isPrimitiveRoot K M hM2 ζ hζ

  have hTj : (tateBase K M).j = qExpand K M (jqModC K) := by
    have h := WeierstrassCurve.map_j (tateLaurent K) (qExpand K M)
    rw [j_tateLaurent] at h
    exact h
  have halgK : ∀ r : K, algebraMap K F r = HahnSeries.C r := fun r => by
    rw [HahnSeries.algebraMap_apply']; simp

  have hqExpand_C : ∀ r : K, qExpand K M (algebraMap K F r) = algebraMap K F r := fun r => by
    rw [halgK, qExpand_C]
  have hqTwist_C : ∀ (u : Kˣ) (r : K), qTwist u (algebraMap K F r) = algebraMap K F r := fun u r => by
    rw [halgK, HahnSeries.C_apply, qTwist_single, zpow_zero, Units.val_one, one_mul]
  let qE : F →ₐ[K] F := { qExpand K M with commutes' := hqExpand_C }
  have hqE : ∀ f, qE f = qExpand K M f := fun f => rfl
  have hTjtr : Transcendental K (tateBase K M).j := by
    rw [hTj, ← hqE]
    exact transcendental_of_algHom qE (qExpand K M).injective (transcendental_jqModC K)
  obtain ⟨φ, hφX⟩ := exists_algEquiv_ratFunc K (k := k) hE hgen
  obtain ⟨ψ, hψX⟩ := exists_algHom_ratFunc K (F := F) hTjtr
  let ι : k →ₐ[K] F := ψ.comp (φ.symm : k →ₐ[K] RatFunc K)
  have hιj : ι E.j = (tateBase K M).j := by
    show ψ (φ.symm E.j) = (tateBase K M).j
    rw [← hφX, AlgEquiv.symm_apply_apply, hψX]
  have hιinj : Function.Injective ι := ι.toRingHom.injective

  letI instkF : Algebra k F := ι.toRingHom.toAlgebra
  have halg_kF : ∀ z : k, algebraMap k F z = ι z := fun z => rfl
  let Ω' : Type u := AlgebraicClosure F
  letI : DecidableEq Ω' := Classical.decEq Ω'
  haveI : IsScalarTower k F Ω' := inferInstance
  have halg_kΩ' : ∀ z : k, algebraMap k Ω' z = algebraMap F Ω' (ι z) := fun z => by
    rw [IsScalarTower.algebraMap_apply k F Ω', halg_kF]

  have hfixι : ∀ z : k, qTwist ζ (ι z) = ι z := by
    intro z
    let g : k →ₐ[K] F :=
      { (qTwist ζ).comp ι.toRingHom with
        commutes' := fun r => by
          show qTwist ζ (ι (algebraMap K k r)) = algebraMap K F r
          rw [AlgHom.commutes, hqTwist_C] }
    have hg : g = ι := algHom_ext_of_adjoin_eq_top K (k := k) hgen g ι (by
      show qTwist ζ (ι E.j) = ι E.j
      rw [hιj, hTj, qTwist_qExpand, zpow_natCast, hζM, qTwist_one_apply])
    exact congrArg (fun h : k →ₐ[K] F => h z) hg
  have hqinv1 : ∀ f : F, qTwist ζ⁻¹ (qTwist ζ f) = f := fun f => by
    rw [qTwist_qTwist, inv_mul_cancel, qTwist_one_apply]
  have hqinv2 : ∀ f : F, qTwist ζ (qTwist ζ⁻¹ f) = f := fun f => by
    rw [qTwist_qTwist, mul_inv_cancel, qTwist_one_apply]
  let τ₀ : F ≃+* F :=
    { qTwist ζ with
      invFun := qTwist ζ⁻¹
      left_inv := hqinv1
      right_inv := hqinv2 }
  have hτ₀ : ∀ f, τ₀ f = qTwist ζ f := fun f => rfl
  let τr : Ω' ≃+* Ω' := IsAlgClosure.equivOfEquiv (R := F) (S := F) Ω' Ω' τ₀
  have hτr : ∀ f : F, τr (algebraMap F Ω' f) = algebraMap F Ω' (qTwist ζ f) := fun f =>
    IsAlgClosure.equivOfEquiv_algebraMap Ω' Ω' τ₀ f
  let τ : Ω' ≃ₐ[k] Ω' :=
    { τr with
      commutes' := fun z => by
        show τr (algebraMap k Ω' z) = algebraMap k Ω' z
        rw [halg_kΩ', hτr, hfixι] }
  have hτ : ∀ f : F, τ (algebraMap F Ω' f) = algebraMap F Ω' (qTwist ζ f) := hτr

  let V : WeierstrassCurve Ω' := E.baseChange Ω'
  let W : WeierstrassCurve Ω' := (tateBase K M).map (algebraMap F Ω')
  haveI : V.IsElliptic := show (E.map _).IsElliptic from inferInstance
  haveI : W.IsElliptic := show ((tateBase K M).map _).IsElliptic from inferInstance
  have hVj : V.j = algebraMap F Ω' (tateBase K M).j := by
    show (E.map (algebraMap k Ω')).j = _
    rw [WeierstrassCurve.map_j, halg_kΩ', hιj]
  have hWj : W.j = algebraMap F Ω' (tateBase K M).j := by
    show ((tateBase K M).map (algebraMap F Ω')).j = _
    rw [WeierstrassCurve.map_j]
  have hjWV : W.j = V.j := by rw [hWj, hVj]
  have hWtr : Transcendental K W.j := by
    rw [hWj]
    exact (transcendental_algebraMap_iff (algebraMap F Ω').injective).2 hTjtr
  have hc₄ : W.c₄ ≠ 0 := c₄_ne_zero_of_transcendental_j W hWtr
  have hc₆ : W.c₆ ≠ 0 := c₆_ne_zero_of_transcendental_j W hWtr
  obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq (E := W) (E' := V) hjWV
  obtain ⟨e, he⟩ := exists_pointEquiv_of_smul_eq C W V hC

  have hTτ₀ : (tateBase K M).map (qTwist ζ) = (tateBase K M) := by
    simp only [tateBase, tateLaurent, WeierstrassCurve.map, qTwist_qExpand, zpow_natCast, hζM,
      qTwist_one_apply]
  have hτcomp : (τ : Ω' →+* Ω').comp (algebraMap F Ω') = (algebraMap F Ω').comp (qTwist ζ) := by
    ext f
    exact hτ f
  have hWmap : W.map (τ : Ω' →+* Ω') = W := by
    show ((tateBase K M).map (algebraMap F Ω')).map (τ : Ω' →+* Ω') = (tateBase K M).map (algebraMap F Ω')
    rw [WeierstrassCurve.map_map, hτcomp, ← WeierstrassCurve.map_map, hTτ₀]
  have hVmap : V.map (τ : Ω' →ₐ[k] Ω') = V := WeierstrassCurve.map_baseChange E _
  have hVmap' : V.map (τ : Ω' →+* Ω') = V := hVmap

  have hfixC : τ ((C.u : Ω') ^ 2) = (C.u : Ω') ^ 2 ∧ τ C.r = C.r := by
    have h1 : (C.map (τ : Ω' →+* Ω')) • W = V := by
      have := congrArg (fun X : WeierstrassCurve Ω' => X.map (τ : Ω' →+* Ω')) hC
      beta_reduce at this
      rw [← WeierstrassCurve.map_variableChange, hWmap, hVmap'] at this
      exact this
    have h2 : (C⁻¹ * C.map (τ : Ω' →+* Ω')) • W = W := by
      rw [mul_smul, h1, ← hC, inv_smul_smul]
    obtain ⟨hu, hr⟩ := u_sq_eq_one_and_r_eq_zero_of_smul_eq _ W h2 hc₄ hc₆
    simp only [VariableChange.mul_def, VariableChange.inv_def, VariableChange.map, Units.val_mul,
      Units.coe_map, MonoidHom.coe_coe, RingHom.coe_coe] at hu hr
    have hu0 : (C.u : Ω') ≠ 0 := C.u.ne_zero
    have hui : ((C.u⁻¹ : Ω'ˣ) : Ω') = (C.u : Ω')⁻¹ := Units.val_inv_eq_inv_val C.u
    rw [hui] at hu hr
    rw [mul_pow, inv_pow, inv_mul_eq_one₀ (pow_ne_zero 2 hu0)] at hu
    have hτu : τ ((C.u : Ω') ^ 2) = (C.u : Ω') ^ 2 := by rw [map_pow]; exact hu.symm
    refine ⟨hτu, ?_⟩
    rw [← hu, inv_pow, mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hu0), mul_one] at hr
    exact (neg_add_eq_zero.1 hr).symm

  let mV : V.toAffine.Point →+ V.toAffine.Point := Point.map (τ : Ω' →ₐ[k] Ω')
  let mW : W.toAffine.Point →+ W.toAffine.Point :=
    mapPt W W (τ : Ω' →+* Ω') (τ : Ω' ≃ₐ[k] Ω').injective hWmap
  have hmV_some : ∀ (a b : Ω') (hab : V.toAffine.Nonsingular a b),
      ∃ h', mV (.some a b hab) = .some (τ a) (τ b) h' := fun a b hab => ⟨_, rfl⟩
  have hmW_some : ∀ (a b : Ω') (hab : W.toAffine.Nonsingular a b),
      ∃ h', mW (.some a b hab) = .some (τ a) (τ b) h' := fun a b hab =>
    mapPt_some W W (τ : Ω' →+* Ω') (τ : Ω' ≃ₐ[k] Ω').injective hWmap a b hab
  have hsign_pt : ∀ R : V.toAffine.Point, e (mV R) = mW (e R) ∨ e (mV R) = -(mW (e R)) := by
    intro R
    rcases R with (_ | ⟨xR, yR, hR⟩)
    · left
      show e (mV 0) = mW (e 0)
      simp only [map_zero]
    · obtain ⟨hτu, hτr'⟩ := hfixC
      obtain ⟨hR', hmap⟩ := hmV_some xR yR hR
      obtain ⟨h₁, he₁⟩ := he (τ xR) (τ yR) hR'
      obtain ⟨h₂, he₂⟩ := he xR yR hR
      rw [hmap, he₁, he₂]
      obtain ⟨h₃, hmap'⟩ := hmW_some ((C.u : Ω') ^ 2 * xR + C.r)
          ((C.u : Ω') ^ 3 * yR + (C.u : Ω') ^ 2 * C.s * xR + C.t) h₂
      rw [hmap']
      apply Point.X_eq_iff.1
      rw [map_add, map_mul, hτu, hτr']
  have hsign : (∀ R, e (mV R) = mW (e R)) ∨ (∀ R, e (mV R) = -(mW (e R))) :=
    forall_eq_or_forall_eq_neg (e.toAddMonoidHom.comp mV) (mW.comp e.toAddMonoidHom) hsign_pt

  obtain ⟨ε, hε, hεsign⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ R, e (mV R) = ε • mW (e R) := by
    rcases hsign with h | h
    · exact ⟨1, Or.inl rfl, fun R => by rw [h, one_zsmul]⟩
    · exact ⟨-1, Or.inr rfl, fun R => by rw [h, neg_one_zsmul]⟩

  let pf : (tateBase K M).toAffine.Point →+ W.toAffine.Point :=
    mapPt (tateBase K M) W (algebraMap F Ω') (algebraMap F Ω').injective rfl
  have hpf_inj : Function.Injective pf := mapPt_injective (tateBase K M) W _ _ rfl
  have hpf_some : ∀ (a b : F) (hab : (tateBase K M).toAffine.Nonsingular a b),
      ∃ h', pf (.some a b hab) = .some (algebraMap F Ω' a) (algebraMap F Ω' b) h' := fun a b hab =>
    mapPt_some (tateBase K M) W _ _ rfl a b hab
  set A : (tateBase K M).toAffine.Point := .some xA yA hA with hAdef
  set B : (tateBase K M).toAffine.Point := .some xB yB hB with hBdef
  set A' : W.toAffine.Point := pf A with hA'def
  set B' : W.toAffine.Point := pf B with hB'def
  have hMA' : M • A' = 0 := by rw [hA'def, ← map_nsmul, hMA, map_zero]
  have hMB' : M • B' = 0 := by rw [hB'def, ← map_nsmul, hMB, map_zero]
  have hind' : ∀ a b : ℤ, a • A' + b • B' = 0 → (M : ℤ) ∣ a ∧ (M : ℤ) ∣ b := by
    intro a b hab
    apply hind a b
    apply hpf_inj
    rw [map_add, map_zsmul, map_zsmul, map_zero]
    exact hab

  have hmWA' : mW A' = A' := by
    obtain ⟨h₁, e₁⟩ := hpf_some xA yA hA
    rw [hA'def, hAdef, e₁]
    obtain ⟨h₂, e₂⟩ := hmW_some _ _ h₁
    rw [e₂]
    have hx : τ (algebraMap F Ω' xA) = algebraMap F Ω' xA := by rw [hτ, hτxA]
    have hy : τ (algebraMap F Ω' yA) = algebraMap F Ω' yA := by rw [hτ, hτyA]
    simp only [hx, hy]
  have hmWB' : mW B' = A' + B' := by
    obtain ⟨h₁, e₁⟩ := hpf_some xB yB hB
    obtain ⟨h₃, e₃⟩ := hpf_some (qTwist ζ xB) (qTwist ζ yB) hB'
    have lhs : mW B' =
        Point.some (algebraMap F Ω' (qTwist ζ xB)) (algebraMap F Ω' (qTwist ζ yB)) h₃ := by
      rw [hB'def, hBdef, e₁]
      obtain ⟨h₂, e₂⟩ := hmW_some _ _ h₁
      rw [e₂]
      have hx : τ (algebraMap F Ω' xB) = algebraMap F Ω' (qTwist ζ xB) := hτ xB
      have hy : τ (algebraMap F Ω' yB) = algebraMap F Ω' (qTwist ζ yB) := hτ yB
      simp only [hx, hy]
    rw [lhs, ← e₃, hAB, map_add]

  set P₁' : V.toAffine.Point := e.symm A' with hP₁'
  set P₂' : V.toAffine.Point := e.symm B' with hP₂'
  have hMP₁' : M • P₁' = 0 := by rw [hP₁', ← map_nsmul, hMA', map_zero]
  have hMP₂' : M • P₂' = 0 := by rw [hP₂', ← map_nsmul, hMB', map_zero]
  have hindV : ∀ a b : ℤ, a • P₁' + b • P₂' = 0 → (M : ℤ) ∣ a ∧ (M : ℤ) ∣ b := by
    intro a b hab
    apply hind' a b
    have := congrArg e hab
    rw [map_add, map_zsmul, map_zsmul, hP₁', hP₂', AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, map_zero] at this
    exact this
  have hmV₁ : mV P₁' = ε • P₁' := by
    apply e.injective
    rw [hεsign, hP₁', AddEquiv.apply_symm_apply, hmWA', map_zsmul, AddEquiv.apply_symm_apply]
  have hmV₂ : mV P₂' = ε • (P₁' + P₂') := by
    apply e.injective
    rw [hεsign, hP₂', AddEquiv.apply_symm_apply, hmWB', map_zsmul, map_add, hP₁',
      AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

  let Ω₀ : IntermediateField k Ω' := algebraicClosure k Ω'
  haveI : IsAlgClosure k Ω₀ := inferInstance
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI : IsAlgClosed Ω' := inferInstance
  let θ : Ω ≃ₐ[k] Ω₀ := IsAlgClosure.equiv k Ω Ω₀
  let κ : Ω →ₐ[k] Ω' := (IntermediateField.val Ω₀).comp (θ : Ω →ₐ[k] Ω₀)
  have hκ : ∀ z : Ω, κ z = ((θ z : Ω₀) : Ω') := fun z => rfl
  let τ₀₀ : Ω₀ ≃ₐ[k] Ω₀ := algebraicClosure.algEquivOfAlgEquiv τ
  have hτ₀₀ : ∀ z : Ω₀, ((τ₀₀ z : Ω₀) : Ω') = τ z := fun z => rfl
  let σ : Ω ≃ₐ[k] Ω := θ.trans (τ₀₀.trans θ.symm)
  have hκσ : ∀ z : Ω, κ (σ z) = τ (κ z) := by
    intro z
    show ((θ (θ.symm (τ₀₀ (θ z))) : Ω₀) : Ω') = τ ((θ z : Ω₀) : Ω')
    rw [AlgEquiv.apply_symm_apply, hτ₀₀]
  have hcomp : κ.comp (σ : Ω →ₐ[k] Ω) = (τ : Ω' →ₐ[k] Ω').comp κ := by
    ext z
    exact hκσ z
  let κp : (E.baseChange Ω).toAffine.Point →+ V.toAffine.Point := Point.map κ
  have hκp_inj : Function.Injective κp := Point.map_injective κ
  have hκp_nat : ∀ P : (E.baseChange Ω).toAffine.Point,
      κp (Point.map (σ : Ω →ₐ[k] Ω) P) = mV (κp P) := by
    intro P
    show Point.map κ (Point.map _ P) = Point.map _ (Point.map κ P)
    rw [Point.map_map, Point.map_map, hcomp]

  have hMΩ : (M : Ω) ≠ 0 := fun h =>
    hM ((algebraMap K Ω).injective (by rw [map_natCast, map_zero]; exact h))
  have hMΩ' : (M : Ω') ≠ 0 := fun h =>
    hM ((algebraMap K Ω').injective (by rw [map_natCast, map_zero]; exact h))
  have htorΩ : Nat.card {Q : (E.baseChange Ω).toAffine.Point // M • Q = 0} = M ^ 2 :=
    natCard_torsion_of_isAlgClosed (Ω := Ω) E M hMΩ
  have htorΩ' : Nat.card {Q : V.toAffine.Point // M • Q = 0} = M ^ 2 :=
    natCard_torsion_of_isAlgClosed (Ω := Ω') E M hMΩ'
  obtain ⟨P₁, hMP₁, hP₁⟩ := exists_eq_of_nsmul_eq_zero κp hκp_inj M htorΩ htorΩ' P₁' hMP₁'
  obtain ⟨P₂, hMP₂, hP₂⟩ := exists_eq_of_nsmul_eq_zero κp hκp_inj M htorΩ htorΩ' P₂' hMP₂'
  refine ⟨P₁, P₂, σ, ε, hMP₁, hMP₂, ?_, hε, ?_, ?_⟩
  · intro a b hab
    apply hindV a b
    rw [← hP₁, ← hP₂, ← map_zsmul, ← map_zsmul, ← map_add, hab, map_zero]
  · apply hκp_inj
    rw [hκp_nat, hP₁, hmV₁, map_zsmul, hP₁]
  · apply hκp_inj
    rw [hκp_nat, hP₂, hmV₂, map_zsmul, map_add, hP₁, hP₂]

end Main

end P2MKcCuspMonodromy

end

p2m_open "WeierstrassCurve~cusp WeierstrassCurve.Affine"

universe u v in
theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0)
    (k Ω : Type v) [Field k] [Field Ω] [DecidableEq Ω] [Algebra K k] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower K k Ω] [IsAlgClosure k Ω] (E : WeierstrassCurve k) [E.IsElliptic]
    (hE : Transcendental K E.j) (hgen : IntermediateField.adjoin K ({E.j} : Set k) = ⊤) :
    ∃ (P₁ P₂ : (E.baseChange Ω).toAffine.Point) (σ : Ω ≃ₐ[k] Ω) (ε : ℤ),
      M • P₁ = 0 ∧ M • P₂ = 0 ∧
      (∀ a b : ℤ, a • P₁ + b • P₂ = 0 → (M : ℤ) ∣ a ∧ (M : ℤ) ∣ b) ∧
      (ε = 1 ∨ ε = -1) ∧
      WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P₁ = ε • P₁ ∧
      WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P₂ = ε • (P₁ + P₂) :=
  P2MKcCuspMonodromy.main K M hM k Ω E hE hgen

end S_WeierstrassCurve_exists_algEquiv_map_eq_smul_and_map_eq_smul_add_of_transcendental_j
end P2MW
export P2MW.S_WeierstrassCurve_exists_algEquiv_map_eq_smul_and_map_eq_smul_add_of_transcendental_j (solution)
