-- Prove2me | solution 1 for WeierstrassCurve.natCard_fibre_dvd_jWidth_of_variableChange_orbitMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/549148cb-f546-54fd-9aa2-c7e45da17427

import Mathlib
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_WeierstrassCurve_card_stabilizer_variableChange_eq_two_mul_jWidth
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Theorems.Thm_WeierstrassCurve_variableChange_mk_neg_one_smul_eq_self
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_natCard_fibre_dvd_jWidth_of_variableChange_orbitMap

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

noncomputable section

namespace P2MS12G1

variable {K : Type*} [Field K] [DecidableEq K]

def castPt {W₁ W₂ : WeierstrassCurve K} (e : W₁ = W₂) : W₁.toAffine.Point ≃+ W₂.toAffine.Point := by
  subst e; exact AddEquiv.refl _

theorem castPt_eq_iff_heq {W₁ W₂ : WeierstrassCurve K} (e : W₁ = W₂) (P : W₁.toAffine.Point)
    (Q : W₂.toAffine.Point) : castPt e P = Q ↔ HEq P Q := by
  subst e; exact Iff.rfl.trans heq_iff_eq.symm

def autPt {W : WeierstrassCurve K} (γ : VariableChange K) (hγ : γ • W = W) :
    W.toAffine.Point →+ W.toAffine.Point :=
  (castPt hγ).toAddMonoidHom.comp
    (AddMonoidHom.mk' (Point.vcInvFun γ W.toAffine) (Point.vcInvFun_add γ W.toAffine))

theorem autPt_apply {W : WeierstrassCurve K} (γ : VariableChange K) (hγ : γ • W = W)
    (P : W.toAffine.Point) : autPt γ hγ P = castPt hγ (Point.vcInvFun γ W.toAffine P) := rfl

theorem autPt_eq_iff_heq {W : WeierstrassCurve K} (γ : VariableChange K) (hγ : γ • W = W)
    (P Q : W.toAffine.Point) : autPt γ hγ P = Q ↔ HEq (Point.vcInvFun γ W.toAffine P) Q := by
  rw [autPt_apply, castPt_eq_iff_heq]

theorem heq_some {V V' : WeierstrassCurve.Affine K} (hV : V' = V) {x y : K}
    {h : V.Nonsingular x y} {h' : V'.Nonsingular x y} :
    HEq (Point.some x y h' : V'.Point) (Point.some x y h : V.Point) := by
  subst hV; rfl

theorem some_eq_some {V : WeierstrassCurve.Affine K} {x₁ y₁ x₂ y₂ : K}
    (hx : x₁ = x₂) (hy : y₁ = y₂) {h₁ : V.Nonsingular x₁ y₁} {h₂ : V.Nonsingular x₂ y₂} :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
  subst hx hy; rfl

theorem nonsingular_vcInv {W : WeierstrassCurve K} (γ : VariableChange K) (hγ : γ • W = W)
    {x y : K} (h : W.toAffine.Nonsingular x y) :
    W.toAffine.Nonsingular (vcXInv γ x) (vcYInv γ x y) := by
  have h' : (γ • W).toAffine.Nonsingular (vcXInv γ x) (vcYInv γ x y) :=
    (nonsingular_variableChange_iff (vcXInv γ x) (vcYInv γ x y)).mpr
      (by rwa [vcX_vcXInv, vcY_vcYInv])
  rwa [hγ] at h'

theorem autPt_some {W : WeierstrassCurve K} (γ : VariableChange K) (hγ : γ • W = W) {x y : K}
    (h : W.toAffine.Nonsingular x y) :
    autPt γ hγ (.some x y h) = .some (vcXInv γ x) (vcYInv γ x y) (nonsingular_vcInv γ hγ h) := by
  rw [autPt_eq_iff_heq]
  show HEq (Point.some (vcXInv γ x) (vcYInv γ x y) _ : (γ • W).toAffine.Point) _
  exact heq_some (congrArg WeierstrassCurve.toAffine hγ)

abbrev Aut (W : WeierstrassCurve K) : Subgroup (VariableChange K) :=
  MulAction.stabilizer (VariableChange K) W

theorem smul_eq_of_mem_Aut {W : WeierstrassCurve K} (γ : Aut W) : (γ : VariableChange K) • W = W :=
  MulAction.mem_stabilizer_iff.mp γ.2

theorem one_u : (1 : VariableChange K).u = 1 := rfl
theorem one_r : (1 : VariableChange K).r = 0 := rfl
theorem one_s : (1 : VariableChange K).s = 0 := rfl
theorem one_t : (1 : VariableChange K).t = 0 := rfl
theorem mul_u (C C' : VariableChange K) : (C * C').u = C.u * C'.u := rfl
theorem mul_r (C C' : VariableChange K) : (C * C').r = C.r * C'.u ^ 2 + C'.r := rfl
theorem mul_s (C C' : VariableChange K) : (C * C').s = C'.u * C.s + C'.s := rfl
theorem mul_t (C C' : VariableChange K) :
    (C * C').t = C.t * C'.u ^ 3 + C.r * C'.s * C'.u ^ 2 + C'.t := rfl

theorem vcXInv_one (x : K) : vcXInv (1 : VariableChange K) x = x := by
  rw [vcXInv, one_u, one_r]; simp

theorem vcYInv_one (x y : K) : vcYInv (1 : VariableChange K) x y = y := by
  rw [vcYInv, one_u, one_r, one_s, one_t]; simp

theorem vcXInv_mul (C C' : VariableChange K) (x : K) :
    vcXInv (C * C') x = vcXInv C (vcXInv C' x) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  have hu' : (C'.u : K) ≠ 0 := C'.u.ne_zero
  simp only [vcXInv, mul_u, mul_r, Units.val_inv_eq_inv_val, Units.val_mul]
  field_simp
  ring

theorem vcYInv_mul (C C' : VariableChange K) (x y : K) :
    vcYInv (C * C') x y = vcYInv C (vcXInv C' x) (vcYInv C' x y) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  have hu' : (C'.u : K) ≠ 0 := C'.u.ne_zero
  simp only [vcXInv, vcYInv, mul_u, mul_r, mul_s, mul_t, Units.val_inv_eq_inv_val, Units.val_mul]
  field_simp
  ring

scoped instance instMulActionAutPoint (W : WeierstrassCurve K) : MulAction (Aut W) W.toAffine.Point where
  smul γ P := autPt γ.1 (smul_eq_of_mem_Aut γ) P
  one_smul P := by
    change autPt (1 : VariableChange K) _ P = P
    rcases P with _ | ⟨x, y, h⟩
    · exact map_zero (autPt (1 : VariableChange K) _)
    · rw [autPt_some]
      exact some_eq_some (vcXInv_one x) (vcYInv_one x y)
  mul_smul γ δ P := by
    change autPt (γ.1 * δ.1) _ P = autPt γ.1 _ (autPt δ.1 _ P)
    rcases P with _ | ⟨x, y, h⟩
    · show autPt (γ.1 * δ.1) _ 0 = autPt γ.1 _ (autPt δ.1 _ 0)
      simp only [map_zero]
    · rw [autPt_some, autPt_some, autPt_some]
      exact some_eq_some (vcXInv_mul _ _ x) (vcYInv_mul _ _ x y)

theorem aut_smul_def {W : WeierstrassCurve K} (γ : Aut W) (P : W.toAffine.Point) :
    γ • P = autPt γ.1 (smul_eq_of_mem_Aut γ) P := rfl

scoped instance instDistribMulActionAutPoint (W : WeierstrassCurve K) :
    DistribMulAction (Aut W) W.toAffine.Point where
  smul_zero γ := map_zero (autPt γ.1 (smul_eq_of_mem_Aut γ))
  smul_add γ P Q := map_add (autPt γ.1 (smul_eq_of_mem_Aut γ)) P Q

open scoped Pointwise

abbrev CycSub (W : WeierstrassCurve K) (N : ℕ) : Type _ :=
  {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N}

theorem natCard_smul_addSubgroup {W : WeierstrassCurve K} (γ : Aut W) (H : AddSubgroup W.toAffine.Point) :
    Nat.card (γ • H : AddSubgroup W.toAffine.Point) = Nat.card H := by
  rw [AddSubgroup.pointwise_smul_def]
  exact (Nat.card_congr (H.equivMapOfInjective _ (MulAction.injective γ)).toEquiv).symm

theorem isAddCyclic_smul_addSubgroup {W : WeierstrassCurve K} (γ : Aut W)
    (H : AddSubgroup W.toAffine.Point) [hH : IsAddCyclic H] :
    IsAddCyclic (γ • H : AddSubgroup W.toAffine.Point) := by
  rw [AddSubgroup.pointwise_smul_def]
  exact isAddCyclic_of_surjective (H.equivMapOfInjective _ (MulAction.injective γ))
    (H.equivMapOfInjective _ (MulAction.injective γ)).surjective

scoped instance instMulActionAutCycSub (W : WeierstrassCurve K) (N : ℕ) : MulAction (Aut W) (CycSub W N) where
  smul γ H := ⟨γ • H.1, ⟨by haveI := H.2.1; exact isAddCyclic_smul_addSubgroup γ H.1,
    (natCard_smul_addSubgroup γ H.1).trans H.2.2⟩⟩
  one_smul H := Subtype.ext (one_smul (Aut W) H.1)
  mul_smul γ δ H := Subtype.ext (mul_smul γ δ H.1)

theorem coe_smul_cycSub {W : WeierstrassCurve K} {N : ℕ} (γ : Aut W) (H : CycSub W N) :
    ((γ • H : CycSub W N) : AddSubgroup W.toAffine.Point) = γ • (H : AddSubgroup W.toAffine.Point) := rfl

theorem rel_iff_mem_orbit {W : WeierstrassCurve K} {N : ℕ} [NeZero N] (H H' : CycSub W N) :
    (∃ γ : VariableChange K, γ • W = W ∧
        ∀ T ∈ H.1, ∃ T' ∈ H'.1, HEq (Point.vcInvFun γ W.toAffine T) T') ↔
      H' ∈ MulAction.orbit (Aut W) H := by
  constructor
  · rintro ⟨γ, hγ, h⟩
    let g : Aut W := ⟨γ, MulAction.mem_stabilizer_iff.mpr hγ⟩
    have hle : (g • H.1 : AddSubgroup W.toAffine.Point) ≤ H'.1 := by
      intro P hP
      obtain ⟨T, hT, rfl⟩ := (AddSubgroup.mem_smul_pointwise_iff_exists P g H.1).mp hP
      obtain ⟨T', hT', hh⟩ := h T hT
      have : g • T = T' := (autPt_eq_iff_heq γ hγ T T').mpr hh
      rwa [this]
    haveI : Finite H'.1 := Nat.finite_of_card_ne_zero (by rw [H'.2.2]; exact NeZero.ne N)
    have heq : (g • H.1 : AddSubgroup W.toAffine.Point) = H'.1 :=
      AddSubgroup.eq_of_le_of_card_ge hle (by rw [natCard_smul_addSubgroup, H.2.2, H'.2.2])
    exact MulAction.mem_orbit_iff.mpr ⟨g, Subtype.ext heq⟩
  · intro hmem
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hmem
    refine ⟨g.1, smul_eq_of_mem_Aut g, fun T hT => ⟨g • T, ?_, ?_⟩⟩
    · exact AddSubgroup.smul_mem_pointwise_smul T g H.1 hT
    · exact (autPt_eq_iff_heq g.1 (smul_eq_of_mem_Aut g) T _).mp rfl

def negVC (W : WeierstrassCurve K) : VariableChange K := ⟨-1, 0, -W.a₁, -W.a₃⟩

theorem negVC_smul (W : WeierstrassCurve K) : negVC W • W = W :=
  WeierstrassCurve.variableChange_mk_neg_one_smul_eq_self W

def negAut (W : WeierstrassCurve K) : Aut W := ⟨negVC W, MulAction.mem_stabilizer_iff.mpr (negVC_smul W)⟩

theorem negAut_smul_point {W : WeierstrassCurve K} (P : W.toAffine.Point) : negAut W • P = -P := by
  change autPt (negVC W) _ P = -P
  rcases P with _ | ⟨x, y, h⟩
  · show autPt (negVC W) _ 0 = -0
    rw [map_zero, neg_zero]
  · rw [autPt_some, Point.neg_some]
    refine some_eq_some ?_ ?_
    · show ((((negVC W).u⁻¹ : Kˣ) : K)) ^ 2 * (x - (negVC W).r) = x
      simp [negVC]
    · show ((((negVC W).u⁻¹ : Kˣ) : K)) ^ 3 * (y - (negVC W).t - (negVC W).s * (x - (negVC W).r))
          = W.toAffine.negY x y
      rw [Affine.negY]
      simp [negVC]
      ring

theorem negAut_mul_self (W : WeierstrassCurve K) : negAut W * negAut W = 1 := by
  refine Subtype.ext (VariableChange.ext ?_ ?_ ?_ ?_)
  · show (negVC W).u * (negVC W).u = 1
    simp [negVC]
  · show (negVC W).r * (negVC W).u ^ 2 + (negVC W).r = 0
    simp [negVC]
  · show (negVC W).u * (negVC W).s + (negVC W).s = 0
    simp [negVC]
  · show (negVC W).t * (negVC W).u ^ 3 + (negVC W).r * (negVC W).s * (negVC W).u ^ 2 + (negVC W).t = 0
    simp only [negVC]
    push_cast
    ring

theorem negAut_ne_one (W : WeierstrassCurve K) (h2 : ringChar K ≠ 2) : negAut W ≠ 1 := by
  intro h
  have hu : ((negVC W).u : K) = ((1 : VariableChange K).u : K) :=
    congrArg (fun g : Aut W => ((g.1).u : K)) h
  rw [one_u] at hu
  have hneg : ((negVC W).u : K) = -1 := by simp [negVC]
  rw [hneg, Units.val_one] at hu
  have : (2 : K) = 0 := by linear_combination -hu
  exact Ring.two_ne_zero h2 this

theorem orderOf_negAut (W : WeierstrassCurve K) (h2 : ringChar K ≠ 2) : orderOf (negAut W) = 2 :=
  orderOf_eq_prime (by rw [pow_two, negAut_mul_self]) (negAut_ne_one W h2)

theorem negAut_smul_addSubgroup {W : WeierstrassCurve K} (H : AddSubgroup W.toAffine.Point) :
    negAut W • H = H := by
  ext P
  rw [AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem]
  have hinv : (negAut W)⁻¹ = negAut W :=
    inv_eq_of_mul_eq_one_right (negAut_mul_self W)
  rw [hinv, negAut_smul_point]
  exact neg_mem_iff

theorem negAut_mem_stabilizer {W : WeierstrassCurve K} {N : ℕ} (H : CycSub W N) :
    negAut W ∈ MulAction.stabilizer (Aut W) H :=
  MulAction.mem_stabilizer_iff.mpr (Subtype.ext (negAut_smul_addSubgroup H.1))

theorem natCard_orbit_dvd_jWidth [IsAlgClosed K] (h2 : ringChar K ≠ 2) (h3 : ringChar K ≠ 3)
    {W : WeierstrassCurve K} [W.IsElliptic] {N : ℕ} (H : CycSub W N) :
    Nat.card (MulAction.orbit (Aut W) H) ∣ ModularCurve.jWidth W.j := by
  have hG : Nat.card (Aut W) = 2 * ModularCurve.jWidth W.j :=
    WeierstrassCurve.card_stabilizer_variableChange_eq_two_mul_jWidth h2 h3 W
  have hos : (MulAction.stabilizer (Aut W) H).index * Nat.card (MulAction.stabilizer (Aut W) H)
      = Nat.card (Aut W) := Subgroup.index_mul_card _
  have hidx : (MulAction.stabilizer (Aut W) H).index = Nat.card (MulAction.orbit (Aut W) H) := by
    rw [MulAction.index_stabilizer]; rfl
  have h2dvd : 2 ∣ Nat.card (MulAction.stabilizer (Aut W) H) := by
    have := orderOf_dvd_natCard (⟨negAut W, negAut_mem_stabilizer H⟩ : MulAction.stabilizer (Aut W) H)
    rwa [Subgroup.orderOf_mk, orderOf_negAut W h2] at this
  obtain ⟨c, hc⟩ := h2dvd
  rw [hidx, hG, hc] at hos
  refine ⟨c, ?_⟩
  have : 2 * (Nat.card (MulAction.orbit (Aut W) H) * c) = 2 * ModularCurve.jWidth W.j := by
    rw [← hos]; ring
  omega

end P2MS12G1
p2m_reactivate "P2MW.S_WeierstrassCurve_natCard_fibre_dvd_jWidth_of_variableChange_orbitMap.P2MS12G1"

end
p2m_reactivate "P2MW.S_WeierstrassCurve_natCard_fibre_dvd_jWidth_of_variableChange_orbitMap.P2MS12G1"

open P2MS12G1 in
theorem solution
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (h2 : ringChar K ≠ 2) (h3 : ringChar K ≠ 3)
    (W : WeierstrassCurve K) [W.IsElliptic] (N : ℕ) [NeZero N] {α : Type*}
    (f : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} → α)
    (hf : ∀ H H', f H = f H' ↔ ∃ γ : VariableChange K, γ • W = W ∧
      ∀ T ∈ H.1, ∃ T' ∈ H'.1, HEq (Point.vcInvFun γ W.toAffine T) T')
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N}) :
    Nat.card {H' : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} //
        f H' = f H} ∣ ModularCurve.jWidth W.j := by
  have e : {H' : CycSub W N // f H' = f H} ≃ MulAction.orbit (Aut W) H :=
    Equiv.subtypeEquivRight (fun H' => by
      rw [eq_comm, hf H H', rel_iff_mem_orbit H H']
      try rfl)
  rw [Nat.card_congr e]
  exact natCard_orbit_dvd_jWidth h2 h3 H

#print axioms solution

end S_WeierstrassCurve_natCard_fibre_dvd_jWidth_of_variableChange_orbitMap
end P2MW
export P2MW.S_WeierstrassCurve_natCard_fibre_dvd_jWidth_of_variableChange_orbitMap (solution)
