-- Prove2me | solution 1 for WeierstrassCurve.natCard_stabilizer_variableChange_eq_twentyFour_of_j_eq_zero_of_charP_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/47ebf39e-61d5-5ce3-840a-651bccc53050

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_natCard_stabilizer_variableChange_eq_twentyFour_of_j_eq_zero_of_charP_two

set_option autoImplicit false

open Polynomial MulAction

namespace AUT24

theorem natCard_subtype_eval_eq_zero {F : Type*} [Field F] [IsAlgClosed F] (p : F[X])
    (hsep : p.Separable) : Nat.card {x : F // p.eval x = 0} = p.natDegree := by
  classical
  have hp0 : p ≠ 0 := hsep.ne_zero
  have e : {x : F // p.eval x = 0} ≃ {x : F // x ∈ p.roots.toFinset} :=
    Equiv.subtypeEquivRight fun x => by rw [Multiset.mem_toFinset, mem_roots hp0, IsRoot.def]
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe,
    Multiset.toFinset_card_of_nodup (nodup_roots hsep), IsAlgClosed.card_roots_eq_natDegree]

theorem separable_of_derivative_eq_C {F : Type*} [Field F] (p : F[X]) {a : F} (ha : a ≠ 0)
    (hd : derivative p = C a) : p.Separable := by
  rw [separable_def, hd]
  exact ⟨0, C a⁻¹, by rw [zero_mul, zero_add, ← C_mul, inv_mul_cancel₀ ha, C_1]⟩

theorem natCard_sigma_of_forall_eq {α : Type*} {β : α → Type*} {n : ℕ} (hn : n ≠ 0)
    (h : ∀ a, Nat.card (β a) = n) : Nat.card (Σ a, β a) = Nat.card α * n := by
  have hfin : ∀ a, Finite (β a) := fun a => Nat.finite_of_card_ne_zero ((h a).symm ▸ hn)
  let e : (Σ a, β a) ≃ α × Fin n :=
    (Equiv.sigmaCongrRight fun a => Finite.equivFinOfCardEq (h a)).trans
      (Equiv.sigmaEquivProd α (Fin n))
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]

section NF

variable {F : Type*} [Field F] [CharP F 2] (W : WeierstrassCurve F) [W.IsCharTwoJEqZeroNF]
  (C : WeierstrassCurve.VariableChange F)

private theorem two_eq_zero' : (2 : F) = 0 := CharTwo.two_eq_zero

theorem vc_a₁ : (C • W).a₁ = 0 := by
  rw [WeierstrassCurve.variableChange_a₁, W.a₁_of_isCharTwoJEqZeroNF]
  linear_combination (((C.u⁻¹ : Fˣ) : F) * C.s) * two_eq_zero' (F := F)

theorem vc_a₂ : (C • W).a₂ = ((C.u⁻¹ : Fˣ) : F) ^ 2 * (C.r + C.s ^ 2) := by
  rw [WeierstrassCurve.variableChange_a₂, W.a₁_of_isCharTwoJEqZeroNF, W.a₂_of_isCharTwoJEqZeroNF]
  linear_combination (((C.u⁻¹ : Fˣ) : F) ^ 2 * (C.r - C.s ^ 2)) * two_eq_zero' (F := F)

theorem vc_a₃ : (C • W).a₃ = ((C.u⁻¹ : Fˣ) : F) ^ 3 * W.a₃ := by
  rw [WeierstrassCurve.variableChange_a₃, W.a₁_of_isCharTwoJEqZeroNF]
  linear_combination (((C.u⁻¹ : Fˣ) : F) ^ 3 * C.t) * two_eq_zero' (F := F)

theorem vc_a₄ : (C • W).a₄ = ((C.u⁻¹ : Fˣ) : F) ^ 4 * (W.a₄ + C.s * W.a₃ + C.r ^ 2) := by
  rw [WeierstrassCurve.variableChange_a₄, W.a₁_of_isCharTwoJEqZeroNF, W.a₂_of_isCharTwoJEqZeroNF]
  linear_combination (((C.u⁻¹ : Fˣ) : F) ^ 4 * (-C.s * W.a₃ + C.r ^ 2 - C.s * C.t)) *
    two_eq_zero' (F := F)

theorem vc_a₆ : (C • W).a₆ =
    ((C.u⁻¹ : Fˣ) : F) ^ 6 * (W.a₆ + C.r * W.a₄ + C.r ^ 3 + C.t * W.a₃ + C.t ^ 2) := by
  rw [WeierstrassCurve.variableChange_a₆, W.a₁_of_isCharTwoJEqZeroNF, W.a₂_of_isCharTwoJEqZeroNF]
  linear_combination (-((C.u⁻¹ : Fˣ) : F) ^ 6 * (C.t * W.a₃ + C.t ^ 2)) * two_eq_zero' (F := F)

theorem mem_stabilizer_iff_nf (ha₃ : W.a₃ ≠ 0) :
    C ∈ stabilizer (WeierstrassCurve.VariableChange F) W ↔
      (C.u : F) ^ 3 = 1 ∧ C.r = C.s ^ 2 ∧
        C.s ^ 4 + W.a₃ * C.s + (1 + C.u) * W.a₄ = 0 ∧
        C.t ^ 2 + W.a₃ * C.t + (C.s ^ 6 + W.a₄ * C.s ^ 2) = 0 := by
  have h2 : (2 : F) = 0 := two_eq_zero'
  have huv : (C.u : F) * ((C.u⁻¹ : Fˣ) : F) = 1 := C.u.mul_inv
  have hv0 : ((C.u⁻¹ : Fˣ) : F) ≠ 0 := C.u⁻¹.ne_zero
  constructor
  · intro hC
    rw [mem_stabilizer_iff] at hC

    have e2 := congrArg WeierstrassCurve.a₂ hC
    rw [vc_a₂, W.a₂_of_isCharTwoJEqZeroNF] at e2
    have hrs : C.r + C.s ^ 2 = 0 := (mul_eq_zero.mp e2).resolve_left (pow_ne_zero 2 hv0)
    have hr : C.r = C.s ^ 2 := by linear_combination hrs - C.s ^ 2 * h2

    have e3 := congrArg WeierstrassCurve.a₃ hC
    rw [vc_a₃] at e3
    have hv3 : ((C.u⁻¹ : Fˣ) : F) ^ 3 = 1 := by
      have h : (((C.u⁻¹ : Fˣ) : F) ^ 3 - 1) * W.a₃ = 0 := by linear_combination e3
      exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right ha₃)
    have hu3 : (C.u : F) ^ 3 = 1 := by
      linear_combination (-(C.u : F) ^ 3) * hv3 +
        (((C.u : F) * ((C.u⁻¹ : Fˣ) : F)) ^ 2 + (C.u : F) * ((C.u⁻¹ : Fˣ) : F) + 1) * huv
    have hv : ((C.u⁻¹ : Fˣ) : F) = (C.u : F) ^ 2 := by
      linear_combination (C.u : F) ^ 2 * huv - ((C.u⁻¹ : Fˣ) : F) * hu3

    have e4 := congrArg WeierstrassCurve.a₄ hC
    rw [vc_a₄, hv] at e4
    have hs : C.s ^ 4 + W.a₃ * C.s + (1 + C.u) * W.a₄ = 0 := by
      linear_combination (C.u : F) * e4
        - ((C.u : F) ^ 6 + (C.u : F) ^ 3 + 1) * (W.a₄ + C.s * W.a₃ + C.r ^ 2) * hu3
        - (C.r + C.s ^ 2) * hr + ((C.u : F) * W.a₄) * h2

    have e6 := congrArg WeierstrassCurve.a₆ hC
    rw [vc_a₆, hv] at e6
    have ht : C.t ^ 2 + W.a₃ * C.t + (C.s ^ 6 + W.a₄ * C.s ^ 2) = 0 := by
      linear_combination e6
        - ((C.u : F) ^ 9 + (C.u : F) ^ 6 + (C.u : F) ^ 3 + 1) *
            (W.a₆ + C.r * W.a₄ + C.r ^ 3 + C.t * W.a₃ + C.t ^ 2) * hu3
        - (C.r ^ 2 + C.r * C.s ^ 2 + C.s ^ 4 + W.a₄) * hr
    exact ⟨hu3, hr, hs, ht⟩
  · rintro ⟨hu3, hr, hs, ht⟩
    have hv : ((C.u⁻¹ : Fˣ) : F) = (C.u : F) ^ 2 := by
      linear_combination (C.u : F) ^ 2 * huv - ((C.u⁻¹ : Fˣ) : F) * hu3
    rw [mem_stabilizer_iff]
    ext
    · rw [vc_a₁, W.a₁_of_isCharTwoJEqZeroNF]
    · rw [vc_a₂, W.a₂_of_isCharTwoJEqZeroNF]
      linear_combination ((C.u⁻¹ : Fˣ) : F) ^ 2 * hr +
        (((C.u⁻¹ : Fˣ) : F) ^ 2 * C.s ^ 2) * h2
    · rw [vc_a₃, hv]
      linear_combination (((C.u : F) ^ 3 + 1) * W.a₃) * hu3
    · rw [vc_a₄, hv]
      linear_combination (C.u : F) ^ 8 * hs + ((C.u : F) ^ 8 * (C.r + C.s ^ 2)) * hr
        - (((C.u : F) ^ 6 + (C.u : F) ^ 3 + 1) * W.a₄) * hu3 - W.a₄ * h2
    · rw [vc_a₆, hv]
      linear_combination (C.u : F) ^ 12 * ht
        + ((C.u : F) ^ 12 * (W.a₄ + C.r ^ 2 + C.r * C.s ^ 2 + C.s ^ 4)) * hr
        + (((C.u : F) ^ 9 + (C.u : F) ^ 6 + (C.u : F) ^ 3 + 1) * W.a₆) * hu3

noncomputable def stabEquiv (ha₃ : W.a₃ ≠ 0) :
    stabilizer (WeierstrassCurve.VariableChange F) W ≃
      Σ u : {u : F // u ^ 3 = 1},
        Σ s : {s : F // s ^ 4 + W.a₃ * s + (1 + u.1) * W.a₄ = 0},
          {t : F // t ^ 2 + W.a₃ * t + (s.1 ^ 6 + W.a₄ * s.1 ^ 2) = 0} where
  toFun C :=
    have h := (mem_stabilizer_iff_nf W C.1 ha₃).mp C.2
    ⟨⟨C.1.u, h.1⟩, ⟨C.1.s, h.2.2.1⟩, ⟨C.1.t, h.2.2.2⟩⟩
  invFun x :=
    ⟨⟨Units.mk0 x.1.1 (by
        intro h0
        have h := x.1.2
        rw [h0] at h
        norm_num at h), x.2.1.1 ^ 2, x.2.1.1, x.2.2.1⟩,
      (mem_stabilizer_iff_nf W _ ha₃).mpr ⟨x.1.2, rfl, x.2.1.2, x.2.2.2⟩⟩
  left_inv C := by
    obtain ⟨-, hr, -, -⟩ := (mem_stabilizer_iff_nf W C.1 ha₃).mp C.2
    apply Subtype.ext
    exact WeierstrassCurve.VariableChange.ext (Units.ext rfl) hr.symm rfl rfl
  right_inv x := by
    obtain ⟨⟨u, hu⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩ := x
    rfl

theorem natCard_stabilizer_nf [IsAlgClosed F] (ha₃ : W.a₃ ≠ 0) :
    Nat.card (stabilizer (WeierstrassCurve.VariableChange F) W) = 24 := by
  have h2' : ((2 : ℕ) : F) = 0 := CharP.cast_eq_zero F 2
  have h3' : ((3 : ℕ) : F) = 1 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, Nat.cast_succ, h2', zero_add]
  have h4' : ((4 : ℕ) : F) = 0 := (CharP.cast_eq_zero_iff F 2 4).mpr (by norm_num)

  have hT : ∀ c : F, Nat.card {t : F // t ^ 2 + W.a₃ * t + c = 0} = 2 := by
    intro c
    have hd : derivative (X ^ 2 + C W.a₃ * X + C c : F[X]) = C W.a₃ := by
      rw [derivative_add, derivative_add, derivative_X_pow, h2', C_0, zero_mul, zero_add,
        derivative_C_mul_X, derivative_C, add_zero]
    have hsep := separable_of_derivative_eq_C _ ha₃ hd
    have hdeg : (X ^ 2 + C W.a₃ * X + C c : F[X]).natDegree = 2 := by compute_degree!
    have e : {t : F // t ^ 2 + W.a₃ * t + c = 0} ≃
        {t : F // (X ^ 2 + C W.a₃ * X + C c : F[X]).eval t = 0} :=
      Equiv.subtypeEquivRight fun t => by simp
    rw [Nat.card_congr e, natCard_subtype_eval_eq_zero _ hsep, hdeg]

  have hS : ∀ u : F, Nat.card {s : F // s ^ 4 + W.a₃ * s + (1 + u) * W.a₄ = 0} = 4 := by
    intro u
    have hd : derivative (X ^ 4 + C W.a₃ * X + C ((1 + u) * W.a₄) : F[X]) = C W.a₃ := by
      rw [derivative_add, derivative_add, derivative_X_pow, h4', C_0, zero_mul, zero_add,
        derivative_C_mul_X, derivative_C, add_zero]
    have hsep := separable_of_derivative_eq_C _ ha₃ hd
    have hdeg : (X ^ 4 + C W.a₃ * X + C ((1 + u) * W.a₄) : F[X]).natDegree = 4 := by
      compute_degree!
    have e : {s : F // s ^ 4 + W.a₃ * s + (1 + u) * W.a₄ = 0} ≃
        {s : F // (X ^ 4 + C W.a₃ * X + C ((1 + u) * W.a₄) : F[X]).eval s = 0} :=
      Equiv.subtypeEquivRight fun s => by simp
    rw [Nat.card_congr e, natCard_subtype_eval_eq_zero _ hsep, hdeg]

  have hU : Nat.card {u : F // u ^ 3 = 1} = 3 := by
    have hsep : (X ^ 3 - 1 : F[X]).Separable := by
      rw [separable_def]
      have hd : derivative (X ^ 3 - 1 : F[X]) = X ^ 2 := by
        rw [derivative_sub, derivative_X_pow, h3', C_1, one_mul, derivative_one, sub_zero]
      rw [hd]
      exact ⟨-1, X, by ring⟩
    have hdeg : (X ^ 3 - 1 : F[X]).natDegree = 3 := by compute_degree!
    have e : {u : F // u ^ 3 = 1} ≃ {u : F // (X ^ 3 - 1 : F[X]).eval u = 0} :=
      Equiv.subtypeEquivRight fun u => by simp [sub_eq_zero]
    rw [Nat.card_congr e, natCard_subtype_eval_eq_zero _ hsep, hdeg]
  have hinner : ∀ u : {u : F // u ^ 3 = 1},
      Nat.card (Σ s : {s : F // s ^ 4 + W.a₃ * s + (1 + u.1) * W.a₄ = 0},
        {t : F // t ^ 2 + W.a₃ * t + (s.1 ^ 6 + W.a₄ * s.1 ^ 2) = 0}) = 8 := by
    intro u
    rw [natCard_sigma_of_forall_eq (n := 2) two_ne_zero (fun s => hT _), hS u.1]
  rw [Nat.card_congr (stabEquiv W ha₃),
    natCard_sigma_of_forall_eq (n := 8) (by norm_num) hinner, hU]

end NF

end AUT24

theorem solution
    {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]
    (E : WeierstrassCurve F) [E.IsElliptic] (hj : E.j = 0) :
    Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange F) E) = 24 := by
  have ha₁ : E.a₁ = 0 := E.j_eq_zero_iff_of_char_two.mp hj
  haveI := E.toCharTwoJEqZeroNF_spec ha₁
  set W := E.toCharTwoJEqZeroNF • E with hW
  have ha₃ : W.a₃ ≠ 0 := by
    intro h
    have hΔ : W.Δ = 0 := by
      rw [W.Δ_of_isCharTwoJEqZeroNF_of_char_two, h, zero_pow four_ne_zero]
    exact W.isUnit_Δ.ne_zero hΔ
  rw [Nat.card_congr (MulAction.stabilizerEquivStabilizer hW).toEquiv]
  exact AUT24.natCard_stabilizer_nf W ha₃

end S_WeierstrassCurve_natCard_stabilizer_variableChange_eq_twentyFour_of_j_eq_zero_of_charP_two
end P2MW
export P2MW.S_WeierstrassCurve_natCard_stabilizer_variableChange_eq_twentyFour_of_j_eq_zero_of_charP_two (solution)
