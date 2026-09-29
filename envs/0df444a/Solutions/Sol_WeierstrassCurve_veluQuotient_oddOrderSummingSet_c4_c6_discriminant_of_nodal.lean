-- Prove2me | solution 1 for WeierstrassCurve.veluQuotient_oddOrderSummingSet_c4_c6_discriminant_of_nodal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/1b66f0d1-121b-51e7-99e8-dc4b96b861e1

import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Theorems.Thm_WeierstrassCurve_exists_addEquiv_point_variableChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_c4_c6_discriminant_of_nodal

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_c4_c6_discriminant_of_nodal.WeierstrassCurve WeierstrassCurve.Affine Polynomial"

set_option autoImplicit false
set_option Elab.async false

section Expansions
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (S : Finset (R × R))

private lemma veluQuotient_c₄ :
    (W.veluQuotient S).c₄ = W.c₄ + 240 * W.veluTSum S := by
  simp only [c₄, veluQuotient_b₂, veluQuotient_b₄]; ring

private lemma veluQuotient_c₆ :
    (W.veluQuotient S).c₆ = W.c₆ + 504 * W.b₂ * W.veluTSum S + 6048 * W.veluWSum S := by
  simp only [c₆, veluQuotient_b₂, veluQuotient_b₄, veluQuotient_b₆]; ring

private lemma Ψ₂Sq_eval_eq (W : WeierstrassCurve R) (x : R) :
    W.Ψ₂Sq.eval x = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
  simp only [Ψ₂Sq, eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat, map_ofNat]

end Expansions

section SummingSetPlumbing
variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

omit [DecidableEq F] in
private lemma nonsingular_coordsOrZero {P : W.toAffine.Point} (hP : P ≠ 0) :
    W.toAffine.Nonsingular P.coordsOrZero.1 P.coordsOrZero.2 := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · exact h

omit [DecidableEq F] in
private lemma eq_some_coordsOrZero {P : W.toAffine.Point} (hP : P ≠ 0) :
    P = .some P.coordsOrZero.1 P.coordsOrZero.2 (nonsingular_coordsOrZero W hP) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · rfl

omit [DecidableEq F] in
private lemma eq_of_coordsOrZero_eq {P P' : W.toAffine.Point}
    (hP : P ≠ 0) (hP' : P' ≠ 0) (h : P.coordsOrZero = P'.coordsOrZero) : P = P' := by
  rcases P with _ | ⟨x, y, hh⟩
  · exact absurd rfl hP
  rcases P' with _ | ⟨x', y', hh'⟩
  · exact absurd rfl hP'
  obtain ⟨hx, hy⟩ := Prod.mk.injEq .. |>.mp h
  subst hx hy; rfl

variable {W} {Q : W.toAffine.Point} {n : ℕ} (hQord : addOrderOf Q = n)

include hQord in
private lemma nsmul_ne_zero_of_lt {k : ℕ} (hk1 : 1 ≤ k) (hkn : k < n) : k • Q ≠ 0 := by
  intro h0
  have hdvd := addOrderOf_dvd_of_nsmul_eq_zero h0
  rw [hQord] at hdvd
  exact absurd (Nat.le_of_dvd hk1 hdvd) (not_le.mpr hkn)

include hQord in
private lemma nsmul_inj_of_lt {m : ℕ} (hm : m < n)
    {j k : ℕ} (hj : j ∈ Finset.Icc 1 m) (hk : k ∈ Finset.Icc 1 m)
    (hjk : j • Q = k • Q) : j = k := by
  rw [Finset.mem_Icc] at hj hk
  rcases le_total j k with hle | hle
  · have hsub : (k - j) • Q = 0 := add_right_cancel (b := j • Q)
      (by rw [← add_nsmul, Nat.sub_add_cancel hle, zero_add, hjk])
    have hdvd := addOrderOf_dvd_of_nsmul_eq_zero hsub; rw [hQord] at hdvd
    have : k - j = 0 := Nat.eq_zero_of_dvd_of_lt hdvd
      (lt_of_le_of_lt (Nat.sub_le k j) (lt_of_le_of_lt hk.2 hm))
    omega
  · have hsub : (j - k) • Q = 0 := add_right_cancel (b := k • Q)
      (by rw [← add_nsmul, Nat.sub_add_cancel hle, zero_add, ← hjk])
    have hdvd := addOrderOf_dvd_of_nsmul_eq_zero hsub; rw [hQord] at hdvd
    have : j - k = 0 := Nat.eq_zero_of_dvd_of_lt hdvd
      (lt_of_le_of_lt (Nat.sub_le j k) (lt_of_le_of_lt hj.2 hm))
    omega

include hQord in
private lemma coordsOrZero_nsmul_injOn {m : ℕ} (hm : m < n) :
    Set.InjOn (fun k => (k • Q).coordsOrZero) (Finset.Icc 1 m : Set ℕ) := by
  intro j hj k hk hjk
  simp only at hjk
  have hj' := Finset.mem_coe.mp hj; have hk' := Finset.mem_coe.mp hk
  rw [Finset.mem_Icc] at hj' hk'
  have hjQ : j • Q ≠ 0 := nsmul_ne_zero_of_lt hQord hj'.1 (lt_of_le_of_lt hj'.2 hm)
  have hkQ : k • Q ≠ 0 := nsmul_ne_zero_of_lt hQord hk'.1 (lt_of_le_of_lt hk'.2 hm)
  exact nsmul_inj_of_lt hQord hm (Finset.mem_coe.mp hj) (Finset.mem_coe.mp hk)
    (eq_of_coordsOrZero_eq W hjQ hkQ hjk)

include hQord in
private lemma veluTSum_oddOrderSummingSet {m : ℕ} (hm : m < n) :
    W.veluTSum (W.oddOrderSummingSet Q m)
      = ∑ k ∈ Finset.Icc 1 m,
          (6 * ((k • Q).coordsOrZero.1) ^ 2 + W.b₂ * ((k • Q).coordsOrZero.1) + W.b₄) := by
  rw [veluTSum, oddOrderSummingSet, Finset.sum_image (coordsOrZero_nsmul_injOn hQord hm)]
  exact Finset.sum_congr rfl fun k _ => veluT_eq W _ _

include hQord in
private lemma veluWSum_oddOrderSummingSet {m : ℕ} (hm : m < n) :
    W.veluWSum (W.oddOrderSummingSet Q m)
      = ∑ k ∈ Finset.Icc 1 m,
          (W.Ψ₂Sq.eval ((k • Q).coordsOrZero.1)
           + ((k • Q).coordsOrZero.1)
             * (6 * ((k • Q).coordsOrZero.1) ^ 2 + W.b₂ * ((k • Q).coordsOrZero.1) + W.b₄)) := by
  rw [veluWSum, oddOrderSummingSet, Finset.sum_image (coordsOrZero_nsmul_injOn hQord hm)]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_Icc] at hk
  have hkQ : k • Q ≠ 0 := nsmul_ne_zero_of_lt hQord hk.1 (lt_of_le_of_lt hk.2 hm)
  rw [show W.veluW ((k • Q).coordsOrZero.1) ((k • Q).coordsOrZero.2)
        = W.veluU ((k • Q).coordsOrZero.1) ((k • Q).coordsOrZero.2)
          + ((k • Q).coordsOrZero.1)
            * W.veluT ((k • Q).coordsOrZero.1) ((k • Q).coordsOrZero.2) from rfl,
    W.veluU_eq_Ψ₂Sq_eval (nonsingular_coordsOrZero W hkQ).1, veluT_eq]

end SummingSetPlumbing

section MasterGlue
variable {F K : Type*} [Field F] [DecidableEq F] [Field K] (ι : F →+* K)
variable (W : WeierstrassCurve F)
variable {Q : W.toAffine.Point} {n : ℕ} (hQord : addOrderOf Q = n)
variable {m : ℕ} (hm : m < n)
variable (δ x₀ : K) (z : ℕ → K)
variable (hb₂ : ι W.b₂ = δ ^ 2 - 12 * x₀)
variable (hb₄ : ι W.b₄ = 6 * x₀ ^ 2 - δ ^ 2 * x₀)
variable (hb₆ : ι W.b₆ = δ ^ 2 * x₀ ^ 2 - 4 * x₀ ^ 3)
variable (hb₈ : ι W.b₈ = 3 * x₀ ^ 4 - δ ^ 2 * x₀ ^ 3)
variable (hz : ∀ k ∈ Finset.Icc 1 m, ι ((k • Q).coordsOrZero.1) = x₀ + δ ^ 2 * z k)

include hQord hm hb₂ hb₄ hz in
private lemma ι_veluTSum :
    ι (W.veluTSum (W.oddOrderSummingSet Q m))
      = δ ^ 4 * ∑ k ∈ Finset.Icc 1 m, (z k + 6 * (z k) ^ 2) := by
  rw [veluTSum_oddOrderSummingSet hQord hm, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [map_add, map_mul, map_pow, map_ofNat]
  rw [hz k hk, hb₂, hb₄]; ring

include hQord hm hb₂ hb₄ hb₆ hz in
private lemma ι_veluWSum :
    ι (W.veluWSum (W.oddOrderSummingSet Q m))
      = δ ^ 6 * ∑ k ∈ Finset.Icc 1 m, (2 * (z k) ^ 2 + 10 * (z k) ^ 3)
        + x₀ * (δ ^ 4 * ∑ k ∈ Finset.Icc 1 m, (z k + 6 * (z k) ^ 2)) := by
  rw [veluWSum_oddOrderSummingSet hQord hm, map_sum,
    show δ ^ 6 * ∑ k ∈ Finset.Icc 1 m, (2 * (z k) ^ 2 + 10 * (z k) ^ 3)
        + x₀ * (δ ^ 4 * ∑ k ∈ Finset.Icc 1 m, (z k + 6 * (z k) ^ 2))
        = ∑ k ∈ Finset.Icc 1 m, (δ ^ 6 * (2 * (z k) ^ 2 + 10 * (z k) ^ 3)
            + x₀ * (δ ^ 4 * (z k + 6 * (z k) ^ 2))) by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_add_distrib]]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Ψ₂Sq_eval_eq]
  simp only [map_add, map_mul, map_pow, map_ofNat]
  rw [hz k hk, hb₂, hb₄, hb₆]; ring

omit [DecidableEq F] in
include hb₂ hb₄ in
private lemma ι_c₄ : ι W.c₄ = δ ^ 4 := by
  have : ι W.c₄ = ι W.b₂ ^ 2 - 24 * ι W.b₄ := by
    simp only [c₄, map_sub, map_mul, map_pow, map_ofNat]
  rw [this, hb₂, hb₄]; ring

omit [DecidableEq F] in
include hb₂ hb₄ hb₆ in
private lemma ι_c₆ : ι W.c₆ = -δ ^ 6 := by
  have : ι W.c₆ = -ι W.b₂ ^ 3 + 36 * ι W.b₂ * ι W.b₄ - 216 * ι W.b₆ := by
    simp only [c₆, map_add, map_neg, map_sub, map_mul, map_pow, map_ofNat]
  rw [this, hb₂, hb₄, hb₆]; ring

variable (hιinj : Function.Injective ι)

include hιinj hQord hm hb₂ hb₄ hz in
private lemma master_c₄
    (hT : 240 * ∑ k ∈ Finset.Icc 1 m, (z k + 6 * (z k) ^ 2) = (n : K) ^ 4 - 1) :
    (W.veluQuotient (W.oddOrderSummingSet Q m)).c₄ = (n : F) ^ 4 * W.c₄ := by
  apply hιinj
  rw [map_mul, map_pow, map_natCast,
    show (W.veluQuotient (W.oddOrderSummingSet Q m)).c₄
        = W.c₄ + 240 * W.veluTSum (W.oddOrderSummingSet Q m) from veluQuotient_c₄ .., map_add,
    map_mul, map_ofNat, ι_veluTSum ι W hQord hm δ x₀ z hb₂ hb₄ hz, ι_c₄ ι W δ x₀ hb₂ hb₄]
  linear_combination δ ^ 4 * hT

include hιinj hQord hm hb₂ hb₄ hb₆ hz in
private lemma master_c₆
    (hW : 504 * ∑ k ∈ Finset.Icc 1 m, (z k + 6 * (z k) ^ 2)
          + 6048 * ∑ k ∈ Finset.Icc 1 m, (2 * (z k) ^ 2 + 10 * (z k) ^ 3)
          = 1 - (n : K) ^ 6) :
    (W.veluQuotient (W.oddOrderSummingSet Q m)).c₆ = (n : F) ^ 6 * W.c₆ := by
  apply hιinj
  rw [map_mul, map_pow, map_natCast,
    show (W.veluQuotient (W.oddOrderSummingSet Q m)).c₆
        = W.c₆ + 504 * W.b₂ * W.veluTSum (W.oddOrderSummingSet Q m)
          + 6048 * W.veluWSum (W.oddOrderSummingSet Q m) from veluQuotient_c₆ .., map_add,
    map_add, map_mul, map_mul, map_mul, map_ofNat, map_ofNat,
    ι_veluTSum ι W hQord hm δ x₀ z hb₂ hb₄ hz,
    ι_veluWSum ι W hQord hm δ x₀ z hb₂ hb₄ hb₆ hz,
    ι_c₆ ι W δ x₀ hb₂ hb₄ hb₆, hb₂]
  linear_combination δ ^ 6 * hW

include hιinj hQord hm hb₂ hb₄ hb₆ hb₈ hz in
private lemma master_Δ
    (hD : let τ := ∑ k ∈ Finset.Icc 1 m, (z k + 6 * (z k) ^ 2)
          let ω := ∑ k ∈ Finset.Icc 1 m, (2 * (z k) ^ 2 + 10 * (z k) ^ 3)
          τ + 7 * ω - 47 * τ ^ 2 - 3528 * τ * ω - 21168 * ω ^ 2 + 8000 * τ ^ 3 = 0) :
    (W.veluQuotient (W.oddOrderSummingSet Q m)).Δ = 0 := by
  apply hιinj; rw [map_zero]
  set τ := ∑ k ∈ Finset.Icc 1 m, (z k + 6 * (z k) ^ 2) with hτdef
  set ω := ∑ k ∈ Finset.Icc 1 m, (2 * (z k) ^ 2 + 10 * (z k) ^ 3) with hωdef
  simp only at hD
  have htS : ι (W.veluTSum (W.oddOrderSummingSet Q m)) = δ ^ 4 * τ :=
    ι_veluTSum ι W hQord hm δ x₀ z hb₂ hb₄ hz
  have hwS : ι (W.veluWSum (W.oddOrderSummingSet Q m)) = δ ^ 6 * ω + x₀ * (δ ^ 4 * τ) :=
    ι_veluWSum ι W hQord hm δ x₀ z hb₂ hb₄ hb₆ hz
  rw [show (W.veluQuotient (W.oddOrderSummingSet Q m)).Δ
        = -W.b₂ ^ 2 * (W.veluQuotient (W.oddOrderSummingSet Q m)).b₈
          - 8 * (W.veluQuotient (W.oddOrderSummingSet Q m)).b₄ ^ 3
          - 27 * (W.veluQuotient (W.oddOrderSummingSet Q m)).b₆ ^ 2
          + 9 * W.b₂ * (W.veluQuotient (W.oddOrderSummingSet Q m)).b₄
              * (W.veluQuotient (W.oddOrderSummingSet Q m)).b₆ from by
      simp only [WeierstrassCurve.Δ, veluQuotient_b₂],
    veluQuotient_b₄, veluQuotient_b₆, veluQuotient_b₈]
  simp only [map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat]
  rw [htS, hwS, hb₂, hb₄, hb₆, hb₈]
  linear_combination δ ^ 12 * hD

end MasterGlue

section BridgeFromPort
variable {F K : Type*} [Field F] [DecidableEq F] [Field K] (ι : F →+* K)
variable (W : WeierstrassCurve F)
variable {Q : W.toAffine.Point} {n : ℕ} (hQord : addOrderOf Q = n)
variable (δ x₀ u : K)
variable (hxfm : ∀ (i : ℕ) (x y : F) (h : W.toAffine.Nonsingular x y),
    i • Q = .some x y h → (ι x - x₀) * (1 - u ^ i) ^ 2 = δ ^ 2 * u ^ i)
variable (hprim : ∀ k ∈ Finset.Icc 1 (n - 1), u ^ k ≠ 1)

include hQord hxfm hprim in
private lemma hz_from_port {m : ℕ} (hm : m ≤ n - 1) :
    ∀ k ∈ Finset.Icc 1 m,
      ι ((k • Q).coordsOrZero.1) = x₀ + δ ^ 2 * (u ^ k / (1 - u ^ k) ^ 2) := by
  intro k hk
  rw [Finset.mem_Icc] at hk
  have hk' : k ∈ Finset.Icc 1 (n - 1) := Finset.mem_Icc.mpr ⟨hk.1, le_trans hk.2 hm⟩
  have hkn : k < n := by
    have := (Finset.mem_Icc.mp hk').2; omega
  have hkQ : k • Q ≠ 0 := nsmul_ne_zero_of_lt hQord hk.1 hkn
  have hne1 : (1 : K) - u ^ k ≠ 0 := sub_ne_zero.mpr (Ne.symm (hprim k hk'))
  have hclr := hxfm k _ _ (nonsingular_coordsOrZero W hkQ) (eq_some_coordsOrZero W hkQ)
  field_simp; linear_combination hclr

end BridgeFromPort

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map_b₄ Affine map_c₄ Affine.negY Affine.Y_eq_of_Y_ne Affine.slope_of_X_ne mk.injEq a₃ Affine.Point.add_of_Y_eq Affine.addPolynomial_slope b_relation a₁ map map_b₂ b₂ variableChange_b₂ variableChange_a₃ mk Ψ₂Sq a₄ variableChange_b₈ a₂ Affine.map_equation a₆ Affine.Point.some Affine.nonsingular_iff' variableChange_a₆ Affine.negAddY Affine.Point.zero_def c₆ variableChange_b₆ variableChange_a₂ Affine.nonsingular_add toAffine Affine.Point map_b₆ map_injective Affine.Point.add_some Affine.addPolynomial_eq b₆ b₈ variableChange_a₁ Affine.Point.some_ne_zero variableChange_b₄ variableChange_a₄ Δ c₄ VariableChange Affine.addY Affine.equation_iff Affine.map_nonsingular map_b₈ baseChange j b₄ veluT veluU veluW veluT_eq veluU_eq_Ψ₂Sq_eval veluTSum veluWSum veluQuotient veluQuotient_b₂ veluQuotient_b₄ veluQuotient_b₆ veluQuotient_b₈ oddOrderSummingSet exists_addEquiv_point_variableChange"
p2m_open "WeierstrassCurve"

open WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

variable {k : Type*} [Field k]

private structure _root_.WeierstrassCurve.IsNodalNormalForm (V : WeierstrassCurve k) (δ : k) : Prop where
  ha₁ : V.a₁ = -δ
  ha₂ : V.a₂ = 0
  ha₃ : V.a₃ = 0
  ha₄ : V.a₄ = 0
  ha₆ : V.a₆ = 0
  hδ : δ ≠ 0

p2m_export "WeierstrassCurve" "IsNodalNormalForm"
p2m_export_all "WeierstrassCurve" "IsNodalNormalForm"

private noncomputable def _root_.WeierstrassCurve.nodalCoord (V : WeierstrassCurve k) (δ : k) : V.toAffine.Point → k
  | .zero => 1
  | @Affine.Point.some _ _ _ x y _ => (y - δ * x) / y

p2m_export "WeierstrassCurve" "nodalCoord"
@[scoped simp]
private theorem nodalCoord_zero (V : WeierstrassCurve k) (δ : k) : V.nodalCoord δ 0 = 1 := rfl

@[scoped simp]
private theorem nodalCoord_some (V : WeierstrassCurve k) (δ : k) {x y : k}
    (h : V.toAffine.Nonsingular x y) :
    V.nodalCoord δ (.some x y h) = (y - δ * x) / y := rfl

namespace IsNodalNormalForm

variable {V : WeierstrassCurve k} {δ : k} (N : V.IsNodalNormalForm δ)
include N

private theorem _root_.WeierstrassCurve.IsNodalNormalForm.equation_iff (x y : k) : V.toAffine.Equation x y ↔ (y - δ * x) * y = x ^ 3 := by
  rw [Affine.equation_iff, N.ha₁, N.ha₂, N.ha₃, N.ha₄, N.ha₆]
  constructor <;> intro h <;> linear_combination h

p2m_export "WeierstrassCurve.IsNodalNormalForm" "equation_iff"

private theorem _root_.WeierstrassCurve.IsNodalNormalForm.not_origin {x y : k} (h : V.toAffine.Nonsingular x y) : ¬(x = 0 ∧ y = 0) := by
  rintro ⟨rfl, rfl⟩
  obtain ⟨-, hX | hY⟩ := (Affine.nonsingular_iff' _ _).mp h
  · apply hX
    rw [N.ha₁, N.ha₂, N.ha₄]
    ring
  · apply hY
    rw [N.ha₁, N.ha₃]
    ring

p2m_export "WeierstrassCurve.IsNodalNormalForm" "not_origin"

private theorem _root_.WeierstrassCurve.IsNodalNormalForm.y_ne_zero {x y : k} (h : V.toAffine.Nonsingular x y) : y ≠ 0 := by
  intro hy
  have hfac := (N.equation_iff x y).mp h.1
  rw [hy, mul_zero] at hfac
  exact N.not_origin h ⟨(pow_eq_zero_iff (n := 3) (by norm_num)).mp hfac.symm, hy⟩

p2m_export "WeierstrassCurve.IsNodalNormalForm" "y_ne_zero"

private theorem _root_.WeierstrassCurve.IsNodalNormalForm.tangent_ne_zero {x y : k} (h : V.toAffine.Nonsingular x y) : y - δ * x ≠ 0 := by
  intro h1
  have hfac := (N.equation_iff x y).mp h.1
  rw [h1, zero_mul] at hfac
  have hx : x = 0 := (pow_eq_zero_iff (n := 3) (by norm_num)).mp hfac.symm
  refine N.not_origin h ⟨hx, ?_⟩
  rw [hx, mul_zero, sub_zero] at h1
  exact h1

p2m_export "WeierstrassCurve.IsNodalNormalForm" "tangent_ne_zero"
private theorem _root_.WeierstrassCurve.IsNodalNormalForm.nodalCoord_ne_zero (P : V.toAffine.Point) : V.nodalCoord δ P ≠ 0 := by
  rcases P with _ | ⟨x, y, h⟩
  · exact one_ne_zero
  · rw [nodalCoord_some]
    exact div_ne_zero (N.tangent_ne_zero h) (N.y_ne_zero h)

p2m_export "WeierstrassCurve.IsNodalNormalForm" "nodalCoord_ne_zero"

private theorem _root_.WeierstrassCurve.IsNodalNormalForm.nodalCoord_eq_one_iff (P : V.toAffine.Point) : V.nodalCoord δ P = 1 ↔ P = 0 := by
  rcases P with _ | ⟨x, y, h⟩
  · exact ⟨fun _ => Affine.Point.zero_def.symm, fun _ => rfl⟩
  · rw [nodalCoord_some]
    constructor
    · intro h1
      have hy := N.y_ne_zero h
      have hxy : y - δ * x = y := (div_eq_one_iff_eq hy).mp h1
      have hx : x = 0 := by
        have hδx : δ * x = 0 := by linear_combination -hxy
        exact (mul_eq_zero.mp hδx).resolve_left N.hδ
      have hfac := (N.equation_iff x y).mp h.1
      rw [hx, mul_zero, sub_zero] at hfac
      have hy0 : y = 0 := mul_self_eq_zero.mp (by rw [hfac]; ring)
      exact absurd hy0 hy
    · intro hcon
      exact absurd hcon (Affine.Point.some_ne_zero h)

p2m_export "WeierstrassCurve.IsNodalNormalForm" "nodalCoord_eq_one_iff"

private theorem _root_.WeierstrassCurve.IsNodalNormalForm.x_mul_sq_eq {x y : k} (h : V.toAffine.Nonsingular x y) :
    x * (1 - V.nodalCoord δ (.some x y h)) ^ 2 = δ ^ 2 * V.nodalCoord δ (.some x y h) := by
  rw [nodalCoord_some]
  set u := (y - δ * x) / y with hu_def
  have hy := N.y_ne_zero h
  have hfac : (y - δ * x) * y = x ^ 3 := (N.equation_iff x y).mp h.1
  have hu : u * y = y - δ * x := div_mul_cancel₀ _ hy
  have h1 : (1 - u) * y = δ * x := by linear_combination -hu
  apply mul_right_cancel₀ (pow_ne_zero 2 hy)
  linear_combination x * ((1 - u) * y + δ * x) * h1 - δ ^ 2 * y * hu - δ ^ 2 * hfac

p2m_export "WeierstrassCurve.IsNodalNormalForm" "x_mul_sq_eq"
section GroupLaw

variable [DecidableEq k]

private theorem _root_.WeierstrassCurve.IsNodalNormalForm.nodalCoord_mul (P Q : V.toAffine.Point) :
    V.nodalCoord δ (P + Q) = V.nodalCoord δ P * V.nodalCoord δ Q := by
  have ha₁' : V.toAffine.a₁ = -δ := N.ha₁
  have ha₂' : V.toAffine.a₂ = 0 := N.ha₂
  have ha₃' : V.toAffine.a₃ = 0 := N.ha₃
  have ha₄' : V.toAffine.a₄ = 0 := N.ha₄
  have ha₆' : V.toAffine.a₆ = 0 := N.ha₆
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · rw [← Affine.Point.zero_def, zero_add, nodalCoord_zero, one_mul]
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rw [← Affine.Point.zero_def, add_zero, nodalCoord_zero, mul_one]
  by_cases hxy : x₁ = x₂ ∧ y₁ = V.toAffine.negY x₂ y₂
  ·
    rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2, nodalCoord_zero, nodalCoord_some, nodalCoord_some,
      hxy.1, hxy.2]
    have hl₁ := N.tangent_ne_zero h₂
    have hl₂ := N.y_ne_zero h₂
    have hnum : V.toAffine.negY x₂ y₂ - δ * x₂ = -y₂ := by
      rw [Affine.negY, ha₁', ha₃']
      ring
    have hden : V.toAffine.negY x₂ y₂ = -(y₂ - δ * x₂) := by
      rw [Affine.negY, ha₁', ha₃']
      ring
    rw [hnum, hden, neg_div_neg_eq, div_mul_div_comm, mul_comm y₂ (y₂ - δ * x₂)]
    exact (div_self (mul_ne_zero hl₁ hl₂)).symm
  ·
    have hP := N.y_ne_zero h₁
    have hQ := N.y_ne_zero h₂
    have hR := N.y_ne_zero (Affine.nonsingular_add h₁ h₂ hxy)

    have hcubic := Affine.addPolynomial_slope h₁.1 h₂.1 hxy
    rw [Affine.addPolynomial_eq, neg_inj, Cubic.prod_X_sub_C_eq, Cubic.toPoly_injective] at hcubic
    have E2 := congrArg Cubic.c hcubic
    have E3 := congrArg Cubic.d hcubic
    dsimp only at E2 E3

    have hline : y₂ = V.toAffine.slope x₁ x₂ y₁ y₂ * (x₂ - x₁) + y₁ := by
      by_cases hx : x₁ = x₂
      · subst hx
        have hy : y₁ ≠ V.toAffine.negY x₁ y₂ := fun h => hxy ⟨rfl, h⟩
        rw [sub_self, mul_zero, zero_add]
        exact (Affine.Y_eq_of_Y_ne h₁.1 h₂.1 rfl hy).symm
      · rw [Affine.slope_of_X_ne hx]
        field_simp [sub_ne_zero.mpr hx]
        ring
    rw [Affine.Point.add_some hxy, nodalCoord_some, nodalCoord_some, nodalCoord_some,
      div_mul_div_comm, div_eq_div_iff hR (mul_ne_zero hP hQ)]
    simp only [Affine.addY, Affine.negAddY, Affine.negY] at hR ⊢
    set ℓ := V.toAffine.slope x₁ x₂ y₁ y₂ with hℓ
    set X₃ := V.toAffine.addX x₁ x₂ ℓ with hX₃
    have E1 : X₃ = ℓ ^ 2 + V.toAffine.a₁ * ℓ - V.toAffine.a₂ - x₁ - x₂ := by rw [hX₃]; rfl
    simp only [ha₁', ha₂', ha₃', ha₄', ha₆'] at E1 E2 E3 ⊢
    linear_combination
      δ * (δ * x₁ * X₃ + ℓ * x₁ ^ 2 - ℓ * x₁ * X₃ - x₁ * y₁ - X₃ * y₁) * hline
      + ((ℓ - δ) ^ 3 - ℓ ^ 3) * E3
      - (y₁ - ℓ * x₁) * ((ℓ - δ) ^ 2 - ℓ ^ 2) * E2
      - δ * (y₁ - ℓ * x₁) ^ 2 * E1

p2m_export "WeierstrassCurve.IsNodalNormalForm" "nodalCoord_mul"

private theorem _root_.WeierstrassCurve.IsNodalNormalForm.nodalCoord_nsmul (n : ℕ) (P : V.toAffine.Point) :
    V.nodalCoord δ (n • P) = V.nodalCoord δ P ^ n := by
  induction n with
  | zero => rw [zero_nsmul, nodalCoord_zero, pow_zero]
  | succ m ih => rw [succ_nsmul, N.nodalCoord_mul, ih, pow_succ]

p2m_export "WeierstrassCurve.IsNodalNormalForm" "nodalCoord_nsmul"

private theorem _root_.WeierstrassCurve.IsNodalNormalForm.isPrimitiveRoot_nodalCoord (P : V.toAffine.Point) :
    IsPrimitiveRoot (V.nodalCoord δ P) (addOrderOf P) :=
  (IsPrimitiveRoot.iff_def _ _).mpr
    ⟨by rw [← N.nodalCoord_nsmul, addOrderOf_nsmul_eq_zero, nodalCoord_zero],
     fun l hl => addOrderOf_dvd_iff_nsmul_eq_zero.mpr
       ((N.nodalCoord_eq_one_iff _).mp (by rw [N.nodalCoord_nsmul]; exact hl))⟩

p2m_export "WeierstrassCurve.IsNodalNormalForm" "isPrimitiveRoot_nodalCoord"
end GroupLaw

end IsNodalNormalForm

section Production

variable {V : WeierstrassCurve k}

private theorem c₄_eq_sq_of_singular {x₀ y₀ : k}
    (hdx : V.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * V.a₂ * x₀ + V.a₄) = 0)
    (hdy : 2 * y₀ + V.a₁ * x₀ + V.a₃ = 0) :
    V.c₄ = (V.b₂ + 12 * x₀) ^ 2 := by
  have ha₄' : V.a₄ = V.a₁ * y₀ - 3 * x₀ ^ 2 - 2 * V.a₂ * x₀ := by linear_combination -hdx
  have ha₃' : V.a₃ = -2 * y₀ - V.a₁ * x₀ := by linear_combination hdy
  simp only [WeierstrassCurve.c₄, b₂, b₄, ha₄', ha₃']
  ring

private theorem two_mul_tangentRoot_add_a₁_ne_zero {x₀ y₀ w : k}
    (hdx : V.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * V.a₂ * x₀ + V.a₄) = 0)
    (hdy : 2 * y₀ + V.a₁ * x₀ + V.a₃ = 0)
    (hw : w ^ 2 + V.a₁ * w - (V.a₂ + 3 * x₀) = 0)
    (hc₄ : V.c₄ ≠ 0) :
    2 * w + V.a₁ ≠ 0 := by
  intro hcon
  apply hc₄
  have hr : (2 * w + V.a₁) ^ 2 = V.b₂ + 12 * x₀ := by
    simp only [b₂]
    linear_combination 4 * hw
  rw [c₄_eq_sq_of_singular hdx hdy, ← hr, hcon]
  ring

private theorem isNodalNormalForm_variableChange {x₀ y₀ w : k}
    (heq : V.toAffine.Equation x₀ y₀)
    (hdx : V.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * V.a₂ * x₀ + V.a₄) = 0)
    (hdy : 2 * y₀ + V.a₁ * x₀ + V.a₃ = 0)
    (hw : w ^ 2 + V.a₁ * w - (V.a₂ + 3 * x₀) = 0)
    (hc₄ : V.c₄ ≠ 0) :
    ((⟨1, x₀, -V.a₁ - w, y₀⟩ : VariableChange k) • V).IsNodalNormalForm (2 * w + V.a₁) where
  ha₁ := by
    simp only [variableChange_a₁, inv_one, Units.val_one, one_mul]
    ring
  ha₂ := by
    simp only [variableChange_a₂, inv_one, Units.val_one, one_pow, one_mul]
    linear_combination -hw
  ha₃ := by
    simp only [variableChange_a₃, inv_one, Units.val_one, one_pow, one_mul]
    linear_combination hdy
  ha₄ := by
    simp only [variableChange_a₄, inv_one, Units.val_one, one_pow, one_mul]
    linear_combination -hdx + (V.a₁ + w) * hdy
  ha₆ := by
    simp only [variableChange_a₆, inv_one, Units.val_one, one_pow, one_mul]
    linear_combination -(Affine.equation_iff x₀ y₀).mp heq
  hδ := two_mul_tangentRoot_add_a₁_ne_zero hdx hdy hw hc₄

end Production

section Node

variable (W : WeierstrassCurve k)

private theorem _root_.WeierstrassCurve.exists_singular_point (hΔ : W.Δ = 0) (hc₄ : W.c₄ ≠ 0) :
    ∃ x₀ y₀ : k, W.toAffine.Equation x₀ y₀ ∧
      W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄) = 0 ∧
      2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 := by
  by_cases h2 : (2 : k) = 0
  ·
    have hΔ' := hΔ
    simp only [WeierstrassCurve.Δ, b₂, b₄, b₆, b₈] at hΔ'
    have ha₁ : W.a₁ ≠ 0 := by
      intro ha
      apply hc₄
      have e : W.c₄ = W.a₁ ^ 4 + 2 * (4 * W.a₁ ^ 2 * W.a₂ - 12 * W.a₁ * W.a₃ + 8 * W.a₂ ^ 2
          - 24 * W.a₄) := by
        simp only [WeierstrassCurve.c₄, b₂, b₄]
        ring
      rw [e, ha, h2]
      ring
    set x₀ : k := W.a₃ / W.a₁ with hx₀_def
    have hx : W.a₁ * x₀ = W.a₃ := mul_div_cancel₀ _ ha₁
    set y₀ : k := (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄) / W.a₁ with hy₀_def
    have hy : W.a₁ * y₀ = 3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄ := mul_div_cancel₀ _ ha₁
    have hY : W.a₁ ^ 3 * y₀ = 3 * W.a₃ ^ 2 + 2 * W.a₁ * W.a₂ * W.a₃ + W.a₁ ^ 2 * W.a₄ := by
      linear_combination W.a₁ ^ 2 * hy + (3 * (W.a₁ * x₀ + W.a₃) + 2 * W.a₁ * W.a₂) * hx
    refine ⟨x₀, y₀, ?_, by linear_combination hy, by linear_combination (y₀ + W.a₃) * h2 + hx⟩
    rw [Affine.equation_iff]
    have key : W.a₁ ^ 6 * (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
        - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) =
        (W.a₁ ^ 3 * y₀) ^ 2 + W.a₁ ^ 3 * (W.a₁ * x₀) * (W.a₁ ^ 3 * y₀)
          + W.a₁ ^ 3 * W.a₃ * (W.a₁ ^ 3 * y₀) - W.a₁ ^ 3 * (W.a₁ * x₀) ^ 3
          - W.a₁ ^ 4 * W.a₂ * (W.a₁ * x₀) ^ 2 - W.a₁ ^ 5 * W.a₄ * (W.a₁ * x₀)
          - W.a₁ ^ 6 * W.a₆ := by ring
    conv_rhs at key => rw [hY, hx]
    have h0 : W.a₁ ^ 6 * (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
        - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) = 0 := by
      rw [key]
      linear_combination hΔ' + (2 * W.a₁ ^ 4 * W.a₂ * W.a₃ ^ 2 + 6 * W.a₁ ^ 4 * W.a₂ * W.a₆
        - 2 * W.a₁ ^ 3 * W.a₂ * W.a₃ * W.a₄ + 2 * W.a₁ ^ 3 * W.a₃ ^ 3
        - 18 * W.a₁ ^ 3 * W.a₃ * W.a₆ + 6 * W.a₁ ^ 2 * W.a₂ ^ 2 * W.a₃ ^ 2
        + 24 * W.a₁ ^ 2 * W.a₂ ^ 2 * W.a₆ - 4 * W.a₁ ^ 2 * W.a₂ * W.a₄ ^ 2
        + 18 * W.a₁ ^ 2 * W.a₃ ^ 2 * W.a₄ - 36 * W.a₁ ^ 2 * W.a₄ * W.a₆
        - 8 * W.a₁ * W.a₂ ^ 2 * W.a₃ * W.a₄ - 12 * W.a₁ * W.a₂ * W.a₃ ^ 3
        - 72 * W.a₁ * W.a₂ * W.a₃ * W.a₆ + 48 * W.a₁ * W.a₃ * W.a₄ ^ 2 + 8 * W.a₂ ^ 3 * W.a₃ ^ 2
        + 32 * W.a₂ ^ 3 * W.a₆ - 8 * W.a₂ ^ 2 * W.a₄ ^ 2 - 36 * W.a₂ * W.a₃ ^ 2 * W.a₄
        - 144 * W.a₂ * W.a₄ * W.a₆ + 18 * W.a₃ ^ 4 + 108 * W.a₃ ^ 2 * W.a₆ + 32 * W.a₄ ^ 3
        + 216 * W.a₆ ^ 2) * h2
    exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left (pow_ne_zero 6 ha₁))
  ·
    have hΔ' := hΔ
    simp only [WeierstrassCurve.Δ] at hΔ'
    set x₀ : k := (18 * W.b₆ - W.b₂ * W.b₄) / W.c₄ with hx₀_def
    have hcx : W.c₄ * x₀ = 18 * W.b₆ - W.b₂ * W.b₄ := mul_div_cancel₀ _ hc₄

    have ht : 6 * x₀ ^ 2 + W.b₂ * x₀ + W.b₄ = 0 := by
      have key : W.c₄ ^ 2 * (6 * x₀ ^ 2 + W.b₂ * x₀ + W.b₄) =
          6 * (W.c₄ * x₀) ^ 2 + W.b₂ * (W.c₄ * x₀) * W.c₄ + W.b₄ * W.c₄ ^ 2 := by ring
      rw [hcx] at key
      have h0 : W.c₄ ^ 2 * (6 * x₀ ^ 2 + W.b₂ * x₀ + W.b₄) = 0 := by
        rw [key]
        simp only [WeierstrassCurve.c₄]
        linear_combination (-72) * hΔ' + (-18 * W.b₂ ^ 2) * W.b_relation
      exact (mul_eq_zero.mp h0).resolve_left (pow_ne_zero 2 hc₄)

    have hg : 4 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 2 * W.b₄ * x₀ + W.b₆ = 0 := by
      have key : W.c₄ ^ 3 * (4 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 2 * W.b₄ * x₀ + W.b₆) =
          4 * (W.c₄ * x₀) ^ 3 + W.b₂ * (W.c₄ * x₀) ^ 2 * W.c₄
            + 2 * W.b₄ * (W.c₄ * x₀) * W.c₄ ^ 2 + W.b₆ * W.c₄ ^ 3 := by ring
      rw [hcx] at key
      have h0 : W.c₄ ^ 3 * (4 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 2 * W.b₄ * x₀ + W.b₆) = 0 := by
        rw [key]
        simp only [WeierstrassCurve.c₄]
        linear_combination (4 * (-W.b₂ ^ 3 + 36 * W.b₂ * W.b₄ - 216 * W.b₆)) * hΔ'
          + (W.b₂ ^ 2 * (-W.b₂ ^ 3 + 36 * W.b₂ * W.b₄ - 216 * W.b₆)) * W.b_relation
      exact (mul_eq_zero.mp h0).resolve_left (pow_ne_zero 3 hc₄)
    set y₀ : k := -(W.a₁ * x₀ + W.a₃) / 2 with hy₀_def
    have hy : 2 * y₀ = -(W.a₁ * x₀ + W.a₃) := mul_div_cancel₀ _ h2
    have hdy : 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 := by linear_combination hy
    have hdx : W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄) = 0 := by
      have h0 : 2 * (W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)) = 0 := by
        simp only [b₂, b₄] at ht
        linear_combination W.a₁ * hdy - ht
      exact (mul_eq_zero.mp h0).resolve_left h2
    refine ⟨x₀, y₀, ?_, hdx, hdy⟩
    rw [Affine.equation_iff]
    have h4 : (4 : k) ≠ 0 := by
      rw [show (4 : k) = 2 * 2 by norm_num]
      exact mul_ne_zero h2 h2
    have h0 : 4 * (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀
        - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) = 0 := by
      simp only [b₂, b₄, b₆] at hg
      linear_combination (2 * y₀ + W.a₁ * x₀ + W.a₃) * hdy - hg
    exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left h4)

p2m_export "WeierstrassCurve" "exists_singular_point"
end Node

section PointBaseChange

variable (K : Type*) [Field K] [Algebra k K]

private theorem nonsingular_baseChange {V : WeierstrassCurve k} {x y : k}
    (h : V.toAffine.Nonsingular x y) :
    (V.baseChange K).toAffine.Nonsingular (algebraMap k K x) (algebraMap k K y) :=
  (WeierstrassCurve.Affine.map_nonsingular (W := V.toAffine)
    (f := ((Algebra.ofId k K).toRingHom : k →+* K)) (RingHom.injective _) x y).mpr h

variable [DecidableEq k] [DecidableEq K]

private noncomputable def pointBaseChange (V : WeierstrassCurve k) :
    V.toAffine.Point →+ (V.baseChange K).toAffine.Point :=
  Point.map (W' := V) (Algebra.ofId k K)

variable {K}

private theorem pointBaseChange_some {V : WeierstrassCurve k} {x y : k} (h : V.toAffine.Nonsingular x y) :
    pointBaseChange K V (Point.some x y h) =
      Point.some (algebraMap k K x) (algebraMap k K y) (nonsingular_baseChange K h) :=
  rfl

private theorem pointBaseChange_injective (V : WeierstrassCurve k) :
    Function.Injective (pointBaseChange K V) :=
  Point.map_injective (W' := V) (f := Algebra.ofId k K)

private theorem addOrderOf_pointBaseChange (V : WeierstrassCurve k) (P : V.toAffine.Point) :
    addOrderOf (pointBaseChange K V P) = addOrderOf P :=
  addOrderOf_injective _ (pointBaseChange_injective V) P

end PointBaseChange

section Frame

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

open Polynomial in

private theorem _root_.WeierstrassCurve.nodal_frame (hΔ : W.Δ = 0) (hc₄ : W.c₄ ≠ 0) (Q : W.toAffine.Point) :
    ∃ x₀ δ u : AlgebraicClosure F,
      IsPrimitiveRoot u (addOrderOf Q) ∧
      algebraMap F (AlgebraicClosure F) W.b₂ = δ ^ 2 - 12 * x₀ ∧
      algebraMap F (AlgebraicClosure F) W.b₄ = 6 * x₀ ^ 2 - δ ^ 2 * x₀ ∧
      algebraMap F (AlgebraicClosure F) W.b₆ = δ ^ 2 * x₀ ^ 2 - 4 * x₀ ^ 3 ∧
      algebraMap F (AlgebraicClosure F) W.b₈ = 3 * x₀ ^ 4 - δ ^ 2 * x₀ ^ 3 ∧
      ∀ (i : ℕ) (x y : F) (h : W.toAffine.Nonsingular x y), i • Q = .some x y h →
        (algebraMap F (AlgebraicClosure F) x - x₀) * (1 - u ^ i) ^ 2 = δ ^ 2 * u ^ i := by
  classical
  obtain ⟨x₀, y₀, heq, hdx, hdy⟩ := W.exists_singular_point hΔ hc₄
  set φ := algebraMap F (AlgebraicClosure F) with hφ

  have hc₄' : (W.baseChange (AlgebraicClosure F)).c₄ ≠ 0 := by
    rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_c₄]
    exact (map_ne_zero φ).mpr hc₄
  have heq' : (W.baseChange (AlgebraicClosure F)).toAffine.Equation (φ x₀) (φ y₀) :=
    (WeierstrassCurve.Affine.map_equation (W := W.toAffine) (f := φ) φ.injective x₀ y₀).mpr heq
  have hdx' : (W.baseChange (AlgebraicClosure F)).a₁ * φ y₀
      - (3 * φ x₀ ^ 2 + 2 * (W.baseChange (AlgebraicClosure F)).a₂ * φ x₀
        + (W.baseChange (AlgebraicClosure F)).a₄) = 0 := by
    have h := congrArg φ hdx
    rw [map_sub, map_mul, map_add, map_add, map_mul, map_mul, map_mul, map_pow, map_ofNat,
      map_ofNat, _root_.map_zero] at h
    exact h
  have hdy' : 2 * φ y₀ + (W.baseChange (AlgebraicClosure F)).a₁ * φ x₀
      + (W.baseChange (AlgebraicClosure F)).a₃ = 0 := by
    have h := congrArg φ hdy
    rw [map_add, map_add, map_mul, map_mul, map_ofNat, _root_.map_zero] at h
    exact h
  have hb₂K : (W.baseChange (AlgebraicClosure F)).b₂ = φ W.b₂ := by
    rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_b₂]
  have hb₄K : (W.baseChange (AlgebraicClosure F)).b₄ = φ W.b₄ := by
    rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_b₄]
  have hb₆K : (W.baseChange (AlgebraicClosure F)).b₆ = φ W.b₆ := by
    rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_b₆]
  have hb₈K : (W.baseChange (AlgebraicClosure F)).b₈ = φ W.b₈ := by
    rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_b₈]

  obtain ⟨w, hw⟩ : ∃ w : AlgebraicClosure F,
      w ^ 2 + (W.baseChange (AlgebraicClosure F)).a₁ * w
        - ((W.baseChange (AlgebraicClosure F)).a₂ + 3 * φ x₀) = 0 := by
    set p : (AlgebraicClosure F)[X] := X ^ 2 + C ((W.baseChange (AlgebraicClosure F)).a₁) * X
      - C ((W.baseChange (AlgebraicClosure F)).a₂ + 3 * φ x₀) with hp
    have hdeg : p.degree = 2 := by
      rw [hp, sub_eq_add_neg, ← C_neg]
      compute_degree!
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_root p (by rw [hdeg]; decide)
    refine ⟨w, ?_⟩
    have := hw
    simp only [hp, IsRoot.def, eval_sub, eval_add, eval_pow, eval_X, eval_mul, eval_C] at this
    linear_combination this

  set C : VariableChange (AlgebraicClosure F) :=
    ⟨1, φ x₀, -(W.baseChange (AlgebraicClosure F)).a₁ - w, φ y₀⟩ with hC
  have N : (C • W.baseChange (AlgebraicClosure F)).IsNodalNormalForm
      (2 * w + (W.baseChange (AlgebraicClosure F)).a₁) :=
    isNodalNormalForm_variableChange heq' hdx' hdy' hw hc₄'
  set δ := 2 * w + (W.baseChange (AlgebraicClosure F)).a₁ with hδ
  obtain ⟨e, he⟩ := (W.baseChange (AlgebraicClosure F)).exists_addEquiv_point_variableChange C

  have nb₂ : (C • W.baseChange (AlgebraicClosure F)).b₂ = δ ^ 2 := by
    rw [WeierstrassCurve.b₂, N.ha₁, N.ha₂]
    ring
  have nb₄ : (C • W.baseChange (AlgebraicClosure F)).b₄ = 0 := by
    rw [WeierstrassCurve.b₄, N.ha₁, N.ha₃, N.ha₄]
    ring
  have nb₆ : (C • W.baseChange (AlgebraicClosure F)).b₆ = 0 := by
    rw [WeierstrassCurve.b₆, N.ha₃, N.ha₆]
    ring
  have nb₈ : (C • W.baseChange (AlgebraicClosure F)).b₈ = 0 := by
    rw [WeierstrassCurve.b₈, N.ha₁, N.ha₂, N.ha₃, N.ha₄, N.ha₆]
    ring
  have vb₂ := (W.baseChange (AlgebraicClosure F)).variableChange_b₂ C
  have vb₄ := (W.baseChange (AlgebraicClosure F)).variableChange_b₄ C
  have vb₆ := (W.baseChange (AlgebraicClosure F)).variableChange_b₆ C
  have vb₈ := (W.baseChange (AlgebraicClosure F)).variableChange_b₈ C
  rw [hb₂K] at vb₂ vb₄ vb₆ vb₈
  rw [hb₄K] at vb₄ vb₆ vb₈
  rw [hb₆K] at vb₆ vb₈
  rw [hb₈K] at vb₈
  simp only [hC, inv_one, Units.val_one, one_pow, one_mul] at vb₂ vb₄ vb₆ vb₈ nb₂ nb₄ nb₆ nb₈
  have hb₂ : φ W.b₂ = δ ^ 2 - 12 * φ x₀ := by linear_combination nb₂ - vb₂
  have hb₄ : φ W.b₄ = 6 * φ x₀ ^ 2 - δ ^ 2 * φ x₀ := by
    linear_combination nb₄ - vb₄ - φ x₀ * hb₂
  have hb₆ : φ W.b₆ = δ ^ 2 * φ x₀ ^ 2 - 4 * φ x₀ ^ 3 := by
    linear_combination nb₆ - vb₆ - 2 * φ x₀ * hb₄ - φ x₀ ^ 2 * hb₂
  have hb₈ : φ W.b₈ = 3 * φ x₀ ^ 4 - δ ^ 2 * φ x₀ ^ 3 := by
    linear_combination nb₈ - vb₈ - 3 * φ x₀ * hb₆ - 3 * φ x₀ ^ 2 * hb₄ - φ x₀ ^ 3 * hb₂
  refine ⟨φ x₀, δ, (C • W.baseChange (AlgebraicClosure F)).nodalCoord δ
    (e (pointBaseChange (AlgebraicClosure F) W Q)), ?_, hb₂, hb₄, hb₆, hb₈, ?_⟩
  · rw [← addOrderOf_pointBaseChange (K := AlgebraicClosure F) W Q, ← AddEquiv.addOrderOf_eq e]
    exact N.isPrimitiveRoot_nodalCoord _
  · intro i x y h hi
    obtain ⟨h', he'⟩ := he (φ x) (φ y) (nonsingular_baseChange (AlgebraicClosure F) h)
    rw [← N.nodalCoord_nsmul, ← map_nsmul, ← map_nsmul, hi, pointBaseChange_some, he']
    have key := N.x_mul_sq_eq h'
    have hX : ((C.u⁻¹ : (AlgebraicClosure F)ˣ) : AlgebraicClosure F) ^ 2 * (φ x - C.r)
        = φ x - φ x₀ := by
      simp only [hC, inv_one, Units.val_one, one_pow, one_mul]
    linear_combination key
      - (1 - (C • W.baseChange (AlgebraicClosure F)).nodalCoord δ (.some _ _ h')) ^ 2 * hX

p2m_export "WeierstrassCurve" "nodal_frame"
end Frame

end WeierstrassCurve
p2m_reactivate "P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_c4_c6_discriminant_of_nodal.WeierstrassCurve"

namespace RbAux4

open Polynomial Finset

private def E1 (n : ℕ) : ℤ := n.choose 3 - n * (n / 2).choose 2

private def E2 (n : ℕ) : ℤ :=
  n.choose 5 - (n / 2 - 1).choose 2 * E1 n - (n / 2).choose 4 * n

private def E3 (n : ℕ) : ℤ :=
  n.choose 7 - (n / 2 - 2).choose 2 * E2 n - (n / 2 - 1).choose 4 * E1 n
    - (n / 2).choose 6 * n

variable {K : Type*} [Field K]

private def tau (u : K) (n l : ℕ) : K := (1 - u ^ l) * (1 - u ^ (n - l))

private def esym (u : K) (n m j : ℕ) : K :=
  ∑ t ∈ powersetCard j (Icc 1 m), ∏ l ∈ t, tau u n l

section Basic

variable {u : K} {n : ℕ}

private lemma one_sub_pow_ne_zero (hu : IsPrimitiveRoot u n) {k : ℕ}
    (hk1 : 1 ≤ k) (hk2 : k < n) : (1 : K) - u ^ k ≠ 0 := by
  have h := hu.pow_ne_one_of_pos_of_lt (Nat.one_le_iff_ne_zero.mp hk1) hk2
  exact sub_ne_zero.mpr fun hc => h hc.symm

private lemma natCast_ne_zero (hu : IsPrimitiveRoot u n) (hn : Odd n) : (n : K) ≠ 0 := by
  intro h
  have hn0 : n ≠ 0 := hn.pos.ne'
  have hdvd : ringChar K ∣ n := (ringChar.spec K n).mp h
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hprime | hzero
  · haveI : Fact (ringChar K).Prime := ⟨hprime⟩
    obtain ⟨d, hd⟩ := hdvd
    have hd0 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with rfl | h'
      · simp at hd; exact absurd hd hn0
      · exact h'
    have hdn : d < n := by
      rw [hd]
      exact lt_mul_iff_one_lt_left hd0 |>.mpr hprime.one_lt
    have h1 : (u ^ d - 1 : K) ^ ringChar K = 0 := by
      rw [sub_pow_char, ← pow_mul, mul_comm d (ringChar K), ← hd, hu.pow_eq_one]
      simp
    have h2 : u ^ d = 1 := by
      have h15 : (u ^ d - 1 : K) = 0 :=
        pow_eq_zero_iff hprime.ne_zero |>.mp h1
      exact sub_eq_zero.mp h15
    have h3 : n ∣ d := (hu.pow_eq_one_iff_dvd d).mp h2
    exact absurd (Nat.le_of_dvd hd0 h3) (not_le.mpr hdn)
  · rw [hzero] at hdvd
    exact hn0 (zero_dvd_iff.mp hdvd)

private lemma w_reflect (hu : IsPrimitiveRoot u n) {l : ℕ} (hl2 : l < n) :
    (1 - u ^ (n - l)) * u ^ l = -(1 - u ^ l) := by
  have h1 : u ^ (n - l) * u ^ l = 1 := by
    rw [← pow_add, Nat.sub_add_cancel hl2.le, hu.pow_eq_one]
  linear_combination -h1

private lemma tau_ne_zero (hu : IsPrimitiveRoot u n) (hn : Odd n) {l : ℕ}
    (hl1 : 1 ≤ l) (hl2 : l ≤ n / 2) : tau u n l ≠ 0 := by
  have hn0 : 0 < n := hn.pos
  have hl : l < n := lt_of_le_of_lt hl2 (Nat.div_lt_self hn0 one_lt_two)
  exact mul_ne_zero (one_sub_pow_ne_zero hu hl1 hl)
    (one_sub_pow_ne_zero hu (by omega) (by omega))

private lemma tau_mul_z (hu : IsPrimitiveRoot u n) (hn : Odd n) {l : ℕ}
    (hl1 : 1 ≤ l) (hl2 : l ≤ n / 2) {z : K}
    (hz : z * (1 - u ^ l) ^ 2 = u ^ l) : tau u n l * z = -1 := by
  have hn0 : 0 < n := hn.pos
  have hl : l < n := lt_of_le_of_lt hl2 (Nat.div_lt_self hn0 one_lt_two)
  have hw := one_sub_pow_ne_zero hu hl1 hl
  have hrefl := w_reflect hu hl
  have key : (tau u n l * z + 1) * (1 - u ^ l) = 0 := by
    unfold tau
    linear_combination (1 - u ^ (n - l)) * hz + hrefl
  rcases mul_eq_zero.mp key with h | h
  · linear_combination h
  · exact absurd h hw

private lemma prod_one_sub_pow (hu : IsPrimitiveRoot u n) (hn : 0 < n) :
    ∏ k ∈ Ico 1 n, (1 - u ^ k) = (n : K) := by
  classical

  have hstep1 : ∏ k ∈ range n, (X - C (u ^ k)) = X ^ n - 1 := by
    set d : K[X] := (X ^ n - 1) - ∏ k ∈ range n, (X - C (u ^ k)) with hdd
    have hmon2 : (∏ k ∈ range n, (X - C (u ^ k)) : K[X]).Monic :=
      monic_prod_of_monic _ _ fun k _ => monic_X_sub_C _
    have hdeg2 : (∏ k ∈ range n, (X - C (u ^ k)) : K[X]).natDegree = n := by
      rw [natDegree_prod _ _ fun k _ => X_sub_C_ne_zero _]
      simp only [natDegree_X_sub_C]
      simp
    by_cases hd0 : d = 0
    · have := sub_eq_zero.mp hd0
      exact this.symm
    · exfalso
      have hdeg1 : (X ^ n - 1 : K[X]).natDegree = n := by
        rw [natDegree_sub_eq_left_of_natDegree_lt] <;>
          simp [hn]
      have hdegle : d.natDegree ≤ n := by
        refine le_trans (natDegree_sub_le _ _) ?_
        rw [hdeg1, hdeg2, max_self]
      have hcn : d.coeff n = 0 := by
        have h1 : (X ^ n - 1 : K[X]).coeff n = 1 := by
          simp [coeff_X_pow, coeff_one, hn.ne']
        have h2 : (∏ k ∈ range n, (X - C (u ^ k)) : K[X]).coeff n = 1 := by
          have h := hmon2.leadingCoeff
          rwa [leadingCoeff, hdeg2] at h
        rw [hdd, coeff_sub, h1, h2, sub_self]
      have hdeglt : d.natDegree < n := by
        rcases lt_or_eq_of_le hdegle with h | h
        · exact h
        · exfalso
          apply hd0
          rw [← leadingCoeff_eq_zero, leadingCoeff, h]
          exact hcn
      have hroot : ∀ j ∈ range n, IsRoot d (u ^ j) := by
        intro j hj
        simp only [IsRoot, hdd, eval_sub, eval_pow, eval_X, eval_one, eval_prod, eval_sub,
          eval_C]
        have h1 : (u ^ j) ^ n = 1 := by
          rw [← pow_mul, mul_comm, pow_mul, hu.pow_eq_one, one_pow]
        have h2 : ∏ k ∈ range n, (u ^ j - u ^ k) = 0 :=
          Finset.prod_eq_zero hj (by ring)
        rw [h1, h2]
        ring
      have hsub : (range n).image (u ^ ·) ⊆ d.roots.toFinset := by
        intro x hx
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
        rw [Multiset.mem_toFinset, mem_roots hd0]
        exact hroot j hj
      have hinj : Set.InjOn (u ^ ·) ↑(range n) := hu.injOn_pow
      have hcard1 : ((range n).image (u ^ ·)).card = n := by
        rw [Finset.card_image_of_injOn hinj, card_range]
      have : n ≤ d.natDegree :=
        le_trans (le_trans (le_trans hcard1.ge (Finset.card_le_card hsub))
          (Multiset.toFinset_card_le _)) (card_roots' d)
      omega

  have hsplit : (X - 1 : K[X]) * ∏ k ∈ Ico 1 n, (X - C (u ^ k))
      = ∏ k ∈ range n, (X - C (u ^ k)) := by
    rw [range_eq_Ico, Finset.prod_eq_prod_Ico_succ_bot hn]
    simp
  have hgeom : (X - 1 : K[X]) * ∑ i ∈ range n, X ^ i = X ^ n - 1 := by
    have h := geom_sum_mul (X : K[X]) n
    linear_combination h
  have hcancel : ∏ k ∈ Ico 1 n, (X - C (u ^ k)) = ∑ i ∈ range n, X ^ i := by
    have hX1 : (X - 1 : K[X]) ≠ 0 := by
      simpa using X_sub_C_ne_zero (1 : K)
    apply mul_left_cancel₀ hX1
    rw [hsplit, hstep1, hgeom]

  have := congrArg (eval 1) hcancel
  simpa [eval_prod, eval_geom_sum] using this

private lemma prod_tau_eq (hu : IsPrimitiveRoot u n) (hn : Odd n) :
    ∏ l ∈ Icc 1 (n / 2), tau u n l = (n : K) := by
  have hn0 : 0 < n := hn.pos
  have hm : n / 2 + 1 ≤ n := by
    obtain ⟨j, hj⟩ := hn; omega

  have h1 : ∏ l ∈ Icc 1 (n / 2), tau u n l
      = (∏ l ∈ Icc 1 (n / 2), (1 - u ^ l)) * ∏ l ∈ Icc 1 (n / 2), (1 - u ^ (n - l)) := by
    rw [← Finset.prod_mul_distrib]; rfl

  have h2 : ∏ l ∈ Icc 1 (n / 2), (1 - u ^ (n - l))
      = ∏ k ∈ Ico (n / 2 + 1) n, (1 - u ^ k) := by
    refine Finset.prod_nbij (fun l => n - l) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_Icc] at ha
      simp only [Finset.mem_Ico]
      obtain ⟨j, hj⟩ := hn
      omega
    · intro a ha b hb hab
      simp only [coe_Icc, Set.mem_Icc] at ha hb
      have hab' : n - a = n - b := hab
      omega
    · intro k hk
      simp only [coe_Ico, Set.mem_Ico] at hk
      refine ⟨n - k, ?_, ?_⟩
      · simp only [coe_Icc, Set.mem_Icc]
        obtain ⟨j, hj⟩ := hn
        omega
      · simp only
        omega
    · intro a _
      rfl

  have h3 : (∏ l ∈ Icc 1 (n / 2), (1 - u ^ l)) * ∏ k ∈ Ico (n / 2 + 1) n, (1 - u ^ k)
      = ∏ k ∈ Ico 1 n, (1 - u ^ k) := by
    have : Icc 1 (n / 2) = Ico 1 (n / 2 + 1) := by
      ext x; simp
    rw [this, Finset.prod_Ico_consecutive]
    · omega
    · exact hm
  rw [h1, h2, h3, prod_one_sub_pow hu hn0]

private lemma esym_top (hu : IsPrimitiveRoot u n) (hn : Odd n) :
    esym u n (n / 2) (n / 2) = (n : K) := by
  unfold esym
  have hc : (Icc 1 (n / 2)).card = n / 2 := by simp
  nth_rewrite 1 [← hc]
  rw [Finset.powersetCard_self, Finset.sum_singleton]
  exact prod_tau_eq hu hn

end Basic
p2m_reactivate "P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_c4_c6_discriminant_of_nodal.WeierstrassCurve"

section Star

variable {u : K} {n : ℕ}

private lemma eq_of_roots {p q : K[X]} {d : ℕ} (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d)
    (hc : p.coeff d = q.coeff d) (S : Finset K) (hS : d ≤ S.card)
    (hroots : ∀ x ∈ S, eval x p = 0 ∧ eval x q = 0) : p = q := by
  classical
  set D := p - q with hD
  by_cases hD0 : D = 0
  · exact sub_eq_zero.mp hD0
  · exfalso
    have hDle : D.natDegree ≤ d := le_trans (natDegree_sub_le _ _) (max_le hp hq)
    have hDc : D.coeff d = 0 := by rw [hD, coeff_sub, hc, sub_self]
    have hDlt : D.natDegree < d := by
      rcases lt_or_eq_of_le hDle with h | h
      · exact h
      · exfalso
        apply hD0
        rw [← leadingCoeff_eq_zero, leadingCoeff, h]
        exact hDc
    have hsub : S ⊆ D.roots.toFinset := by
      intro x hx
      rw [Multiset.mem_toFinset, mem_roots hD0]
      have h := hroots x hx
      simp [IsRoot, hD, h.1, h.2]
    have : S.card ≤ D.natDegree :=
      le_trans (le_trans (Finset.card_le_card hsub) (Multiset.toFinset_card_le _))
        (card_roots' D)
    omega

private lemma L_expand {n : ℕ} (hn : Odd n) : ((1 : K[X]) - X) ^ n + X ^ n
    = ∑ i ∈ range n, C ((-1 : K) ^ i * (n.choose i : K)) * X ^ i := by
  have h1 : ((1 : K[X]) - X) = -X + 1 := by ring
  rw [h1, add_pow]
  have h2 : ∀ i ∈ range (n + 1),
      (-X : K[X]) ^ i * 1 ^ (n - i) * (n.choose i : K[X])
        = C ((-1 : K) ^ i * (n.choose i : K)) * X ^ i := by
    intro i _
    rw [one_pow, mul_one, neg_pow]
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
    ring
  rw [Finset.sum_congr rfl h2, Finset.sum_range_succ]
  have h3 : C ((-1 : K) ^ n * (n.choose n : K)) * X ^ n = -(X ^ n) := by
    rw [Nat.choose_self, hn.neg_one_pow]
    simp
  rw [h3]
  ring

private lemma L_coeff {n : ℕ} (hn : Odd n) {c : ℕ} (hc : c < n) :
    (((1 : K[X]) - X) ^ n + X ^ n).coeff c = (-1 : K) ^ c * (n.choose c : K) := by
  classical
  rw [L_expand hn, finsetSum_coeff]
  have h4 : ∀ i ∈ range n,
      (C ((-1 : K) ^ i * (n.choose i : K)) * X ^ i).coeff c
        = if i = c then (-1 : K) ^ i * (n.choose i : K) else 0 := by
    intro i _
    rw [coeff_C_mul, coeff_X_pow]
    by_cases h : c = i
    · rw [if_pos h, if_pos h.symm, mul_one]
    · rw [if_neg h, if_neg fun hc' => h hc'.symm, mul_zero]
  rw [Finset.sum_congr rfl h4, Finset.sum_ite_eq' (range n) c,
    if_pos (Finset.mem_range.mpr hc)]

private lemma star (hu : IsPrimitiveRoot u n) (hn : Odd n) :
    ((1 : K[X]) - X) ^ n + X ^ n
      = ∏ l ∈ Icc 1 (n / 2), (1 + C (tau u n l) * (X ^ 2 - X)) := by
  classical
  have hn0 : 0 < n := hn.pos
  obtain ⟨mj, hmj⟩ := id hn
  have hm2 : n / 2 * 2 = n - 1 := by omega

  have hquad : ∀ l ∈ Icc 1 (n / 2), (1 + C (tau u n l) * (X ^ 2 - X) : K[X])
      = C (tau u n l) * X ^ 2 + C (-(tau u n l)) * X + C 1 := by
    intro l _
    rw [map_neg, map_one]
    ring
  have hfac_ne : ∀ l ∈ Icc 1 (n / 2), tau u n l ≠ 0 := fun l hl =>
    tau_ne_zero hu ⟨mj, hmj⟩ (Finset.mem_Icc.mp hl).1 (Finset.mem_Icc.mp hl).2

  have hLdeg : (((1 : K[X]) - X) ^ n + X ^ n).natDegree ≤ n - 1 := by
    rw [L_expand hn]
    refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    refine le_trans (natDegree_C_mul_le _ _) ?_
    rw [natDegree_X_pow]
    exact Nat.le_sub_one_of_lt (Finset.mem_range.mp hi)
  have hLcoeff : (((1 : K[X]) - X) ^ n + X ^ n).coeff (n - 1) = (n : K) := by
    rw [L_coeff hn (by omega)]
    have h6 : (-1 : K) ^ (n - 1) = 1 := by
      have : Even (n - 1) := ⟨mj, by omega⟩
      exact this.neg_one_pow
    have h7 : n.choose (n - 1) = n := by
      rw [Nat.choose_symm (by omega), Nat.choose_one_right]
    rw [h6, h7, one_mul]

  have hPne : ∀ l ∈ Icc 1 (n / 2),
      (C (tau u n l) * X ^ 2 + C (-(tau u n l)) * X + C 1 : K[X]) ≠ 0 := by
    intro l hl h0
    have hd : (C (tau u n l) * X ^ 2 + C (-(tau u n l)) * X + C 1 : K[X]).natDegree = 2 :=
      natDegree_quadratic (hfac_ne l hl)
    rw [h0] at hd
    simp at hd
  have hPdeg :
      (∏ l ∈ Icc 1 (n / 2), (1 + C (tau u n l) * (X ^ 2 - X)) : K[X]).natDegree
        = n - 1 := by
    rw [Finset.prod_congr rfl hquad, natDegree_prod _ _ hPne]
    have h8 : ∀ l ∈ Icc 1 (n / 2),
        (C (tau u n l) * X ^ 2 + C (-(tau u n l)) * X + C 1 : K[X]).natDegree = 2 :=
      fun l hl => natDegree_quadratic (hfac_ne l hl)
    rw [Finset.sum_congr rfl h8, Finset.sum_const, Nat.card_Icc]
    simpa using hm2
  have hPcoeff :
      (∏ l ∈ Icc 1 (n / 2), (1 + C (tau u n l) * (X ^ 2 - X)) : K[X]).coeff (n - 1)
        = (n : K) := by
    have h9 :
        (∏ l ∈ Icc 1 (n / 2), (1 + C (tau u n l) * (X ^ 2 - X)) : K[X]).leadingCoeff
          = (n : K) := by
      rw [Finset.prod_congr rfl hquad, leadingCoeff_prod]
      have h10 : ∀ l ∈ Icc 1 (n / 2),
          (C (tau u n l) * X ^ 2 + C (-(tau u n l)) * X + C 1 : K[X]).leadingCoeff
            = tau u n l := fun l hl => leadingCoeff_quadratic (hfac_ne l hl)
      rw [Finset.prod_congr rfl h10]
      exact prod_tau_eq hu ⟨mj, hmj⟩
    rw [← h9, leadingCoeff, hPdeg]

  have hLeval : ∀ k, 1 ≤ k → k < n →
      eval ((1 - u ^ k)⁻¹) (((1 : K[X]) - X) ^ n + X ^ n) = 0 := by
    intro k hk1 hk2
    have hw := one_sub_pow_ne_zero hu hk1 hk2
    have hkn : (u ^ k) ^ n = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hu.pow_eq_one, one_pow]
    have h1 : (1 : K) - (1 - u ^ k)⁻¹ = -u ^ k * (1 - u ^ k)⁻¹ := by
      field_simp
      ring
    rw [eval_add, eval_pow, eval_pow, eval_sub, eval_one, eval_X, h1, mul_pow,
      hn.neg_pow, hkn]
    ring
  have hPeval : ∀ k, 1 ≤ k → k < n →
      eval ((1 - u ^ k)⁻¹)
        (∏ l ∈ Icc 1 (n / 2), (1 + C (tau u n l) * (X ^ 2 - X))) = 0 := by
    intro k hk1 hk2
    have hw := one_sub_pow_ne_zero hu hk1 hk2
    have hval : ∀ l, (l = k ∨ l = n - k) →
        eval ((1 - u ^ k)⁻¹) (1 + C (tau u n l) * (X ^ 2 - X)) = 0 := by
      intro l hlk
      have hτ : tau u n l * u ^ k = -((1 - u ^ k) * (1 - u ^ k)) := by
        rcases hlk with rfl | rfl
        · have hr := w_reflect hu hk2
          unfold tau
          linear_combination (1 - u ^ l) * hr
        · have hr := w_reflect hu hk2
          unfold tau
          rw [Nat.sub_sub_self hk2.le]
          linear_combination (1 - u ^ k) * hr
      rw [eval_add, eval_one, eval_mul, eval_C, eval_sub, eval_pow, eval_X]
      field_simp
      linear_combination hτ
    rw [eval_prod]
    by_cases hkm : k ≤ n / 2
    · exact Finset.prod_eq_zero (Finset.mem_Icc.mpr ⟨hk1, hkm⟩) (hval k (Or.inl rfl))
    · refine Finset.prod_eq_zero (i := n - k) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        (hval (n - k) (Or.inr rfl))

  set S : Finset K := (Ico 1 n).image (fun k => (1 - u ^ k)⁻¹) with hS
  have hScard : S.card = n - 1 := by
    rw [hS, Finset.card_image_of_injOn, Nat.card_Ico]
    intro a ha b hb hab
    simp only [coe_Ico, Set.mem_Ico] at ha hb
    have h1 : (1 : K) - u ^ a = 1 - u ^ b := inv_injective hab
    have h2 : u ^ a = u ^ b := by linear_combination -h1
    exact hu.injOn_pow (Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)))
      (Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega))) h2
  refine eq_of_roots hLdeg (le_of_eq hPdeg) (by rw [hLcoeff, hPcoeff]) S
    (by rw [hScard]) ?_
  intro x hx
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
  rw [Finset.mem_Ico] at hk
  exact ⟨hLeval k hk.1 hk.2, hPeval k hk.1 hk.2⟩

private lemma star_expand (u : K) (n : ℕ) :
    ∏ l ∈ Icc 1 (n / 2), (1 + C (tau u n l) * (X ^ 2 - X))
      = ∑ j ∈ range (n / 2 + 1), C (esym u n (n / 2) j) * (X ^ 2 - X) ^ j := by
  classical
  have h1 : ∀ l ∈ Icc 1 (n / 2),
      (1 + C (tau u n l) * (X ^ 2 - X) : K[X])
        = C (tau u n l) * (X ^ 2 - X) + 1 := fun l _ => by ring
  rw [Finset.prod_congr rfl h1, Finset.prod_add]
  have hc : #(Icc 1 (n / 2)) = n / 2 := by simp
  rw [Finset.sum_powerset, hc]
  refine Finset.sum_congr rfl fun j hj => ?_
  unfold esym
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hcard : #t = j := (Finset.mem_powersetCard.mp ht).2
  rw [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib, Finset.prod_const,
    hcard, map_prod]

end Star
p2m_reactivate "P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_c4_c6_discriminant_of_nodal.WeierstrassCurve"

section Extraction

variable {u : K} {n : ℕ}

private lemma esym_zero (u : K) (n m : ℕ) : esym u n m 0 = 1 := by
  unfold esym
  rw [Finset.powersetCard_zero, Finset.sum_singleton, Finset.prod_empty]

private lemma sub_one_pow_coeff (j i : ℕ) :
    ((X - 1 : K[X]) ^ j).coeff i
      = if i ≤ j then ((-1 : K) ^ (j - i) * ((j.choose i : ℕ) : K)) else 0 := by
  classical
  have hexp : (X - 1 : K[X]) ^ j
      = ∑ k ∈ range (j + 1), C ((-1 : K) ^ (j - k) * (j.choose k : K)) * X ^ k := by
    have h1 : (X - 1 : K[X]) = X + C (-1 : K) := by
      rw [map_neg, map_one]
      ring
    rw [h1, add_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
    ring
  rw [hexp, finsetSum_coeff]
  have h4 : ∀ k ∈ range (j + 1),
      (C ((-1 : K) ^ (j - k) * (j.choose k : K)) * X ^ k).coeff i
        = if k = i then (-1 : K) ^ (j - k) * (j.choose k : K) else 0 := by
    intro k _
    rw [coeff_C_mul, coeff_X_pow]
    by_cases h : i = k
    · rw [if_pos h, if_pos h.symm, mul_one]
    · rw [if_neg h, if_neg fun hc => h hc.symm, mul_zero]
  rw [Finset.sum_congr rfl h4, Finset.sum_ite_eq' (range (j + 1)) i]
  simp only [Finset.mem_range, Nat.lt_succ_iff]

private lemma coeff_XX (j c : ℕ) :
    ((X ^ 2 - X : K[X]) ^ j).coeff c
      = if j ≤ c ∧ c ≤ 2 * j
          then ((-1 : K) ^ (j - (c - j)) * ((j.choose (c - j) : ℕ) : K))
          else 0 := by
  rw [show (X ^ 2 - X : K[X]) = (X - 1) * X from by ring, mul_pow, coeff_mul_X_pow',
    sub_one_pow_coeff]
  by_cases h1 : j ≤ c
  · by_cases h2 : c - j ≤ j
    · rw [if_pos h1, if_pos h2, if_pos ⟨h1, by omega⟩]
    · rw [if_pos h1, if_neg h2, if_neg (by rintro ⟨-, hh⟩; omega)]
  · rw [if_neg h1, if_neg (by rintro ⟨hh, -⟩; omega)]

private lemma coeff_window (hu : IsPrimitiveRoot u n) (hn : Odd n) {r : ℕ}
    (hr : 1 ≤ r) (hm : r ≤ n / 2) :
    ∑ j ∈ range (n / 2 + 1), esym u n (n / 2) j *
        (if j ≤ 2 * (n / 2 - r) ∧ 2 * (n / 2 - r) ≤ 2 * j
          then ((-1 : K) ^ (j - (2 * (n / 2 - r) - j)) *
            ((j.choose (2 * (n / 2 - r) - j) : ℕ) : K))
          else 0)
      = ((n.choose (2 * r + 1) : ℕ) : K) := by
  classical
  obtain ⟨mj, hmj⟩ := id hn
  have hM := (star hu hn).trans (star_expand u n)
  have h0 := congrArg (fun p => p.coeff (2 * (n / 2 - r))) hM
  rw [L_coeff hn (by omega), finsetSum_coeff] at h0
  have hsummand : ∀ j ∈ range (n / 2 + 1),
      (C (esym u n (n / 2) j) * (X ^ 2 - X) ^ j).coeff (2 * (n / 2 - r))
        = esym u n (n / 2) j *
            (if j ≤ 2 * (n / 2 - r) ∧ 2 * (n / 2 - r) ≤ 2 * j
              then ((-1 : K) ^ (j - (2 * (n / 2 - r) - j)) *
                ((j.choose (2 * (n / 2 - r) - j) : ℕ) : K))
              else 0) := by
    intro j _
    rw [coeff_C_mul, coeff_XX]
  rw [Finset.sum_congr rfl hsummand] at h0
  rw [← h0]
  have hceven : (-1 : K) ^ (2 * (n / 2 - r)) = 1 := by
    have he : Even (2 * (n / 2 - r)) := ⟨n / 2 - r, two_mul _⟩
    exact he.neg_one_pow
  have hcsymm : n.choose (2 * (n / 2 - r)) = n.choose (2 * r + 1) := by
    have h := (Nat.choose_symm (by omega : 2 * (n / 2 - r) ≤ n)).symm
    rw [h, show n - 2 * (n / 2 - r) = 2 * r + 1 by omega]
  rw [hceven, hcsymm, one_mul]

private lemma esym_row1 (hu : IsPrimitiveRoot u n) (hn : Odd n) (hm : 1 ≤ n / 2) :
    esym u n (n / 2) (n / 2 - 1) = ((E1 n : ℤ) : K) := by
  classical
  obtain ⟨mj, hmj⟩ := id hn
  have hw := coeff_window hu hn le_rfl hm
  rw [show n / 2 + 1 = (n / 2 - 1) + 1 + 1 by omega, Finset.sum_range_succ,
    Finset.sum_range_succ, show n / 2 - 1 + 1 = n / 2 by omega] at hw
  have hlow : ∑ j ∈ range (n / 2 - 1), esym u n (n / 2) j *
      (if j ≤ 2 * (n / 2 - 1) ∧ 2 * (n / 2 - 1) ≤ 2 * j
        then ((-1 : K) ^ (j - (2 * (n / 2 - 1) - j)) *
          ((j.choose (2 * (n / 2 - 1) - j) : ℕ) : K))
        else 0) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    have hjlt := Finset.mem_range.mp hj
    have hneg : ¬(j ≤ 2 * (n / 2 - 1) ∧ 2 * (n / 2 - 1) ≤ 2 * j) := by
      rintro ⟨-, h2⟩
      omega
    rw [if_neg hneg, mul_zero]
  rw [hlow, zero_add] at hw
  have ht1 : esym u n (n / 2) (n / 2 - 1) *
      (if n / 2 - 1 ≤ 2 * (n / 2 - 1) ∧ 2 * (n / 2 - 1) ≤ 2 * (n / 2 - 1)
        then ((-1 : K) ^ ((n / 2 - 1) - (2 * (n / 2 - 1) - (n / 2 - 1))) *
          (((n / 2 - 1).choose (2 * (n / 2 - 1) - (n / 2 - 1)) : ℕ) : K))
        else 0) = esym u n (n / 2) (n / 2 - 1) := by
    rw [if_pos ⟨by omega, le_rfl⟩, show 2 * (n / 2 - 1) - (n / 2 - 1) = n / 2 - 1 by omega,
      show (n / 2 - 1) - (n / 2 - 1) = 0 by omega, pow_zero, Nat.choose_self, Nat.cast_one,
      one_mul, mul_one]
  have ht2 : esym u n (n / 2) (n / 2) *
      (if n / 2 ≤ 2 * (n / 2 - 1) ∧ 2 * (n / 2 - 1) ≤ 2 * (n / 2)
        then ((-1 : K) ^ ((n / 2) - (2 * (n / 2 - 1) - (n / 2))) *
          (((n / 2).choose (2 * (n / 2 - 1) - (n / 2)) : ℕ) : K))
        else 0) = (((n / 2).choose 2 : ℕ) : K) * (n : K) := by
    rw [esym_top hu hn]
    by_cases h2 : 2 ≤ n / 2
    · rw [if_pos ⟨by omega, by omega⟩, show 2 * (n / 2 - 1) - n / 2 = n / 2 - 2 by omega,
        show n / 2 - (n / 2 - 2) = 2 by omega, Nat.choose_symm h2, neg_one_sq, one_mul]
      ring
    · rw [if_neg (by rintro ⟨h1, -⟩; omega),
        show (n / 2).choose 2 = 0 from Nat.choose_eq_zero_of_lt (by omega)]
      simp
  rw [ht1, ht2, show 2 * 1 + 1 = 3 from rfl] at hw
  have hE : ((E1 n : ℤ) : K) = ((n.choose 3 : ℕ) : K) - (n : K) * (((n / 2).choose 2 : ℕ) : K) := by
    unfold E1
    push_cast
    ring
  rw [hE]
  linear_combination hw

private lemma esym_row2 (hu : IsPrimitiveRoot u n) (hn : Odd n) (hm : 2 ≤ n / 2) :
    esym u n (n / 2) (n / 2 - 2) = ((E2 n : ℤ) : K) := by
  classical
  obtain ⟨mj, hmj⟩ := id hn
  have hw := coeff_window hu hn (by omega : 1 ≤ 2) hm
  rw [show n / 2 + 1 = (n / 2 - 2) + 1 + 1 + 1 by omega, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, show n / 2 - 2 + 1 = n / 2 - 1 by omega,
    show n / 2 - 2 + 2 = n / 2 by omega] at hw
  have hlow : ∑ j ∈ range (n / 2 - 2), esym u n (n / 2) j *
      (if j ≤ 2 * (n / 2 - 2) ∧ 2 * (n / 2 - 2) ≤ 2 * j
        then ((-1 : K) ^ (j - (2 * (n / 2 - 2) - j)) *
          ((j.choose (2 * (n / 2 - 2) - j) : ℕ) : K))
        else 0) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    have hjlt := Finset.mem_range.mp hj
    have hneg : ¬(j ≤ 2 * (n / 2 - 2) ∧ 2 * (n / 2 - 2) ≤ 2 * j) := by
      rintro ⟨-, h2⟩
      omega
    rw [if_neg hneg, mul_zero]
  rw [hlow, zero_add] at hw
  have ht1 : esym u n (n / 2) (n / 2 - 2) *
      (if n / 2 - 2 ≤ 2 * (n / 2 - 2) ∧ 2 * (n / 2 - 2) ≤ 2 * (n / 2 - 2)
        then ((-1 : K) ^ ((n / 2 - 2) - (2 * (n / 2 - 2) - (n / 2 - 2))) *
          (((n / 2 - 2).choose (2 * (n / 2 - 2) - (n / 2 - 2)) : ℕ) : K))
        else 0) = esym u n (n / 2) (n / 2 - 2) := by
    rw [if_pos ⟨by omega, le_rfl⟩, show 2 * (n / 2 - 2) - (n / 2 - 2) = n / 2 - 2 by omega,
      show (n / 2 - 2) - (n / 2 - 2) = 0 by omega, pow_zero, Nat.choose_self, Nat.cast_one,
      one_mul, mul_one]
  have ht2 : esym u n (n / 2) (n / 2 - 1) *
      (if n / 2 - 1 ≤ 2 * (n / 2 - 2) ∧ 2 * (n / 2 - 2) ≤ 2 * (n / 2 - 1)
        then ((-1 : K) ^ ((n / 2 - 1) - (2 * (n / 2 - 2) - (n / 2 - 1))) *
          (((n / 2 - 1).choose (2 * (n / 2 - 2) - (n / 2 - 1)) : ℕ) : K))
        else 0) = (((n / 2 - 1).choose 2 : ℕ) : K) * esym u n (n / 2) (n / 2 - 1) := by
    by_cases h3 : 3 ≤ n / 2
    · rw [if_pos ⟨by omega, by omega⟩,
        show 2 * (n / 2 - 2) - (n / 2 - 1) = n / 2 - 1 - 2 by omega,
        show (n / 2 - 1) - (n / 2 - 1 - 2) = 2 by omega,
        Nat.choose_symm (by omega : 2 ≤ n / 2 - 1), neg_one_sq, one_mul]
      ring
    · rw [if_neg (by rintro ⟨h1, -⟩; omega),
        show (n / 2 - 1).choose 2 = 0 from Nat.choose_eq_zero_of_lt (by omega)]
      simp
  have ht3 : esym u n (n / 2) (n / 2) *
      (if n / 2 ≤ 2 * (n / 2 - 2) ∧ 2 * (n / 2 - 2) ≤ 2 * (n / 2)
        then ((-1 : K) ^ ((n / 2) - (2 * (n / 2 - 2) - (n / 2))) *
          (((n / 2).choose (2 * (n / 2 - 2) - (n / 2)) : ℕ) : K))
        else 0) = (((n / 2).choose 4 : ℕ) : K) * (n : K) := by
    rw [esym_top hu hn]
    by_cases h4 : 4 ≤ n / 2
    · rw [if_pos ⟨by omega, by omega⟩,
        show 2 * (n / 2 - 2) - n / 2 = n / 2 - 4 by omega,
        show n / 2 - (n / 2 - 4) = 4 by omega,
        Nat.choose_symm (by omega : 4 ≤ n / 2),
        show ((-1 : K) ^ 4 : K) = 1 by norm_num, one_mul]
      ring
    · rw [if_neg (by rintro ⟨h1, -⟩; omega),
        show (n / 2).choose 4 = 0 from Nat.choose_eq_zero_of_lt (by omega)]
      simp
  rw [ht1, ht2, ht3, show 2 * 2 + 1 = 5 from rfl, esym_row1 hu hn (by omega)] at hw
  have hE : ((E2 n : ℤ) : K) = ((n.choose 5 : ℕ) : K)
      - (((n / 2 - 1).choose 2 : ℕ) : K) * ((E1 n : ℤ) : K)
      - (((n / 2).choose 4 : ℕ) : K) * (n : K) := by
    unfold E2
    push_cast
    ring
  rw [hE]
  linear_combination hw

private lemma esym_row3 (hu : IsPrimitiveRoot u n) (hn : Odd n) (hm : 3 ≤ n / 2) :
    esym u n (n / 2) (n / 2 - 3) = ((E3 n : ℤ) : K) := by
  classical
  obtain ⟨mj, hmj⟩ := id hn
  have hw := coeff_window hu hn (by omega : 1 ≤ 3) hm
  rw [show n / 2 + 1 = (n / 2 - 3) + 1 + 1 + 1 + 1 by omega, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    show n / 2 - 3 + 1 = n / 2 - 2 by omega, show n / 2 - 3 + 2 = n / 2 - 1 by omega,
    show n / 2 - 3 + 3 = n / 2 by omega] at hw
  have hlow : ∑ j ∈ range (n / 2 - 3), esym u n (n / 2) j *
      (if j ≤ 2 * (n / 2 - 3) ∧ 2 * (n / 2 - 3) ≤ 2 * j
        then ((-1 : K) ^ (j - (2 * (n / 2 - 3) - j)) *
          ((j.choose (2 * (n / 2 - 3) - j) : ℕ) : K))
        else 0) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    have hjlt := Finset.mem_range.mp hj
    have hneg : ¬(j ≤ 2 * (n / 2 - 3) ∧ 2 * (n / 2 - 3) ≤ 2 * j) := by
      rintro ⟨-, h2⟩
      omega
    rw [if_neg hneg, mul_zero]
  rw [hlow, zero_add] at hw
  have ht1 : esym u n (n / 2) (n / 2 - 3) *
      (if n / 2 - 3 ≤ 2 * (n / 2 - 3) ∧ 2 * (n / 2 - 3) ≤ 2 * (n / 2 - 3)
        then ((-1 : K) ^ ((n / 2 - 3) - (2 * (n / 2 - 3) - (n / 2 - 3))) *
          (((n / 2 - 3).choose (2 * (n / 2 - 3) - (n / 2 - 3)) : ℕ) : K))
        else 0) = esym u n (n / 2) (n / 2 - 3) := by
    rw [if_pos ⟨by omega, le_rfl⟩, show 2 * (n / 2 - 3) - (n / 2 - 3) = n / 2 - 3 by omega,
      show (n / 2 - 3) - (n / 2 - 3) = 0 by omega, pow_zero, Nat.choose_self, Nat.cast_one,
      one_mul, mul_one]
  have ht2 : esym u n (n / 2) (n / 2 - 2) *
      (if n / 2 - 2 ≤ 2 * (n / 2 - 3) ∧ 2 * (n / 2 - 3) ≤ 2 * (n / 2 - 2)
        then ((-1 : K) ^ ((n / 2 - 2) - (2 * (n / 2 - 3) - (n / 2 - 2))) *
          (((n / 2 - 2).choose (2 * (n / 2 - 3) - (n / 2 - 2)) : ℕ) : K))
        else 0) = (((n / 2 - 2).choose 2 : ℕ) : K) * esym u n (n / 2) (n / 2 - 2) := by
    by_cases h4 : 4 ≤ n / 2
    · rw [if_pos ⟨by omega, by omega⟩,
        show 2 * (n / 2 - 3) - (n / 2 - 2) = n / 2 - 2 - 2 by omega,
        show (n / 2 - 2) - (n / 2 - 2 - 2) = 2 by omega,
        Nat.choose_symm (by omega : 2 ≤ n / 2 - 2), neg_one_sq, one_mul]
      ring
    · rw [if_neg (by rintro ⟨h1, -⟩; omega),
        show (n / 2 - 2).choose 2 = 0 from Nat.choose_eq_zero_of_lt (by omega)]
      simp
  have ht3 : esym u n (n / 2) (n / 2 - 1) *
      (if n / 2 - 1 ≤ 2 * (n / 2 - 3) ∧ 2 * (n / 2 - 3) ≤ 2 * (n / 2 - 1)
        then ((-1 : K) ^ ((n / 2 - 1) - (2 * (n / 2 - 3) - (n / 2 - 1))) *
          (((n / 2 - 1).choose (2 * (n / 2 - 3) - (n / 2 - 1)) : ℕ) : K))
        else 0) = (((n / 2 - 1).choose 4 : ℕ) : K) * esym u n (n / 2) (n / 2 - 1) := by
    by_cases h5 : 5 ≤ n / 2
    · rw [if_pos ⟨by omega, by omega⟩,
        show 2 * (n / 2 - 3) - (n / 2 - 1) = n / 2 - 1 - 4 by omega,
        show (n / 2 - 1) - (n / 2 - 1 - 4) = 4 by omega,
        Nat.choose_symm (by omega : 4 ≤ n / 2 - 1),
        show ((-1 : K) ^ 4 : K) = 1 by norm_num, one_mul]
      ring
    · rw [if_neg (by rintro ⟨h1, -⟩; omega),
        show (n / 2 - 1).choose 4 = 0 from Nat.choose_eq_zero_of_lt (by omega)]
      simp
  have ht4 : esym u n (n / 2) (n / 2) *
      (if n / 2 ≤ 2 * (n / 2 - 3) ∧ 2 * (n / 2 - 3) ≤ 2 * (n / 2)
        then ((-1 : K) ^ ((n / 2) - (2 * (n / 2 - 3) - (n / 2))) *
          (((n / 2).choose (2 * (n / 2 - 3) - (n / 2)) : ℕ) : K))
        else 0) = (((n / 2).choose 6 : ℕ) : K) * (n : K) := by
    rw [esym_top hu hn]
    by_cases h6 : 6 ≤ n / 2
    · rw [if_pos ⟨by omega, by omega⟩,
        show 2 * (n / 2 - 3) - n / 2 = n / 2 - 6 by omega,
        show n / 2 - (n / 2 - 6) = 6 by omega,
        Nat.choose_symm (by omega : 6 ≤ n / 2),
        show ((-1 : K) ^ 6 : K) = 1 by norm_num, one_mul]
      ring
    · rw [if_neg (by rintro ⟨h1, -⟩; omega),
        show (n / 2).choose 6 = 0 from Nat.choose_eq_zero_of_lt (by omega)]
      simp
  rw [ht1, ht2, ht3, ht4, show 2 * 3 + 1 = 7 from rfl, esym_row1 hu hn (by omega),
    esym_row2 hu hn (by omega)] at hw
  have hE : ((E3 n : ℤ) : K) = ((n.choose 7 : ℕ) : K)
      - (((n / 2 - 2).choose 2 : ℕ) : K) * ((E2 n : ℤ) : K)
      - (((n / 2 - 1).choose 4 : ℕ) : K) * ((E1 n : ℤ) : K)
      - (((n / 2).choose 6 : ℕ) : K) * (n : K) := by
    unfold E3
    push_cast
    ring
  rw [hE]
  linear_combination hw

end Extraction
p2m_reactivate "P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_c4_c6_discriminant_of_nodal.WeierstrassCurve"

section Zsums

variable {u : K} {n : ℕ}

private def fsym (f : ℕ → K) (s : Finset ℕ) (j : ℕ) : K :=
  ∑ t ∈ powersetCard j s, ∏ l ∈ t, f l

private lemma fsym_zero (f : ℕ → K) (s : Finset ℕ) : fsym f s 0 = 1 := by
  unfold fsym
  rw [Finset.powersetCard_zero, Finset.sum_singleton, Finset.prod_empty]

private lemma fsym_eq_zero_of_card_lt {f : ℕ → K} {s : Finset ℕ} {j : ℕ}
    (h : s.card < j) : fsym f s j = 0 := by
  unfold fsym
  rw [Finset.powersetCard_eq_empty.mpr h, Finset.sum_empty]

private lemma fsym_insert (f : ℕ → K) {a : ℕ} {s : Finset ℕ} (ha : a ∉ s) (j : ℕ) :
    fsym f (insert a s) (j + 1) = fsym f s (j + 1) + f a * fsym f s j := by
  classical
  unfold fsym
  rw [Finset.powersetCard_succ_insert ha]
  have hdisj : Disjoint (powersetCard (j + 1) s) ((powersetCard j s).image (insert a)) := by
    rw [Finset.disjoint_right]
    intro t htim hts
    obtain ⟨t', _, rfl⟩ := Finset.mem_image.mp htim
    exact ha ((Finset.mem_powersetCard.mp hts).1 (Finset.mem_insert_self a t'))
  rw [Finset.sum_union hdisj]
  congr 1
  have hinj : ∀ t₁ ∈ powersetCard j s, ∀ t₂ ∈ powersetCard j s,
      insert a t₁ = insert a t₂ → t₁ = t₂ := by
    intro t₁ h₁ t₂ h₂ heq
    have ha₁ : a ∉ t₁ := fun hc => ha ((Finset.mem_powersetCard.mp h₁).1 hc)
    have ha₂ : a ∉ t₂ := fun hc => ha ((Finset.mem_powersetCard.mp h₂).1 hc)
    have := congrArg (Finset.erase · a) heq
    simpa [Finset.erase_insert ha₁, Finset.erase_insert ha₂] using this
  rw [Finset.sum_image hinj]
  have hins : ∀ t ∈ powersetCard j s, ∏ l ∈ insert a t, f l = f a * ∏ l ∈ t, f l := by
    intro t ht
    exact Finset.prod_insert fun hc => ha ((Finset.mem_powersetCard.mp ht).1 hc)
  rw [Finset.sum_congr rfl hins, ← Finset.mul_sum]

private lemma psum_ident (f : ℕ → K) (s : Finset ℕ) :
    (∑ l ∈ s, f l) = fsym f s 1
    ∧ (∑ l ∈ s, f l ^ 2) = fsym f s 1 ^ 2 - 2 * fsym f s 2
    ∧ (∑ l ∈ s, f l ^ 3)
        = fsym f s 1 ^ 3 - 3 * fsym f s 1 * fsym f s 2 + 3 * fsym f s 3 := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [fsym_eq_zero_of_card_lt (show (∅ : Finset ℕ).card < 1 by simp),
        fsym_eq_zero_of_card_lt (show (∅ : Finset ℕ).card < 2 by simp),
        fsym_eq_zero_of_card_lt (show (∅ : Finset ℕ).card < 3 by simp)]
  | cons a s ha ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    rw [Finset.sum_cons, Finset.sum_cons, Finset.sum_cons, Finset.cons_eq_insert]
    have e1 : fsym f (insert a s) 1 = fsym f s 1 + f a * fsym f s 0 := fsym_insert f ha 0
    have e2 : fsym f (insert a s) 2 = fsym f s 2 + f a * fsym f s 1 := fsym_insert f ha 1
    have e3 : fsym f (insert a s) 3 = fsym f s 3 + f a * fsym f s 2 := fsym_insert f ha 2
    refine ⟨?_, ?_, ?_⟩
    · rw [e1, fsym_zero, ih1]
      ring
    · rw [e2, e1, fsym_zero, ih2]
      ring
    · rw [e3, e2, e1, fsym_zero, ih3]
      ring

private lemma bridge_core (hu : IsPrimitiveRoot u n) (hn : Odd n)
    (z : ℕ → K) (hz : ∀ k ∈ Icc 1 (n / 2), z k * (1 - u ^ k) ^ 2 = u ^ k)
    {j : ℕ} (hjm : j ≤ n / 2) :
    (n : K) * fsym z (Icc 1 (n / 2)) j = (-1 : K) ^ j * esym u n (n / 2) (n / 2 - j) := by
  classical
  have hpt : ∀ t ∈ powersetCard j (Icc 1 (n / 2)),
      (n : K) * ∏ l ∈ t, z l = (-1 : K) ^ j * ∏ l ∈ Icc 1 (n / 2) \ t, tau u n l := by
    intro t ht
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp ht
    have hsplit : (∏ l ∈ Icc 1 (n / 2) \ t, tau u n l) * ∏ l ∈ t, tau u n l = (n : K) := by
      rw [Finset.prod_sdiff hsub, prod_tau_eq hu hn]
    have hprodtz : (∏ l ∈ t, tau u n l) * ∏ l ∈ t, z l = (-1 : K) ^ j := by
      rw [← Finset.prod_mul_distrib,
        show ((-1 : K) ^ j) = ∏ _l ∈ t, (-1 : K) from by rw [Finset.prod_const, hcard]]
      refine Finset.prod_congr rfl fun l hl => ?_
      have hlmem := hsub hl
      obtain ⟨hl1, hl2⟩ := Finset.mem_Icc.mp hlmem
      exact tau_mul_z hu hn hl1 hl2 (hz l hlmem)
    calc (n : K) * ∏ l ∈ t, z l
        = ((∏ l ∈ Icc 1 (n / 2) \ t, tau u n l) * ∏ l ∈ t, tau u n l) * ∏ l ∈ t, z l := by
          rw [hsplit]
      _ = (∏ l ∈ Icc 1 (n / 2) \ t, tau u n l)
            * ((∏ l ∈ t, tau u n l) * ∏ l ∈ t, z l) := by ring
      _ = (-1 : K) ^ j * ∏ l ∈ Icc 1 (n / 2) \ t, tau u n l := by rw [hprodtz]; ring
  unfold fsym
  rw [Finset.mul_sum, Finset.sum_congr rfl hpt, ← Finset.mul_sum]
  congr 1
  unfold esym
  refine Finset.sum_nbij (fun t => Icc 1 (n / 2) \ t) ?_ ?_ ?_ ?_
  · intro t ht
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp ht
    refine Finset.mem_powersetCard.mpr ⟨Finset.sdiff_subset, ?_⟩
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hcard, Nat.card_Icc]
    omega
  · intro t₁ h₁ t₂ h₂ heq
    simp only [Finset.mem_coe] at h₁ h₂
    have hs₁ := (Finset.mem_powersetCard.mp h₁).1
    have hs₂ := (Finset.mem_powersetCard.mp h₂).1
    have := congrArg (Icc 1 (n / 2) \ ·) heq
    simpa [Finset.sdiff_sdiff_eq_self hs₁, Finset.sdiff_sdiff_eq_self hs₂] using this
  · intro t' ht'
    simp only [Finset.mem_coe] at ht'
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp ht'
    have hc2 : (Icc 1 (n / 2)).card = n / 2 := by rw [Nat.card_Icc]; omega
    refine ⟨Icc 1 (n / 2) \ t', Finset.mem_coe.mpr (Finset.mem_powersetCard.mpr
      ⟨Finset.sdiff_subset, ?_⟩), ?_⟩
    · rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hcard, hc2]
      omega
    · simp only
      rw [Finset.sdiff_sdiff_eq_self hsub]
  · intro t _
    rfl

private lemma bridge1 (hu : IsPrimitiveRoot u n) (hn : Odd n)
    (z : ℕ → K) (hz : ∀ k ∈ Icc 1 (n / 2), z k * (1 - u ^ k) ^ 2 = u ^ k) :
    (n : K) * fsym z (Icc 1 (n / 2)) 1 = -((E1 n : ℤ) : K) := by
  by_cases hjm : 1 ≤ n / 2
  · rw [bridge_core hu hn z hz hjm, esym_row1 hu hn hjm]
    ring
  · have hn1 : n = 1 := by
      obtain ⟨mj, hmj⟩ := id hn
      omega
    subst hn1
    have hcard : (Icc 1 (1 / 2)).card < 1 := by
      rw [Nat.card_Icc]
      omega
    rw [fsym_eq_zero_of_card_lt hcard, mul_zero, show E1 1 = 0 from by decide]
    simp

private lemma bridge2 (hu : IsPrimitiveRoot u n) (hn : Odd n)
    (z : ℕ → K) (hz : ∀ k ∈ Icc 1 (n / 2), z k * (1 - u ^ k) ^ 2 = u ^ k) :
    (n : K) * fsym z (Icc 1 (n / 2)) 2 = ((E2 n : ℤ) : K) := by
  by_cases hjm : 2 ≤ n / 2
  · rw [bridge_core hu hn z hz hjm, esym_row2 hu hn hjm]
    ring
  · have h13 : n = 1 ∨ n = 3 := by
      obtain ⟨mj, hmj⟩ := id hn
      omega
    have hcard : (Icc 1 (n / 2)).card < 2 := by rw [Nat.card_Icc]; omega
    rw [fsym_eq_zero_of_card_lt hcard, mul_zero]
    rcases h13 with rfl | rfl
    · rw [show E2 1 = 0 from by decide]
      simp
    · rw [show E2 3 = 0 from by decide]
      simp

private lemma bridge3 (hu : IsPrimitiveRoot u n) (hn : Odd n)
    (z : ℕ → K) (hz : ∀ k ∈ Icc 1 (n / 2), z k * (1 - u ^ k) ^ 2 = u ^ k) :
    (n : K) * fsym z (Icc 1 (n / 2)) 3 = -((E3 n : ℤ) : K) := by
  by_cases hjm : 3 ≤ n / 2
  · rw [bridge_core hu hn z hz hjm, esym_row3 hu hn hjm]
    ring
  · have h135 : n = 1 ∨ n = 3 ∨ n = 5 := by
      obtain ⟨mj, hmj⟩ := id hn
      omega
    have hcard : (Icc 1 (n / 2)).card < 3 := by rw [Nat.card_Icc]; omega
    rw [fsym_eq_zero_of_card_lt hcard, mul_zero]
    rcases h135 with rfl | rfl | rfl
    · rw [show E3 1 = 0 from by decide]
      simp
    · rw [show E3 3 = 0 from by decide]
      simp
    · rw [show E3 5 = 0 from by decide]
      simp

private lemma Zsum_eval (hu : IsPrimitiveRoot u n) (hn : Odd n)
    (z : ℕ → K) (hz : ∀ k ∈ Icc 1 (n / 2), z k * (1 - u ^ k) ^ 2 = u ^ k) :
    (n : K) * (∑ k ∈ Icc 1 (n / 2), z k) = -((E1 n : ℤ) : K)
    ∧ (n : K) ^ 2 * (∑ k ∈ Icc 1 (n / 2), (z k) ^ 2)
        = ((E1 n ^ 2 - 2 * n * E2 n : ℤ) : K)
    ∧ (n : K) ^ 3 * (∑ k ∈ Icc 1 (n / 2), (z k) ^ 3)
        = ((-(E1 n ^ 3) + 3 * n * E1 n * E2 n - 3 * (n : ℤ) ^ 2 * E3 n : ℤ) : K) := by
  obtain ⟨hp1, hp2, hp3⟩ := psum_ident z (Icc 1 (n / 2))
  have hb1 := bridge1 hu hn z hz
  have hb2 := bridge2 hu hn z hz
  have hb3 := bridge3 hu hn z hz
  refine ⟨?_, ?_, ?_⟩
  · rw [hp1]
    exact hb1
  · rw [hp2]
    push_cast
    linear_combination ((n : K) * fsym z (Icc 1 (n / 2)) 1 - ((E1 n : ℤ) : K)) * hb1
      + (-(2 : K) * (n : K)) * hb2
  · rw [hp3]
    push_cast
    linear_combination ((n : K) ^ 2 * fsym z (Icc 1 (n / 2)) 1 ^ 2
        - (n : K) * fsym z (Icc 1 (n / 2)) 1 * ((E1 n : ℤ) : K) + ((E1 n : ℤ) : K) ^ 2
        - 3 * (n : K) ^ 2 * fsym z (Icc 1 (n / 2)) 2) * hb1
      + (3 * (n : K) * ((E1 n : ℤ) : K)) * hb2
      + (3 * (n : K) ^ 2) * hb3

end Zsums
p2m_reactivate "P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_c4_c6_discriminant_of_nodal.WeierstrassCurve"

section Certificates

private lemma choose_mul_factorial_cast_q (n k : ℕ) :
    ((k.factorial : ℕ) : ℚ) * ((n.choose k : ℕ) : ℚ) = ∏ i ∈ range k, ((n : ℚ) - (i : ℚ)) := by
  by_cases h : k ≤ n
  · have h1 : k.factorial * n.choose k = n.descFactorial k :=
      (Nat.descFactorial_eq_factorial_mul_choose n k).symm
    have h2 : n.descFactorial k = ∏ i ∈ range k, (n - i) := Nat.descFactorial_eq_prod_range n k
    have h3 : (((∏ i ∈ range k, (n - i) : ℕ) : ℕ) : ℚ) = ∏ i ∈ range k, ((n : ℚ) - (i : ℚ)) := by
      rw [Nat.cast_prod]
      refine Finset.prod_congr rfl fun i hi => ?_
      have hin : i ≤ n := le_trans (Nat.le_of_lt_succ (Nat.lt_succ_of_lt (Finset.mem_range.mp hi)))
        (by omega)
      push_cast [Nat.cast_sub hin]
      ring
    rw [← h3, ← h2, ← h1]
    push_cast
    ring
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]
    symm
    refine Finset.prod_eq_zero (Finset.mem_range.mpr (by omega : n < k)) ?_
    simp

private lemma choose_q (n k : ℕ) :
    ((n.choose k : ℕ) : ℚ) = (∏ i ∈ range k, ((n : ℚ) - (i : ℚ))) / ((k.factorial : ℕ) : ℚ) := by
  rw [eq_div_iff (by exact_mod_cast k.factorial_ne_zero : ((k.factorial : ℕ) : ℚ) ≠ 0),
    mul_comm]
  exact choose_mul_factorial_cast_q n k

private lemma E1_q (m : ℕ) :
    ((E1 (2 * m + 1) : ℤ) : ℚ) = (2 * m + 1 : ℚ) * (m : ℚ) * ((m : ℚ) + 1) / 6 := by
  have hm2 : (2 * m + 1) / 2 = m := by omega
  unfold E1
  rw [hm2]
  push_cast
  rw [choose_q (2 * m + 1) 3, choose_q m 2]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  norm_num [Nat.factorial]
  field_simp
  ring

private lemma E2_q (m : ℕ) :
    ((E2 (2 * m + 1) : ℤ) : ℚ)
      = (2 * m + 1 : ℚ) * (m : ℚ) * ((m : ℚ) + 1) * ((m : ℚ) - 1) * ((m : ℚ) + 2) / 120 := by
  have hm2 : (2 * m + 1) / 2 = m := by omega
  by_cases hm : 1 ≤ m
  · unfold E2 E1
    rw [hm2]
    push_cast
    rw [choose_q (2 * m + 1) 5, choose_q (2 * m + 1) 3, choose_q m 2, choose_q m 4,
      choose_q (m - 1) 2]
    push_cast [Nat.cast_sub hm]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    norm_num [Nat.factorial]
    field_simp
    ring
  · have hm0 : m = 0 := by omega
    subst hm0
    rw [show E2 1 = 0 from by decide]
    norm_num

private lemma E3_q (m : ℕ) :
    ((E3 (2 * m + 1) : ℤ) : ℚ)
      = (2 * m + 1 : ℚ) * (m : ℚ) * ((m : ℚ) + 1) * ((m : ℚ) - 1) * ((m : ℚ) + 2)
          * ((m : ℚ) - 2) * ((m : ℚ) + 3) / 5040 := by
  have hm2 : (2 * m + 1) / 2 = m := by omega
  by_cases hm : 2 ≤ m
  · have hm1 : 1 ≤ m := by omega
    unfold E3 E2 E1
    rw [hm2]
    push_cast
    rw [choose_q (2 * m + 1) 7, choose_q (2 * m + 1) 5, choose_q (2 * m + 1) 3,
      choose_q m 2, choose_q m 4, choose_q m 6, choose_q (m - 1) 2, choose_q (m - 1) 4,
      choose_q (m - 2) 2]
    push_cast [Nat.cast_sub hm1, Nat.cast_sub hm]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    norm_num [Nat.factorial]
    field_simp
    ring
  · have h01 : m = 0 ∨ m = 1 := by omega
    rcases h01 with rfl | rfl
    · rw [show E3 1 = 0 from by decide]
      norm_num
    · rw [show E3 3 = 0 from by decide]
      norm_num

private lemma cert_T {n : ℕ} (hn : Odd n) :
    240 * (-(n : ℤ) * E1 n + 6 * E1 n ^ 2 - 12 * n * E2 n)
      = (n : ℤ) ^ 2 * ((n : ℤ) ^ 4 - 1) := by
  obtain ⟨m, rfl⟩ := hn
  qify
  rw [E1_q, E2_q]
  field_simp
  ring

private lemma cert_W {n : ℕ} (hn : Odd n) :
    504 * (-(n : ℤ) ^ 2 * E1 n + 6 * n * E1 n ^ 2 - 12 * (n : ℤ) ^ 2 * E2 n)
        + 6048 * (2 * n * E1 n ^ 2 - 4 * (n : ℤ) ^ 2 * E2 n - 10 * E1 n ^ 3
            + 30 * n * E1 n * E2 n - 30 * (n : ℤ) ^ 2 * E3 n)
      = (n : ℤ) ^ 3 * (1 - (n : ℤ) ^ 6) := by
  obtain ⟨m, rfl⟩ := hn
  qify
  rw [E1_q, E2_q, E3_q]
  field_simp
  ring

private lemma cert_D {n : ℕ} (hn : Odd n) :
    (n : ℤ) ^ 6 * ((-(n : ℤ) ^ 2 * E1 n + 6 * n * E1 n ^ 2 - 12 * (n : ℤ) ^ 2 * E2 n)
          + 7 * (2 * n * E1 n ^ 2 - 4 * (n : ℤ) ^ 2 * E2 n - 10 * E1 n ^ 3
              + 30 * n * E1 n * E2 n - 30 * (n : ℤ) ^ 2 * E3 n))
      - (n : ℤ) ^ 3 * (47 * (-(n : ℤ) ^ 2 * E1 n + 6 * n * E1 n ^ 2 - 12 * (n : ℤ) ^ 2 * E2 n) ^ 2
          + 3528 * (-(n : ℤ) ^ 2 * E1 n + 6 * n * E1 n ^ 2 - 12 * (n : ℤ) ^ 2 * E2 n)
              * (2 * n * E1 n ^ 2 - 4 * (n : ℤ) ^ 2 * E2 n - 10 * E1 n ^ 3
                  + 30 * n * E1 n * E2 n - 30 * (n : ℤ) ^ 2 * E3 n)
          + 21168 * (2 * n * E1 n ^ 2 - 4 * (n : ℤ) ^ 2 * E2 n - 10 * E1 n ^ 3
              + 30 * n * E1 n * E2 n - 30 * (n : ℤ) ^ 2 * E3 n) ^ 2)
      + 8000 * (-(n : ℤ) ^ 2 * E1 n + 6 * n * E1 n ^ 2 - 12 * (n : ℤ) ^ 2 * E2 n) ^ 3
      = 0 := by
  obtain ⟨m, rfl⟩ := hn
  qify
  rw [E1_q, E2_q, E3_q]
  field_simp
  ring

end Certificates
p2m_reactivate "P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_c4_c6_discriminant_of_nodal.WeierstrassCurve"

section Main

variable {u : K} {n : ℕ}

private theorem targets (hu : IsPrimitiveRoot u n) (hn : Odd n)
    (z : ℕ → K) (hz : ∀ k ∈ Icc 1 (n / 2), z k * (1 - u ^ k) ^ 2 = u ^ k) :
    240 * (∑ k ∈ Icc 1 (n / 2), (z k + 6 * z k ^ 2)) = (n : K) ^ 4 - 1
    ∧ 504 * (∑ k ∈ Icc 1 (n / 2), (z k + 6 * z k ^ 2))
        + 6048 * (∑ k ∈ Icc 1 (n / 2), (2 * z k ^ 2 + 10 * z k ^ 3)) = 1 - (n : K) ^ 6
    ∧ (∑ k ∈ Icc 1 (n / 2), (z k + 6 * z k ^ 2))
        + 7 * (∑ k ∈ Icc 1 (n / 2), (2 * z k ^ 2 + 10 * z k ^ 3))
        - 47 * (∑ k ∈ Icc 1 (n / 2), (z k + 6 * z k ^ 2)) ^ 2
        - 3528 * (∑ k ∈ Icc 1 (n / 2), (z k + 6 * z k ^ 2))
            * (∑ k ∈ Icc 1 (n / 2), (2 * z k ^ 2 + 10 * z k ^ 3))
        - 21168 * (∑ k ∈ Icc 1 (n / 2), (2 * z k ^ 2 + 10 * z k ^ 3)) ^ 2
        + 8000 * (∑ k ∈ Icc 1 (n / 2), (z k + 6 * z k ^ 2)) ^ 3 = 0 := by
  obtain ⟨hz1, hz2, hz3⟩ := Zsum_eval hu hn z hz
  push_cast at hz1 hz2 hz3
  have hn0 : (n : K) ≠ 0 := natCast_ne_zero hu hn
  set a := ((E1 n : ℤ) : K) with ha
  set b := ((E2 n : ℤ) : K) with hb
  set c := ((E3 n : ℤ) : K) with hc
  set ST := ∑ k ∈ Icc 1 (n / 2), (z k + 6 * z k ^ 2) with hST
  set SW := ∑ k ∈ Icc 1 (n / 2), (2 * z k ^ 2 + 10 * z k ^ 3) with hSW
  have hctK : (240 : K) * (-(n : K) * a + 6 * a ^ 2 - 12 * (n : K) * b)
      = (n : K) ^ 2 * ((n : K) ^ 4 - 1) := by
    have h := congrArg (fun x : ℤ => (x : K)) (cert_T hn)
    push_cast at h
    linear_combination h
  have hcwK : (504 : K) * (-(n : K) ^ 2 * a + 6 * (n : K) * a ^ 2 - 12 * (n : K) ^ 2 * b)
      + 6048 * (2 * (n : K) * a ^ 2 - 4 * (n : K) ^ 2 * b - 10 * a ^ 3
          + 30 * (n : K) * a * b - 30 * (n : K) ^ 2 * c)
      = (n : K) ^ 3 * (1 - (n : K) ^ 6) := by
    have h := congrArg (fun x : ℤ => (x : K)) (cert_W hn)
    push_cast at h
    linear_combination h
  have hcdK : (n : K) ^ 6 * ((-(n : K) ^ 2 * a + 6 * (n : K) * a ^ 2 - 12 * (n : K) ^ 2 * b)
          + 7 * (2 * (n : K) * a ^ 2 - 4 * (n : K) ^ 2 * b - 10 * a ^ 3
              + 30 * (n : K) * a * b - 30 * (n : K) ^ 2 * c))
      - (n : K) ^ 3 * (47 * (-(n : K) ^ 2 * a + 6 * (n : K) * a ^ 2 - 12 * (n : K) ^ 2 * b) ^ 2
          + 3528 * (-(n : K) ^ 2 * a + 6 * (n : K) * a ^ 2 - 12 * (n : K) ^ 2 * b)
              * (2 * (n : K) * a ^ 2 - 4 * (n : K) ^ 2 * b - 10 * a ^ 3
                  + 30 * (n : K) * a * b - 30 * (n : K) ^ 2 * c)
          + 21168 * (2 * (n : K) * a ^ 2 - 4 * (n : K) ^ 2 * b - 10 * a ^ 3
              + 30 * (n : K) * a * b - 30 * (n : K) ^ 2 * c) ^ 2)
      + 8000 * (-(n : K) ^ 2 * a + 6 * (n : K) * a ^ 2 - 12 * (n : K) ^ 2 * b) ^ 3
      = 0 := by
    have h := congrArg (fun x : ℤ => (x : K)) (cert_D hn)
    push_cast at h
    linear_combination h
  have hsplitT : ST = (∑ k ∈ Icc 1 (n / 2), z k) + 6 * ∑ k ∈ Icc 1 (n / 2), z k ^ 2 := by
    rw [hST, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsplitW : SW = 2 * (∑ k ∈ Icc 1 (n / 2), z k ^ 2)
      + 10 * ∑ k ∈ Icc 1 (n / 2), z k ^ 3 := by
    rw [hSW, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hA : (n : K) ^ 3 * ST = -(n : K) ^ 2 * a + 6 * (n : K) * a ^ 2 - 12 * (n : K) ^ 2 * b := by
    rw [hsplitT]
    linear_combination (n : K) ^ 2 * hz1 + 6 * (n : K) * hz2
  have hB : (n : K) ^ 3 * SW = 2 * (n : K) * a ^ 2 - 4 * (n : K) ^ 2 * b - 10 * a ^ 3
      + 30 * (n : K) * a * b - 30 * (n : K) ^ 2 * c := by
    rw [hsplitW]
    linear_combination 2 * (n : K) * hz2 + 10 * hz3
  refine ⟨?_, ?_, ?_⟩
  · have key : (n : K) ^ 3 * (240 * ST) = (n : K) ^ 3 * ((n : K) ^ 4 - 1) := by
      linear_combination 240 * hA + (n : K) * hctK
    exact mul_left_cancel₀ (pow_ne_zero 3 hn0) key
  · have key : (n : K) ^ 3 * (504 * ST + 6048 * SW) = (n : K) ^ 3 * (1 - (n : K) ^ 6) := by
      linear_combination 504 * hA + 6048 * hB + hcwK
    exact mul_left_cancel₀ (pow_ne_zero 3 hn0) key
  · have key : (n : K) ^ 9 * (ST + 7 * SW - 47 * ST ^ 2 - 3528 * ST * SW - 21168 * SW ^ 2
        + 8000 * ST ^ 3) = (n : K) ^ 9 * 0 := by
      rw [mul_zero]
      linear_combination ((n : K) ^ 6
            - 47 * (n : K) ^ 3 * ((n : K) ^ 3 * ST
              + (-(n : K) ^ 2 * a + 6 * (n : K) * a ^ 2 - 12 * (n : K) ^ 2 * b))
            - 3528 * (n : K) ^ 3 * ((n : K) ^ 3 * SW)
            + 8000 * (((n : K) ^ 3 * ST) ^ 2
              + ((n : K) ^ 3 * ST) * (-(n : K) ^ 2 * a + 6 * (n : K) * a ^ 2
                - 12 * (n : K) ^ 2 * b)
              + (-(n : K) ^ 2 * a + 6 * (n : K) * a ^ 2 - 12 * (n : K) ^ 2 * b) ^ 2)) * hA
        + (7 * (n : K) ^ 6
            - 3528 * (n : K) ^ 3 * (-(n : K) ^ 2 * a + 6 * (n : K) * a ^ 2
              - 12 * (n : K) ^ 2 * b)
            - 21168 * (n : K) ^ 3 * ((n : K) ^ 3 * SW
              + (2 * (n : K) * a ^ 2 - 4 * (n : K) ^ 2 * b - 10 * a ^ 3
                + 30 * (n : K) * a * b - 30 * (n : K) ^ 2 * c))) * hB
        + hcdK
    exact mul_left_cancel₀ (pow_ne_zero 9 hn0) key

end Main
p2m_reactivate "P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_c4_c6_discriminant_of_nodal.WeierstrassCurve"

end RbAux4
p2m_reactivate "P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_c4_c6_discriminant_of_nodal.WeierstrassCurve"

theorem solution
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    (hΔ : W.Δ = 0) (hc₄ : W.c₄ ≠ 0)
    {n : ℕ} (hn : Odd n)
    (Q : W.toAffine.Point) (hQord : addOrderOf Q = n) :
    (W.veluQuotient (W.oddOrderSummingSet Q (n / 2))).c₄ = (n : F) ^ 4 * W.c₄ ∧
    (W.veluQuotient (W.oddOrderSummingSet Q (n / 2))).c₆ = (n : F) ^ 6 * W.c₆ ∧
    (W.veluQuotient (W.oddOrderSummingSet Q (n / 2))).Δ = 0 := by

  obtain ⟨x₀, δ, u, huprim, hb₂, hb₄, hb₆, hb₈, hxfm⟩ := W.nodal_frame hΔ hc₄ Q
  rw [hQord] at huprim
  let ι : F →+* AlgebraicClosure F := algebraMap F (AlgebraicClosure F)
  have hιinj : Function.Injective ι := (algebraMap F (AlgebraicClosure F)).injective

  have hn1 : 1 ≤ n := hn.pos
  have hm_lt : n / 2 < n := Nat.div_lt_self hn1 one_lt_two
  have hm_le : n / 2 ≤ n - 1 := by omega

  have hprim : ∀ k ∈ Finset.Icc 1 (n - 1), u ^ k ≠ 1 := by
    intro k hk; rw [Finset.mem_Icc] at hk
    intro h1
    have hdvd := huprim.dvd_of_pow_eq_one k h1
    exact absurd (Nat.le_of_dvd hk.1 hdvd) (by omega)

  set z : ℕ → AlgebraicClosure F := fun k => u ^ k / (1 - u ^ k) ^ 2 with hzdef
  have hz := hz_from_port ι W hQord δ x₀ u hxfm hprim hm_le
  have hz' : ∀ k ∈ Finset.Icc 1 (n / 2), z k * (1 - u ^ k) ^ 2 = u ^ k := by
    intro k hk; rw [Finset.mem_Icc] at hk
    have hk' : k ∈ Finset.Icc 1 (n - 1) := Finset.mem_Icc.mpr ⟨hk.1, le_trans hk.2 hm_le⟩
    have hne : (1 : AlgebraicClosure F) - u ^ k ≠ 0 := sub_ne_zero.mpr (Ne.symm (hprim k hk'))
    simp only [hzdef]; field_simp

  obtain ⟨hT, hW6, hD⟩ := RbAux4.targets huprim hn z hz'

  refine ⟨master_c₄ ι W hQord hm_lt δ x₀ z hb₂ hb₄ hz hιinj hT,
          master_c₆ ι W hQord hm_lt δ x₀ z hb₂ hb₄ hb₆ hz hιinj hW6,
          master_Δ ι W hQord hm_lt δ x₀ z hb₂ hb₄ hb₆ hb₈ hz hιinj ?_⟩
  simp only; exact hD

end S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_c4_c6_discriminant_of_nodal
end P2MW
export P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_c4_c6_discriminant_of_nodal (solution)
