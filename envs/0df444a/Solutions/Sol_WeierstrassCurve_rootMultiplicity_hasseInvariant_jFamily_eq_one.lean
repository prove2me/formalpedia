-- Prove2me | solution 1 for WeierstrassCurve.rootMultiplicity_hasseInvariant_jFamily_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/4bfac8b7-4c4a-509e-b5a4-cb126b5889c3

import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_Polynomial_DeuringPolynomial
import Definitions.Def_ModularCurve_LegendreJ
import Theorems.Thm_WeierstrassCurve_hasseInvariant_pow_mul_delta_pow_eq_of_j_eq
import Theorems.Thm_WeierstrassCurve_hasseInvariant_legendreCurve
import Theorems.Thm_WeierstrassCurve_j_legendreCurve
import Theorems.Thm_WeierstrassCurve_isElliptic_legendreCurve_iff
import Theorems.Thm_ModularCurve_ssJSetHasse_eq_image_legendreJ
import Theorems.Thm_ModularCurve_ssJSet_eq_ssJSetHasse
import Theorems.Thm_Polynomial_separable_deuringPolynomial_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_rootMultiplicity_hasseInvariant_jFamily_eq_one
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"
set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false

open ModularCurve Polynomial

noncomputable section

namespace P2mWs11DK3

theorem hasseInvariant_map {R A : Type*} [CommRing R] [CommRing A] (q : ℕ)
    (W : WeierstrassCurve R) (φ : R →+* A) :
    (W.map φ).hasseInvariant q = φ (W.hasseInvariant q) := by
  unfold WeierstrassCurve.hasseInvariant
  have : (W.map φ).twoTorsionPolynomial = Cubic.map φ W.twoTorsionPolynomial := by
    simp only [WeierstrassCurve.twoTorsionPolynomial, Cubic.map, WeierstrassCurve.map_b₂,
      WeierstrassCurve.map_b₄, WeierstrassCurve.map_b₆, map_ofNat, map_mul]
  rw [this, Cubic.map_toPoly, ← Polynomial.map_pow, Polynomial.coeff_map]

variable {k : Type*} [Field k] [DecidableEq k]

def primeAt (l₀ : k) : IsDedekindDomain.HeightOneSpectrum k[X] :=
  ⟨Ideal.span {X - C l₀}, (Ideal.span_singleton_prime (X_sub_C_ne_zero l₀)).mpr (prime_X_sub_C l₀),
    by rw [ne_eq, Ideal.span_singleton_eq_bot]; exact X_sub_C_ne_zero l₀⟩

def vAt (l₀ : k) : Valuation (RatFunc k) (WithZero (Multiplicative ℤ)) :=
  (primeAt l₀).valuation (RatFunc k)

theorem vAt_coe (l₀ : k) (p : k[X]) :
    vAt l₀ (algebraMap k[X] (RatFunc k) p) = (primeAt l₀).intValuation p :=
  IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap _ p

theorem vAt_coe_lt_one_iff (l₀ : k) (p : k[X]) :
    vAt l₀ (algebraMap k[X] (RatFunc k) p) < 1 ↔ p.eval l₀ = 0 := by
  rw [vAt_coe, IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_dvd]
  show Ideal.span {X - C l₀} ∣ Ideal.span {p} ↔ _
  rw [Ideal.span_singleton_dvd_span_singleton_iff_dvd, dvd_iff_isRoot, IsRoot.def]

theorem vAt_coe_eq_one_iff (l₀ : k) (p : k[X]) :
    vAt l₀ (algebraMap k[X] (RatFunc k) p) = 1 ↔ p.eval l₀ ≠ 0 := by
  rw [← not_iff_not, not_not, ← vAt_coe_lt_one_iff l₀ p]
  constructor
  · intro h
    exact lt_of_le_of_ne (by rw [vAt_coe]; exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _) h
  · intro h
    exact ne_of_lt h

theorem vAt_coe_eq_exp_neg_rootMultiplicity (l₀ : k) {p : k[X]} (hp : p ≠ 0) :
    vAt l₀ (algebraMap k[X] (RatFunc k) p) = WithZero.exp (-(rootMultiplicity l₀ p : ℤ)) := by
  rw [vAt_coe]
  have key : ∀ m : ℕ, (primeAt l₀).intValuation p ≤ WithZero.exp (-(m : ℤ)) ↔ m ≤ rootMultiplicity l₀ p := by
    intro m
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_dvd]
    show Ideal.span {X - C l₀} ^ m ∣ Ideal.span {p} ↔ _
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_dvd_span_singleton_iff_dvd, le_rootMultiplicity_iff hp]
  obtain ⟨c, hc⟩ : ∃ c : ℕ, (primeAt l₀).intValuation p = WithZero.exp (-(c : ℤ)) := by
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_def, if_neg hp]
    exact ⟨_, rfl⟩
  rw [hc] at key ⊢
  have h1 : c ≤ rootMultiplicity l₀ p := (key c).mp le_rfl
  have h2 : rootMultiplicity l₀ p ≤ c := by
    have := (key (rootMultiplicity l₀ p)).mpr le_rfl
    rw [WithZero.exp_le_exp] at this
    omega
  rw [le_antisymm h1 h2]

end P2mWs11DK3

namespace P2mWs11DK3

variable {k : Type*} [Field k] [DecidableEq k]

local notation "KK" => RatFunc k
local notation "ι" => (algebraMap k[X] (RatFunc k))

def Pnum : k[X] := C ((2 : k) ^ 8) * (X ^ 2 - X + 1) ^ 3
def Pden : k[X] := X ^ 2 * (X - 1) ^ 2

omit [DecidableEq k] in
theorem algebraMap_k_eq (c : k) : algebraMap k KK c = ι (C c) := by
  rw [IsScalarTower.algebraMap_apply k k[X] (RatFunc k)]
  rfl

omit [DecidableEq k] in
theorem legendreJ_ratFunc :
    legendreJ (RatFunc.X : KK) = ι Pnum / ι Pden := by
  unfold legendreJ Pnum Pden
  rw [← RatFunc.algebraMap_X]
  simp only [map_mul, map_pow, map_sub, map_add, map_one]
  congr 2
  rw [← algebraMap_k_eq, map_ofNat]

omit [DecidableEq k] in
theorem eval_Pden_ne_zero {t : k} (ht0 : t ≠ 0) (ht1 : t ≠ 1) : (Pden : k[X]).eval t ≠ 0 := by
  unfold Pden
  simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_one]
  exact mul_ne_zero (pow_ne_zero _ ht0) (pow_ne_zero _ (sub_ne_zero.mpr ht1))

omit [DecidableEq k] in
theorem legendreJ_eq_div (t : k) : legendreJ t = Pnum.eval t / Pden.eval t := by
  unfold legendreJ Pnum Pden
  simp only [eval_mul, eval_pow, eval_sub, eval_add, eval_X, eval_C, eval_one]

omit [DecidableEq k] in
theorem legendreJ_zero : legendreJ (0 : k) = 0 := by
  unfold legendreJ; simp
omit [DecidableEq k] in
theorem legendreJ_one : legendreJ (1 : k) = 0 := by
  unfold legendreJ; simp

theorem vAt_algebraMap_k (l₀ : k) {c : k} (hc : c ≠ 0) : vAt l₀ (algebraMap k KK c) = 1 := by
  rw [algebraMap_k_eq, vAt_coe_eq_one_iff]
  rwa [eval_C]

theorem vAt_eval₂_le_one (l₀ : k) (p : k[X]) {x : KK} (hx : vAt l₀ x ≤ 1) :
    vAt l₀ (p.eval₂ (algebraMap k KK) x) ≤ 1 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [eval₂_add]
    exact le_trans (Valuation.map_add _ _ _) (max_le hp hq)
  | monomial n c =>
    rw [eval₂_monomial, Valuation.map_mul, Valuation.map_pow]
    have hc : vAt l₀ (algebraMap k KK c) ≤ 1 := by
      by_cases hc0 : c = 0
      · rw [hc0, map_zero, Valuation.map_zero]
        exact zero_le'
      · exact (vAt_algebraMap_k l₀ hc0).le
    exact mul_le_one' hc (pow_le_one' hx n)

section AtRoot

variable (l₀ : k) (a : k) (hl : legendreJ l₀ = a) (ha0 : a ≠ 0) (ha1728 : a ≠ 1728)
include hl ha0

omit [DecidableEq k] in
theorem l₀_ne_zero : l₀ ≠ 0 := by
  rintro rfl
  rw [legendreJ_zero] at hl
  exact ha0 hl.symm

omit [DecidableEq k] in
theorem l₀_ne_one : l₀ ≠ 1 := by
  rintro rfl
  rw [legendreJ_one] at hl
  exact ha0 hl.symm

omit [DecidableEq k] in
theorem eval_Pnum_eq : (Pnum : k[X]).eval l₀ = a * (Pden : k[X]).eval l₀ := by
  have hden := eval_Pden_ne_zero (l₀_ne_zero l₀ a hl ha0) (l₀_ne_one l₀ a hl ha0)
  rw [legendreJ_eq_div] at hl
  rw [← hl, div_mul_cancel₀ _ hden]

theorem vAt_Pden : vAt l₀ (ι Pden) = 1 :=
  (vAt_coe_eq_one_iff l₀ _).mpr (eval_Pden_ne_zero (l₀_ne_zero l₀ a hl ha0) (l₀_ne_one l₀ a hl ha0))

theorem vAt_Pnum : vAt l₀ (ι Pnum) = 1 := by
  rw [vAt_coe_eq_one_iff, eval_Pnum_eq l₀ a hl ha0]
  exact mul_ne_zero ha0 (eval_Pden_ne_zero (l₀_ne_zero l₀ a hl ha0) (l₀_ne_one l₀ a hl ha0))

theorem vAt_J : vAt l₀ (legendreJ (RatFunc.X : KK)) = 1 := by
  rw [legendreJ_ratFunc, map_div₀, vAt_Pnum l₀ a hl ha0, vAt_Pden l₀ a hl ha0, div_one]

theorem vAt_J_sub_lt : vAt l₀ (legendreJ (RatFunc.X : KK) - algebraMap k KK a) < 1 := by
  have hden := vAt_Pden l₀ a hl ha0
  have hden0 : ι Pden ≠ 0 := fun h => by rw [h, Valuation.map_zero] at hden; exact zero_ne_one hden
  have : legendreJ (RatFunc.X : KK) - algebraMap k KK a = ι (Pnum - C a * Pden) / ι Pden := by
    rw [legendreJ_ratFunc, map_sub, map_mul, ← algebraMap_k_eq, sub_div, mul_div_cancel_right₀ _ hden0]
  rw [this, map_div₀, hden, div_one, vAt_coe_lt_one_iff]
  rw [eval_sub, eval_mul, eval_C, eval_Pnum_eq l₀ a hl ha0, sub_self]

include ha1728 in
theorem vAt_J_sub_1728 : vAt l₀ (legendreJ (RatFunc.X : KK) - 1728) = 1 := by
  have hden := vAt_Pden l₀ a hl ha0
  have hden0 : ι Pden ≠ 0 := fun h => by rw [h, Valuation.map_zero] at hden; exact zero_ne_one hden
  have : legendreJ (RatFunc.X : KK) - 1728 = ι (Pnum - C 1728 * Pden) / ι Pden := by
    rw [legendreJ_ratFunc, map_sub, map_mul, ← algebraMap_k_eq, map_ofNat, sub_div,
      mul_div_cancel_right₀ _ hden0]
  rw [this, map_div₀, hden, div_one, vAt_coe_eq_one_iff]
  rw [eval_sub, eval_mul, eval_C, eval_Pnum_eq l₀ a hl ha0, ← sub_mul]
  exact mul_ne_zero (sub_ne_zero.mpr ha1728)
    (eval_Pden_ne_zero (l₀_ne_zero l₀ a hl ha0) (l₀_ne_one l₀ a hl ha0))

end AtRoot

end P2mWs11DK3

namespace P2mWs11DK3

variable {k : Type*} [Field k] [DecidableEq k]

local notation "KK" => RatFunc k
local notation "ι" => (algebraMap k[X] (RatFunc k))

def Wt : WeierstrassCurve k[X] := ⟨1, 0, 0, -36 * X, -X⟩

omit [DecidableEq k] in
theorem Wt_Δ : (Wt : WeierstrassCurve k[X]).Δ = X * (1 + 1728 * X) ^ 2 := by
  simp only [Wt, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

omit [DecidableEq k] in
theorem Wt_c₄ : (Wt : WeierstrassCurve k[X]).c₄ = 1 + 1728 * X := by
  simp only [Wt, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

def φτ (τ : KK) : k[X] →+* KK := Polynomial.eval₂RingHom (algebraMap k KK) τ

omit [DecidableEq k] in
theorem φτ_X (τ : KK) : φτ τ X = τ := eval₂_X _ _

def Eτ (τ : KK) : WeierstrassCurve KK := (Wt : WeierstrassCurve k[X]).map (φτ τ)

omit [DecidableEq k] in
theorem Eτ_Δ (τ : KK) : (Eτ τ).Δ = τ * (1 + 1728 * τ) ^ 2 := by
  rw [Eτ, WeierstrassCurve.map_Δ, Wt_Δ]
  simp only [map_mul, map_pow, map_add, map_one, map_ofNat, φτ_X]

omit [DecidableEq k] in
theorem Eτ_c₄ (τ : KK) : (Eτ τ).c₄ = 1 + 1728 * τ := by
  rw [Eτ, WeierstrassCurve.map_c₄, Wt_c₄]
  simp only [map_mul, map_add, map_one, map_ofNat, φτ_X]

omit [DecidableEq k] in
theorem Eτ_hasseInvariant (q : ℕ) (τ : KK) :
    (Eτ τ).hasseInvariant q = ((Wt : WeierstrassCurve k[X]).hasseInvariant q).eval₂ (algebraMap k KK) τ := by
  rw [Eτ, hasseInvariant_map]
  rfl

omit [DecidableEq k] in
theorem Eτ_isElliptic {τ : KK} (hτ : τ ≠ 0) (hc : 1 + 1728 * τ ≠ 0) : (Eτ τ).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, Eτ_Δ]
  exact isUnit_iff_ne_zero.mpr (mul_ne_zero hτ (pow_ne_zero _ hc))

omit [DecidableEq k] in
theorem Eτ_j {τ : KK} [(Eτ τ).IsElliptic] (hτ : τ ≠ 0) (hc : 1 + 1728 * τ ≠ 0) :
    (Eτ τ).j = (1 + 1728 * τ) / τ := by
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ', Eτ_c₄, Eτ_Δ]
  field_simp

omit [DecidableEq k] in
theorem legendreCurve_Δ (t : KK) : (WeierstrassCurve.legendreCurve t).Δ = 16 * t ^ 2 * (t - 1) ^ 2 := by
  simp only [WeierstrassCurve.legendreCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

omit [DecidableEq k] in
theorem algebraMap_eq_eval₂ (p : k[X]) : ι p = p.eval₂ (algebraMap k KK) RatFunc.X := by
  have h := Polynomial.aeval_algebraMap_apply (RatFunc k) (X : k[X]) p
  rw [RatFunc.algebraMap_X] at h
  rw [Polynomial.aeval_def] at h
  rw [h]
  congr 1
  exact (Polynomial.aeval_X_left_apply p).symm

omit [DecidableEq k] in
theorem eval_map_int (p : ℤ[X]) :
    (p.map (Int.castRingHom KK)).eval (RatFunc.X : KK) = ι (p.map (Int.castRingHom k)) := by
  rw [algebraMap_eq_eval₂, Polynomial.eval_map, Polynomial.eval₂_map]
  congr 1
  exact RingHom.ext_int _ _

theorem hasse_identity (q : ℕ) [Fact q.Prime] [CharP k q] (E E' : WeierstrassCurve KK)
    [E.IsElliptic] [E'.IsElliptic] (hj : E.j = E'.j) :
    E.hasseInvariant q ^ 12 * E'.Δ ^ (q - 1) = E'.hasseInvariant q ^ 12 * E.Δ ^ (q - 1) := by
  let F := AlgebraicClosure KK
  let f : KK →+* F := algebraMap KK F
  have h := WeierstrassCurve.hasseInvariant_pow_mul_delta_pow_eq_of_j_eq q (E.map f) (E'.map f)
    (by rw [WeierstrassCurve.map_j, WeierstrassCurve.map_j, hj])
  rw [hasseInvariant_map, hasseInvariant_map, WeierstrassCurve.map_Δ, WeierstrassCurve.map_Δ,
    ← map_pow, ← map_pow, ← map_pow, ← map_pow, ← map_mul, ← map_mul] at h
  exact f.injective h

end P2mWs11DK3

namespace P2mWs11DK3

variable {k : Type*} [Field k] [DecidableEq k]

local notation "KK" => RatFunc k
local notation "ι" => (algebraMap k[X] (RatFunc k))

omit [DecidableEq k] in
theorem natCast_ne_zero_of_lt (q : ℕ) [Fact q.Prime] [CharP k q] {n : ℕ} (hn0 : n ≠ 0) (hn : n < q) :
    (n : k) ≠ 0 := by
  intro h
  rw [CharP.cast_eq_zero_iff k q] at h
  exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hn0) hn h

omit [Field k] [DecidableEq k] in
theorem eq_exp_of_ne_zero {x : WithZero (Multiplicative ℤ)} (hx : x ≠ 0) : ∃ z : ℤ, x = WithZero.exp z :=
  ⟨Multiplicative.toAdd (WithZero.unzero hx), by
    show x = ((Multiplicative.ofAdd (Multiplicative.toAdd (WithZero.unzero hx)) : Multiplicative ℤ) :
      WithZero (Multiplicative ℤ))
    rw [ofAdd_toAdd, WithZero.coe_unzero]⟩

omit [Field k] [DecidableEq k] in
theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (hx : x < 1) : x ≤ WithZero.exp (-1 : ℤ) := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_le'
  · obtain ⟨z, rfl⟩ := eq_exp_of_ne_zero h0
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
    rw [WithZero.exp_le_exp]
    omega

theorem main (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) [CharP k q] [IsAlgClosed k]
    (a : k) (ha : a ∈ ssJSet q k) (h0 : a ≠ 0) (h1728 : a ≠ 1728) :
    rootMultiplicity (a - 1728)⁻¹ ((Wt : WeierstrassCurve k[X]).hasseInvariant q) = 1 := by
  have hqp : q.Prime := Fact.out
  have hq2 : q ≠ 2 := by omega
  have hodd : Odd q := hqp.odd_of_ne_two hq2

  rw [ModularCurve.ssJSet_eq_ssJSetHasse q hq2 k, ModularCurve.ssJSetHasse_eq_image_legendreJ q hq2 k] at ha
  obtain ⟨l₀, hH, hl⟩ := ha
  change ((deuringPolynomial q).map (Int.castRingHom k)).eval l₀ = 0 at hH
  have hl0 : l₀ ≠ 0 := l₀_ne_zero l₀ a hl h0
  have hl1 : l₀ ≠ 1 := l₀_ne_one l₀ a hl h0

  set J : KK := legendreJ (RatFunc.X : KK) with hJ
  set τ : KK := (J - 1728)⁻¹ with hτdef
  have vJ : vAt l₀ J = 1 := vAt_J l₀ a hl h0
  have vJ1728 : vAt l₀ (J - 1728) = 1 := vAt_J_sub_1728 l₀ a hl h0 h1728
  have vJa : vAt l₀ (J - algebraMap k KK a) < 1 := vAt_J_sub_lt l₀ a hl h0
  have hne : ∀ {x : KK}, vAt l₀ x = 1 → x ≠ 0 := fun h hx => by
    rw [hx, Valuation.map_zero] at h
    exact zero_ne_one h
  have hJ1728 : J - 1728 ≠ 0 := hne vJ1728
  have vτ : vAt l₀ τ = 1 := by rw [hτdef, map_inv₀, vJ1728, inv_one]
  have hτ0 : τ ≠ 0 := inv_ne_zero hJ1728
  have h1728τ : 1 + 1728 * τ = J / (J - 1728) := by
    rw [hτdef, eq_div_iff hJ1728, add_mul, inv_mul_cancel_right₀ hJ1728]
    ring
  have v1728τ : vAt l₀ (1 + 1728 * τ) = 1 := by rw [h1728τ, map_div₀, vJ, vJ1728, div_one]
  have hc : 1 + 1728 * τ ≠ 0 := hne v1728τ

  have vX : vAt l₀ (RatFunc.X : KK) = 1 := by
    rw [← RatFunc.algebraMap_X, vAt_coe_eq_one_iff, eval_X]
    exact hl0
  have vX1 : vAt l₀ (RatFunc.X - 1 : KK) = 1 := by
    rw [← RatFunc.algebraMap_X, ← map_one (algebraMap k[X] (RatFunc k)), ← map_sub, vAt_coe_eq_one_iff,
      eval_sub, eval_X, eval_one]
    exact sub_ne_zero.mpr hl1
  have hX0 : (RatFunc.X : KK) ≠ 0 := hne vX
  have hX1 : (RatFunc.X : KK) ≠ 1 := fun h => by
    have h' := vX1
    rw [h, sub_self, Valuation.map_zero] at h'
    exact zero_ne_one h'

  have h2k : (2 : k) ≠ 0 := by exact_mod_cast natCast_ne_zero_of_lt (k := k) q two_ne_zero (by omega)
  have h2 : (2 : KK) ≠ 0 := by
    rw [show (2 : KK) = algebraMap k KK 2 from (map_ofNat _ 2).symm]
    exact (_root_.map_ne_zero _).mpr h2k

  haveI hE : (Eτ τ).IsElliptic := Eτ_isElliptic hτ0 hc
  have hjE : (Eτ τ).j = J := by
    rw [Eτ_j hτ0 hc, h1728τ, hτdef, div_inv_eq_mul, div_mul_cancel₀ _ hJ1728]
  haveI hE' : (WeierstrassCurve.legendreCurve (RatFunc.X : KK)).IsElliptic :=
    (WeierstrassCurve.isElliptic_legendreCurve_iff _ h2).mpr ⟨hX0, hX1⟩
  have hjE' : (WeierstrassCurve.legendreCurve (RatFunc.X : KK)).j = J := WeierstrassCurve.j_legendreCurve _
  have hid := hasse_identity q (Eτ τ) (WeierstrassCurve.legendreCurve (RatFunc.X : KK)) (hjE.trans hjE'.symm)
  rw [Eτ_hasseInvariant, Eτ_Δ, legendreCurve_Δ, WeierstrassCurve.hasseInvariant_legendreCurve hodd,
    eval_map_int] at hid

  set h : k[X] := (Wt : WeierstrassCurve k[X]).hasseInvariant q with hh
  set Hq : k[X] := (deuringPolynomial q).map (Int.castRingHom k) with hHq

  have h16k : (16 : k) ≠ 0 := by
    have := pow_ne_zero 4 h2k
    norm_num at this
    exact this
  have h4k : (4 : k) ≠ 0 := by
    have := pow_ne_zero 2 h2k
    norm_num at this
    exact this
  have v16 : vAt l₀ (16 : KK) = 1 := by
    rw [show (16 : KK) = algebraMap k KK 16 from (map_ofNat _ 16).symm]
    exact vAt_algebraMap_k l₀ h16k
  have v4 : vAt l₀ ((-4) ^ ((q - 1) / 2) : KK) = 1 := by
    rw [Valuation.map_pow, Valuation.map_neg,
      show (4 : KK) = algebraMap k KK 4 from (map_ofNat _ 4).symm, vAt_algebraMap_k l₀ h4k, one_pow]
  have hsep : Hq.Separable := Polynomial.separable_deuringPolynomial_map q
  have hHq0 : Hq ≠ 0 := fun h0' => Polynomial.not_separable_zero (h0' ▸ hsep)
  have hrootHq : rootMultiplicity l₀ Hq = 1 := by
    apply le_antisymm
    · rw [← Polynomial.count_roots Hq]
      exact Multiset.nodup_iff_count_le_one.mp (Polynomial.nodup_roots hsep) l₀
    · exact (Polynomial.rootMultiplicity_pos hHq0).mpr hH
  have vHq : vAt l₀ (ι Hq) = WithZero.exp (-1 : ℤ) := by
    rw [vAt_coe_eq_exp_neg_rootMultiplicity l₀ hHq0, hrootHq]
    rfl
  have vDen : vAt l₀ ((16 : KK) * RatFunc.X ^ 2 * (RatFunc.X - 1) ^ 2) = 1 := by
    rw [Valuation.map_mul, Valuation.map_mul, Valuation.map_pow, Valuation.map_pow, v16, vX, vX1]
    simp
  have vΔE : vAt l₀ (τ * (1 + 1728 * τ) ^ 2) = 1 := by
    rw [Valuation.map_mul, Valuation.map_pow, vτ, v1728τ]
    simp

  have hv := congrArg (vAt l₀) hid
  rw [Valuation.map_mul (vAt l₀) (_ ^ 12), Valuation.map_mul (vAt l₀) (_ ^ 12), Valuation.map_pow,
    Valuation.map_pow, Valuation.map_pow, Valuation.map_pow, vDen, vΔE, Valuation.map_mul, v4, vHq,
    one_pow, mul_one, mul_one, one_mul] at hv

  set A : KK := h.eval₂ (algebraMap k KK) τ with hA
  have hA0 : vAt l₀ A ≠ 0 := by
    intro h0'
    rw [h0', zero_pow (by norm_num)] at hv
    exact (pow_ne_zero 12 WithZero.coe_ne_zero) hv.symm
  have vA : vAt l₀ A = WithZero.exp (-1 : ℤ) := by
    obtain ⟨z, hz⟩ := eq_exp_of_ne_zero hA0
    rw [hz] at hv ⊢
    rw [← WithZero.exp_nsmul, ← WithZero.exp_nsmul] at hv
    have := WithZero.exp_injective hv
    simp only [nsmul_eq_mul] at this
    have hz' : z = -1 := by omega
    rw [hz']

  have hh0 : h ≠ 0 := by
    intro h0'
    apply hA0
    rw [hA, h0', eval₂_zero, Valuation.map_zero]

  set τ₀ : k := (a - 1728)⁻¹ with hτ₀
  obtain ⟨g, hfac, hndvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd h hh0 τ₀
  set r := rootMultiplicity τ₀ h with hr
  have hAfac : A = (τ - algebraMap k KK τ₀) ^ r * g.eval₂ (algebraMap k KK) τ := by
    rw [hA]
    conv_lhs => rw [hfac]
    rw [eval₂_mul, eval₂_pow, eval₂_sub, eval₂_X, eval₂_C]

  have ha1728 : algebraMap k KK (a - 1728) ≠ 0 := (_root_.map_ne_zero _).mpr (sub_ne_zero.mpr h1728)
  have hdiff : τ - algebraMap k KK τ₀ = (algebraMap k KK a - J) / ((J - 1728) * algebraMap k KK (a - 1728)) := by
    rw [hτ₀, map_inv₀, hτdef, inv_sub_inv hJ1728 ha1728]
    congr 1
    rw [map_sub, map_ofNat]
    ring
  have vdiff : vAt l₀ (τ - algebraMap k KK τ₀) < 1 := by
    rw [hdiff, map_div₀, Valuation.map_mul, vJ1728, one_mul,
      vAt_algebraMap_k l₀ (sub_ne_zero.mpr h1728), div_one, Valuation.map_sub_swap]
    exact vJa
  have vg : vAt l₀ (g.eval₂ (algebraMap k KK) τ) ≤ 1 := vAt_eval₂_le_one l₀ g vτ.le

  have hr1 : r ≤ 1 := by
    have h1 : vAt l₀ A ≤ WithZero.exp (-1 : ℤ) ^ r := by
      rw [hAfac, Valuation.map_mul, Valuation.map_pow]
      calc vAt l₀ (τ - algebraMap k KK τ₀) ^ r * vAt l₀ (g.eval₂ (algebraMap k KK) τ)
          ≤ WithZero.exp (-1 : ℤ) ^ r * 1 :=
            mul_le_mul' (pow_le_pow_left' (le_exp_neg_one_of_lt_one vdiff) r) vg
        _ = WithZero.exp (-1 : ℤ) ^ r := mul_one _
    rw [vA, ← WithZero.exp_nsmul, WithZero.exp_le_exp, nsmul_eq_mul] at h1
    omega

  have hr0 : r ≠ 0 := by
    intro hr0
    have hnot : ¬ (X - C τ₀) ∣ h := by
      rw [hfac, hr0, pow_zero, one_mul]
      exact hndvd
    have hev : h.eval τ₀ ≠ 0 := fun he => hnot (dvd_iff_isRoot.mpr he)
    have hdec : h = C (h.eval τ₀) + (X - C τ₀) * (h /ₘ (X - C τ₀)) := by
      conv_lhs => rw [← modByMonic_add_div h (X - C τ₀), modByMonic_X_sub_C_eq_C_eval]
    have hA' : A = algebraMap k KK (h.eval τ₀) +
        (τ - algebraMap k KK τ₀) * (h /ₘ (X - C τ₀)).eval₂ (algebraMap k KK) τ := by
      rw [hA]
      conv_lhs => rw [hdec]
      rw [eval₂_add, eval₂_C, eval₂_mul, eval₂_sub, eval₂_X, eval₂_C]
    have hv1 : vAt l₀ A = 1 := by
      rw [hA', Valuation.map_add_eq_of_lt_left]
      · exact vAt_algebraMap_k l₀ hev
      · rw [vAt_algebraMap_k l₀ hev, Valuation.map_mul]
        calc vAt l₀ (τ - algebraMap k KK τ₀) * vAt l₀ ((h /ₘ (X - C τ₀)).eval₂ (algebraMap k KK) τ)
            ≤ vAt l₀ (τ - algebraMap k KK τ₀) * 1 :=
              mul_le_mul_right (vAt_eval₂_le_one l₀ _ vτ.le) _
          _ < 1 := by rw [mul_one]; exact vdiff
    rw [vA] at hv1
    have := WithZero.exp_injective (hv1.trans WithZero.exp_zero.symm)
    omega
  omega

end P2mWs11DK3

end

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q)
    (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (a : k) (ha : a ∈ ssJSet q k) (h0 : a ≠ 0) (h1728 : a ≠ 1728) :
    Polynomial.rootMultiplicity (a - 1728)⁻¹ (WeierstrassCurve.hasseInvariant q (⟨1, 0, 0, -36 * Polynomial.X, -Polynomial.X⟩ : WeierstrassCurve (Polynomial k))) = 1 :=
  P2mWs11DK3.main q hq a ha h0 h1728

end S_WeierstrassCurve_rootMultiplicity_hasseInvariant_jFamily_eq_one
end P2MW
export P2MW.S_WeierstrassCurve_rootMultiplicity_hasseInvariant_jFamily_eq_one (solution)
