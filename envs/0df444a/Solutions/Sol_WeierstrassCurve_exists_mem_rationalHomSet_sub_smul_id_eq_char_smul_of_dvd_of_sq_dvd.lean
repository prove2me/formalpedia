-- Prove2me | solution 1 for WeierstrassCurve.exists_mem_rationalHomSet_sub_smul_id_eq_char_smul_of_dvd_of_sq_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/3262331f-0308-5628-8a4b-cff1d5618686

import Mathlib
import Theorems.Thm_Polynomial_isCoprime_and_wronskian_ne_zero_comp_of_wronskian_ne_zero
import Definitions.Def_WeierstrassCurve_RationalEnd
import Theorems.Thm_WeierstrassCurve_exists_xCoord_rep_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_natDegree_lt_of_xCoord_rep
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_Psi2Sq_mul_wronskian_sq
import Theorems.Thm_WeierstrassCurve_isCoprime_Phi_PsiSq
import Theorems.Thm_WeierstrassCurve_Psi2Sq_ne_zero_of_isElliptic
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_some_eq_some_div
import Theorems.Thm_WeierstrassCurve_Affine_evalEval_psi_sq
import Theorems.Thm_WeierstrassCurve_exists_forall_mem_zmultiples_of_char_nsmul_eq_zero
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_comp_eq_of_ker_le_of_xCoord_expand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_sub_smul_id_eq_char_smul_of_dvd_of_sq_dvd
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

open Polynomial

namespace DeuringMaxP
namespace Poly

variable {k : Type*} [Field k]

theorem wronskian_C_mul (a : k) (u v : k[X]) :
    wronskian (C a * u) (C a * v) = C a ^ 2 * wronskian u v := by
  simp only [wronskian, derivative_mul, derivative_C, zero_mul, zero_add]
  ring

theorem wronskian_map {S : Type*} [Field S] (f : k →+* S) (u v : k[X]) :
    wronskian (u.map f) (v.map f) = (wronskian u v).map f := by
  simp only [wronskian, derivative_map, Polynomial.map_mul, Polynomial.map_sub]

theorem derivative_expand_pow_eq_zero (p : ℕ) [Fact p.Prime] [CharP k p] {j : ℕ} (hj : j ≠ 0)
    (f : k[X]) : derivative (expand k (p ^ j) f) = 0 := by
  rw [derivative_expand]
  have : ((p ^ j : ℕ) : k[X]) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero k[X] p, zero_pow hj]
  rw [this, zero_mul, mul_zero]

theorem wronskian_expand_pow_eq_zero (p : ℕ) [Fact p.Prime] [CharP k p] {j : ℕ} (hj : j ≠ 0)
    (f g : k[X]) : wronskian (expand k (p ^ j) f) (expand k (p ^ j) g) = 0 := by
  simp only [wronskian, derivative_expand_pow_eq_zero p hj, mul_zero, zero_mul, sub_self]

theorem ne_C_mul_of_wronskian_ne_zero {u v : k[X]} (hw : wronskian u v ≠ 0) (c : k) :
    u ≠ C c * v := by
  rintro rfl
  apply hw
  simp only [wronskian, derivative_mul, derivative_C, zero_mul, zero_add]
  ring

theorem max_natDegree_pos_of_wronskian_ne_zero {u v : k[X]} (hw : wronskian u v ≠ 0) :
    0 < max u.natDegree v.natDegree := by
  by_contra h
  push Not at h
  have hu : u.natDegree = 0 := by omega
  have hv : v.natDegree = 0 := by omega
  apply hw
  rw [eq_C_of_natDegree_eq_zero hu, eq_C_of_natDegree_eq_zero hv]
  simp [wronskian]

theorem ne_zero_of_isCoprime_of_pos {u v : k[X]} (huv : IsCoprime u v)
    (h : 0 < max u.natDegree v.natDegree) : u ≠ 0 ∧ v ≠ 0 := by
  constructor
  · rintro rfl
    have := natDegree_eq_zero_of_isUnit (isCoprime_zero_left.mp huv)
    simp [this] at h
  · rintro rfl
    have := natDegree_eq_zero_of_isUnit (isCoprime_zero_right.mp huv)
    simp [this] at h

theorem ne_C_mul_of_isCoprime_of_pos {u v : k[X]} (huv : IsCoprime u v)
    (h : 0 < max u.natDegree v.natDegree) (c : k) : u ≠ C c * v := by
  intro huc
  have hvu : v ∣ u := ⟨C c, by rw [huc, mul_comm]⟩
  have hunit : IsUnit v := huv.isUnit_of_dvd' hvu (dvd_refl v)
  have hv0 : v.natDegree = 0 := natDegree_eq_zero_of_isUnit hunit
  have hu0 : u.natDegree = 0 := by
    apply Nat.eq_zero_of_le_zero
    rw [huc]; exact (natDegree_C_mul_le _ _).trans_eq hv0
  omega

theorem eval_ne_zero_of_isCoprime {u v : k[X]} (huv : IsCoprime u v) {x : k} (hv : v.eval x = 0) :
    u.eval x ≠ 0 := by
  intro hu
  obtain ⟨a, b, hab⟩ := huv
  have := congr_arg (eval x) hab
  simp [hu, hv] at this

theorem exists_C_mul_of_mul_eq_mul {u₁ v₁ u₂ v₂ : k[X]} (h₁ : IsCoprime u₁ v₁) (h₂ : IsCoprime u₂ v₂)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (heq : u₁ * v₂ = u₂ * v₁) :
    ∃ c : k, c ≠ 0 ∧ u₂ = C c * u₁ ∧ v₂ = C c * v₁ := by
  have d12 : u₁ ∣ u₂ := h₁.dvd_of_dvd_mul_right ⟨v₂, by rw [heq]⟩
  have d21 : u₂ ∣ u₁ := h₂.dvd_of_dvd_mul_right ⟨v₁, by rw [← heq]⟩
  obtain ⟨w, hw⟩ := associated_of_dvd_dvd d12 d21
  obtain ⟨c, hc, hcw⟩ := Polynomial.isUnit_iff.mp w.isUnit
  refine ⟨c, hc.ne_zero, by rw [← hw, ← hcw, mul_comm], ?_⟩
  have : u₁ * v₂ = u₁ * (C c * v₁) := by
    rw [heq, ← hw, ← hcw]; ring
  exact mul_left_cancel₀ hu₁ this

section CharP

variable (p : ℕ) [Fact p.Prime] [CharP k p]

theorem exists_expand_wronskian_ne_zero {u v : k[X]} (huv : IsCoprime u v)
    (h : 0 < max u.natDegree v.natDegree) :
    ∃ (e : ℕ) (u₀ v₀ : k[X]), u = expand k (p ^ e) u₀ ∧ v = expand k (p ^ e) v₀ ∧
      IsCoprime u₀ v₀ ∧ 0 < max u₀.natDegree v₀.natDegree ∧ wronskian u₀ v₀ ≠ 0 := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero

  suffices H : ∀ n : ℕ, ∀ u v : k[X], max u.natDegree v.natDegree = n → IsCoprime u v →
      0 < max u.natDegree v.natDegree →
      ∃ (e : ℕ) (u₀ v₀ : k[X]), u = expand k (p ^ e) u₀ ∧ v = expand k (p ^ e) v₀ ∧
        IsCoprime u₀ v₀ ∧ 0 < max u₀.natDegree v₀.natDegree ∧ wronskian u₀ v₀ ≠ 0 from
    H _ u v rfl huv h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u v hn huv hpos
    by_cases hw : wronskian u v ≠ 0
    · exact ⟨0, u, v, by simp, by simp, huv, hpos, hw⟩
    push Not at hw
    obtain ⟨hdu, hdv⟩ := huv.wronskian_eq_zero_iff.mp hw
    set u₁ := contract p u
    set v₁ := contract p v
    have hu : u = expand k p u₁ := (expand_contract p hdu hp).symm
    have hv : v = expand k p v₁ := (expand_contract p hdv hp).symm
    have hcop : IsCoprime u₁ v₁ := by
      rw [hu, hv, isCoprime_expand hp] at huv; exact huv
    have hdeg_u : u.natDegree = u₁.natDegree * p := by rw [hu, natDegree_expand]
    have hdeg_v : v.natDegree = v₁.natDegree * p := by rw [hv, natDegree_expand]
    have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
    have hmax : max u.natDegree v.natDegree = max u₁.natDegree v₁.natDegree * p := by
      rw [hdeg_u, hdeg_v, Nat.mul_max_mul_right]
    have hpos₁ : 0 < max u₁.natDegree v₁.natDegree := by
      rcases Nat.eq_zero_or_pos (max u₁.natDegree v₁.natDegree) with h0 | h0
      · rw [hmax, h0, zero_mul] at hpos; exact absurd hpos (lt_irrefl 0)
      · exact h0
    have hlt : max u₁.natDegree v₁.natDegree < n := by
      rw [← hn, hmax]
      exact lt_mul_of_one_lt_right hpos₁ hp1
    obtain ⟨e, u₀, v₀, hu₀, hv₀, hc₀, hpos₀, hw₀⟩ := ih _ hlt u₁ v₁ rfl hcop hpos₁
    refine ⟨e + 1, u₀, v₀, ?_, ?_, hc₀, hpos₀, hw₀⟩
    · rw [hu, hu₀, expand_expand, pow_succ']
    · rw [hv, hv₀, expand_expand, pow_succ']

theorem expand_exponent_le {u₁ v₁ u₂ v₂ c₁ c₁' c₂ c₂' : k[X]} {a b : ℕ}
    (h₁ : IsCoprime u₁ v₁) (h₂ : IsCoprime u₂ v₂) (heq : u₁ * v₂ = u₂ * v₁)
    (ha : u₁ = expand k (p ^ a) c₁) (ha' : v₁ = expand k (p ^ a) c₁')
    (hb : u₂ = expand k (p ^ b) c₂) (hb' : v₂ = expand k (p ^ b) c₂')
    (hw₁ : wronskian c₁ c₁' ≠ 0) (hw₂ : wronskian c₂ c₂' ≠ 0) : b ≤ a := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  by_contra hlt
  push Not at hlt
  have hu₁ : u₁ ≠ 0 := by
    intro h0; apply hw₁
    have : c₁ = 0 := expand_injective (pow_pos hp a) (by rw [← ha, h0, map_zero])
    rw [this, wronskian_zero_left]
  have hu₂ : u₂ ≠ 0 := by
    intro h0; apply hw₂
    have : c₂ = 0 := expand_injective (pow_pos hp b) (by rw [← hb, h0, map_zero])
    rw [this, wronskian_zero_left]
  obtain ⟨c, hc, hcu, hcv⟩ := exists_C_mul_of_mul_eq_mul h₁ h₂ hu₁ hu₂ heq

  obtain ⟨j, hj⟩ : ∃ j, b = a + j := ⟨b - a, by omega⟩
  have hj0 : j ≠ 0 := by omega
  have e1 : C c * c₁ = expand k (p ^ j) c₂ := by
    apply expand_injective (pow_pos hp a)
    rw [map_mul, expand_C, ← ha, ← hcu, hb, hj, pow_add, mul_comm (p ^ a), ← expand_expand,
      expand_expand, expand_expand, mul_comm]
  have e2 : C c * c₁' = expand k (p ^ j) c₂' := by
    apply expand_injective (pow_pos hp a)
    rw [map_mul, expand_C, ← ha', ← hcv, hb', hj, pow_add, mul_comm (p ^ a), ← expand_expand,
      expand_expand, expand_expand, mul_comm]
  have hz : wronskian (C c * c₁) (C c * c₁') = 0 := by
    rw [e1, e2, wronskian_expand_pow_eq_zero p hj0]
  rw [wronskian_C_mul] at hz
  rcases mul_eq_zero.mp hz with h | h
  · exact hc (by simpa using h)
  · exact hw₁ h

theorem expand_exponent_unique {u₁ v₁ u₂ v₂ c₁ c₁' c₂ c₂' : k[X]} {a b : ℕ}
    (h₁ : IsCoprime u₁ v₁) (h₂ : IsCoprime u₂ v₂) (heq : u₁ * v₂ = u₂ * v₁)
    (ha : u₁ = expand k (p ^ a) c₁) (ha' : v₁ = expand k (p ^ a) c₁')
    (hb : u₂ = expand k (p ^ b) c₂) (hb' : v₂ = expand k (p ^ b) c₂')
    (hw₁ : wronskian c₁ c₁' ≠ 0) (hw₂ : wronskian c₂ c₂' ≠ 0) : a = b :=
  le_antisymm
    (expand_exponent_le p h₂ h₁ (by rw [mul_comm, heq, mul_comm]) hb hb' ha ha' hw₂ hw₁)
    (expand_exponent_le p h₁ h₂ heq ha ha' hb hb' hw₁ hw₂)

end CharP

noncomputable def hom (m : ℕ) (u v s : k[X]) : k[X] :=
  ∑ i ∈ Finset.range (m + 1), C (s.coeff i) * u ^ i * v ^ (m - i)

theorem eval_hom {m : ℕ} {u v s : k[X]} (hs : s.natDegree ≤ m) {x x' : k}
    (hx : x' * v.eval x = u.eval x) :
    (hom m u v s).eval x = (v.eval x) ^ m * s.eval x' := by
  simp only [hom, eval_finsetSum, eval_mul, eval_pow, eval_C]
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hs), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [← hx, mul_pow, show (v.eval x) ^ m = (v.eval x) ^ i * (v.eval x) ^ (m - i) by
    rw [← pow_add, Nat.add_sub_cancel' (Nat.lt_succ_iff.mp hi)]]
  ring

theorem eval_hom_div {m : ℕ} {u v s : k[X]} (hs : s.natDegree ≤ m) {x : k} (hv : v.eval x ≠ 0) :
    (hom m u v s).eval x = (v.eval x) ^ m * s.eval (u.eval x / v.eval x) :=
  eval_hom hs (div_mul_cancel₀ _ hv)

theorem comp_core [IsAlgClosed k] {u v s t : k[X]} (huv : IsCoprime u v)
    (hu : 0 < max u.natDegree v.natDegree) (hw : wronskian u v ≠ 0) (hst : IsCoprime s t)
    (hs : 0 < max s.natDegree t.natDegree) (hw' : wronskian s t ≠ 0) :
    IsCoprime (hom (max s.natDegree t.natDegree) u v s) (hom (max s.natDegree t.natDegree) u v t) ∧
      0 < max (hom (max s.natDegree t.natDegree) u v s).natDegree
        (hom (max s.natDegree t.natDegree) u v t).natDegree ∧
      wronskian (hom (max s.natDegree t.natDegree) u v s)
        (hom (max s.natDegree t.natDegree) u v t) ≠ 0 :=
  Polynomial.isCoprime_and_wronskian_ne_zero_comp_of_wronskian_ne_zero huv hu hw hst hs hw'
    (fun x hx => eval_hom_div (le_max_left _ _) hx) (fun x hx => eval_hom_div (le_max_right _ _) hx)

section Twist

variable (p : ℕ) [Fact p.Prime] [CharP k p]

theorem eval_pow_eq_eval_map_iterateFrobenius (u : k[X]) (y : k) (j : ℕ) :
    (u.eval y) ^ (p ^ j) = (u.map (iterateFrobenius k p j)).eval (y ^ (p ^ j)) := by
  rw [eval_map, ← iterateFrobenius_def, ← iterateFrobenius_def p j y, eval₂_at_apply]

theorem isCoprime_map_iff {u v : k[X]} (f : k →+* k) : IsCoprime (u.map f) (v.map f) ↔ IsCoprime u v :=
  isCoprime_map f

theorem natDegree_map' (u : k[X]) (f : k →+* k) : (u.map f).natDegree = u.natDegree :=
  natDegree_map_eq_of_injective f.injective u

theorem wronskian_map_ne_zero_iff {u v : k[X]} (f : k →+* k) :
    wronskian (u.map f) (v.map f) ≠ 0 ↔ wronskian u v ≠ 0 := by
  rw [wronskian_map, Ne, Polynomial.map_eq_zero_iff f.injective]

end Twist

section Comp

variable (p : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]

theorem exists_comp_expand {u v s t a₁ a₂ b₁ b₂ : k[X]} {a b : ℕ}
    (hu : u = expand k (p ^ b) b₁) (hv : v = expand k (p ^ b) b₂)
    (hs : s = expand k (p ^ a) a₁) (ht : t = expand k (p ^ a) a₂)
    (hbc : IsCoprime b₁ b₂) (hbpos : 0 < max b₁.natDegree b₂.natDegree) (hbw : wronskian b₁ b₂ ≠ 0)
    (hac : IsCoprime a₁ a₂) (hapos : 0 < max a₁.natDegree a₂.natDegree) (haw : wronskian a₁ a₂ ≠ 0) :
    ∃ U₀ V₀ : k[X], IsCoprime U₀ V₀ ∧ 0 < max U₀.natDegree V₀.natDegree ∧ wronskian U₀ V₀ ≠ 0 ∧
      ∀ x : k, v.eval x ≠ 0 → t.eval (u.eval x / v.eval x) ≠ 0 →
        (expand k (p ^ (a + b)) V₀).eval x ≠ 0 ∧
        (expand k (p ^ (a + b)) U₀).eval x / (expand k (p ^ (a + b)) V₀).eval x =
          s.eval (u.eval x / v.eval x) / t.eval (u.eval x / v.eval x) := by
  set σ := iterateFrobenius k p a
  set b₁' := b₁.map σ
  set b₂' := b₂.map σ
  have hbc' : IsCoprime b₁' b₂' := (isCoprime_map σ).mpr hbc
  have hbpos' : 0 < max b₁'.natDegree b₂'.natDegree := by
    rwa [natDegree_map' b₁ σ, natDegree_map' b₂ σ]
  have hbw' : wronskian b₁' b₂' ≠ 0 := (wronskian_map_ne_zero_iff σ).mpr hbw
  set m := max a₁.natDegree a₂.natDegree
  obtain ⟨hc, hpos, hw⟩ := comp_core hbc' hbpos' hbw' hac hapos haw
  refine ⟨hom m b₁' b₂' a₁, hom m b₁' b₂' a₂, hc, hpos, hw, fun x hvx htx => ?_⟩
  set z := x ^ (p ^ (a + b)) with hz
  set w := u.eval x / v.eval x with hw_def
  have hz' : z = (x ^ (p ^ b)) ^ (p ^ a) := by rw [hz, ← pow_mul, ← pow_add, add_comm]
  have e₁ : b₁'.eval z = (u.eval x) ^ (p ^ a) := by
    rw [hz', hu, expand_eval, eval_pow_eq_eval_map_iterateFrobenius p]
  have e₂ : b₂'.eval z = (v.eval x) ^ (p ^ a) := by
    rw [hz', hv, expand_eval, eval_pow_eq_eval_map_iterateFrobenius p]
  have hb₂z : b₂'.eval z ≠ 0 := by rw [e₂]; exact pow_ne_zero _ hvx
  have hwz : w ^ (p ^ a) * b₂'.eval z = b₁'.eval z := by
    rw [e₁, e₂, hw_def, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hvx)]
  have hs' : s.eval w = a₁.eval (w ^ (p ^ a)) := by rw [hs, expand_eval]
  have ht' : t.eval w = a₂.eval (w ^ (p ^ a)) := by rw [ht, expand_eval]
  have hU : (expand k (p ^ (a + b)) (hom m b₁' b₂' a₁)).eval x = (b₂'.eval z) ^ m * s.eval w := by
    rw [expand_eval, ← hz, eval_hom (le_max_left _ _) hwz, hs']
  have hV : (expand k (p ^ (a + b)) (hom m b₁' b₂' a₂)).eval x = (b₂'.eval z) ^ m * t.eval w := by
    rw [expand_eval, ← hz, eval_hom (le_max_right _ _) hwz, ht']
  have hVne : (b₂'.eval z) ^ m * t.eval w ≠ 0 := mul_ne_zero (pow_ne_zero _ hb₂z) htx
  refine ⟨by rwa [hV], ?_⟩
  rw [hU, hV, mul_div_mul_left _ _ (pow_ne_zero _ hb₂z)]

end Comp

theorem eq_of_eval_eq_off_finite [Infinite k] {f g : k[X]} {S : Set k} (hS : S.Finite)
    (h : ∀ x, x ∉ S → f.eval x = g.eval x) : f = g := by
  apply eq_of_infinite_eval_eq
  apply Set.Infinite.mono (s := Sᶜ)
  · intro x hx; exact h x hx
  · exact hS.infinite_compl

theorem finite_fibre {u v : k[X]} (huv : IsCoprime u v) (h : 0 < max u.natDegree v.natDegree)
    (c : k) : {x : k | u.eval x = c * v.eval x}.Finite := by
  have hne : u - C c * v ≠ 0 := sub_ne_zero.mpr (ne_C_mul_of_isCoprime_of_pos huv h c)
  refine (finite_setOf_isRoot hne).subset ?_
  intro x hx
  simp only [Set.mem_setOf_eq] at hx ⊢
  simp [IsRoot, hx]

end DeuringMaxP.Poly

namespace DeuringMaxP

open WeierstrassCurve WeierstrassCurve.Affine Polynomial DeuringMaxP.Poly

variable {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k]

omit [DecidableEq k] in
theorem exists_nonsingular (W : WeierstrassCurve k) [W.IsElliptic] (x : k) :
    ∃ y, W.toAffine.Nonsingular x y := by
  set q : k[X] := X ^ 2 + C (W.a₁ * x + W.a₃) * X - C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)
    with hq
  have hdeg : q.degree = 2 := by
    rw [hq]; compute_degree!
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root q (by rw [hdeg]; decide)
  refine ⟨y, (Affine.equation_iff_nonsingular).mp ?_⟩
  rw [Affine.equation_iff]
  simp only [hq, IsRoot.def, eval_sub, eval_add, eval_pow, eval_X, eval_mul, eval_C] at hy
  linear_combination hy

section XPair

variable {W₁ W₂ W₃ : WeierstrassCurve k}

def IsXPair (f : W₁.toAffine.Point → W₂.toAffine.Point) (u v : k[X]) (B : Set k) : Prop :=
  IsCoprime u v ∧ 0 < max u.natDegree v.natDegree ∧ B.Finite ∧
    ∀ (x y : k) (h : W₁.toAffine.Nonsingular x y), x ∉ B →
      ∃ (x' y' : k) (h' : W₂.toAffine.Nonsingular x' y'),
        f (.some x y h) = .some x' y' h' ∧ x' * v.eval x = u.eval x

variable [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic]

theorem IsXPair.eval_ne_zero {f : W₁.toAffine.Point → W₂.toAffine.Point} {u v : k[X]} {B : Set k}
    (hf : IsXPair f u v B) {x : k} (hx : x ∉ B) : v.eval x ≠ 0 := by
  obtain ⟨y, hy⟩ := exists_nonsingular W₁ x
  obtain ⟨x', y', h', -, hx'⟩ := hf.2.2.2 x y hy hx
  intro hv
  rw [hv, mul_zero] at hx'
  exact eval_ne_zero_of_isCoprime hf.1 hv hx'.symm

theorem IsXPair.mul_eq_mul {f : W₁.toAffine.Point → W₂.toAffine.Point} {u₁ v₁ u₂ v₂ : k[X]}
    {B₁ B₂ : Set k} (h₁ : IsXPair f u₁ v₁ B₁) (h₂ : IsXPair f u₂ v₂ B₂) :
    u₁ * v₂ = u₂ * v₁ := by
  apply eq_of_eval_eq_off_finite (h₁.2.2.1.union h₂.2.2.1)
  intro x hx
  rw [Set.mem_union, not_or] at hx
  obtain ⟨y, hy⟩ := exists_nonsingular W₁ x
  obtain ⟨x₁, y₁, h₁', e₁, r₁⟩ := h₁.2.2.2 x y hy hx.1
  obtain ⟨x₂, y₂, h₂', e₂, r₂⟩ := h₂.2.2.2 x y hy hx.2
  rw [e₁] at e₂
  obtain ⟨rfl, -⟩ := (Affine.Point.some.injEq _ _ _ _ _ _).mp e₂
  rw [eval_mul, eval_mul, ← r₁, ← r₂]; ring

omit [W₂.IsElliptic] in

theorem exists_isXPair {α : W₁.toAffine.Point →+ W₂.toAffine.Point} [W₂.IsElliptic]
    (hα : α ∈ rationalHomSet k W₁ W₂) (hα0 : α ≠ 0) : ∃ u v B, IsXPair α u v B := by
  obtain ⟨u, v, B, huv, hB, hrep⟩ := WeierstrassCurve.exists_xCoord_rep_of_mem_rationalHomSet k W₁ W₂ hα hα0
  have hlt : v.natDegree < u.natDegree :=
    WeierstrassCurve.natDegree_lt_of_xCoord_rep W₁ W₂ α huv hB hrep
  exact ⟨u, v, B, huv, lt_of_lt_of_le (lt_of_le_of_lt (Nat.zero_le _) hlt) (le_max_left _ _), hB,
    hrep⟩

end XPair

section Height

variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable {W₁ W₂ W₃ : WeierstrassCurve k}

def HasHeight (f : W₁.toAffine.Point → W₂.toAffine.Point) (e : ℕ) : Prop :=
  ∃ (u v : k[X]) (B : Set k) (u₀ v₀ : k[X]), IsXPair f u v B ∧
    u = expand k (p ^ e) u₀ ∧ v = expand k (p ^ e) v₀ ∧
    IsCoprime u₀ v₀ ∧ 0 < max u₀.natDegree v₀.natDegree ∧ wronskian u₀ v₀ ≠ 0

variable [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic]

theorem hasHeight_unique {f : W₁.toAffine.Point → W₂.toAffine.Point} {a b : ℕ}
    (ha : HasHeight p f a) (hb : HasHeight p f b) : a = b := by
  obtain ⟨u₁, v₁, B₁, c₁, c₁', h₁, hu₁, hv₁, -, -, hw₁⟩ := ha
  obtain ⟨u₂, v₂, B₂, c₂, c₂', h₂, hu₂, hv₂, -, -, hw₂⟩ := hb
  exact expand_exponent_unique p h₁.1 h₂.1 (h₁.mul_eq_mul h₂) hu₁ hv₁ hu₂ hv₂ hw₁ hw₂

omit [W₂.IsElliptic] in
theorem exists_hasHeight [W₂.IsElliptic] {α : W₁.toAffine.Point →+ W₂.toAffine.Point}
    (hα : α ∈ rationalHomSet k W₁ W₂) (hα0 : α ≠ 0) : ∃ e, HasHeight p α e := by
  obtain ⟨u, v, B, h⟩ := exists_isXPair hα hα0
  obtain ⟨e, u₀, v₀, hu, hv, hc, hpos, hw⟩ := exists_expand_wronskian_ne_zero p h.1 h.2.1
  exact ⟨e, u, v, B, u₀, v₀, h, hu, hv, hc, hpos, hw⟩

theorem HasHeight.of_isXPair {f : W₁.toAffine.Point → W₂.toAffine.Point} {u v : k[X]} {B : Set k}
    (h : IsXPair f u v B) : ∃ e, HasHeight p f e := by
  obtain ⟨e, u₀, v₀, hu, hv, hc, hpos, hw⟩ := exists_expand_wronskian_ne_zero p h.1 h.2.1
  exact ⟨e, u, v, B, u₀, v₀, h, hu, hv, hc, hpos, hw⟩

theorem HasHeight.comp {f : W₂.toAffine.Point → W₃.toAffine.Point}
    {g : W₁.toAffine.Point → W₂.toAffine.Point} {a b : ℕ}
    (hf : HasHeight p f a) (hg : HasHeight p g b) : HasHeight p (f ∘ g) (a + b) := by
  obtain ⟨s, t, Bf, a₁, a₂, hfx, hs, ht, hac, hapos, haw⟩ := hf
  obtain ⟨u, v, Bg, b₁, b₂, hgx, hu, hv, hbc, hbpos, hbw⟩ := hg
  obtain ⟨U₀, V₀, hc, hpos, hw, hsem⟩ :=
    exists_comp_expand p hu hv hs ht hbc hbpos hbw hac hapos haw
  have hp : (p ^ (a + b)) ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  refine ⟨expand k (p ^ (a + b)) U₀, expand k (p ^ (a + b)) V₀,
    Bg ∪ ⋃ c ∈ Bf, {x : k | u.eval x = c * v.eval x}, U₀, V₀, ⟨?_, ?_, ?_, ?_⟩, rfl, rfl, hc, hpos, hw⟩
  · exact (isCoprime_expand hp).mpr hc
  · rw [natDegree_expand, natDegree_expand, Nat.mul_max_mul_right]
    exact Nat.mul_pos hpos (Nat.pos_of_ne_zero hp)
  · exact hgx.2.2.1.union (hfx.2.2.1.biUnion fun c _ => finite_fibre hgx.1 hgx.2.1 c)
  · intro x y h hx
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists] at hx
    obtain ⟨hxg, hxf⟩ := hx
    obtain ⟨x', y', h', e₁, r₁⟩ := hgx.2.2.2 x y h hxg
    have hvx : v.eval x ≠ 0 := hgx.eval_ne_zero hxg
    have hx' : x' = u.eval x / v.eval x := by rw [← r₁, mul_div_cancel_right₀ _ hvx]
    have hx'B : x' ∉ Bf := fun hmem => hxf x' hmem (by rw [← r₁])
    obtain ⟨x'', y'', h'', e₂, r₂⟩ := hfx.2.2.2 x' y' h' hx'B
    have htx : t.eval x' ≠ 0 := hfx.eval_ne_zero hx'B
    obtain ⟨hV, hUV⟩ := hsem x hvx (by rwa [← hx'])
    refine ⟨x'', y'', h'', by rw [Function.comp_apply, e₁, e₂], ?_⟩
    rw [← hx'] at hUV
    rw [← eq_div_iff hV, hUV, eq_div_iff htx, r₂]

theorem hasHeight_id : HasHeight p (id : W₁.toAffine.Point → W₁.toAffine.Point) 0 := by
  refine ⟨X, 1, ∅, X, 1, ⟨isCoprime_one_right, by simp, Set.finite_empty, ?_⟩, by simp, by simp,
    isCoprime_one_right, by simp, ?_⟩
  · intro x y h _
    exact ⟨x, y, h, rfl, by simp⟩
  · simp [wronskian]

theorem HasHeight.iterate {f : W₁.toAffine.Point → W₁.toAffine.Point} {e : ℕ} (hf : HasHeight p f e) :
    ∀ n : ℕ, HasHeight p (f^[n]) (n * e)
  | 0 => by simpa using hasHeight_id p
  | n + 1 => by
    rw [Function.iterate_succ', Nat.succ_mul, add_comm]
    exact HasHeight.comp p hf (HasHeight.iterate hf n)

end Height

section HomSet

open scoped Polynomial.Bivariate

variable {F : Type*} [Field F] (K : Type*) [Field K] [Algebra F K] [DecidableEq K]

theorem isRationallyRepresented_neg_id (W : WeierstrassCurve F) :
    IsRationallyRepresented K W W (-(AddMonoidHom.id _)) := by
  refine ⟨C X, 1, -Polynomial.X - C (C W.a₁ * X + C W.a₃), 1, ∅, Set.finite_empty,
    fun x y h _ => ?_⟩
  have e0 : evalEvalBC K (1 : F[X][Y]) x y = 1 := by simp [evalEvalBC, Polynomial.evalEval]
  have e1 : evalEvalBC K (C X : F[X][Y]) x y = x := by simp [evalEvalBC, Polynomial.evalEval]
  have e2 : evalEvalBC K (-Polynomial.X - C (C W.a₁ * X + C W.a₃) : F[X][Y]) x y =
      (W.baseChange K).toAffine.negY x y := by
    simp [evalEvalBC, Polynomial.evalEval, Affine.negY, WeierstrassCurve.baseChange]
    ring
  refine ⟨by rw [e0]; exact one_ne_zero, by rw [e0]; exact one_ne_zero, ?_⟩
  rw [e0, e1, e2, div_one, div_one, AddMonoidHom.neg_apply, AddMonoidHom.id_apply,
    Affine.Point.neg_some]
  exact ⟨_, rfl⟩

variable {K}

theorem neg_mem_rationalHomSet {W₁ W₂ : WeierstrassCurve F}
    {α : (W₁.baseChange K).toAffine.Point →+ (W₂.baseChange K).toAffine.Point}
    (hα : α ∈ rationalHomSet K W₁ W₂) : -α ∈ rationalHomSet K W₁ W₂ := by
  have h := WeierstrassCurve.comp_mem_rationalHomSet K W₁ W₂ W₂ hα
    (Or.inr (isRationallyRepresented_neg_id K W₂))
  have e : (-(AddMonoidHom.id _)).comp α = -α := by ext P; simp
  rwa [e] at h

variable [IsAlgClosed K]

theorem sub_mem_rationalHomSet {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic]
    {α β : (W₁.baseChange K).toAffine.Point →+ (W₂.baseChange K).toAffine.Point}
    (hα : α ∈ rationalHomSet K W₁ W₂) (hβ : β ∈ rationalHomSet K W₁ W₂) :
    α - β ∈ rationalHomSet K W₁ W₂ := by
  rw [sub_eq_add_neg]
  exact WeierstrassCurve.add_mem_rationalHomSet K W₁ W₂ hα (neg_mem_rationalHomSet hβ)

theorem zsmul_mem_rationalHomSet {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic]
    {α : (W₁.baseChange K).toAffine.Point →+ (W₂.baseChange K).toAffine.Point}
    (hα : α ∈ rationalHomSet K W₁ W₂) (n : ℤ) : n • α ∈ rationalHomSet K W₁ W₂ := by
  induction n using Int.induction_on with
  | zero => rw [zero_zsmul]; exact zero_mem_rationalHomSet K W₁ W₂
  | succ n ih =>
    rw [add_zsmul, one_zsmul]
    exact WeierstrassCurve.add_mem_rationalHomSet K W₁ W₂ ih hα
  | pred n ih =>
    rw [sub_zsmul, one_zsmul]
    exact sub_mem_rationalHomSet ih hα

end HomSet

section MulP

variable (p : ℕ) [Fact p.Prime] [CharP k p] (W : WeierstrassCurve k) [W.IsElliptic]

theorem wronskian_Φ_ΨSq_eq_zero : wronskian (W.Φ p) (W.ΨSq p) = 0 := by
  have h := WeierstrassCurve.Psi2Sq_mul_wronskian_sq W (p : ℤ)
  have hp : ((p : ℤ) : k) = 0 := by rw [Int.cast_natCast]; exact CharP.cast_eq_zero k p
  rw [hp, zero_pow two_ne_zero, C_0, zero_mul] at h
  have h2 := (mul_eq_zero.mp h).resolve_left (WeierstrassCurve.Psi2Sq_ne_zero_of_isElliptic W)
  have h3 : derivative (W.Φ p) * W.ΨSq p - W.Φ p * derivative (W.ΨSq p) = 0 := pow_eq_zero_iff
    two_ne_zero |>.mp h2
  rw [wronskian, ← neg_eq_zero, neg_sub', sub_neg_eq_add]
  linear_combination h3

theorem ΨSq_ne_zero : W.ΨSq p ≠ 0 := by
  intro h0
  have hc := WeierstrassCurve.isCoprime_Phi_PsiSq W (p : ℤ)
  rw [h0, isCoprime_zero_right] at hc
  have := natDegree_eq_zero_of_isUnit hc
  rw [WeierstrassCurve.natDegree_Φ] at this
  simp [(Fact.out : p.Prime).ne_zero] at this

theorem isXPair_mulP :
    IsXPair (fun P : W.toAffine.Point => (p : ℤ) • P) (W.Φ p) (W.ΨSq p) {x | (W.ΨSq p).IsRoot x} := by
  refine ⟨WeierstrassCurve.isCoprime_Phi_PsiSq W p, ?_, finite_setOf_isRoot (ΨSq_ne_zero p W), ?_⟩
  · rw [WeierstrassCurve.natDegree_Φ]
    exact lt_of_lt_of_le (by simp [(Fact.out : p.Prime).pos]) (le_max_left _ _)
  · intro x y h hx
    simp only [Set.mem_setOf_eq, IsRoot.def] at hx
    have hψ : (W.ψ p).evalEval x y ≠ 0 := by
      intro h0
      have := WeierstrassCurve.Affine.evalEval_psi_sq W h.1 (p : ℤ)
      rw [h0] at this
      exact hx (by simpa using this.symm)
    obtain ⟨y', h', e⟩ := WeierstrassCurve.Affine.Point.zsmul_some_eq_some_div W h hψ
    exact ⟨_, y', h', e, div_mul_cancel₀ _ hx⟩

theorem exists_mulP_core : ∃ (π : ℕ) (r₁ r₂ : k[X]), 1 ≤ π ∧
    W.Φ p = expand k (p ^ π) r₁ ∧ W.ΨSq p = expand k (p ^ π) r₂ ∧
    IsCoprime r₁ r₂ ∧ 0 < max r₁.natDegree r₂.natDegree ∧ wronskian r₁ r₂ ≠ 0 := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hcop := WeierstrassCurve.isCoprime_Phi_PsiSq W (p : ℤ)
  obtain ⟨hd1, hd2⟩ := hcop.wronskian_eq_zero_iff.mp (wronskian_Φ_ΨSq_eq_zero p W)
  have e1 : W.Φ p = expand k p (contract p (W.Φ p)) := (expand_contract p hd1 hp).symm
  have e2 : W.ΨSq p = expand k p (contract p (W.ΨSq p)) := (expand_contract p hd2 hp).symm
  have hcop' : IsCoprime (contract p (W.Φ p)) (contract p (W.ΨSq p)) := by
    rw [e1, e2, isCoprime_expand hp] at hcop; exact hcop
  have hpos' : 0 < max (contract p (W.Φ p)).natDegree (contract p (W.ΨSq p)).natDegree := by
    refine lt_of_lt_of_le ?_ (le_max_left _ _)
    have hdeg : (W.Φ p).natDegree = (contract p (W.Φ p)).natDegree * p := by
      conv_lhs => rw [e1]
      rw [natDegree_expand]
    rw [WeierstrassCurve.natDegree_Φ] at hdeg
    by_contra h0
    push Not at h0
    have : (contract p (W.Φ (p : ℤ))).natDegree = 0 := by omega
    rw [this, zero_mul] at hdeg
    simp [hp] at hdeg
  obtain ⟨e, r₁, r₂, hr₁, hr₂, hc, hpos, hw⟩ := exists_expand_wronskian_ne_zero p hcop' hpos'
  refine ⟨e + 1, r₁, r₂, Nat.le_add_left 1 e, ?_, ?_, hc, hpos, hw⟩
  · rw [e1, hr₁, expand_expand, pow_succ']
  · rw [e2, hr₂, expand_expand, pow_succ']

end MulP

section Iterate

variable {G : Type*} [AddCommGroup G]

theorem exists_iterate_eq (δ : G →+ G) (p t' q' : ℤ)
    (hδδ : ∀ P, δ (δ P) = (p * t') • δ P - (p ^ 2 * q') • P) (n : ℕ) :
    ∃ a b : ℤ, ∀ P, (δ : G → G)^[n + 1] P = (p ^ n) • (a • δ P + (p * b) • P) := by
  induction n with
  | zero => exact ⟨1, 0, fun P => by simp⟩
  | succ n ih =>
    obtain ⟨a, b, hab⟩ := ih
    refine ⟨a * t' + b, -(a * q'), fun P => ?_⟩
    rw [Function.iterate_succ_apply', hab, map_zsmul, map_add, map_zsmul, map_zsmul, hδδ]
    module

theorem iterate_zsmul (c : ℤ) (n : ℕ) :
    (fun P : G => c • P)^[n] = fun P => (c ^ n) • P := by
  induction n with
  | zero => funext P; simp
  | succ n ih =>
    funext P
    rw [Function.iterate_succ_apply', ih, smul_smul, pow_succ']

end Iterate

section Main

variable (p : ℕ) [Fact p.Prime] [CharP k p] (W : WeierstrassCurve k) [W.IsElliptic]

theorem some_ne_zero' {x y : k} (h : W.toAffine.Nonsingular x y) :
    (Affine.Point.some x y h : W.toAffine.Point) ≠ 0 := by
  intro h0; cases h0

theorem main {β : W.toAffine.Point →+ W.toAffine.Point}
    (hβ : β ∈ WeierstrassCurve.rationalHomSet k W W) (t q : ℤ)
    (hchar : β.comp β + q • AddMonoidHom.id _ = t • β) (k₀ : ℤ) (h₁ : (p : ℤ) ∣ t - 2 * k₀)
    (h₂ : (p : ℤ) ^ 2 ∣ k₀ ^ 2 - t * k₀ + q) :
    ∃ γ ∈ WeierstrassCurve.rationalHomSet k W W, β - k₀ • AddMonoidHom.id _ = (p : ℤ) • γ := by
  obtain ⟨t', ht'⟩ := h₁
  obtain ⟨q', hq'⟩ := h₂
  set δ : W.toAffine.Point →+ W.toAffine.Point := β - k₀ • AddMonoidHom.id _ with hδ_def
  have hidmem : (AddMonoidHom.id _ : W.toAffine.Point →+ W.toAffine.Point) ∈ rationalHomSet k W W :=
    id_mem_rationalHomSet k W
  have hδmem : δ ∈ rationalHomSet k W W :=
    sub_mem_rationalHomSet (K := k) hβ (zsmul_mem_rationalHomSet (K := k) hidmem k₀)

  have hδδ : ∀ P, δ (δ P) = ((p : ℤ) * t') • δ P - ((p : ℤ) ^ 2 * q') • P := by
    intro P
    have e1 : β (β P) + q • P = t • β P := by
      have := DFunLike.congr_fun hchar P
      simpa using this
    have e2 : ∀ Q, δ Q = β Q - k₀ • Q := fun Q => by simp [hδ_def]
    rw [e2, e2, map_sub, map_zsmul, eq_sub_of_add_eq e1]
    have hq : q = (p : ℤ) ^ 2 * q' - k₀ ^ 2 + t * k₀ := by linarith
    have ht : t = (p : ℤ) * t' + 2 * k₀ := by linarith
    rw [hq, ht]
    module
  by_cases hδ0 : δ = 0
  · exact ⟨0, zero_mem_rationalHomSet k W W, by rw [smul_zero]; exact hδ0⟩
  have hδsurj : Function.Surjective δ :=
    WeierstrassCurve.surjective_of_mem_rationalHomSet k hδmem hδ0

  obtain ⟨π, r₁, r₂, hπ1, hΦ, hΨ, hrc, hrpos, hrw⟩ := exists_mulP_core p W
  have hPpair := isXPair_mulP p W
  have hHp : HasHeight p (fun P : W.toAffine.Point => (p : ℤ) • P) π :=
    ⟨_, _, _, r₁, r₂, hPpair, hΦ, hΨ, hrc, hrpos, hrw⟩
  have hHpn : ∀ n : ℕ, HasHeight p (fun P : W.toAffine.Point => ((p : ℤ) ^ n) • P) (n * π) := by
    intro n
    rw [← iterate_zsmul]
    exact HasHeight.iterate p hHp n

  obtain ⟨e, hHe⟩ := exists_hasHeight p hδmem hδ0
  have hle : π ≤ e := by
    obtain ⟨a, b, hab⟩ := exists_iterate_eq δ p t' q' hδδ π
    set ε : W.toAffine.Point →+ W.toAffine.Point := a • δ + ((p : ℤ) * b) • AddMonoidHom.id _
      with hε_def
    have hεmem : ε ∈ rationalHomSet k W W :=
      WeierstrassCurve.add_mem_rationalHomSet k W W (zsmul_mem_rationalHomSet (K := k) hδmem a)
        (zsmul_mem_rationalHomSet (K := k) hidmem _)
    have heqf : (δ : W.toAffine.Point → W.toAffine.Point)^[π + 1] =
        (fun P : W.toAffine.Point => ((p : ℤ) ^ π) • P) ∘ ε := by
      funext P
      rw [hab P, Function.comp_apply]
      simp [hε_def]
    have hε0 : ε ≠ 0 := by
      intro h0
      obtain ⟨y, hy⟩ := exists_nonsingular W 0
      obtain ⟨Q, hQ⟩ := (hδsurj.iterate (π + 1)) (Affine.Point.some 0 y hy)
      rw [heqf, h0] at hQ
      exact some_ne_zero' W hy (by rw [← hQ]; simp)
    obtain ⟨eε, hHε⟩ := exists_hasHeight p hεmem hε0
    have H1 : HasHeight p ((δ : W.toAffine.Point → W.toAffine.Point)^[π + 1]) ((π + 1) * e) :=
      HasHeight.iterate p hHe (π + 1)
    have H2 : HasHeight p ((fun P : W.toAffine.Point => ((p : ℤ) ^ π) • P) ∘ ε) (π * π + eε) :=
      (hHpn π).comp p hHε
    rw [heqf] at H1
    have hEq : (π + 1) * e = π * π + eε := hasHeight_unique p H1 H2
    by_contra hlt
    push Not at hlt
    have h3 : (π + 1) * (e + 1) ≤ (π + 1) * π := Nat.mul_le_mul_left (π + 1) hlt
    nlinarith

  obtain ⟨u, v, Bδ, c₁, c₂, hδpair, hu, hv, hcc, hcpos, hcw⟩ := hHe
  set d₁ := expand k (p ^ (e - π)) c₁ with hd₁
  set d₂ := expand k (p ^ (e - π)) c₂ with hd₂
  have hpe : p ^ e = p ^ π * p ^ (e - π) := by rw [← pow_add, Nat.add_sub_cancel' hle]
  have hu' : u = expand k (p ^ π) d₁ := by rw [hu, hd₁, expand_expand, ← hpe]
  have hv' : v = expand k (p ^ π) d₂ := by rw [hv, hd₂, expand_expand, ← hpe]
  have hd : IsCoprime d₁ d₂ :=
    (isCoprime_expand (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)).mpr hcc

  have hker : ∀ T : W.toAffine.Point, (p : ℤ) • T = 0 → δ T = 0 := by
    obtain ⟨T₀, hT₀, hgen⟩ := WeierstrassCurve.exists_forall_mem_zmultiples_of_char_nsmul_eq_zero p W
    have hT₀' : (p : ℤ) • T₀ = 0 := by rw [natCast_zsmul]; exact hT₀
    have hpT : p • δ T₀ = 0 := by rw [← map_nsmul, hT₀, map_zero]
    obtain ⟨c, hc⟩ := AddSubgroup.mem_zmultiples_iff.mp (hgen _ hpT)
    have key : δ T₀ = 0 := by
      by_cases h0 : T₀ = 0
      · rw [← hc, h0, smul_zero]
      have hord : addOrderOf T₀ = p := addOrderOf_eq_prime hT₀ h0
      have h2 : (c * c) • T₀ = 0 := by
        have h3 := hδδ T₀
        rw [← hc, map_zsmul, ← hc, smul_smul] at h3
        rw [h3, show ((p : ℤ) * t') • c • T₀ = (t' * c) • ((p : ℤ) • T₀) by module,
          show ((p : ℤ) ^ 2 * q') • T₀ = ((p : ℤ) * q') • ((p : ℤ) • T₀) by module, hT₀']
        simp
      have hdvd : (p : ℤ) ∣ c * c := by
        rw [← hord, addOrderOf_dvd_iff_zsmul_eq_zero]; exact h2
      have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
      obtain ⟨d, hd⟩ : (p : ℤ) ∣ c := (hpp.dvd_or_dvd hdvd).elim id id
      rw [← hc, hd, mul_comm, mul_smul, hT₀', smul_zero]
    intro T hT
    have hT' : p • T = 0 := by rw [← natCast_zsmul]; exact hT
    obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp (hgen T hT')
    rw [← hm, map_zsmul, key, smul_zero]

  set ρ : W.toAffine.Point →+ W.toAffine.Point := (p : ℤ) • AddMonoidHom.id _ with hρ_def
  have hρmem : ρ ∈ rationalHomSet k W W := zsmul_mem_rationalHomSet (K := k) hidmem _
  have hρapply : ∀ P, ρ P = (p : ℤ) • P := fun P => by simp [hρ_def]
  set B : Set k := {x | (W.ΨSq p).IsRoot x} ∪ Bδ with hB_def
  have hBfin : B.Finite := hPpair.2.2.1.union hδpair.2.2.1
  have hρ0 : ρ ≠ 0 := by
    obtain ⟨x, hx⟩ := hBfin.infinite_compl.nonempty
    obtain ⟨y, hy⟩ := exists_nonsingular W x
    obtain ⟨x', y', h', e1, -⟩ := hPpair.2.2.2 x y hy (fun h => hx (Or.inl h))
    intro h0
    have : ρ (Affine.Point.some x y hy) = 0 := by rw [h0]; rfl
    rw [hρapply] at this
    exact some_ne_zero' W h' (by rw [← e1]; exact this)
  have hρx : ∀ (x y : k) (h : W.toAffine.Nonsingular x y), x ∉ B →
      ∃ (x' y' : k) (h' : W.toAffine.Nonsingular x' y'),
        ρ (Affine.Point.some x y h) = Affine.Point.some x' y' h' ∧
          x' * r₂.eval (x ^ p ^ π) = r₁.eval (x ^ p ^ π) := by
    intro x y h hx
    obtain ⟨x', y', h', e1, r1⟩ := hPpair.2.2.2 x y h (fun h => hx (Or.inl h))
    refine ⟨x', y', h', by rw [hρapply]; exact e1, ?_⟩
    rw [← expand_eval, ← expand_eval, ← hΦ, ← hΨ]; exact r1
  have hδx : ∀ (x y : k) (h : W.toAffine.Nonsingular x y), x ∉ B →
      ∃ (x' y' : k) (h' : W.toAffine.Nonsingular x' y'),
        δ (Affine.Point.some x y h) = Affine.Point.some x' y' h' ∧
          x' * d₂.eval (x ^ p ^ π) = d₁.eval (x ^ p ^ π) := by
    intro x y h hx
    obtain ⟨x', y', h', e1, r1⟩ := hδpair.2.2.2 x y h (fun h => hx (Or.inr h))
    refine ⟨x', y', h', e1, ?_⟩
    rw [← expand_eval, ← expand_eval, ← hu', ← hv']; exact r1
  obtain ⟨γ, hγ, hγeq⟩ :=
    WeierstrassCurve.exists_mem_rationalHomSet_comp_eq_of_ker_le_of_xCoord_expand p W W W
      hρmem hδmem hρ0 hδ0 (fun T hT => hker T (by rw [← hρapply]; exact hT)) π hrc hrw hd hBfin
      hρx hδx
  refine ⟨γ, hγ, ?_⟩
  have hfin : δ = (p : ℤ) • γ := by
    rw [hγeq]
    ext P
    change γ (ρ P) = ((p : ℤ) • γ) P
    rw [hρapply]
    have h1 : γ ((p : ℤ) • P) = (p : ℤ) • γ P := γ.map_zsmul p P
    have h2 : ((p : ℤ) • γ) P = (p : ℤ) • γ P := by simp
    exact h1.trans h2.symm
  exact hfin

end Main

end DeuringMaxP

theorem solution {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k] (p : ℕ) [Fact p.Prime] [CharP k p] (W : WeierstrassCurve k) [W.IsElliptic] {β : W.toAffine.Point →+ W.toAffine.Point} (hβ : β ∈ WeierstrassCurve.rationalHomSet k W W) (t q : ℤ) (hchar : β.comp β + q • AddMonoidHom.id _ = t • β) (k₀ : ℤ) (h₁ : (p : ℤ) ∣ t - 2 * k₀) (h₂ : (p : ℤ) ^ 2 ∣ k₀ ^ 2 - t * k₀ + q) : ∃ γ ∈ WeierstrassCurve.rationalHomSet k W W, β - k₀ • AddMonoidHom.id _ = (p : ℤ) • γ :=
  DeuringMaxP.main p W hβ t q hchar k₀ h₁ h₂

end S_WeierstrassCurve_exists_mem_rationalHomSet_sub_smul_id_eq_char_smul_of_dvd_of_sq_dvd
end P2MW
export P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_sub_smul_id_eq_char_smul_of_dvd_of_sq_dvd (solution)
