-- Prove2me | solution 1 for WeierstrassCurve.exists_mem_rationalHomSet_comp_eq_of_ker_le_of_xCoord_expand
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/0b80ccf5-bbcf-5d5b-83c8-10f32d1e2786

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Theorems.Thm_Polynomial_isCoprime_and_wronskian_ne_zero_comp_of_wronskian_ne_zero
import Theorems.Thm_Polynomial_exists_frobenius_iterate_eq_rational_of_comp_rational_eq_rational
import Theorems.Thm_WeierstrassCurve_exists_frobenius_comp_rational_of_comp_eq_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_Psi2Sq_ne_zero_of_isElliptic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_comp_eq_of_ker_le_of_xCoord_expand

open Polynomial

namespace FactorP
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

end FactorP.Poly

namespace FactorP

open WeierstrassCurve WeierstrassCurve.Affine Polynomial FactorP.Poly

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

def xco {W : WeierstrassCurve k} : W.toAffine.Point → k
  | 0 => 0
  | .some x _ _ => x

omit [IsAlgClosed k] [DecidableEq k] in
@[scoped simp] theorem xco_some {W : WeierstrassCurve k} {x y : k} (h : W.toAffine.Nonsingular x y) :
    xco (.some x y h) = x := rfl

omit [IsAlgClosed k] in
theorem xco_neg {W : WeierstrassCurve k} (P : W.toAffine.Point) : xco (-P) = xco P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [Affine.Point.neg_some]; rfl

omit [IsAlgClosed k] in

theorem eq_or_eq_neg_of_x_eq {W : WeierstrassCurve k} {x y₁ y₂ : k} (h₁ : W.toAffine.Nonsingular x y₁)
    (h₂ : W.toAffine.Nonsingular x y₂) :
    (Affine.Point.some x y₁ h₁ : W.toAffine.Point) = .some x y₂ h₂ ∨
      (Affine.Point.some x y₁ h₁ : W.toAffine.Point) = -.some x y₂ h₂ := by
  rcases Affine.Y_eq_of_X_eq h₁.1 h₂.1 rfl with h | h
  · left; subst h; rfl
  · right; rw [Affine.Point.neg_some]; subst h; rfl

noncomputable def pt (W : WeierstrassCurve k) [W.IsElliptic] (c : k) : W.toAffine.Point :=
  .some c (Classical.choose (exists_nonsingular W c)) (Classical.choose_spec (exists_nonsingular W c))

omit [DecidableEq k] in
theorem xco_pt (W : WeierstrassCurve k) [W.IsElliptic] (c : k) : xco (pt W c) = c := rfl

theorem some_eq_pt_or {W : WeierstrassCurve k} [W.IsElliptic] {x y : k} (h : W.toAffine.Nonsingular x y) :
    (Affine.Point.some x y h : W.toAffine.Point) = pt W x ∨ (Affine.Point.some x y h : W.toAffine.Point) = -pt W x :=
  eq_or_eq_neg_of_x_eq h _

theorem xco_map_some_eq {W W' : WeierstrassCurve k} [W.IsElliptic] (f : W.toAffine.Point →+ W'.toAffine.Point)
    {x y : k} (h : W.toAffine.Nonsingular x y) : xco (f (.some x y h)) = xco (f (pt W x)) := by
  rcases some_eq_pt_or h with e | e
  · rw [e]
  · rw [e, map_neg, xco_neg]

omit [DecidableEq k] in
theorem infinite_point (W : WeierstrassCurve k) [W.IsElliptic] : Infinite W.toAffine.Point :=
  Infinite.of_injective (pt W) fun a b hab => by
    have := congr_arg xco hab
    rwa [xco_pt, xco_pt] at this

omit [IsAlgClosed k] in

theorem finite_fibre_pt (W : WeierstrassCurve k) (c : k) :
    {P : W.toAffine.Point | ∃ (y : k) (h : W.toAffine.Nonsingular c y), P = .some c y h}.Finite := by
  have hne : (W.toAffine.polynomial.map (evalRingHom c)) ≠ 0 :=
    (WeierstrassCurve.Affine.monic_polynomial.map _).ne_zero
  have hfin : (⋃ y ∈ {y : k | W.toAffine.Equation c y},
      {P : W.toAffine.Point | ∃ h : W.toAffine.Nonsingular c y, P = .some c y h}).Finite := by
    refine Set.Finite.biUnion ?_ fun y _ => ?_
    · refine (Polynomial.finite_setOf_isRoot hne).subset ?_
      intro y hy
      simp only [Set.mem_setOf_eq, IsRoot.def, map_evalRingHom_eval]
      exact hy
    · refine Set.Subsingleton.finite ?_
      rintro P ⟨h1, rfl⟩ Q ⟨h2, rfl⟩
      rfl
  refine hfin.subset ?_
  rintro P ⟨y, h, rfl⟩
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  exact ⟨y, h.left, h, rfl⟩

theorem not_const_abscissa {W₁ W₃ : WeierstrassCurve k} [W₁.IsElliptic] [W₃.IsElliptic]
    {δ : W₁.toAffine.Point → W₃.toAffine.Point} (hsurj : Function.Surjective δ) {B : Set k}
    (hB : B.Finite) (c : k)
    (hrep : ∀ (x y : k) (h : W₁.toAffine.Nonsingular x y), x ∉ B →
      ∃ (y' : k) (h' : W₃.toAffine.Nonsingular c y'), δ (.some x y h) = .some c y' h') : False := by
  haveI := infinite_point W₃

  set F : Set W₁.toAffine.Point := insert 0 (⋃ x ∈ B, {P | ∃ (y : k) (h : W₁.toAffine.Nonsingular x y),
    P = .some x y h}) with hF
  have hFfin : F.Finite := (hB.biUnion fun x _ => finite_fibre_pt W₁ x).insert 0
  have hcover : (Set.univ : Set W₃.toAffine.Point) ⊆
      δ '' F ∪ {Q | ∃ (y : k) (h : W₃.toAffine.Nonsingular c y), Q = .some c y h} := by
    intro Q _
    obtain ⟨P, rfl⟩ := hsurj Q
    rcases P with _ | ⟨x, y, h⟩
    · exact Or.inl ⟨0, by simp [hF], rfl⟩
    · by_cases hx : x ∈ B
      · left
        refine ⟨.some x y h, ?_, rfl⟩
        rw [hF]
        refine Set.mem_insert_of_mem _ ?_
        simp only [Set.mem_iUnion, Set.mem_setOf_eq]
        exact ⟨x, hx, y, h, rfl⟩
      · right
        obtain ⟨y', h', e⟩ := hrep x y h hx
        exact ⟨y', h', e⟩
  have hfin : (Set.univ : Set W₃.toAffine.Point).Finite :=
    ((hFfin.image δ).union (finite_fibre_pt W₃ c)).subset hcover
  exact Set.infinite_univ hfin

noncomputable def UV (W : WeierstrassCurve k) : ℕ → k[X] × k[X]
  | 0 => (0, 1)
  | n + 1 => ((UV W n).2 - (C W.a₁ * X + C W.a₃) * (UV W n).1,
      (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆) * (UV W n).1)

omit [IsAlgClosed k] [DecidableEq k] in
theorem pow_eq_UV (W : WeierstrassCurve k) {x y : k} (h : W.toAffine.Equation x y) (n : ℕ) :
    y ^ n = ((UV W n).1).eval x * y + ((UV W n).2).eval x := by
  induction n with
  | zero => simp [UV]
  | succ n ih =>
    rw [Affine.equation_iff] at h
    have hy2 : y ^ 2 = -(W.a₁ * x + W.a₃) * y + (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) := by
      linear_combination h
    simp only [UV, eval_sub, eval_mul, eval_add, eval_pow, eval_C, eval_X]
    rw [pow_succ, ih]
    linear_combination (((UV W n).1).eval x) * hy2

omit [IsAlgClosed k] [DecidableEq k] in

theorem UV_mul_sub (p : ℕ) [Fact p.Prime] [CharP k p] (W : WeierstrassCurve k) {x y : k}
    (h : W.toAffine.Equation x y) (j : ℕ) :
    ((UV W (p ^ j)).1).eval x * (y - W.toAffine.negY x y) = (y - W.toAffine.negY x y) ^ (p ^ j) := by
  have h' : W.toAffine.Equation x (W.toAffine.negY x y) := (Affine.equation_neg x y).mpr h
  have e1 := pow_eq_UV W h (p ^ j)
  have e2 := pow_eq_UV W h' (p ^ j)
  rw [sub_pow_char_pow, e1, e2]
  ring

omit [IsAlgClosed k] [DecidableEq k] in

theorem sub_negY_sq (W : WeierstrassCurve k) {x y : k} (h : W.toAffine.Equation x y) :
    (y - W.toAffine.negY x y) ^ 2 = W.Ψ₂Sq.eval x := by
  rw [Affine.equation_iff] at h
  simp only [Affine.negY, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  linear_combination (4 : k) * h

omit [IsAlgClosed k] [DecidableEq k] in
theorem UV_eval_ne_zero (p : ℕ) [Fact p.Prime] [CharP k p] (W : WeierstrassCurve k) {x y : k}
    (h : W.toAffine.Equation x y) (hx : W.Ψ₂Sq.eval x ≠ 0) (j : ℕ) :
    ((UV W (p ^ j)).1).eval x ≠ 0 := by
  intro h0
  have e := UV_mul_sub p W h j
  rw [h0, zero_mul] at e
  have : y - W.toAffine.negY x y = 0 := pow_eq_zero_iff (pow_ne_zero j (Fact.out : p.Prime).ne_zero) |>.mp e.symm
  apply hx
  rw [← sub_negY_sq W h, this, zero_pow two_ne_zero]

end FactorP
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_comp_eq_of_ker_le_of_xCoord_expand.FactorP"

namespace FactorP

open WeierstrassCurve WeierstrassCurve.Affine Polynomial FactorP.Poly
open scoped Polynomial.Bivariate

variable {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]

omit [IsAlgClosed k] [DecidableEq k] [Fact p.Prime] [CharP k p] in

theorem some_eq_of_x_eq {W : WeierstrassCurve k} {x₁ x₂ y : k} (h : W.toAffine.Nonsingular x₁ y)
    (hx : x₁ = x₂) : ∃ h', (Affine.Point.some x₁ y h : W.toAffine.Point) = .some x₂ y h' := by
  subst hx; exact ⟨h, rfl⟩

omit [IsAlgClosed k] [DecidableEq k] [Fact p.Prime] [CharP k p] in

theorem evalEvalBC_self (P : k[X][Y]) (x y : k) : evalEvalBC k P x y = P.evalEval x y := by
  simp [evalEvalBC, Algebra.algebraMap_self, Polynomial.map_id]

section MainProof

variable {W₁ W₂ W₃ : WeierstrassCurve k} [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic]
  {ρ : W₁.toAffine.Point →+ W₂.toAffine.Point} {δ : W₁.toAffine.Point →+ W₃.toAffine.Point}
  (e : ℕ) {r₁ r₂ d₁ d₂ : k[X]} (hr : IsCoprime r₁ r₂) (hd : IsCoprime d₁ d₂) {B : Set k}
  (hρx : ∀ (x y : k) (h : W₁.toAffine.Nonsingular x y), x ∉ B →
    ∃ (x' y' : k) (h' : W₂.toAffine.Nonsingular x' y'),
      ρ (.some x y h) = .some x' y' h' ∧ x' * r₂.eval (x ^ p ^ e) = r₁.eval (x ^ p ^ e))
  (hδx : ∀ (x y : k) (h : W₁.toAffine.Nonsingular x y), x ∉ B →
    ∃ (x' y' : k) (h' : W₃.toAffine.Nonsingular x' y'),
      δ (.some x y h) = .some x' y' h' ∧ x' * d₂.eval (x ^ p ^ e) = d₁.eval (x ^ p ^ e))

include hr hρx in
theorem ρ_val {x : k} (hx : x ∉ B) (y : k) (h : W₁.toAffine.Nonsingular x y) :
    r₂.eval (x ^ p ^ e) ≠ 0 ∧ ∃ (y₂ : k) (h₂ : W₂.toAffine.Nonsingular (r₁.eval (x ^ p ^ e) / r₂.eval (x ^ p ^ e)) y₂),
      ρ (.some x y h) = .some _ y₂ h₂ := by
  obtain ⟨x', y', h', e1, r1⟩ := hρx x y h hx
  have hr2 : r₂.eval (x ^ p ^ e) ≠ 0 := fun h0 =>
    eval_ne_zero_of_isCoprime hr h0 (by rw [← r1, h0, mul_zero])
  have hx' : x' = r₁.eval (x ^ p ^ e) / r₂.eval (x ^ p ^ e) := by rw [← r1, mul_div_cancel_right₀ _ hr2]
  subst hx'
  exact ⟨hr2, y', h', e1⟩

include hd hδx in
theorem δ_val {x : k} (hx : x ∉ B) (y : k) (h : W₁.toAffine.Nonsingular x y) :
    d₂.eval (x ^ p ^ e) ≠ 0 ∧ ∃ (y₃ : k) (h₃ : W₃.toAffine.Nonsingular (d₁.eval (x ^ p ^ e) / d₂.eval (x ^ p ^ e)) y₃),
      δ (.some x y h) = .some _ y₃ h₃ := by
  obtain ⟨x', y', h', e1, r1⟩ := hδx x y h hx
  have hd2 : d₂.eval (x ^ p ^ e) ≠ 0 := fun h0 =>
    eval_ne_zero_of_isCoprime hd h0 (by rw [← r1, h0, mul_zero])
  have hx' : x' = d₁.eval (x ^ p ^ e) / d₂.eval (x ^ p ^ e) := by rw [← r1, mul_div_cancel_right₀ _ hd2]
  subst hx'
  exact ⟨hd2, y', h', e1⟩

include hd hδx in

theorem d_pos (hδsurj : Function.Surjective δ) (hB : B.Finite) : 0 < max d₁.natDegree d₂.natDegree := by
  by_contra h0
  push Not at h0
  have e1 : d₁ = C (d₁.coeff 0) := eq_C_of_natDegree_eq_zero (by omega)
  have e2 : d₂ = C (d₂.coeff 0) := eq_C_of_natDegree_eq_zero (by omega)
  refine not_const_abscissa hδsurj hB (d₁.coeff 0 / d₂.coeff 0) fun x y h hx => ?_
  obtain ⟨-, y₃, h₃, e3⟩ := δ_val p e hd hδx hx y h
  have hc : d₁.eval (x ^ p ^ e) / d₂.eval (x ^ p ^ e) = d₁.coeff 0 / d₂.coeff 0 := by
    conv_lhs => rw [e1, e2, eval_C, eval_C]
  obtain ⟨h', e4⟩ := some_eq_of_x_eq h₃ hc
  exact ⟨y₃, h', e3.trans e4⟩

include hr hd hρx hδx in
theorem main (hρ : ρ ∈ rationalHomSet k W₁ W₂) (hδ : δ ∈ rationalHomSet k W₁ W₃) (hρ0 : ρ ≠ 0)
    (hδ0 : δ ≠ 0) (hker : ∀ T : W₁.toAffine.Point, ρ T = 0 → δ T = 0)
    (hrw : wronskian r₁ r₂ ≠ 0) (hB : B.Finite) :
    ∃ γ ∈ rationalHomSet k W₂ W₃, δ = γ.comp ρ := by
  have hp : p.Prime := Fact.out
  have hchar : ringExpChar k = p := ringExpChar.eq k p

  have hρsurj : Function.Surjective ρ := WeierstrassCurve.surjective_of_mem_rationalHomSet k hρ hρ0
  have hδsurj : Function.Surjective δ := WeierstrassCurve.surjective_of_mem_rationalHomSet k hδ hδ0
  have hkerle : ρ.ker ≤ δ.ker := fun T hT => by
    rw [AddMonoidHom.mem_ker] at hT ⊢; exact hker T hT
  set μ : W₂.toAffine.Point →+ W₃.toAffine.Point :=
    ρ.liftOfRightInverse (Function.surjInv hρsurj) (Function.rightInverse_surjInv hρsurj) ⟨δ, hkerle⟩
    with hμ_def
  have hμρ : ∀ P, μ (ρ P) = δ P := fun P =>
    ρ.liftOfRightInverse_comp_apply _ _ ⟨δ, hkerle⟩ P
  have hμcomp : μ.comp ρ = δ := AddMonoidHom.ext hμρ
  suffices hμmem : μ ∈ rationalHomSet k W₂ W₃ from ⟨μ, hμmem, hμcomp.symm⟩

  have hrpos : 0 < max r₁.natDegree r₂.natDegree := max_natDegree_pos_of_wronskian_ne_zero hrw
  have hdpos : 0 < max d₁.natDegree d₂.natDegree := d_pos p e hd hδx hδsurj hB
  have hq0 : p ^ e ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hrE : IsCoprime (expand k (p ^ e) r₁) (expand k (p ^ e) r₂) := (isCoprime_expand hq0).mpr hr
  have hrEpos : 0 < max (expand k (p ^ e) r₁).natDegree (expand k (p ^ e) r₂).natDegree := by
    rw [natDegree_expand, natDegree_expand, Nat.mul_max_mul_right]
    exact Nat.mul_pos hrpos (Nat.pos_of_ne_zero hq0)
  have hfne : ∀ c : k, expand k (p ^ e) r₁ ≠ C c * expand k (p ^ e) r₂ :=
    ne_C_mul_of_isCoprime_of_pos hrE hrEpos

  set m : k → k := fun c => xco (μ (pt W₂ c)) with hm_def
  have hm : ∀ x, x ∉ B → m (r₁.eval (x ^ p ^ e) / r₂.eval (x ^ p ^ e)) =
      d₁.eval (x ^ p ^ e) / d₂.eval (x ^ p ^ e) := by
    intro x hx
    obtain ⟨y, h⟩ := exists_nonsingular W₁ x
    obtain ⟨-, y₂, h₂, e2⟩ := ρ_val p e hr hρx hx y h
    obtain ⟨-, y₃, h₃, e3⟩ := δ_val p e hd hδx hx y h
    have := xco_map_some_eq μ h₂
    rw [← e2, hμρ, e3, xco_some] at this
    exact this.symm

  obtain ⟨t, hn, hd', T, hT, hdesc⟩ :=
    Polynomial.exists_frobenius_iterate_eq_rational_of_comp_rational_eq_rational (F := k) k
      (expand k (p ^ e) r₁) (expand k (p ^ e) r₂) (expand k (p ^ e) d₁) (expand k (p ^ e) d₂) hfne
      m B hB (fun x hx => by
        obtain ⟨y, h⟩ := exists_nonsingular W₁ x
        obtain ⟨hr2, -⟩ := ρ_val p e hr hρx hx y h
        obtain ⟨hd2, -⟩ := δ_val p e hd hδx hx y h
        simp only [coe_aeval_eq_eval, expand_eval]
        exact ⟨hr2, hd2, hm x hx⟩)
  simp only [hchar, coe_aeval_eq_eval] at hdesc

  have hd'0 : hd' ≠ 0 := by
    obtain ⟨u, hu⟩ := hT.infinite_compl.nonempty
    intro h0
    exact (hdesc u hu).1 (by rw [h0, eval_zero])
  set G := GCDMonoid.gcd hn hd' with hG
  have hG0 : G ≠ 0 := gcd_ne_zero_of_right hd'0
  set m₁ := hn / G with hm₁_def
  set m₂ := hd' / G with hm₂_def
  have hm₁ : G * m₁ = hn := EuclideanDomain.mul_div_cancel' hG0 (GCDMonoid.gcd_dvd_left _ _)
  have hm₂ : G * m₂ = hd' := EuclideanDomain.mul_div_cancel' hG0 (GCDMonoid.gcd_dvd_right _ _)
  have hmc : IsCoprime m₁ m₂ := isCoprime_div_gcd_div_gcd hd'0
  have hmval : ∀ u, u ∉ T → m₂.eval u ≠ 0 ∧ m u ^ p ^ t = m₁.eval u / m₂.eval u := by
    intro u hu
    obtain ⟨h1, h2⟩ := hdesc u hu
    rw [← hm₂, eval_mul] at h1
    obtain ⟨hGu, hm2u⟩ := mul_ne_zero_iff.mp h1
    refine ⟨hm2u, ?_⟩
    rw [h2, ← hm₁, ← hm₂, eval_mul, eval_mul, mul_div_mul_left _ _ hGu]

  set B' : Set k := B ∪ ⋃ τ ∈ T, {x | (expand k (p ^ e) r₁).eval x = τ * (expand k (p ^ e) r₂).eval x}
    with hB'
  have hB'fin : B'.Finite := hB.union (hT.biUnion fun τ _ => finite_fibre hrE hrEpos τ)
  have hB'out : ∀ x, x ∉ B' → x ∉ B ∧ r₁.eval (x ^ p ^ e) / r₂.eval (x ^ p ^ e) ∉ T := by
    intro x hx
    simp only [hB', Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists,
      expand_eval] at hx
    obtain ⟨hxB, hxT⟩ := hx
    refine ⟨hxB, fun hmem => hxT _ hmem ?_⟩
    obtain ⟨y, h⟩ := exists_nonsingular W₁ x
    obtain ⟨hr2, -⟩ := ρ_val p e hr hρx hxB y h
    rw [div_mul_cancel₀ _ hr2]

  have hmpos : 0 < max m₁.natDegree m₂.natDegree := by
    by_contra h0
    push Not at h0
    have e1 : m₁ = C (m₁.coeff 0) := eq_C_of_natDegree_eq_zero (by omega)
    have e2 : m₂ = C (m₂.coeff 0) := eq_C_of_natDegree_eq_zero (by omega)
    set c₀ := m₁.coeff 0 / m₂.coeff 0
    set c₁ := (iterateFrobeniusEquiv k p t).symm c₀ with hc₁
    have hmc₁ : ∀ u, u ∉ T → m u = c₁ := by
      intro u hu
      obtain ⟨-, h2⟩ := hmval u hu
      have h3 : m u ^ p ^ t = c₀ := by
        rw [h2]; conv_lhs => rw [e1, e2, eval_C, eval_C]
      apply (iterateFrobeniusEquiv k p t).injective
      rw [hc₁, RingEquiv.apply_symm_apply, iterateFrobeniusEquiv_def, h3]
    refine not_const_abscissa hδsurj hB'fin c₁ fun x y h hx => ?_
    obtain ⟨hxB, hxT⟩ := hB'out x hx
    obtain ⟨-, y₃, h₃, e3⟩ := δ_val p e hd hδx hxB y h
    have hc : d₁.eval (x ^ p ^ e) / d₂.eval (x ^ p ^ e) = c₁ := by rw [← hm x hxB, hmc₁ _ hxT]
    obtain ⟨h', e4⟩ := some_eq_of_x_eq h₃ hc
    exact ⟨y₃, h', e3.trans e4⟩

  obtain ⟨s, n₁, n₂, hn₁, hn₂, hnc, hnpos, hnw⟩ := exists_expand_wronskian_ne_zero p hmc hmpos
  obtain ⟨e', c₁, c₂, hc₁, hc₂, hcc, hcpos, hcw⟩ := exists_expand_wronskian_ne_zero p hd hdpos

  obtain ⟨U₀, V₀, hUc, hUpos, hUw, hUsem⟩ := exists_comp_expand p (u := expand k (p ^ e) r₁)
    (v := expand k (p ^ e) r₂) rfl rfl hn₁ hn₂ hr hrpos hrw hnc hnpos hnw

  set σ : k →+* k := iterateFrobenius k p t with hσ
  set C₁ := c₁.map σ with hC₁
  set C₂ := c₂.map σ with hC₂
  have hCc : IsCoprime C₁ C₂ := (isCoprime_map σ).mpr hcc
  have hCpos : 0 < max C₁.natDegree C₂.natDegree := by rwa [hC₁, hC₂, natDegree_map', natDegree_map']
  have hCw : wronskian C₁ C₂ ≠ 0 := (wronskian_map_ne_zero_iff σ).mpr hcw
  have hpowE : p ^ (e' + e + t) = p ^ e * p ^ t * p ^ e' := by ring
  have hCeval : ∀ (dd cc : k[X]), dd = expand k (p ^ e') cc → ∀ x : k,
      (dd.eval (x ^ p ^ e)) ^ p ^ t = (expand k (p ^ (e' + e + t)) (cc.map σ)).eval x := by
    intro dd cc hdd x
    rw [eval_pow_eq_eval_map_iterateFrobenius p, hdd, map_expand, expand_eval, expand_eval, hpowE,
      pow_mul, pow_mul]

  have hagree : ∀ x, x ∉ B' →
      (expand k (p ^ (s + e)) U₀).eval x * (expand k (p ^ (e' + e + t)) C₂).eval x =
        (expand k (p ^ (e' + e + t)) C₁).eval x * (expand k (p ^ (s + e)) V₀).eval x := by
    intro x hx
    obtain ⟨hxB, hxT⟩ := hB'out x hx
    obtain ⟨y, h⟩ := exists_nonsingular W₁ x
    obtain ⟨hr2, -⟩ := ρ_val p e hr hρx hxB y h
    obtain ⟨hd2, -⟩ := δ_val p e hd hδx hxB y h
    have hr2' : (expand k (p ^ e) r₂).eval x ≠ 0 := by rwa [expand_eval]
    have hfx : (expand k (p ^ e) r₁).eval x / (expand k (p ^ e) r₂).eval x =
        r₁.eval (x ^ p ^ e) / r₂.eval (x ^ p ^ e) := by rw [expand_eval, expand_eval]
    obtain ⟨hm2, hmu⟩ := hmval _ hxT
    obtain ⟨hV, hratio⟩ := hUsem x hr2' (by rwa [hfx])
    rw [hfx, ← hmu, hm x hxB, div_pow, hCeval d₁ c₁ hc₁ x, hCeval d₂ c₂ hc₂ x] at hratio
    have hC2 : (expand k (p ^ (e' + e + t)) C₂).eval x ≠ 0 := by
      rw [← hCeval d₂ c₂ hc₂ x]; exact pow_ne_zero _ hd2
    rw [div_eq_div_iff hV hC2] at hratio
    exact hratio
  have hpolyeq : expand k (p ^ (s + e)) U₀ * expand k (p ^ (e' + e + t)) C₂ =
      expand k (p ^ (e' + e + t)) C₁ * expand k (p ^ (s + e)) V₀ := by
    refine eq_of_eval_eq_off_finite hB'fin fun x hx => ?_
    rw [eval_mul, eval_mul]; exact hagree x hx
  have hexp : s + e = e' + e + t :=
    expand_exponent_unique p ((isCoprime_expand (pow_ne_zero _ hp.ne_zero)).mpr hUc)
      ((isCoprime_expand (pow_ne_zero _ hp.ne_zero)).mpr hCc) hpolyeq rfl rfl rfl rfl hUw hCw
  have hst : s = e' + t := by omega

  set τ : k →+* k := ((iterateFrobeniusEquiv k p t).symm : k ≃+* k).toRingHom with hτ
  have hστ : σ.comp τ = RingHom.id k := by
    ext x
    simp only [hσ, hτ, RingHom.coe_comp, Function.comp_apply, RingHom.id_apply,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    rw [← iterateFrobeniusEquiv_apply, RingEquiv.apply_symm_apply]
  set A := expand k (p ^ e') (n₁.map τ) with hA
  set Bp := expand k (p ^ e') (n₂.map τ) with hBp
  have hABeval : ∀ (nn : k[X]) (u : k),
      ((expand k (p ^ e') (nn.map τ)).eval u) ^ p ^ t = (expand k (p ^ s) nn).eval u := by
    intro nn u
    rw [eval_pow_eq_eval_map_iterateFrobenius p, ← hσ, map_expand, Polynomial.map_map, hστ,
      Polynomial.map_id, expand_eval, expand_eval, ← pow_mul, ← pow_add, add_comm, hst]
  have hmx : ∀ u, u ∉ T → Bp.eval u ≠ 0 ∧ m u = A.eval u / Bp.eval u := by
    intro u hu
    obtain ⟨hm2, hmu⟩ := hmval u hu
    have hB0 : Bp.eval u ≠ 0 := by
      intro h0
      apply hm2
      rw [hn₂, ← hABeval n₂ u, ← hBp, h0, zero_pow (pow_ne_zero _ hp.ne_zero)]
    refine ⟨hB0, ?_⟩
    apply (iterateFrobeniusEquiv k p t).injective
    rw [iterateFrobeniusEquiv_def, iterateFrobeniusEquiv_def, hmu, div_pow, hA, hBp, hABeval, hABeval,
      ← hn₁, ← hn₂]
  have hABc : IsCoprime A Bp := (isCoprime_expand (pow_ne_zero _ hp.ne_zero)).mpr ((isCoprime_map τ).mpr hnc)
  have hABpos : 0 < max A.natDegree Bp.natDegree := by
    rw [hA, hBp, natDegree_expand, natDegree_expand, natDegree_map', natDegree_map', Nat.mul_max_mul_right]
    exact Nat.mul_pos hnpos (Nat.pos_of_ne_zero (pow_ne_zero _ hp.ne_zero))
  have hBp0 : Bp ≠ 0 := (ne_zero_of_isCoprime_of_pos hABc hABpos).2

  obtain ⟨t₂, nX, dX, nY, dY, B₂, hB₂, hyrep⟩ :=
    WeierstrassCurve.exists_frobenius_comp_rational_of_comp_eq_of_mem_rationalHomSet (F := k) k
      W₁ W₂ W₃ hρ hδ hδ0 hμcomp
  simp only [hchar] at hyrep
  set Upol := (UV W₃ (p ^ t₂)).1 with hUpol
  set Vpol := (UV W₃ (p ^ t₂)).2 with hVpol
  set Uh := hom Upol.natDegree A Bp Upol with hUh
  set Vh := hom Vpol.natDegree A Bp Vpol with hVh
  set Bfin : Set k := B₂ ∪ T ∪ {x | Bp.eval x = 0} ∪
    ⋃ r ∈ (W₃.Ψ₂Sq.roots.toFinset : Set k), {x | A.eval x = r * Bp.eval x} with hBfin_def
  have hBfin : Bfin.Finite := by
    refine ((hB₂.union hT).union (finite_setOf_isRoot hBp0)).union ?_
    exact (W₃.Ψ₂Sq.roots.toFinset.finite_toSet).biUnion fun r _ => finite_fibre hABc hABpos r
  refine Or.inr ⟨C A, C Bp, (nY * C (Bp ^ Vpol.natDegree) - C Vh * dY) * C (Bp ^ Upol.natDegree),
    dY * C (Bp ^ Vpol.natDegree * Uh), Bfin, hBfin, ?_⟩
  intro x y h hx
  simp only [hBfin_def, Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists,
    Finset.mem_coe, Multiset.mem_toFinset] at hx
  obtain ⟨⟨⟨hxB₂, hxT⟩, hxBp⟩, hxΨ⟩ := hx
  obtain ⟨hdX, hdY, x', y', h', hμP, -, hy'⟩ := hyrep x y h hxB₂
  rw [evalEvalBC_self, evalEvalBC_self] at hy'
  rw [evalEvalBC_self] at hdX hdY

  obtain ⟨hBx, hmxx⟩ := hmx x hxT
  have hx' : x' = A.eval x / Bp.eval x := by
    rw [← hmxx]
    have e2 := xco_map_some_eq μ h
    exact (congrArg xco hμP).symm.trans e2

  have hΨ : W₃.Ψ₂Sq.eval x' ≠ 0 := by
    intro h0
    refine hxΨ x' ((mem_roots (WeierstrassCurve.Psi2Sq_ne_zero_of_isElliptic W₃)).mpr h0) ?_
    rw [hx', div_mul_cancel₀ _ hBx]
  have hU0 : Upol.eval x' ≠ 0 := UV_eval_ne_zero p W₃ h'.1 hΨ t₂

  have hy'val : y' * Upol.eval x' * dY.evalEval x y =
      nY.evalEval x y - Vpol.eval x' * dY.evalEval x y := by
    have := pow_eq_UV W₃ h'.1 (p ^ t₂)
    rw [hy', div_eq_iff hdY] at this
    linear_combination -this
  have hUh_eval : Uh.eval x = Bp.eval x ^ Upol.natDegree * Upol.eval x' := by
    rw [hUh, hx']; exact eval_hom_div le_rfl hBx
  have hVh_eval : Vh.eval x = Bp.eval x ^ Vpol.natDegree * Vpol.eval x' := by
    rw [hVh, hx']; exact eval_hom_div le_rfl hBx
  have eX : evalEvalBC k (C A : k[X][Y]) x y / evalEvalBC k (C Bp : k[X][Y]) x y = x' := by
    rw [evalEvalBC_self, evalEvalBC_self, evalEval_C, evalEval_C, hx']
  have hden : evalEvalBC k (dY * C (Bp ^ Vpol.natDegree * Uh)) x y ≠ 0 := by
    rw [evalEvalBC_self, evalEval_mul, evalEval_C, eval_mul, eval_pow, hUh_eval]
    exact mul_ne_zero hdY (mul_ne_zero (pow_ne_zero _ hBx) (mul_ne_zero (pow_ne_zero _ hBx) hU0))
  have eY : evalEvalBC k ((nY * C (Bp ^ Vpol.natDegree) - C Vh * dY) * C (Bp ^ Upol.natDegree)) x y /
      evalEvalBC k (dY * C (Bp ^ Vpol.natDegree * Uh)) x y = y' := by
    rw [div_eq_iff hden]
    simp only [evalEvalBC_self, evalEval_mul, evalEval_sub, evalEval_C, eval_mul, eval_pow, hUh_eval,
      hVh_eval]
    linear_combination (-(Bp.eval x ^ Vpol.natDegree * Bp.eval x ^ Upol.natDegree)) * hy'val
  refine ⟨by rw [evalEvalBC_self, evalEval_C]; exact hBx, hden, ?_⟩
  rw [hμP]
  obtain ⟨h₁, e₁⟩ := some_eq_of_x_eq h' eX.symm
  refine ⟨(by rw [eY]; exact h₁), ?_⟩
  rw [e₁]
  congr 1
  exact eY.symm

end MainProof
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_comp_eq_of_ker_le_of_xCoord_expand.FactorP"

end FactorP
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_comp_eq_of_ker_le_of_xCoord_expand.FactorP"

theorem solution {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k] (p : ℕ) [Fact p.Prime] [CharP k p] (W₁ W₂ W₃ : WeierstrassCurve k) [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic] {ρ : W₁.toAffine.Point →+ W₂.toAffine.Point} {δ : W₁.toAffine.Point →+ W₃.toAffine.Point} (hρ : ρ ∈ WeierstrassCurve.rationalHomSet k W₁ W₂) (hδ : δ ∈ WeierstrassCurve.rationalHomSet k W₁ W₃) (hρ0 : ρ ≠ 0) (hδ0 : δ ≠ 0) (hker : ∀ T : W₁.toAffine.Point, ρ T = 0 → δ T = 0) (e : ℕ) {r₁ r₂ d₁ d₂ : Polynomial k} (hr : IsCoprime r₁ r₂) (hrw : Polynomial.wronskian r₁ r₂ ≠ 0) (hd : IsCoprime d₁ d₂) {B : Set k} (hB : B.Finite) (hρx : ∀ (x y : k) (h : W₁.toAffine.Nonsingular x y), x ∉ B → ∃ (x' y' : k) (h' : W₂.toAffine.Nonsingular x' y'), ρ (WeierstrassCurve.Affine.Point.some x y h) = WeierstrassCurve.Affine.Point.some x' y' h' ∧ x' * r₂.eval (x ^ p ^ e) = r₁.eval (x ^ p ^ e)) (hδx : ∀ (x y : k) (h : W₁.toAffine.Nonsingular x y), x ∉ B → ∃ (x' y' : k) (h' : W₃.toAffine.Nonsingular x' y'), δ (WeierstrassCurve.Affine.Point.some x y h) = WeierstrassCurve.Affine.Point.some x' y' h' ∧ x' * d₂.eval (x ^ p ^ e) = d₁.eval (x ^ p ^ e)) : ∃ γ ∈ WeierstrassCurve.rationalHomSet k W₂ W₃, δ = γ.comp ρ :=
  FactorP.main p e hr hd hρx hδx hρ hδ hρ0 hδ0 hker hrw hB

end S_WeierstrassCurve_exists_mem_rationalHomSet_comp_eq_of_ker_le_of_xCoord_expand
end P2MW
export P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_comp_eq_of_ker_le_of_xCoord_expand (solution)
