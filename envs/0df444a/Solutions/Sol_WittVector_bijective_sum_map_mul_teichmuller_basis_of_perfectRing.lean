-- Prove2me | solution 1 for WittVector.bijective_sum_map_mul_teichmuller_basis_of_perfectRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/e78f70fe-51b5-5d14-9a03-3dafcab64d1c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WittVector_bijective_sum_map_mul_teichmuller_basis_of_perfectRing

set_option autoImplicit false

open scoped BigOperators

namespace P2mKcWittTeichBasis

open WittVector

universe u v w

variable {p : ℕ} [hp : Fact p.Prime]

section general

variable {R : Type u} [CommRing R]

local notation "𝕎" => WittVector p

noncomputable def vIter (n : ℕ) : 𝕎 R →+ 𝕎 R where
  toFun x := (⇑(verschiebung : 𝕎 R →+ 𝕎 R))^[n] x
  map_zero' := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, map_zero]
  map_add' x y := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', ih, map_add]

theorem vIter_apply (n : ℕ) (x : 𝕎 R) :
    vIter (p := p) n x = (⇑(verschiebung : 𝕎 R →+ 𝕎 R))^[n] x := rfl

def LowZero (n : ℕ) (x : 𝕎 R) : Prop := ∀ m, m < n → x.coeff m = 0

theorem lowZero_iff_mem_ker (n : ℕ) (x : 𝕎 R) :
    LowZero (p := p) n x ↔ x ∈ RingHom.ker (WittVector.truncate (p := p) n) := by
  rw [WittVector.mem_ker_truncate]; rfl

theorem LowZero.add {n : ℕ} {x y : 𝕎 R} (hx : LowZero (p := p) n x) (hy : LowZero n y) :
    LowZero n (x + y) := by
  rw [lowZero_iff_mem_ker] at hx hy ⊢; exact Ideal.add_mem _ hx hy

theorem LowZero.sub {n : ℕ} {x y : 𝕎 R} (hx : LowZero (p := p) n x) (hy : LowZero n y) :
    LowZero n (x - y) := by
  rw [lowZero_iff_mem_ker] at hx hy ⊢; exact Ideal.sub_mem _ hx hy

theorem LowZero.neg {n : ℕ} {x : 𝕎 R} (hx : LowZero (p := p) n x) : LowZero n (-x) := by
  rw [lowZero_iff_mem_ker] at hx ⊢; exact neg_mem hx

theorem LowZero.mul_left {n : ℕ} {x : 𝕎 R} (y : 𝕎 R) (hx : LowZero (p := p) n x) :
    LowZero n (y * x) := by
  rw [lowZero_iff_mem_ker] at hx ⊢; exact Ideal.mul_mem_left _ y hx

theorem LowZero.mul_right {n : ℕ} {x : 𝕎 R} (y : 𝕎 R) (hx : LowZero (p := p) n x) :
    LowZero n (x * y) := by
  rw [lowZero_iff_mem_ker] at hx ⊢; exact Ideal.mul_mem_right y _ hx

theorem lowZero_zero (n : ℕ) : LowZero (p := p) n (0 : 𝕎 R) := fun m _ => WittVector.zero_coeff _ _ m

theorem LowZero.sum {ι : Type w} (s : Finset ι) {n : ℕ} {f : ι → 𝕎 R}
    (h : ∀ i ∈ s, LowZero (p := p) n (f i)) : LowZero n (∑ i ∈ s, f i) := by
  simp only [lowZero_iff_mem_ker] at h ⊢; exact Ideal.sum_mem _ h

omit hp in
theorem LowZero.mono {n m : ℕ} (hmn : m ≤ n) {x : 𝕎 R} (hx : LowZero (p := p) n x) :
    LowZero m x := fun i hi => hx i (lt_of_lt_of_le hi hmn)

theorem lowZero_vIter (n : ℕ) (x : 𝕎 R) : LowZero n (vIter (p := p) n x) := fun _ hm =>
  WittVector.iterate_verschiebung_coeff_eq_zero x hm

theorem coeff_vIter (n : ℕ) (x : 𝕎 R) (j : ℕ) : (vIter (p := p) n x).coeff (j + n) = x.coeff j :=
  WittVector.iterate_verschiebung_coeff x n j

theorem coeff_vIter_self (n : ℕ) (x : 𝕎 R) : (vIter (p := p) n x).coeff n = x.coeff 0 := by
  simpa only [zero_add] using coeff_vIter (p := p) n x 0

theorem LowZero.eq_vIter_shift {n : ℕ} {x : 𝕎 R} (hx : LowZero (p := p) n x) :
    x = vIter n (x.shift n) :=
  WittVector.eq_iterate_verschiebung hx

omit hp in

theorem LowZero.succ {n : ℕ} {x : 𝕎 R} (hx : LowZero (p := p) n x) (hn : x.coeff n = 0) :
    LowZero (n + 1) x := by
  intro m hm
  rcases Nat.lt_succ_iff_lt_or_eq.mp hm with h | h
  · exact hx m h
  · rw [h]; exact hn

theorem lowZero_sub_of_coeff_eq {n : ℕ} {x y : 𝕎 R} (h : ∀ m, m < n → x.coeff m = y.coeff m) :
    LowZero (p := p) n (x - y) := by
  rw [lowZero_iff_mem_ker, RingHom.mem_ker, map_sub, sub_eq_zero]
  ext i
  simp only [WittVector.coeff_truncate]
  exact h i i.2

theorem coeff_eq_of_lowZero_sub {n : ℕ} {x y : 𝕎 R} (h : LowZero (p := p) n (x - y)) :
    ∀ m, m < n → x.coeff m = y.coeff m := by
  rw [lowZero_iff_mem_ker, RingHom.mem_ker, map_sub, sub_eq_zero] at h
  intro m hm
  have := congrArg (TruncatedWittVector.coeff (⟨m, hm⟩ : Fin n)) h
  simpa only [WittVector.coeff_truncate] using this

theorem LowZero.map {S : Type v} [CommRing S] (f : R →+* S) {n : ℕ} {x : 𝕎 R}
    (hx : LowZero (p := p) n x) : LowZero n (WittVector.map f x) := by
  intro m hm; rw [WittVector.map_coeff, hx m hm, map_zero]

theorem map_vIter {S : Type v} [CommRing S] (f : R →+* S) (n : ℕ) (x : 𝕎 R) :
    WittVector.map f (vIter (p := p) n x) = vIter n (WittVector.map f x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [vIter_apply, Function.iterate_succ_apply'] at ih ⊢
    rw [WittVector.map_verschiebung, ih]

theorem vIter_mul (n : ℕ) (x y : 𝕎 R) :
    vIter (p := p) n x * y = vIter n (x * (⇑(WittVector.frobenius : 𝕎 R →+* 𝕎 R))^[n] y) :=
  WittVector.iterate_verschiebung_mul_left x y n

variable [CharP R p]

theorem iterate_frobenius_teichmuller (n : ℕ) (e : R) :
    (⇑(WittVector.frobenius : 𝕎 R →+* 𝕎 R))^[n] (teichmuller p e) = teichmuller p (e ^ p ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, WittVector.frobenius_eq_map_frobenius,
      WittVector.map_teichmuller, frobenius_def, ← pow_mul, ← pow_succ]

end general

section main

variable {k : Type u} {l : Type v} [CommRing k] [CommRing l] [Algebra k l] {ι : Type w} [Fintype ι]

local notation "𝕎" => WittVector p

noncomputable def L (e : ι → l) : (ι → 𝕎 k) →+ 𝕎 l where
  toFun a := ∑ i, WittVector.map (algebraMap k l) (a i) * teichmuller p (e i)
  map_zero' := by simp
  map_add' a a' := by
    simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem L_apply (e : ι → l) (a : ι → 𝕎 k) :
    L (p := p) e a = ∑ i, WittVector.map (algebraMap k l) (a i) * teichmuller p (e i) := rfl

theorem lowZero_L (e : ι → l) {n : ℕ} {a : ι → 𝕎 k} (ha : ∀ i, LowZero (p := p) n (a i)) :
    LowZero n (L (p := p) e a) := by
  rw [L_apply]
  exact LowZero.sum _ fun i _ => ((ha i).map (algebraMap k l)).mul_right _

variable [CharP l p]

theorem L_vShift (e : ι → l) (n : ℕ) (s : ι → 𝕎 k) :
    L (p := p) e (fun i => vIter n (s i)) =
      vIter n (∑ i, WittVector.map (algebraMap k l) (s i) * teichmuller p (e i ^ p ^ n)) := by
  rw [L_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_vIter, vIter_mul, iterate_frobenius_teichmuller]

omit [CharP l p] in

def twist (e : ι → l) (n : ℕ) (c : ι → k) : l := ∑ i, algebraMap k l (c i) * e i ^ p ^ n

theorem coeff_L_vShift (e : ι → l) (n : ℕ) (s : ι → 𝕎 k) :
    (L (p := p) e (fun i => vIter n (s i))).coeff n = twist (p := p) e n fun i => (s i).coeff 0 := by
  rw [L_vShift, coeff_vIter_self, ← WittVector.constantCoeff_apply, map_sum]
  unfold twist
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply,
    WittVector.map_coeff, WittVector.teichmuller_coeff_zero]

variable [CharP k p] [PerfectRing k p] [PerfectRing l p]

omit [CharP l p] [PerfectRing l p] in

theorem algebraMap_iterateFrobeniusEquiv_symm_pow (n : ℕ) (c : k) :
    algebraMap k l ((iterateFrobeniusEquiv k p n).symm c) ^ p ^ n = algebraMap k l c := by
  rw [← map_pow, ← iterateFrobenius_def, ← iterateFrobeniusEquiv_apply,
    RingEquiv.apply_symm_apply]

theorem twist_bijective (b : Module.Basis ι k l) (n : ℕ) :
    Function.Bijective (twist (p := p) (k := k) (⇑b) n) := by

  have key : ∀ c : ι → k, twist (p := p) (k := k) (⇑b) n c =
      iterateFrobeniusEquiv l p n (∑ i, (iterateFrobeniusEquiv k p n).symm (c i) • b i) := by
    intro c
    rw [map_sum]
    unfold twist
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul, iterateFrobeniusEquiv_apply, iterateFrobeniusEquiv_apply,
      iterateFrobenius_def, iterateFrobenius_def, algebraMap_iterateFrobeniusEquiv_symm_pow]
  constructor
  · intro c c' h
    rw [key, key] at h
    have h1 := (iterateFrobeniusEquiv l p n).injective h
    have h2 : (fun i => (iterateFrobeniusEquiv k p n).symm (c i)) =
        fun i => (iterateFrobeniusEquiv k p n).symm (c' i) := by
      have := b.equivFun.symm.injective (a₁ := fun i => (iterateFrobeniusEquiv k p n).symm (c i))
        (a₂ := fun i => (iterateFrobeniusEquiv k p n).symm (c' i))
      apply this
      simpa only [Module.Basis.equivFun_symm_apply] using h1
    funext i
    exact (iterateFrobeniusEquiv k p n).symm.injective (congrFun h2 i)
  · intro y
    refine ⟨fun i => iterateFrobeniusEquiv k p n (b.repr ((iterateFrobeniusEquiv l p n).symm y) i),
      ?_⟩
    rw [key]
    simp only [RingEquiv.symm_apply_apply]
    rw [b.sum_repr, RingEquiv.apply_symm_apply]

theorem L_injective (b : Module.Basis ι k l) : Function.Injective (L (p := p) (k := k) (⇑b)) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra hne

  have hex : ∃ n, ∃ i, (a i).coeff n ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact hne (funext fun i => WittVector.ext fun n => by simpa using hall n i)
  classical
  let n := Nat.find hex
  obtain ⟨i₀, hi₀⟩ : ∃ i, (a i).coeff n ≠ 0 := Nat.find_spec hex
  have hlow : ∀ i, LowZero (p := p) n (a i) := by
    intro i m hm
    by_contra h
    exact Nat.find_min hex hm ⟨i, h⟩

  set s : ι → 𝕎 k := fun i => (a i).shift n with hs
  have ha' : a = fun i => vIter n (s i) := funext fun i => (hlow i).eq_vIter_shift
  have hcoeff := coeff_L_vShift (p := p) (⇑b) n s
  rw [← ha', ha, WittVector.zero_coeff] at hcoeff

  have h0 : twist (p := p) (k := k) (⇑b) n (fun _ => (0 : k)) = 0 := by simp [twist]
  have := (twist_bijective (p := p) b n).1 (hcoeff.symm.trans h0.symm)
  have hi : (s i₀).coeff 0 = 0 := congrFun this i₀
  rw [hs, WittVector.shift_coeff, add_zero] at hi
  exact hi₀ hi

theorem step (b : Module.Basis ι k l) (x : 𝕎 l) (n : ℕ) (a : ι → 𝕎 k)
    (ha : LowZero (p := p) n (x - L (p := p) (⇑b) a)) :
    ∃ a' : ι → 𝕎 k, (∀ i, LowZero (p := p) n (a' i - a i)) ∧
      LowZero (p := p) (n + 1) (x - L (p := p) (⇑b) a') := by
  set r := x - L (p := p) (⇑b) a with hr
  obtain ⟨c, hc⟩ := (twist_bijective (p := p) b n).2 (r.coeff n)
  refine ⟨a + fun i => vIter n (teichmuller p (c i)), fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, add_sub_cancel_left]
    exact lowZero_vIter _ _
  · have hsplit : x - L (p := p) (⇑b) (a + fun i => vIter n (teichmuller p (c i))) =
        r - L (p := p) (⇑b) (fun i => vIter n (teichmuller p (c i))) := by
      rw [map_add, hr]; abel
    rw [hsplit]
    refine LowZero.succ (ha.sub (lowZero_L _ fun i => lowZero_vIter _ _)) ?_

    have hrV : r = vIter n (r.shift n) := ha.eq_vIter_shift
    have hdiff : r - L (p := p) (⇑b) (fun i => vIter n (teichmuller p (c i))) =
        vIter n (r.shift n - ∑ i, WittVector.map (algebraMap k l) (teichmuller p (c i)) *
          teichmuller p (b i ^ p ^ n)) := by
      rw [L_vShift, map_sub, ← hrV]
    rw [hdiff, coeff_vIter_self, ← WittVector.constantCoeff_apply, map_sub, map_sum,
      WittVector.constantCoeff_apply, WittVector.shift_coeff, add_zero, sub_eq_zero, ← hc]
    unfold twist
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply,
      WittVector.map_coeff, WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero]

noncomputable def approx (b : Module.Basis ι k l) (x : 𝕎 l) :
    (n : ℕ) → {a : ι → 𝕎 k // LowZero (p := p) n (x - L (p := p) (⇑b) a)}
  | 0 => ⟨0, fun _ hm => absurd hm (Nat.not_lt_zero _)⟩
  | n + 1 =>
    ⟨Classical.choose (step b x n (approx b x n).1 (approx b x n).2),
      (Classical.choose_spec (step b x n (approx b x n).1 (approx b x n).2)).2⟩

theorem approx_succ_congr (b : Module.Basis ι k l) (x : 𝕎 l) (n : ℕ) (i : ι) :
    LowZero (p := p) n ((approx (p := p) b x (n + 1)).1 i - (approx (p := p) b x n).1 i) :=
  (Classical.choose_spec (step b x n (approx b x n).1 (approx b x n).2)).1 i

theorem approx_coeff_stable (b : Module.Basis ι k l) (x : 𝕎 l) (i : ι) (m : ℕ) :
    ∀ n n', m < n → n ≤ n' →
      ((approx (p := p) b x n').1 i).coeff m = ((approx (p := p) b x n).1 i).coeff m := by
  intro n n' hm hnn'
  induction hnn' with
  | refl => rfl
  | @step n' hle ih =>
    rw [← ih]
    exact coeff_eq_of_lowZero_sub (approx_succ_congr b x n' i) m (lt_of_lt_of_le hm hle)

noncomputable def limit (b : Module.Basis ι k l) (x : 𝕎 l) (i : ι) : 𝕎 k :=
  WittVector.mk p fun m => ((approx (p := p) b x (m + 1)).1 i).coeff m

theorem limit_congr (b : Module.Basis ι k l) (x : 𝕎 l) (n : ℕ) (i : ι) :
    LowZero (p := p) n (limit (p := p) b x i - (approx (p := p) b x n).1 i) := by
  refine lowZero_sub_of_coeff_eq fun m hm => ?_
  unfold limit
  rw [WittVector.coeff_mk]
  exact (approx_coeff_stable b x i m (m + 1) n (Nat.lt_succ_self m) hm).symm

theorem L_surjective (b : Module.Basis ι k l) : Function.Surjective (L (p := p) (k := k) (⇑b)) := by
  intro x
  refine ⟨limit b x, ?_⟩
  rw [← sub_eq_zero]
  refine WittVector.ext fun m => ?_
  rw [WittVector.zero_coeff]

  have h1 : LowZero (p := p) (m + 1) (x - L (p := p) (⇑b) (approx b x (m + 1)).1) :=
    (approx b x (m + 1)).2
  have h2 : LowZero (p := p) (m + 1)
      (L (p := p) (⇑b) (limit b x) - L (p := p) (⇑b) (approx b x (m + 1)).1) := by
    rw [← map_sub]
    exact lowZero_L _ fun i => limit_congr b x (m + 1) i
  have h3 : LowZero (p := p) (m + 1) (L (p := p) (⇑b) (limit b x) - x) := by
    have := h2.sub h1
    have e : L (p := p) (⇑b) (limit b x) - L (p := p) (⇑b) (approx b x (m + 1)).1 -
        (x - L (p := p) (⇑b) (approx b x (m + 1)).1) = L (p := p) (⇑b) (limit b x) - x := by abel
    rwa [e] at this
  exact h3 m (Nat.lt_succ_self m)

end main

end P2mKcWittTeichBasis

universe u v w

theorem solution
    (p : ℕ) [Fact p.Prime] {k : Type u} {l : Type v} [CommRing k] [CommRing l]
    [CharP k p] [CharP l p] [PerfectRing k p] [PerfectRing l p] [Algebra k l]
    {ι : Type w} [Fintype ι] (b : Module.Basis ι k l) :
    Function.Bijective fun a : ι → WittVector p k =>
      ∑ i, WittVector.map (algebraMap k l) (a i) * WittVector.teichmuller p (b i) :=
  ⟨P2mKcWittTeichBasis.L_injective (p := p) b, P2mKcWittTeichBasis.L_surjective (p := p) b⟩

end S_WittVector_bijective_sum_map_mul_teichmuller_basis_of_perfectRing
end P2MW
export P2MW.S_WittVector_bijective_sum_map_mul_teichmuller_basis_of_perfectRing (solution)
