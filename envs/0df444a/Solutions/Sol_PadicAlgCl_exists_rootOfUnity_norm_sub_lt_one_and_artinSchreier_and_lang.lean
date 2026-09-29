-- Prove2me | solution 1 for PadicAlgCl.exists_rootOfUnity_norm_sub_lt_one_and_artinSchreier_and_lang
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/031ed409-7eee-5084-947a-907689630830

import Mathlib
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Definitions.Def_PadicComplex_GaloisAction
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicAlgCl_exists_rootOfUnity_norm_sub_lt_one_and_artinSchreier_and_lang

set_option autoImplicit false

open scoped TensorProduct

namespace Ws47
namespace U1C

open Polynomial

variable {p : ℕ} [Fact p.Prime]

theorem hp : p.Prime := Fact.out

theorem norm_natCast_le_one (n : ℕ) : ‖(n : PadicAlgCl p)‖ ≤ 1 := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) n, norm_algebraMap']
  exact_mod_cast Padic.norm_int_le_one (p := p) (n : ℤ)

theorem norm_p_lt_one : ‖(p : PadicAlgCl p)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p, norm_algebraMap', Padic.norm_natCast_lt_one_iff]

theorem norm_eq_one_of_pow_eq_one {x : PadicAlgCl p} {n : ℕ} (hn : n ≠ 0) (hx : x ^ n = 1) : ‖x‖ = 1 := by
  have h := congrArg norm hx
  rw [norm_pow, norm_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).mp h

theorem norm_sum_le_one {ι : Type} (s : Finset ι) (f : ι → PadicAlgCl p) (h : ∀ i ∈ s, ‖f i‖ ≤ 1) :
    ‖∑ i ∈ s, f i‖ ≤ 1 :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one h

theorem norm_pow_sub_pow_le {a b : PadicAlgCl p} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (n : ℕ) :
    ‖a ^ n - b ^ n‖ ≤ ‖a - b‖ := by
  rw [← geom_sum₂_mul, norm_mul]
  refine mul_le_of_le_one_left (norm_nonneg _) (norm_sum_le_one _ _ fun i _ => ?_)
  rw [norm_mul, norm_pow, norm_pow]
  exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) ha) (pow_nonneg (norm_nonneg _) _)
    (pow_le_one₀ (norm_nonneg _) hb)

theorem norm_one_sub_pow_le {ω : PadicAlgCl p} (hω : ‖ω‖ ≤ 1) (i : ℕ) : ‖1 - ω ^ i‖ ≤ ‖1 - ω‖ := by
  have h := norm_pow_sub_pow_le (p := p) (norm_one (α := PadicAlgCl p)).le hω i
  rwa [one_pow] at h

theorem norm_sub_le_max' (u w : PadicAlgCl p) : ‖u - w‖ ≤ max ‖u‖ ‖w‖ := by
  simpa [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max u (-w)

theorem exists_lt_one_of_prod_lt_one {ι : Type} {s : Finset ι} {f : ι → ℝ} (_h0 : ∀ i ∈ s, 0 ≤ f i)
    (h1 : ∀ i ∈ s, f i ≤ 1) (h : ∏ i ∈ s, f i < 1) : ∃ i ∈ s, f i < 1 := by
  by_contra hne
  push Not at hne
  have : ∏ i ∈ s, f i = 1 := Finset.prod_eq_one fun i hi => le_antisymm (h1 i hi) (hne i hi)
  rw [this] at h
  exact lt_irrefl _ h

theorem exists_isPrimitiveRoot_norm_one_sub_lt_one :
    ∃ μ : PadicAlgCl p, IsPrimitiveRoot μ p ∧ ‖1 - μ‖ < 1 := by
  haveI : NeZero ((p : ℕ) : PadicAlgCl p) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
  obtain ⟨μ, hμ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl p) p
  have hprod : (p : PadicAlgCl p) = ∏ ν ∈ primitiveRoots p (PadicAlgCl p), (1 - ν) := by
    have h := congrArg (Polynomial.eval (1 : PadicAlgCl p)) (Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hμ)
    simpa [Polynomial.eval_prod] using h
  have hlt : ∏ ν ∈ primitiveRoots p (PadicAlgCl p), ‖1 - ν‖ < 1 := by
    rw [← norm_prod, ← hprod]
    exact norm_p_lt_one
  have hle : ∀ ν ∈ primitiveRoots p (PadicAlgCl p), ‖1 - ν‖ ≤ 1 := fun ν hν => by
    have hν' : IsPrimitiveRoot ν p := (mem_primitiveRoots hp.pos).mp hν
    have : ‖ν‖ = 1 := norm_eq_one_of_pow_eq_one hp.ne_zero hν'.pow_eq_one
    calc ‖1 - ν‖ ≤ max ‖(1 : PadicAlgCl p)‖ ‖ν‖ := norm_sub_le_max' _ _
      _ = 1 := by rw [norm_one, this, max_self]
  obtain ⟨ν, hν, hν1⟩ := exists_lt_one_of_prod_lt_one (fun _ _ => norm_nonneg _) hle hlt
  exact ⟨ν, (mem_primitiveRoots hp.pos).mp hν, hν1⟩

theorem norm_sub_lt_one_of_norm_pow_sub_pow_lt_one {u v : PadicAlgCl p} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (h : ‖u ^ p - v ^ p‖ < 1) : ‖u - v‖ < 1 := by
  obtain ⟨μ, hμ, hμ1⟩ := exists_isPrimitiveRoot_norm_one_sub_lt_one (p := p)
  have hμn : ‖μ‖ = 1 := norm_eq_one_of_pow_eq_one hp.ne_zero hμ.pow_eq_one

  have hfac : u ^ p - v ^ p = ∏ i ∈ Finset.range p, (u - μ ^ i * v) := by
    have h := congrArg (Polynomial.eval u) (X_pow_sub_C_eq_prod hμ hp.pos (rfl : v ^ p = v ^ p))
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_prod] at h
    simpa using h
  have hlt : ∏ i ∈ Finset.range p, ‖u - μ ^ i * v‖ < 1 := by rwa [← norm_prod, ← hfac]
  have hle : ∀ i ∈ Finset.range p, ‖u - μ ^ i * v‖ ≤ 1 := fun i _ =>
    calc ‖u - μ ^ i * v‖ ≤ max ‖u‖ ‖μ ^ i * v‖ := norm_sub_le_max' _ _
      _ ≤ 1 := max_le hu (by rw [norm_mul, norm_pow, hμn, one_pow, one_mul]; exact hv)
  obtain ⟨i, -, hi⟩ := exists_lt_one_of_prod_lt_one (fun _ _ => norm_nonneg _) hle hlt
  have hclose : ‖μ ^ i * v - v‖ < 1 := by
    rw [← sub_one_mul, norm_mul, norm_sub_rev]
    calc ‖1 - μ ^ i‖ * ‖v‖ ≤ ‖1 - μ ^ i‖ * 1 := mul_le_mul_of_nonneg_left hv (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact lt_of_le_of_lt (norm_one_sub_pow_le hμn.le i) hμ1
  calc ‖u - v‖ = ‖(u - μ ^ i * v) + (μ ^ i * v - v)‖ := by rw [sub_add_sub_cancel]
    _ ≤ max ‖u - μ ^ i * v‖ ‖μ ^ i * v - v‖ := IsUltrametricDist.norm_add_le_max _ _
    _ < 1 := max_lt hi hclose

theorem norm_sub_lt_one_of_norm_pow_sub_pow_lt_one' (a : ℕ) {u v : PadicAlgCl p} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (h : ‖u ^ p ^ a - v ^ p ^ a‖ < 1) : ‖u - v‖ < 1 := by
  induction a generalizing u v with
  | zero => simpa using h
  | succ a ih =>
    refine ih hu hv (norm_sub_lt_one_of_norm_pow_sub_pow_lt_one
      (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hu) (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hv) ?_)
    rwa [← pow_mul, ← pow_mul, ← pow_succ]

theorem exists_lt_norm_frobPow_sub_lt_one {x : PadicAlgCl p} (hx : ‖x‖ ≤ 1) :
    ∃ a b : ℕ, a < b ∧ ‖x ^ p ^ b - x ^ p ^ a‖ < 1 := by
  classical

  set A : Subalgebra ℚ_[p] (PadicAlgCl p) := Algebra.adjoin ℚ_[p] {x} with hA
  have hint : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
  haveI : FiniteDimensional ℚ_[p] (Subalgebra.toSubmodule A) :=
    Module.Finite.iff_fg.mpr hint.fg_adjoin_singleton
  set E := ↥(Subalgebra.toSubmodule A) with hE
  haveI : ProperSpace E := FiniteDimensional.proper ℚ_[p] E
  have hmem : ∀ k : ℕ, x ^ p ^ k ∈ Subalgebra.toSubmodule A := fun k =>
    show x ^ p ^ k ∈ A from Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton ℚ_[p] x) _
  let y : ℕ → E := fun k => ⟨x ^ p ^ k, hmem k⟩
  have hy : ∀ k, y k ∈ Metric.closedBall (0 : E) 1 := fun k => by
    rw [Metric.mem_closedBall, dist_zero_right]
    show ‖x ^ p ^ k‖ ≤ 1
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx

  obtain ⟨t, -, htfin, hcover⟩ :=
    finite_cover_balls_of_compact (isCompact_closedBall (0 : E) 1) (zero_lt_one' ℝ)
  haveI : Finite t := htfin.to_subtype
  have hsel : ∀ k, ∃ z : t, y k ∈ Metric.ball (z : E) 1 := fun k => by
    have := hcover (hy k)
    simp only [Set.mem_iUnion] at this
    obtain ⟨z, hz, hzk⟩ := this
    exact ⟨⟨z, hz⟩, hzk⟩
  choose g hg using hsel
  obtain ⟨a, b, hab, hgab⟩ := Finite.exists_ne_map_eq_of_infinite g

  have hclose : ∀ {a b : ℕ}, g a = g b → ‖x ^ p ^ b - x ^ p ^ a‖ < 1 := by
    intro a b h
    have ha := hg a; have hb := hg b
    rw [h] at ha
    rw [Metric.mem_ball, dist_eq_norm] at ha hb
    have ha' : ‖x ^ p ^ a - ((g b : E) : PadicAlgCl p)‖ < 1 := ha
    have hb' : ‖x ^ p ^ b - ((g b : E) : PadicAlgCl p)‖ < 1 := hb
    calc ‖x ^ p ^ b - x ^ p ^ a‖
        = ‖(x ^ p ^ b - ((g b : E) : PadicAlgCl p)) - (x ^ p ^ a - ((g b : E) : PadicAlgCl p))‖ := by
          rw [sub_sub_sub_cancel_right]
      _ ≤ max ‖x ^ p ^ b - ((g b : E) : PadicAlgCl p)‖ ‖x ^ p ^ a - ((g b : E) : PadicAlgCl p)‖ :=
          norm_sub_le_max' _ _
      _ < 1 := max_lt hb' ha'
  rcases lt_or_gt_of_ne hab with h | h
  · exact ⟨a, b, h, hclose hgab⟩
  · exact ⟨b, a, h, hclose hgab.symm⟩

theorem exists_rootOfUnity_norm_sub_lt_one {x : PadicAlgCl p} (hx : ‖x‖ ≤ 1) :
    ∃ ζ : PadicAlgCl p, (ζ = 0 ∨ ∃ m : ℕ, Nat.Coprime p m ∧ ζ ^ m = 1) ∧ ‖x - ζ‖ < 1 := by
  classical
  rcases hx.lt_or_eq with hx1 | hx1
  · exact ⟨0, Or.inl rfl, by rwa [sub_zero]⟩

  obtain ⟨a, b, hab, hclose⟩ := exists_lt_norm_frobPow_sub_lt_one hx
  obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_lt hab
  set q : ℕ := p ^ (f + 1) with hq
  have hxq : ‖x ^ q - x‖ < 1 := by
    refine norm_sub_lt_one_of_norm_pow_sub_pow_lt_one' a (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx) hx ?_
    rwa [← pow_mul, hq, ← pow_add, show f + 1 + a = a + f + 1 by ring]

  have hq1 : 1 ≤ q := Nat.one_le_pow _ _ hp.pos
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (by rw [hx1]; exact one_ne_zero)
  have hxq' : ‖x ^ (q - 1) - 1‖ < 1 := by
    have : x ^ q - x = x * (x ^ (q - 1) - 1) := by
      rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel hq1]
    rwa [this, norm_mul, hx1, one_mul] at hxq

  have hcop : Nat.Coprime p (q - 1) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    have hpq : p ∣ q := dvd_pow_self p (Nat.succ_ne_zero f)
    have : p ∣ q - (q - 1) := Nat.dvd_sub hpq hd
    rw [Nat.sub_sub_self hq1] at this
    exact hp.ne_one (Nat.dvd_one.mp this)
  have hq1' : 0 < q - 1 := by
    have : 1 < q := Nat.one_lt_pow (Nat.succ_ne_zero f) hp.one_lt
    omega

  haveI : NeZero ((q - 1 : ℕ) : PadicAlgCl p) := ⟨Nat.cast_ne_zero.mpr hq1'.ne'⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl p) (q - 1)
  have hfac : x ^ (q - 1) - 1 = ∏ i ∈ Finset.range (q - 1), (x - ξ ^ i) := by
    have h := congrArg (Polynomial.eval x) (X_pow_sub_C_eq_prod hξ hq1' (one_pow (q - 1)))
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_prod] at h
    simpa using h
  have hξn : ‖ξ‖ = 1 := norm_eq_one_of_pow_eq_one hq1'.ne' hξ.pow_eq_one
  have hle : ∀ i ∈ Finset.range (q - 1), ‖x - ξ ^ i‖ ≤ 1 := fun i _ =>
    calc ‖x - ξ ^ i‖ ≤ max ‖x‖ ‖ξ ^ i‖ := norm_sub_le_max' _ _
      _ ≤ 1 := max_le hx (by rw [norm_pow, hξn, one_pow])
  have hlt : ∏ i ∈ Finset.range (q - 1), ‖x - ξ ^ i‖ < 1 := by rwa [← norm_prod, ← hfac]
  obtain ⟨i, -, hi⟩ := exists_lt_one_of_prod_lt_one (fun _ _ => norm_nonneg _) hle hlt
  refine ⟨ξ ^ i, Or.inr ⟨q - 1, hcop, ?_⟩, hi⟩
  rw [← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow]

end Ws47.U1C

theorem solution
    (p : ℕ) [Fact p.Prime] :
    (∀ x : PadicAlgCl p, ‖x‖ ≤ 1 →
      ∃ ζ : PadicAlgCl p, (ζ = 0 ∨ ∃ m : ℕ, Nat.Coprime p m ∧ ζ ^ m = 1) ∧ ‖x - ζ‖ < 1) ∧
    (∀ (q : ℕ), p ∣ q → 1 < q → ∀ c : PadicAlgCl p, ‖c‖ ≤ 1 →
      ∃ y : PadicAlgCl p, (y = 0 ∨ ∃ m : ℕ, Nat.Coprime p m ∧ y ^ m = 1) ∧ ‖y ^ q - y - c‖ < 1) ∧
    (∀ (q : ℕ), p ∣ q → 1 < q → ∀ a : PadicAlgCl p, ‖a‖ = 1 →
      ∃ y : PadicAlgCl p, (∃ m : ℕ, Nat.Coprime p m ∧ y ^ m = 1) ∧ ‖y ^ (q - 1) - a‖ < 1) := by
  have hp : p.Prime := Fact.out
  refine ⟨fun x hx => Ws47.U1C.exists_rootOfUnity_norm_sub_lt_one hx, ?_, ?_⟩
  ·
    intro q hpq hq c hc
    have hdeg : (Polynomial.X ^ q - Polynomial.X - Polynomial.C c : Polynomial (PadicAlgCl p)).degree ≠ 0 := by
      rw [sub_sub, Polynomial.degree_sub_eq_left_of_degree_lt] <;>
        rw [Polynomial.degree_X_pow]
      · exact_mod_cast (by omega : q ≠ 0)
      · refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
        · rw [Polynomial.degree_X]; exact_mod_cast hq
        · exact lt_of_le_of_lt Polynomial.degree_C_le (by exact_mod_cast (by omega : 0 < q))
    obtain ⟨y₀, hy₀⟩ := IsAlgClosed.exists_root _ hdeg
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hy₀

    have hy1 : ‖y₀‖ ≤ 1 := by
      by_contra hgt
      push Not at hgt
      have heq : y₀ ^ q = y₀ + c := by linear_combination hy₀
      have h1 : ‖y₀ ^ q‖ ≤ ‖y₀‖ := by
        rw [heq]
        calc ‖y₀ + c‖ ≤ max ‖y₀‖ ‖c‖ := IsUltrametricDist.norm_add_le_max _ _
          _ = ‖y₀‖ := max_eq_left (hc.trans hgt.le)
      have h2 : ‖y₀‖ < ‖y₀ ^ q‖ := by
        rw [norm_pow]
        conv_lhs => rw [← pow_one ‖y₀‖]
        exact pow_lt_pow_right₀ hgt hq
      exact absurd (lt_of_lt_of_le h2 h1) (lt_irrefl _)
    obtain ⟨ζ, hζ, hclose⟩ := Ws47.U1C.exists_rootOfUnity_norm_sub_lt_one hy1
    have hζ1 : ‖ζ‖ ≤ 1 := by
      rcases hζ with rfl | ⟨m, hm, hζm⟩
      · simp
      · have hm0 : m ≠ 0 := by rintro rfl; exact hp.ne_one (Nat.Coprime.eq_one_of_dvd hm (dvd_zero p))
        exact (Ws47.U1C.norm_eq_one_of_pow_eq_one hm0 hζm).le
    refine ⟨ζ, hζ, ?_⟩
    have : ζ ^ q - ζ - c = (ζ ^ q - y₀ ^ q) - (ζ - y₀) + (y₀ ^ q - y₀ - c) := by ring
    rw [this, hy₀, add_zero]
    calc ‖(ζ ^ q - y₀ ^ q) - (ζ - y₀)‖ ≤ max ‖ζ ^ q - y₀ ^ q‖ ‖ζ - y₀‖ := Ws47.U1C.norm_sub_le_max' _ _
      _ ≤ ‖ζ - y₀‖ := max_le (Ws47.U1C.norm_pow_sub_pow_le hζ1 hy1 q) le_rfl
      _ < 1 := by rwa [norm_sub_rev]
  ·
    intro q hpq hq a ha
    have hq1 : 0 < q - 1 := by omega
    have hdeg : (Polynomial.X ^ (q - 1) - Polynomial.C a : Polynomial (PadicAlgCl p)).degree ≠ 0 := by
      rw [Polynomial.degree_X_pow_sub_C hq1]
      exact_mod_cast hq1.ne'
    obtain ⟨y₀, hy₀⟩ := IsAlgClosed.exists_root _ hdeg
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      sub_eq_zero] at hy₀
    have hy1 : ‖y₀‖ = 1 := by
      have h := congrArg norm hy₀
      rw [norm_pow, ha] at h
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hq1.ne').mp h
    obtain ⟨ζ, hζ, hclose⟩ := Ws47.U1C.exists_rootOfUnity_norm_sub_lt_one hy1.le
    rcases hζ with rfl | ⟨m, hm, hζm⟩
    · rw [sub_zero, hy1] at hclose; exact absurd hclose (lt_irrefl _)
    have hm0 : m ≠ 0 := by rintro rfl; exact hp.ne_one (Nat.Coprime.eq_one_of_dvd hm (dvd_zero p))
    have hζ1 : ‖ζ‖ = 1 := Ws47.U1C.norm_eq_one_of_pow_eq_one hm0 hζm
    refine ⟨ζ, ⟨m, hm, hζm⟩, ?_⟩
    rw [← hy₀]
    calc ‖ζ ^ (q - 1) - y₀ ^ (q - 1)‖ ≤ ‖ζ - y₀‖ := Ws47.U1C.norm_pow_sub_pow_le hζ1.le hy1.le _
      _ < 1 := by rwa [norm_sub_rev]

end S_PadicAlgCl_exists_rootOfUnity_norm_sub_lt_one_and_artinSchreier_and_lang
end P2MW
export P2MW.S_PadicAlgCl_exists_rootOfUnity_norm_sub_lt_one_and_artinSchreier_and_lang (solution)
