-- Prove2me | solution 1 for StrongConv.supp_subset_Icc_limsup
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T00:22:50.973321+00:00
-- url     : https://prove2.me/submissions/3db8ee04-2475-4246-bd44-86e6fe1aadcc

import Definitions.Def_StrongConv
import Mathlib

section
section
section
open Polynomial Filter
namespace StrongConv.SV.PartP
open StrongConv StrongConv.SV
lemma supOn_nonneg (f : ℝ → ℝ) (a b : ℝ) : 0 ≤ supOn f a b :=
  Real.sSup_nonneg (by rintro _ ⟨x, -, rfl⟩; exact abs_nonneg _)

lemma le_supOn {f : ℝ → ℝ} (hf : Continuous f) {a b x : ℝ} (hx : x ∈ Set.Icc a b) :
    |f x| ≤ supOn f a b :=
  le_csSup ((isCompact_Icc.image (continuous_abs.comp hf)).bddAbove) ⟨x, hx, rfl⟩

lemma supOn_le {f : ℝ → ℝ} {a b M : ℝ} (hM : 0 ≤ M) (h : ∀ x ∈ Set.Icc a b, |f x| ≤ M) :
    supOn f a b ≤ M :=
  Real.sSup_le (by rintro _ ⟨x, hx, rfl⟩; exact h x hx) hM

lemma cNorm_nonneg (m : ℕ) (f : ℝ → ℝ) (a b : ℝ) : 0 ≤ cNorm m f a b :=
  Finset.sum_nonneg fun _ _ => supOn_nonneg _ _ _

lemma polyFun_X_pow (p : ℕ) : ((polyFun (X ^ p) : smoothFun) : ℝ → ℝ) = fun x => x ^ p := by
  funext x; simp [polyFun]

lemma cNorm_pow_le (m p : ℕ) (K : ℝ) :
    cNorm m (fun x : ℝ => x ^ p) (-K) K ≤ (m + 1) * ((p + m : ℝ) ^ m * (max 1 K) ^ p) := by
  unfold cNorm
  have hb : ∀ j ∈ Finset.range (m + 1),
      supOn (iteratedDeriv j (fun x : ℝ => x ^ p)) (-K) K ≤ (p + m : ℝ) ^ m * (max 1 K) ^ p := by
    intro j hj
    have hj' : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    apply supOn_le (by positivity)
    intro x hx
    rw [iteratedDeriv_eq_iterate, iter_deriv_pow, abs_mul, Finset.abs_prod, abs_pow]
    have hx1 : |x| ≤ max 1 K := (abs_le.2 ⟨hx.1, hx.2⟩).trans (le_max_right _ _)
    have h1 : ∏ i ∈ Finset.range j, |(p : ℝ) - i| ≤ (p + m : ℝ) ^ m := by
      calc ∏ i ∈ Finset.range j, |(p : ℝ) - i| ≤ ∏ i ∈ Finset.range j, (p + m : ℝ) := by
            apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
            intro i hi
            have hi' : (i : ℝ) ≤ m := by
              have := Finset.mem_range.1 hi; exact_mod_cast (by omega : i ≤ m)
            rw [abs_le]; constructor <;> nlinarith [(Nat.cast_nonneg p : (0:ℝ) ≤ p),
              (Nat.cast_nonneg i : (0:ℝ) ≤ i)]
        _ = (p + m : ℝ) ^ j := by simp
        _ ≤ (p + m : ℝ) ^ m := by
            rcases eq_or_ne p 0 with rfl | hp
            · rcases Nat.eq_zero_or_pos m with rfl | hm
              · simp at hj'; simp [hj']
              · rcases Nat.eq_zero_or_pos j with rfl | hjp
                · simp; exact one_le_pow₀ (by simp; exact_mod_cast hm)
                · simp; exact pow_le_pow_right₀ (by exact_mod_cast hm) hj'
            · apply pow_le_pow_right₀ _ hj'
              have : (1:ℝ) ≤ p := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hp
              linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
    have h2 : |x| ^ (p - j) ≤ (max 1 K) ^ p := by
      calc |x| ^ (p - j) ≤ (max 1 K) ^ (p - j) := pow_le_pow_left₀ (abs_nonneg _) hx1 _
        _ ≤ (max 1 K) ^ p := pow_le_pow_right₀ (le_max_left _ _) (Nat.sub_le _ _)
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  calc _ ≤ ∑ j ∈ Finset.range (m + 1), (p + m : ℝ) ^ m * (max 1 K) ^ p := Finset.sum_le_sum hb
    _ = _ := by simp

/-- The moment roots are bounded above. -/
lemma mom_root_bdd (ν : smoothFun →ₗ[ℝ] ℝ) (hν : IsCSDistribution ν) :
    ∃ M : ℝ, ∀ p : ℕ, |ν (polyFun (X ^ p))| ^ (1 / (p : ℝ)) ≤ M := by
  obtain ⟨c, K, m, hc, hK, hb⟩ := hν
  set D : ℝ := max 1 (c * (m + 1) * (m + 1 : ℝ) ^ m)
  set E : ℝ := 2 ^ m * max 1 K
  refine ⟨D * E, fun p => ?_⟩
  have hD : 1 ≤ D := le_max_left _ _
  have hE : 1 ≤ E := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (le_max_left _ _)
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp; nlinarith
  have hmain : |ν (polyFun (X ^ p))| ≤ D * E ^ p := by
    have h1 := hb (polyFun (X ^ p))
    rw [polyFun_X_pow] at h1
    have h2 := cNorm_pow_le m p K
    have hpm : (p + m : ℝ) ≤ (m + 1) * 2 ^ p := by
      have : (p : ℝ) < 2 ^ p := by exact_mod_cast Nat.lt_two_pow_self
      have : (1 : ℝ) ≤ 2 ^ p := one_le_pow₀ (by norm_num)
      nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
    have h3 : (p + m : ℝ) ^ m ≤ (m + 1 : ℝ) ^ m * (2 ^ m) ^ p := by
      calc (p + m : ℝ) ^ m ≤ ((m + 1) * 2 ^ p) ^ m := pow_le_pow_left₀ (by positivity) hpm _
        _ = _ := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm p m]
    calc |ν (polyFun (X ^ p))| ≤ c * ((m + 1) * ((p + m : ℝ) ^ m * (max 1 K) ^ p)) :=
          h1.trans (mul_le_mul_of_nonneg_left h2 hc.le)
      _ ≤ c * ((m + 1) * ((m + 1 : ℝ) ^ m * (2 ^ m) ^ p * (max 1 K) ^ p)) := by gcongr
      _ = (c * (m + 1) * (m + 1 : ℝ) ^ m) * E ^ p := by rw [mul_pow]; ring
      _ ≤ D * E ^ p := by gcongr; exact le_max_right _ _
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  calc |ν (polyFun (X ^ p))| ^ (1 / (p : ℝ)) ≤ (D * E ^ p) ^ (1 / (p : ℝ)) :=
        Real.rpow_le_rpow (abs_nonneg _) hmain (by positivity)
    _ = D ^ (1 / (p : ℝ)) * E := by
        rw [Real.mul_rpow (by positivity) (by positivity), one_div,
          Real.pow_rpow_inv_natCast (by positivity) hp.ne']
    _ ≤ D * E := by
        gcongr
        calc D ^ (1 / (p : ℝ)) ≤ D ^ (1 : ℝ) := by
              apply Real.rpow_le_rpow_of_exponent_le hD
              rw [div_le_one (by positivity)]; exact_mod_cast hp
          _ = D := Real.rpow_one D

theorem limsup_nonneg (ν : smoothFun →ₗ[ℝ] ℝ) (hν : IsCSDistribution ν) :
    0 ≤ limsup (fun p : ℕ => |ν (polyFun (X ^ p))| ^ (1 / (p : ℝ))) atTop := by
  obtain ⟨M, hM⟩ := mom_root_bdd ν hν
  exact le_limsup_of_frequently_le (Frequently.of_forall fun p => Real.rpow_nonneg (abs_nonneg _) _)
    (isBoundedUnder_of ⟨M, hM⟩)

theorem mom_bound (ν : smoothFun →ₗ[ℝ] ℝ) (hν : IsCSDistribution ν) (s : ℝ)
    (hs : limsup (fun p : ℕ => |ν (polyFun (X ^ p))| ^ (1 / (p : ℝ))) atTop < s) :
    0 < s ∧ ∃ C : ℝ, ∀ p : ℕ, |ν (polyFun (X ^ p))| ≤ C * s ^ p := by
  have hs0 : 0 < s := (limsup_nonneg ν hν).trans_lt hs
  refine ⟨hs0, ?_⟩
  obtain ⟨M, hM⟩ := mom_root_bdd ν hν
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_lt_of_limsup_lt hs (isBoundedUnder_of ⟨M, hM⟩))
  set N' := N + 1
  refine ⟨1 + ∑ p ∈ Finset.range N', |ν (polyFun (X ^ p))| / s ^ p, fun p => ?_⟩
  have hsp : 0 < s ^ p := pow_pos hs0 p
  have hnn : 0 ≤ ∑ p ∈ Finset.range N', |ν (polyFun (X ^ p))| / s ^ p :=
    Finset.sum_nonneg fun _ _ => by positivity
  rcases lt_or_ge p N' with hp | hp
  · have h1 : |ν (polyFun (X ^ p))| / s ^ p ≤ ∑ p ∈ Finset.range N', |ν (polyFun (X ^ p))| / s ^ p :=
      Finset.single_le_sum (f := fun p => |ν (polyFun (X ^ p))| / s ^ p)
        (fun _ _ => by positivity) (Finset.mem_range.2 hp)
    rw [div_le_iff₀ hsp] at h1
    nlinarith
  · have hpN : N ≤ p := by omega
    have hp0 : p ≠ 0 := by omega
    have h1 := (hN p hpN).le
    have h2 : |ν (polyFun (X ^ p))| ≤ s ^ p := by
      rw [← Real.rpow_inv_natCast_pow (abs_nonneg (ν (polyFun (X ^ p)))) hp0]
      rw [one_div] at h1
      exact pow_le_pow_left₀ (by positivity) h1 _
    nlinarith

end StrongConv.SV.PartP
end

section
open Polynomial Filter
namespace StrongConv.SV
/-!
# CGTvH Lemma 4.9 (support bounded by moment growth): Blueprint

Elementary route (no Stieltjes transform): approximate a test function vanishing near
`[-r, r]` by polynomials in `x^q` (Landau convolution), small on a complex disk; Cauchy's
estimate bounds their moments against the moment growth `s^p`, `s < r`.
-/
/-! ## Part P -/
alias mom_bound := StrongConv.SV.PartP.mom_bound

alias limsup_nonneg := StrongConv.SV.PartP.limsup_nonneg

end StrongConv.SV
end

section
open Polynomial Filter
namespace StrongConv.SV.PartP
open StrongConv StrongConv.SV
/-- Weak Faà di Bruno for `x ↦ x ^ q`. -/
lemma faa_pow (q j : ℕ) : ∃ P : ℕ → ℝ[X], ∀ u : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) u → ∀ x : ℝ,
    iteratedDeriv j (fun x => u (x ^ q)) x =
      ∑ i ∈ Finset.range (j + 1), iteratedDeriv i u (x ^ q) * (P i).eval x := by
  induction j with
  | zero => exact ⟨fun _ => 1, fun u _ x => by simp⟩
  | succ j ih =>
    obtain ⟨P, hP⟩ := ih
    refine ⟨fun i => (if i < j + 1 then derivative (P i) else 0) +
      (if i = 0 then 0 else C (q : ℝ) * X ^ (q - 1) * P (i - 1)), fun u hu x => ?_⟩
    have hfun : iteratedDeriv j (fun x => u (x ^ q)) =
        fun x => ∑ i ∈ Finset.range (j + 1), iteratedDeriv i u (x ^ q) * (P i).eval x :=
      funext (hP u hu)
    have hder : ∀ i, HasDerivAt (fun x => iteratedDeriv i u (x ^ q) * (P i).eval x)
        (iteratedDeriv (i + 1) u (x ^ q) * ((q : ℝ) * x ^ (q - 1)) * (P i).eval x +
          iteratedDeriv i u (x ^ q) * (derivative (P i)).eval x) x := by
      intro i
      have h1 : HasDerivAt (iteratedDeriv i u) (iteratedDeriv (i + 1) u (x ^ q)) (x ^ q) := by
        rw [iteratedDeriv_succ]
        exact (hu.differentiable_iteratedDeriv i
          (by exact_mod_cast ENat.natCast_lt_top i)).differentiableAt.hasDerivAt
      have h2 := h1.comp x (hasDerivAt_pow q x)
      exact h2.mul (Polynomial.hasDerivAt (P i) x)
    rw [iteratedDeriv_succ, hfun, (HasDerivAt.fun_sum (A := fun i x => iteratedDeriv i u (x ^ q) * (P i).eval x) fun i _ => hder i).deriv]
    simp only [eval_add, mul_add, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    · symm; rw [Finset.sum_range_succ, if_neg (lt_irrefl _), eval_zero, mul_zero, add_zero]
      apply Finset.sum_congr rfl
      intro i hi
      rw [if_pos (Finset.mem_range.1 hi)]
    · symm; rw [Finset.sum_range_succ', if_pos rfl, eval_zero, mul_zero, add_zero]
      apply Finset.sum_congr rfl
      intro i _
      rw [if_neg (Nat.succ_ne_zero i), Nat.add_sub_cancel]
      simp only [eval_mul, eval_C, eval_pow, eval_X]
      ring

theorem comp_pow_cNorm_le (q m : ℕ) (K : ℝ) (hK : 0 < K) :
    ∃ C : ℝ, ∀ u : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) u →
      cNorm m (fun x => u (x ^ q)) (-K) K ≤ C * cNorm m u (-(K ^ q)) (K ^ q) := by
  choose P hP using faa_pow q
  set S : ℕ → ℝ := fun j => ∑ i ∈ Finset.range (j + 1), supOn (fun x => (P j i).eval x) (-K) K
  refine ⟨∑ j ∈ Finset.range (m + 1), S j, fun u hu => ?_⟩
  set N := cNorm m u (-(K ^ q)) (K ^ q)
  have hN : 0 ≤ N := cNorm_nonneg _ _ _ _
  unfold cNorm
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hjm : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  apply supOn_le (mul_nonneg (Finset.sum_nonneg fun _ _ => supOn_nonneg _ _ _) hN)
  intro x hx
  rw [hP j u hu x]
  have hxq : x ^ q ∈ Set.Icc (-(K ^ q)) (K ^ q) := by
    have : |x ^ q| ≤ K ^ q := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_le.2 ⟨hx.1, hx.2⟩) _
    exact ⟨(abs_le.1 this).1, (abs_le.1 this).2⟩
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  simp only [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ m := by have := Finset.mem_range.1 hi; omega
  rw [abs_mul, mul_comm (supOn _ _ _)]
  apply mul_le_mul _ _ (abs_nonneg _) hN
  · calc |iteratedDeriv i u (x ^ q)| ≤ supOn (iteratedDeriv i u) (-(K ^ q)) (K ^ q) :=
          le_supOn (hu.continuous_iteratedDeriv i (by exact_mod_cast le_top)) hxq
      _ ≤ N := Finset.single_le_sum (f := fun i => supOn (iteratedDeriv i u) (-(K ^ q)) (K ^ q))
          (fun _ _ => supOn_nonneg _ _ _) (Finset.mem_range.2 (by omega))
  · exact le_supOn (P j i).continuous hx

end StrongConv.SV.PartP
end

section
open Polynomial Filter
namespace StrongConv.SV
alias comp_pow_cNorm_le := StrongConv.SV.PartP.comp_pow_cNorm_le

end StrongConv.SV
end

section
open Polynomial Filter
namespace StrongConv.SV.PartP
open StrongConv StrongConv.SV
lemma iteratedDeriv_eventually_zero {h : ℝ → ℝ} {x : ℝ} (hx : h =ᶠ[nhds x] 0) (j : ℕ) :
    iteratedDeriv j h =ᶠ[nhds x] 0 := by
  induction j with
  | zero => simpa using hx
  | succ j ih =>
    rw [iteratedDeriv_succ]
    have := ih.deriv
    refine this.trans ?_
    simp

theorem localize (ν : smoothFun →ₗ[ℝ] ℝ) (hν : IsCSDistribution ν) (f : smoothFun) :
    ∃ g : smoothFun, HasCompactSupport (g : ℝ → ℝ) ∧ ν g = ν f ∧
      ∀ x, (f : ℝ → ℝ) x = 0 → (g : ℝ → ℝ) x = 0 := by
  obtain ⟨c, K, m, hc, hK, hb⟩ := hν
  let χ : ContDiffBump (0 : ℝ) := ⟨K + 1, K + 2, by linarith, by linarith⟩
  have hf : ContDiff ℝ (⊤ : ℕ∞) (f : ℝ → ℝ) := f.2
  let g : smoothFun := ⟨fun x => χ x * (f : ℝ → ℝ) x, (χ.contDiff).mul hf⟩
  have hg : ((g : smoothFun) : ℝ → ℝ) = fun x => χ x * (f : ℝ → ℝ) x := rfl
  refine ⟨g, ?_, ?_, ?_⟩
  · rw [hg]; exact χ.hasCompactSupport.mul_right
  · have h0 : |ν (f - g)| ≤ 0 := by
      refine (hb (f - g)).trans ?_
      have : cNorm m ((f - g : smoothFun) : ℝ → ℝ) (-K) K ≤ 0 := by
        unfold cNorm
        refine (Finset.sum_le_sum fun j _ => supOn_le le_rfl fun x hx => ?_).trans
          (by simp)
        have hev : ((f - g : smoothFun) : ℝ → ℝ) =ᶠ[nhds x] 0 := by
          have : Metric.ball (0 : ℝ) (K + 1) ∈ nhds x :=
            Metric.isOpen_ball.mem_nhds (by
              rw [Metric.mem_ball, Real.dist_eq, sub_zero]
              have := abs_le.2 ⟨hx.1, hx.2⟩; linarith)
          filter_upwards [this] with y hy
          have h1 : χ y = 1 := χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
          simp [hg, h1]
        rw [(iteratedDeriv_eventually_zero hev j).eq_of_nhds]
        simp
      nlinarith
    have := abs_nonpos_iff.1 h0
    rw [map_sub, sub_eq_zero] at this
    exact this.symm
  · intro x hx
    rw [hg]; simp [hx]

theorem odd_root_smooth (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (r : ℝ) (hr : 0 < r) (hfz : ∀ x ∈ Set.Ioo (-r) r, f x = 0) (q : ℕ) (hq : Odd q) :
    ∃ G : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) G ∧ HasCompactSupport G ∧
      (∀ y ∈ Set.Ioo (-(r ^ q)) (r ^ q), G y = 0) ∧ ∀ x, G (x ^ q) = f x := by
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  have hqpos : (0 : ℝ) < 1 / (q : ℝ) := by
    have : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq0
    positivity
  let ρ : ℝ → ℝ := fun y => if 0 ≤ y then y ^ (1 / (q : ℝ)) else -((-y) ^ (1 / (q : ℝ)))
  have habs : ∀ y, |ρ y| = |y| ^ (1 / (q : ℝ)) := by
    intro y
    by_cases hy : 0 ≤ y
    · simp only [ρ, if_pos hy, abs_of_nonneg hy]
      exact abs_of_nonneg (Real.rpow_nonneg hy _)
    · simp only [ρ, if_neg hy, abs_neg, abs_of_neg (not_le.1 hy)]
      exact abs_of_nonneg (Real.rpow_nonneg (by linarith [not_le.1 hy]) _)
  have hρq : ∀ x, ρ (x ^ q) = x := by
    intro x
    rcases le_or_gt 0 x with hx | hx
    · simp only [ρ, if_pos (pow_nonneg hx q), one_div]
      exact Real.pow_rpow_inv_natCast hx hq0
    · have hneg : x ^ q < 0 := hq.pow_neg hx
      simp only [ρ, if_neg (not_le.2 hneg), one_div]
      rw [← hq.neg_pow, Real.pow_rpow_inv_natCast (by linarith) hq0, neg_neg]
  have hrq : (r ^ q) ^ (1 / (q : ℝ)) = r := by
    rw [one_div]; exact Real.pow_rpow_inv_natCast hr.le hq0
  have hGz : ∀ y ∈ Set.Ioo (-(r ^ q)) (r ^ q), f (ρ y) = 0 := by
    intro y hy
    apply hfz
    have h1 : |y| < r ^ q := abs_lt.2 hy
    have h2 : |ρ y| < r := by
      rw [habs, ← hrq]
      exact Real.rpow_lt_rpow (abs_nonneg _) h1 hqpos
    exact abs_lt.1 h2
  refine ⟨fun y => f (ρ y), ?_, ?_, hGz, fun x => by simp only [hρq]⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ Set.Ioo (-(r ^ q)) (r ^ q)
    · apply contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq
      filter_upwards [isOpen_Ioo.mem_nhds hy] with z hz
      exact hGz z hz
    · have hy0 : y ≠ 0 := by
        rintro rfl; apply hy; constructor <;> simp [pow_pos hr q]
      rcases lt_or_gt_of_ne hy0 with hneg | hpos
      · have heq : (fun y => f (ρ y)) =ᶠ[nhds y] (fun y => f (-((-y) ^ (1 / (q : ℝ))))) := by
          filter_upwards [Iio_mem_nhds hneg] with z hz
          simp [ρ, not_le.2 (show z < 0 from hz)]
        apply ContDiffAt.congr_of_eventuallyEq _ heq
        apply hf.contDiffAt.comp
        apply ContDiffAt.neg
        apply (Real.contDiffAt_rpow_const_of_ne (by linarith : -y ≠ 0)).comp
        exact contDiffAt_id.neg
      · have heq : (fun y => f (ρ y)) =ᶠ[nhds y] (fun y => f (y ^ (1 / (q : ℝ)))) := by
          filter_upwards [Ioi_mem_nhds hpos] with z hz
          simp [ρ, (show 0 < z from hz).le]
        apply ContDiffAt.congr_of_eventuallyEq _ heq
        exact hf.contDiffAt.comp _ (Real.contDiffAt_rpow_const_of_ne hy0)
  · obtain ⟨B, hB⟩ := hfc.isCompact.isBounded.subset_closedBall 0
    set B' := max B 0
    apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (B' ^ q))
    intro y hy
    simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] at hy
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have h1 := hB hmem
    simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h1
    have h2 : B' < |ρ y| := by
      rw [habs]
      have : (B' ^ q) ^ (1 / (q : ℝ)) = B' := by
        rw [one_div]; exact Real.pow_rpow_inv_natCast (le_max_right _ _) hq0
      rw [← this]
      exact Real.rpow_lt_rpow (by positivity) hy hqpos
    linarith [le_max_left B 0]

end StrongConv.SV.PartP
end

section
open Polynomial Filter
namespace StrongConv.SV
alias odd_root_smooth := StrongConv.SV.PartP.odd_root_smooth

alias localize := StrongConv.SV.PartP.localize

end StrongConv.SV
end

section
open Polynomial Filter
namespace StrongConv.SV.PartL
open StrongConv StrongConv.SV
open MeasureTheory
open scoped Convolution
/-!
# Part L: Landau polynomial approximation (`landau_approx`)

Convolution with the normalized Landau kernel `(1 - t²/D²)ⁿ` on `[-D, D]` approximates `G` in
`C^m` on `[-A, A]`; the convolution is a polynomial `landauPoly`, small on the complex circle of
radius `s`, `t < s < R/2`, so its coefficients are small by Cauchy's estimate.
-/
theorem iteratedDeriv_poly_eval (P : ℂ[X]) (k : ℕ) :
    iteratedDeriv k (fun z => P.eval z) = fun z => (derivative^[k] P).eval z := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    rw [Polynomial.deriv, Function.iterate_succ_apply']

theorem cauchy_coeff (P : ℂ[X]) (s S : ℝ) (hs : 0 < s)
    (h : ∀ z ∈ Metric.sphere (0 : ℂ) s, ‖P.eval z‖ ≤ S) (p : ℕ) :
    ‖P.coeff p‖ ≤ S / s ^ p := by
  have := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (f := fun z => P.eval z)
    p hs (Polynomial.differentiable P).diffContOnCl h
  rw [iteratedDeriv_poly_eval] at this
  simp only at this
  rw [← coeff_zero_eq_eval_zero, coeff_iterate_derivative] at this
  simp only [zero_add, Nat.descFactorial_self, nsmul_eq_mul, norm_mul, Complex.norm_natCast] at this
  have hf : (0 : ℝ) < p.factorial := by exact_mod_cast p.factorial_pos
  rw [mul_div_assoc] at this
  exact le_of_mul_le_mul_left this hf

noncomputable def kI (D : ℝ) (n : ℕ) : ℝ := ∫ t in (-D)..D, (1 - t ^ 2 / D ^ 2) ^ n

noncomputable def kern (D : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  Set.indicator (Set.Icc (-D) D) (fun t => (1 - t ^ 2 / D ^ 2) ^ n / kI D n) t

theorem base_nonneg {D t : ℝ} (hD : 0 < D) (ht : t ∈ Set.Icc (-D) D) : 0 ≤ 1 - t ^ 2 / D ^ 2 := by
  have : t ^ 2 ≤ D ^ 2 := by nlinarith [ht.1, ht.2]
  rw [sub_nonneg, div_le_one (by positivity)]; exact this

theorem kI_lower {D : ℝ} (hD : 0 < D) {n : ℕ} (hn : 1 ≤ n) : D / (2 * n) ≤ kI D n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set h := D / (2 * n) with hh
  have hh0 : 0 < h := by positivity
  have hhD : h ≤ D := by
    rw [hh, div_le_iff₀ (by positivity)]; nlinarith
  have hcont : Continuous (fun t : ℝ => (1 - t ^ 2 / D ^ 2) ^ n) := by fun_prop
  calc D / (2 * n) = ∫ _ in (-h)..h, (1 / 2 : ℝ) := by
        rw [intervalIntegral.integral_const]; simp [hh]; ring
    _ ≤ ∫ t in (-h)..h, (1 - t ^ 2 / D ^ 2) ^ n := by
        apply intervalIntegral.integral_mono_on (by linarith) (by simp)
          (hcont.intervalIntegrable _ _)
        intro t ht
        have ht2 : t ^ 2 ≤ h ^ 2 := by nlinarith [ht.1, ht.2]
        have hq : t ^ 2 / D ^ 2 ≤ 1 / (4 * n ^ 2) := by
          rw [div_le_iff₀ (by positivity)]
          calc t ^ 2 ≤ h ^ 2 := ht2
            _ = 1 / (4 * n ^ 2) * D ^ 2 := by rw [hh]; field_simp; ring
        have hq0 : 0 ≤ t ^ 2 / D ^ 2 := by positivity
        have hb := one_add_mul_le_pow (a := -(t ^ 2 / D ^ 2)) (by
          have : 1 / (4 * (n : ℝ) ^ 2) ≤ 1 := by
            rw [div_le_one (by positivity)]; nlinarith
          linarith) n
        have h4 : (n : ℝ) * (t ^ 2 / D ^ 2) ≤ 1 / 4 := by
          calc (n : ℝ) * (t ^ 2 / D ^ 2) ≤ n * (1 / (4 * n ^ 2)) :=
                mul_le_mul_of_nonneg_left hq (by positivity)
            _ = 1 / (4 * n) := by field_simp
            _ ≤ 1 / 4 := by
                apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
        have : 1 - t ^ 2 / D ^ 2 = 1 + -(t ^ 2 / D ^ 2) := by ring
        rw [this]; nlinarith
    _ ≤ kI D n := by
        apply intervalIntegral.integral_mono_interval (by linarith) (by linarith) hhD
        · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          exact pow_nonneg (base_nonneg hD ⟨ht.1.le, ht.2⟩) n
        · exact hcont.intervalIntegrable _ _

theorem kI_pos {D : ℝ} (hD : 0 < D) (n : ℕ) : 0 < kI D n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [kI]; linarith
  · exact lt_of_lt_of_le (by positivity) (kI_lower hD hn)

theorem kern_nonneg {D : ℝ} (hD : 0 < D) (n : ℕ) (t : ℝ) : 0 ≤ kern D n t := by
  unfold kern
  by_cases ht : t ∈ Set.Icc (-D) D
  · rw [Set.indicator_of_mem ht]
    exact div_nonneg (pow_nonneg (base_nonneg hD ht) n) (kI_pos hD n).le
  · rw [Set.indicator_of_notMem ht]

theorem kern_integrable (D : ℝ) (n : ℕ) : Integrable (kern D n) := by
  unfold kern
  apply IntegrableOn.integrable_indicator _ measurableSet_Icc
  exact (by fun_prop : Continuous (fun t : ℝ => (1 - t ^ 2 / D ^ 2) ^ n / kI D n)).integrableOn_Icc

theorem kern_integral {D : ℝ} (hD : 0 < D) (n : ℕ) : ∫ t, kern D n t = 1 := by
  unfold kern
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_div]
  exact div_self (kI_pos hD n).ne'

theorem hcs_iteratedDeriv {G : ℝ → ℝ} (hGc : HasCompactSupport G) (j : ℕ) :
    HasCompactSupport (iteratedDeriv j G) := by
  induction j with
  | zero => simpa using hGc
  | succ j ih => rw [iteratedDeriv_succ]; exact ih.deriv

theorem cd_iteratedDeriv {G : ℝ → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv j G) := by
  rw [iteratedDeriv_eq_iterate]; exact ContDiff.iterate_deriv j hG

theorem conv_apply (k g : ℝ → ℝ) (x : ℝ) :
    (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] g) x = ∫ t, k t * g (x - t) := by
  rw [convolution_def]; simp

theorem approx (g : ℝ → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g) {D : ℝ} (hD : 0 < D)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n in atTop, ∀ x, |(kern D n ⋆[ContinuousLinearMap.lsmul ℝ ℝ] g) x - g x| ≤ η := by
  obtain ⟨δ0, hδ0, hδ0'⟩ := Metric.uniformContinuous_iff.mp
    (hgc.uniformContinuous_of_continuous hg) (η / 2) (by positivity)
  obtain ⟨M, hM⟩ := hg.bounded_above_of_compact_support hgc
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  set δ := min (δ0 / 2) D with hδ
  have hδpos : 0 < δ := lt_min (by positivity) hD
  have hδδ0 : δ < δ0 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδD : δ ≤ D := min_le_right _ _
  set r := 1 - δ ^ 2 / D ^ 2 with hr
  have hr0 : 0 ≤ r := by
    rw [hr, sub_nonneg, div_le_one (by positivity)]; nlinarith
  have hr1 : r < 1 := by rw [hr]; have : 0 < δ ^ 2 / D ^ 2 := by positivity
                         linarith
  have ht := tendsto_self_mul_const_pow_of_lt_one hr0 hr1
  have hev : ∀ᶠ n : ℕ in atTop, (n : ℝ) * r ^ n < η / (16 * (M + 1)) :=
    ht.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1 x
  have hkI := kI_lower hD hn1
  have hkIpos := kI_pos hD n
  have hki := kern_integrable D n
  have hbdd : Integrable (fun t => kern D n t * g (x - t)) := by
    apply hki.mul_bdd (c := M)
    · exact (hg.comp (by fun_prop)).aestronglyMeasurable
    · exact Eventually.of_forall (fun t => hM _)
  have hrw : (kern D n ⋆[ContinuousLinearMap.lsmul ℝ ℝ] g) x - g x =
      ∫ t, kern D n t * (g (x - t) - g x) := by
    rw [conv_apply, eq_comm]
    calc ∫ t, kern D n t * (g (x - t) - g x)
        = ∫ t, (kern D n t * g (x - t) - kern D n t * g x) := by
          congr 1; funext t; ring
      _ = (∫ t, kern D n t * g (x - t)) - ∫ t, kern D n t * g x :=
          integral_sub hbdd (hki.mul_const _)
      _ = _ := by rw [integral_mul_const, kern_integral hD, one_mul]
  set c := 2 * M * (r ^ n / kI D n) with hc
  have hbound : Integrable (fun t => η / 2 * kern D n t +
      Set.indicator (Set.Icc (-D) D) (fun _ => c) t) :=
    (hki.const_mul _).add
      ((continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc)
  rw [hrw, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hbound (Eventually.of_forall (fun t => ?_))).trans ?_
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (kern_nonneg hD n t)]
    by_cases htm : t ∈ Set.Icc (-D) D
    · rw [Set.indicator_of_mem htm]
      by_cases htd : |t| < δ
      · have : |g (x - t) - g x| ≤ η / 2 := by
          have := hδ0' (a := x - t) (b := x) (by
            rw [Real.dist_eq]; simp only [sub_sub_cancel_left, abs_neg]; linarith)
          rw [Real.dist_eq] at this; exact this.le
        have hc0 : 0 ≤ c := by positivity
        nlinarith [kern_nonneg hD n t]
      · push Not at htd
        have hk : kern D n t ≤ r ^ n / kI D n := by
          unfold kern; rw [Set.indicator_of_mem htm]
          apply div_le_div_of_nonneg_right _ hkIpos.le
          apply pow_le_pow_left₀ (base_nonneg hD htm)
          rw [hr]
          have : δ ^ 2 ≤ t ^ 2 := by
            have := sq_le_sq' (by linarith [abs_nonneg t, neg_abs_le t, le_abs_self t]) htd
            nlinarith [sq_abs t, abs_nonneg t]
          have : δ ^ 2 / D ^ 2 ≤ t ^ 2 / D ^ 2 := div_le_div_of_nonneg_right this (by positivity)
          linarith
        have h2 : |g (x - t) - g x| ≤ 2 * M := by
          have h1 := hM (x - t); have h2 := hM x
          rw [Real.norm_eq_abs] at h1 h2
          calc |g (x - t) - g x| ≤ |g (x - t)| + |g x| := abs_sub _ _
            _ ≤ 2 * M := by linarith
        have := mul_le_mul hk h2 (abs_nonneg _) (by positivity)
        have : 0 ≤ η / 2 * kern D n t := mul_nonneg (by positivity) (kern_nonneg hD n t)
        rw [hc]; nlinarith
    · unfold kern; rw [Set.indicator_of_notMem htm, Set.indicator_of_notMem htm]; simp
  · rw [integral_add (hki.const_mul _)
      ((continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc),
      integral_const_mul, kern_integral hD, integral_indicator_const _ measurableSet_Icc,
      Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
    have : c * (D - -D) ≤ η / 2 := by
      rw [hc]
      have h1 : r ^ n / kI D n ≤ r ^ n * (2 * n / D) := by
        rw [div_le_iff₀ hkIpos]
        calc r ^ n = r ^ n * (2 * n / D) * (D / (2 * n)) := by
              field_simp
          _ ≤ r ^ n * (2 * n / D) * kI D n := by
              apply mul_le_mul_of_nonneg_left hkI; positivity
      calc 2 * M * (r ^ n / kI D n) * (D - -D) ≤ 2 * M * (r ^ n * (2 * n / D)) * (D - -D) := by
            gcongr; linarith
        _ = 8 * M * (n * r ^ n) := by field_simp; ring
        _ ≤ 8 * M * (η / (16 * (M + 1))) := by gcongr
        _ ≤ η / 2 := by
            rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith
    linarith

noncomputable def Phi (D c : ℝ) (n : ℕ) : ℝ[X][X] :=
  C (C c) * (1 - (X - C X) ^ 2 * C (C (1 / D ^ 2))) ^ n

noncomputable def landauPoly (G : ℝ → ℝ) (D c : ℝ) (n : ℕ) : ℝ[X] :=
  ∑ p ∈ Finset.range ((Phi D c n).natDegree + 1),
    C (∫ y, G y * ((Phi D c n).coeff p).eval y) * X ^ p

theorem Phi_eval₂ {𝕜 : Type*} [RCLike 𝕜] (D c : ℝ) (n : ℕ) (y : ℝ) (w : 𝕜) :
    (Phi D c n).eval₂ (aeval (algebraMap ℝ 𝕜 y)).toRingHom w =
      (c : 𝕜) * (1 - (w - (y : 𝕜)) ^ 2 * ((1 / D ^ 2 : ℝ) : 𝕜)) ^ n := by
  simp [Phi, eval₂_mul, eval₂_pow, eval₂_sub, RCLike.algebraMap_eq_ofReal]

theorem landauPoly_aeval {𝕜 : Type*} [RCLike 𝕜] (G : ℝ → ℝ) (hG : Continuous G)
    (hGc : HasCompactSupport G) (D c : ℝ) (n : ℕ) (w : 𝕜) :
    aeval w (landauPoly G D c n) =
      ∫ y, (G y : 𝕜) * ((c : 𝕜) * (1 - (w - (y : 𝕜)) ^ 2 * ((1 / D ^ 2 : ℝ) : 𝕜)) ^ n) := by
  have hint : ∀ p, Integrable (fun y => G y * ((Phi D c n).coeff p).eval y) := fun p =>
    (hG.mul (Polynomial.continuous _)).integrable_of_hasCompactSupport (hGc.mul_right)
  simp only [landauPoly, map_sum, map_mul, aeval_C, aeval_X_pow, RCLike.algebraMap_eq_ofReal]
  simp_rw [← integral_ofReal, ← integral_mul_const]
  rw [← integral_finsetSum _ (fun p _ => ((hint p).ofReal).mul_const _)]
  congr 1; funext y
  rw [← Phi_eval₂, eval₂_eq_sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  simp [aeval_algebraMap_apply, RCLike.algebraMap_eq_ofReal]
  ring

theorem z_bound (s R B D y : ℝ) (w : ℂ) (hs : 0 < s) (hsR : 2 * s < R) (hw : ‖w‖ = s)
    (hyR : R ≤ |y|) (hyB : |y| ≤ B) (hD : 0 < D)
    (hDbig : (s + B) ^ 4 ≤ R * (R - 2 * s) * D ^ 2) :
    ‖1 - (w - (y : ℂ)) ^ 2 * ((1 / D ^ 2 : ℝ) : ℂ)‖ ≤ 1 - R * (R - 2 * s) / (2 * D ^ 2) := by
  set a := w.re
  set b := w.im
  have hab : a ^ 2 + b ^ 2 = s ^ 2 := by
    rw [← hw, Complex.sq_norm, Complex.normSq_apply]; ring
  set z := 1 - (w - (y : ℂ)) ^ 2 * ((1 / D ^ 2 : ℝ) : ℂ) with hz
  have hre : z.re = 1 - ((a - y) ^ 2 - b ^ 2) / D ^ 2 := by
    simp [hz, pow_two, a, b]; ring
  have him : z.im = -(2 * (a - y) * b) / D ^ 2 := by
    simp [hz, pow_two, a, b]; ring
  set Q := (a - y) ^ 2 - b ^ 2
  set P := (a - y) ^ 2 + b ^ 2
  have hid : Q ^ 2 + (2 * (a - y) * b) ^ 2 = P ^ 2 := by ring
  have ha : |a| ≤ s := by
    rw [← Real.sqrt_sq hs.le, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hb2 : b ^ 2 ≤ s ^ 2 := by nlinarith
  have hQ : R * (R - 2 * s) ≤ Q := by
    have h1 : R - s ≤ |a - y| := by
      have := abs_sub_abs_le_abs_sub y a
      rw [abs_sub_comm] at this; linarith
    have h2 : (R - s) ^ 2 ≤ (a - y) ^ 2 := by
      rw [← sq_abs (a - y)]; exact pow_le_pow_left₀ (by linarith) h1 2
    show R * (R - 2 * s) ≤ (a - y) ^ 2 - b ^ 2
    nlinarith
  have hP0 : 0 ≤ P := by positivity
  have hP : P ≤ (s + B) ^ 2 := by
    have h1 : -(a * y) ≤ s * B := by
      have := abs_mul a y
      have h3 : |a * y| ≤ s * B := by
        rw [abs_mul]; exact mul_le_mul ha hyB (abs_nonneg _) hs.le
      linarith [neg_abs_le (a * y)]
    have h4 : y ^ 2 ≤ B ^ 2 := by
      rw [← sq_abs y]; exact pow_le_pow_left₀ (abs_nonneg _) hyB 2
    show (a - y) ^ 2 + b ^ 2 ≤ (s + B) ^ 2
    nlinarith
  have hD2 : 0 < D ^ 2 := by positivity
  have hsq : ‖z‖ ^ 2 ≤ 1 - R * (R - 2 * s) / D ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    have e : (1 - Q / D ^ 2) * (1 - Q / D ^ 2) + -(2 * (a - y) * b) / D ^ 2 * (-(2 * (a - y) * b) / D ^ 2)
        = 1 - 2 * Q / D ^ 2 + P ^ 2 / D ^ 2 / D ^ 2 := by
      field_simp; linear_combination D ^ 4 * hid
    rw [e]
    have hP2 : P ^ 2 ≤ (s + B) ^ 4 := by
      have := pow_le_pow_left₀ hP0 hP 2; rw [← pow_mul] at this; exact this
    have h5 : P ^ 2 / D ^ 2 / D ^ 2 ≤ R * (R - 2 * s) / D ^ 2 := by
      rw [div_le_div_iff_of_pos_right hD2, div_le_iff₀ hD2]; linarith
    have h6 : R * (R - 2 * s) / D ^ 2 ≤ Q / D ^ 2 := div_le_div_of_nonneg_right hQ hD2.le
    have h7 : 2 * Q / D ^ 2 = 2 * (Q / D ^ 2) := by ring
    linarith
  have : ‖z‖ ≤ (1 + ‖z‖ ^ 2) / 2 := by nlinarith [sq_nonneg (‖z‖ - 1)]
  have e2 : 1 - R * (R - 2 * s) / (2 * D ^ 2) = (1 + (1 - R * (R - 2 * s) / D ^ 2)) / 2 := by
    field_simp; ring
  rw [e2]; linarith

theorem landau_approx (G : ℝ → ℝ) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G)
    (R t : ℝ) (ht : 0 < t) (htR : 2 * t < R) (hGz : ∀ y ∈ Set.Ioo (-R) R, G y = 0)
    (m : ℕ) (A : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ H : ℝ[X], cNorm m (fun y => H.eval y - G y) (-A) A ≤ ε ∧
      ∑ p ∈ Finset.range (H.natDegree + 1), |H.coeff p| * t ^ p ≤ ε := by
  have hGcont : Continuous G := hG.continuous
  obtain ⟨B0, hB0⟩ := hGc.isCompact.isBounded.subset_closedBall (0 : ℝ)
  set B := max B0 0 with hBdef
  have hB : 0 ≤ B := le_max_right _ _
  have hGB : ∀ y, G y ≠ 0 → |y| ≤ B := fun y hy => by
    have := hB0 (subset_tsupport G hy)
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    exact le_trans this (le_max_left _ _)
  have hGR : ∀ y, G y ≠ 0 → R ≤ |y| := by
    intro y hy
    by_contra h
    push Not at h
    exact hy (hGz y ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩)
  set s := (t + R / 2) / 2 with hsdef
  have hts : t < s := by rw [hsdef]; linarith
  have hs0 : 0 < s := by linarith
  have h2s : 2 * s < R := by rw [hsdef]; linarith
  have hR0 : 0 < R := by linarith
  clear_value s
  set δ' := R * (R - 2 * s) with hδ'
  have hδ'0 : 0 < δ' := mul_pos hR0 (by linarith)
  set D := max (max (A + 1 + B) R) (max 1 ((s + B) ^ 4 / δ')) with hDdef
  have hD1 : 1 ≤ D := le_trans (le_max_left _ _) (le_max_right _ _)
  have hD0 : 0 < D := by linarith
  have hDA : A + 1 + B ≤ D := le_trans (le_max_left _ _) (le_max_left _ _)
  have hDR : R ≤ D := le_trans (le_max_right _ _) (le_max_left _ _)
  have hDbig : (s + B) ^ 4 ≤ R * (R - 2 * s) * D ^ 2 := by
    have h1 : (s + B) ^ 4 / δ' ≤ D := le_trans (le_max_right _ _) (le_max_right _ _)
    have h2 : D ≤ D ^ 2 := by nlinarith
    rw [div_le_iff₀ hδ'0] at h1
    rw [← hδ']; nlinarith
  set ρ := 1 - δ' / (2 * D ^ 2) with hρdef
  have hρ0 : 0 ≤ ρ := by
    have h1 : δ' ≤ D ^ 2 := by rw [hδ']; nlinarith
    rw [hρdef, sub_nonneg, div_le_one (by positivity)]; linarith
  have hρ1 : ρ < 1 := by
    rw [hρdef]; have : 0 < δ' / (2 * D ^ 2) := by positivity
    linarith
  set L1 := ∫ y, |G y| with hL1
  have hL10 : 0 ≤ L1 := integral_nonneg (fun _ => abs_nonneg _)
  have ev2 : ∀ᶠ n : ℕ in atTop, L1 * (2 / D) * (n * ρ ^ n) * (s / (s - t)) ≤ ε := by
    have h := ((tendsto_self_mul_const_pow_of_lt_one hρ0 hρ1).const_mul (L1 * (2 / D))).mul_const
      (s / (s - t))
    simp only [mul_zero, zero_mul] at h
    exact h.eventually (ge_mem_nhds hε)
  have ev1 : ∀ j ∈ Finset.range (m + 1), ∀ᶠ n in atTop, ∀ x,
      |(kern D n ⋆[ContinuousLinearMap.lsmul ℝ ℝ] iteratedDeriv j G) x - iteratedDeriv j G x|
        ≤ ε / (m + 1) := fun j _ =>
    approx _ (cd_iteratedDeriv hG j).continuous (hcs_iteratedDeriv hGc j) hD0 _ (by positivity)
  rw [← eventually_all_finset] at ev1
  obtain ⟨n, hn1, hn2, hn3⟩ := (ev1.and (ev2.and (eventually_ge_atTop 1))).exists
  set c := 1 / kI D n with hc
  have hkIpos := kI_pos hD0 n
  have hc0 : 0 ≤ c := by positivity
  set H := landauPoly G D c n with hH
  refine ⟨H, ?_, ?_⟩
  · -- C^m approximation
    have hHreal : ∀ x, H.eval x = ∫ y, G y * (c * (1 - (x - y) ^ 2 * (1 / D ^ 2)) ^ n) := by
      intro x
      have := landauPoly_aeval (𝕜 := ℝ) G hGcont hGc D c n x
      rw [coe_aeval_eq_eval] at this
      simpa using this
    have hconv : ∀ x ∈ Set.Ioo (-A - 1) (A + 1),
        H.eval x = (kern D n ⋆[ContinuousLinearMap.lsmul ℝ ℝ] G) x := by
      intro x hx
      rw [hHreal, conv_apply,
        ← integral_sub_left_eq_self (fun y => G y * (c * (1 - (x - y) ^ 2 * (1 / D ^ 2)) ^ n))
          volume x]
      congr 1; funext u
      simp only [sub_sub_cancel]
      by_cases hG0 : G (x - u) = 0
      · simp [hG0]
      · have h1 := hGB _ hG0
        have hu : u ∈ Set.Icc (-D) D := by
          have h2 : |u| ≤ |x| + |x - u| := by
            have := abs_sub (x) (x - u); simp only [sub_sub_cancel] at this; exact this
          have h3 : |x| < A + 1 := abs_lt.mpr ⟨by linarith [hx.1], hx.2⟩
          constructor <;> linarith [neg_abs_le u, le_abs_self u]
        unfold kern; rw [Set.indicator_of_mem hu, hc]; ring
    have hderiv : ∀ j, ∀ x ∈ Set.Ioo (-A - 1) (A + 1),
        iteratedDeriv j (fun y => H.eval y - G y) x =
          (kern D n ⋆[ContinuousLinearMap.lsmul ℝ ℝ] iteratedDeriv j G) x - iteratedDeriv j G x := by
      intro j
      induction j with
      | zero => intro x hx; simp [hconv x hx]
      | succ j ih =>
        intro x hx
        have hev : iteratedDeriv j (fun y => H.eval y - G y) =ᶠ[nhds x]
            fun z => (kern D n ⋆[ContinuousLinearMap.lsmul ℝ ℝ] iteratedDeriv j G) z -
              iteratedDeriv j G z :=
          Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hx) ih
        simp only [iteratedDeriv_succ]
        rw [hev.deriv_eq]
        have h1 := (hcs_iteratedDeriv hGc j).hasDerivAt_convolution_right
          (ContinuousLinearMap.lsmul ℝ ℝ) (kern_integrable D n).locallyIntegrable
          ((cd_iteratedDeriv hG j).of_le (by exact_mod_cast le_top)) x
        have h2 : HasDerivAt (iteratedDeriv j G) (deriv (iteratedDeriv j G) x) x :=
          ((cd_iteratedDeriv hG j).differentiable (by simp)).differentiableAt.hasDerivAt
        exact (h1.sub h2).deriv
    unfold cNorm
    calc ∑ j ∈ Finset.range (m + 1), supOn (iteratedDeriv j fun y => H.eval y - G y) (-A) A
        ≤ ∑ j ∈ Finset.range (m + 1), ε / (m + 1) := by
          refine Finset.sum_le_sum (fun j hj => ?_)
          unfold supOn
          apply Real.sSup_le _ (by positivity)
          rintro _ ⟨x, hx, rfl⟩
          dsimp only
          rw [hderiv j x ⟨by linarith [hx.1], by linarith [hx.2]⟩]
          exact hn1 j hj x
      _ = ε := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; field_simp
  · -- small coefficients
    have hS : ∀ w ∈ Metric.sphere (0 : ℂ) s,
        ‖(H.map (algebraMap ℝ ℂ)).eval w‖ ≤ L1 * (c * ρ ^ n) := by
      intro w hw
      have hwn : ‖w‖ = s := by simpa using hw
      rw [eval_map_algebraMap, hH, landauPoly_aeval (𝕜 := ℂ) G hGcont hGc D c n w]
      have hint : Integrable (fun y => |G y| * (c * ρ ^ n)) :=
        ((hGcont.integrable_of_hasCompactSupport hGc).abs).mul_const _
      refine (norm_integral_le_of_norm_le hint (Eventually.of_forall fun y => ?_)).trans
        (le_of_eq (integral_mul_const _ _))
      by_cases hG0 : G y = 0
      · simp [hG0]
      · have hz := z_bound s R B D y w hs0 h2s hwn (hGR y hG0) (hGB y hG0) hD0 hDbig
        simp only [norm_mul, norm_pow, RCLike.norm_ofReal, abs_of_nonneg hc0]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply mul_le_mul_of_nonneg_left _ hc0
        apply pow_le_pow_left₀ (norm_nonneg _)
        rw [← hδ'] at hz
        exact hz
    have hcoef : ∀ p, |H.coeff p| ≤ L1 * (c * ρ ^ n) / s ^ p := by
      intro p
      have := cauchy_coeff (H.map (algebraMap ℝ ℂ)) s _ hs0 hS p
      simpa [coeff_map] using this
    set S := L1 * (c * ρ ^ n) with hSdef
    have hS0 : 0 ≤ S := by positivity
    have hq0 : 0 ≤ t / s := by positivity
    have hq1 : t / s < 1 := by rw [div_lt_one hs0]; exact hts
    calc ∑ p ∈ Finset.range (H.natDegree + 1), |H.coeff p| * t ^ p
        ≤ ∑ p ∈ Finset.range (H.natDegree + 1), S * (t / s) ^ p := by
          refine Finset.sum_le_sum (fun p _ => ?_)
          calc |H.coeff p| * t ^ p ≤ S / s ^ p * t ^ p :=
                mul_le_mul_of_nonneg_right (hcoef p) (by positivity)
            _ = S * (t / s) ^ p := by rw [div_pow]; ring
      _ = S * ∑ p ∈ Finset.range (H.natDegree + 1), (t / s) ^ p := by rw [Finset.mul_sum]
      _ ≤ S * (1 / (1 - t / s)) := by
          gcongr
          have := geom_sum_Ico_le_of_lt_one (m := 0) (n := H.natDegree + 1) hq0 hq1
          rwa [← Finset.range_eq_Ico, pow_zero] at this
      _ = S * (s / (s - t)) := by
          congr 1; field_simp
      _ ≤ L1 * (2 / D) * (n * ρ ^ n) * (s / (s - t)) := by
          have hcle : c ≤ 2 * n / D := by
            rw [hc, div_le_div_iff₀ hkIpos hD0]
            have := kI_lower hD0 hn3
            rw [div_le_iff₀ (by positivity)] at this; linarith
          have hst : 0 ≤ s / (s - t) := div_nonneg hs0.le (by linarith)
          rw [hSdef]
          have : L1 * (c * ρ ^ n) ≤ L1 * (2 / D) * (n * ρ ^ n) := by
            have : c * ρ ^ n ≤ 2 * n / D * ρ ^ n :=
              mul_le_mul_of_nonneg_right hcle (pow_nonneg hρ0 n)
            calc L1 * (c * ρ ^ n) ≤ L1 * (2 * n / D * ρ ^ n) :=
                  mul_le_mul_of_nonneg_left this hL10
              _ = L1 * (2 / D) * (n * ρ ^ n) := by ring
          exact mul_le_mul_of_nonneg_right this hst
      _ ≤ ε := hn2

end StrongConv.SV.PartL
end

section
open Polynomial Filter
namespace StrongConv.SV
/-! ## Part L -/
alias landau_approx := StrongConv.SV.PartL.landau_approx

end StrongConv.SV
end

section
open Polynomial Filter
namespace StrongConv.SV.PartV
open StrongConv StrongConv.SV
/-!
# Part V: assembly (`vanish_core`, `supp_subset_Icc_limsup`)
-/
theorem coe_polyFun (P : ℝ[X]) : ((polyFun P : smoothFun) : ℝ → ℝ) = fun x => P.eval x := rfl

theorem cNorm_nonneg (m : ℕ) (f : ℝ → ℝ) (a b : ℝ) : 0 ≤ cNorm m f a b :=
  Finset.sum_nonneg (fun _ _ => Real.sSup_nonneg (by rintro _ ⟨x, _, rfl⟩; exact abs_nonneg _))

theorem polyFun_comp_pow (H : ℝ[X]) (q : ℕ) :
    polyFun (H.comp (X ^ q)) =
      ∑ p ∈ Finset.range (H.natDegree + 1), H.coeff p • polyFun (X ^ (q * p)) := by
  apply Subtype.ext
  funext x
  rw [Submodule.coe_sum, Finset.sum_apply, coe_polyFun]
  simp only [eval_comp, eval_pow, eval_X, Submodule.coe_smul, Pi.smul_apply, coe_polyFun,
    smul_eq_mul]
  rw [eval_eq_sum_range]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [pow_mul]

theorem vanish_core (ν : smoothFun →ₗ[ℝ] ℝ) (hν : IsCSDistribution ν) (C s r : ℝ)
    (hs : 0 < s) (hsr : s < r) (hmom : ∀ p : ℕ, |ν (polyFun (X ^ p))| ≤ C * s ^ p)
    (f : smoothFun) (hf : ∀ x ∈ Set.Ioo (-r) r, (f : ℝ → ℝ) x = 0) : ν f = 0 := by
  have hν' := hν
  obtain ⟨c, K, m, hc, hK, hbound⟩ := hν'
  obtain ⟨g, hgc, hνg, hgz⟩ := localize ν hν f
  have hr : 0 < r := hs.trans hsr
  have hgz' : ∀ x ∈ Set.Ioo (-r) r, (g : ℝ → ℝ) x = 0 := fun x hx => hgz x (hf x hx)
  have hC0 : 0 ≤ C := by
    have := hmom 0; simp only [pow_zero, mul_one] at this; exact (abs_nonneg _).trans this
  -- an odd exponent `q` with `2 s^q < r^q`
  have hsr1 : s / r < 1 := by rw [div_lt_one hr]; exact hsr
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 2) hsr1
  set q := 2 * N + 1 with hqdef
  have hq : Odd q := ⟨N, rfl⟩
  have hsrq : 2 * s ^ q < r ^ q := by
    have h1 : (s / r) ^ q ≤ (s / r) ^ N :=
      pow_le_pow_of_le_one (by positivity) hsr1.le (by omega)
    have h2 : (s / r) ^ q < 1 / 2 := lt_of_le_of_lt h1 hN
    rw [div_pow, div_lt_iff₀ (by positivity)] at h2
    linarith
  obtain ⟨G, hGs, hGc, hGz, hGx⟩ := odd_root_smooth g g.2 hgc r hr hgz' q hq
  obtain ⟨C₁, hC₁⟩ := comp_pow_cNorm_le q m K hK
  set K0 := C + c * |C₁| with hK0
  have hK00 : 0 ≤ K0 := by positivity
  have key : ∀ ε > 0, |ν g| ≤ K0 * ε := by
    intro ε hε
    obtain ⟨H, h1, h2⟩ := landau_approx G hGs hGc (r ^ q) (s ^ q) (pow_pos hs q) hsrq hGz m
      (K ^ q) ε hε
    set h := polyFun (H.comp (X ^ q)) with hh
    have hsplit : ν g = ν h - ν (h - g) := by rw [map_sub]; ring
    -- the polynomial part
    have hνh : |ν h| ≤ C * ε := by
      rw [hh, polyFun_comp_pow, map_sum]
      calc |∑ p ∈ Finset.range (H.natDegree + 1), ν (H.coeff p • polyFun (X ^ (q * p)))|
          ≤ ∑ p ∈ Finset.range (H.natDegree + 1), |ν (H.coeff p • polyFun (X ^ (q * p)))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ p ∈ Finset.range (H.natDegree + 1), C * (|H.coeff p| * (s ^ q) ^ p) := by
            refine Finset.sum_le_sum (fun p _ => ?_)
            rw [map_smul, smul_eq_mul, abs_mul, ← pow_mul]
            calc |H.coeff p| * |ν (polyFun (X ^ (q * p)))| ≤ |H.coeff p| * (C * s ^ (q * p)) :=
                  mul_le_mul_of_nonneg_left (hmom _) (abs_nonneg _)
              _ = C * (|H.coeff p| * s ^ (q * p)) := by ring
        _ = C * ∑ p ∈ Finset.range (H.natDegree + 1), |H.coeff p| * (s ^ q) ^ p := by
            rw [Finset.mul_sum]
        _ ≤ C * ε := mul_le_mul_of_nonneg_left h2 hC0
    -- the remainder
    set u := fun y => H.eval y - G y with hu
    have hus : ContDiff ℝ (⊤ : ℕ∞) u := by
      have : ContDiff ℝ (⊤ : ℕ∞) (fun y => H.eval y) := (polyFun H).2
      exact this.sub hGs
    have hcoe : ((h - g : smoothFun) : ℝ → ℝ) = fun x => u (x ^ q) := by
      funext x
      simp only [Submodule.coe_sub, Pi.sub_apply, hh, coe_polyFun, eval_comp, eval_pow, eval_X,
        hu, hGx]
    have hrest : |ν (h - g)| ≤ c * |C₁| * ε := by
      calc |ν (h - g)| ≤ c * cNorm m (h - g : smoothFun) (-K) K := hbound _
        _ = c * cNorm m (fun x => u (x ^ q)) (-K) K := by rw [hcoe]
        _ ≤ c * (C₁ * cNorm m u (-(K ^ q)) (K ^ q)) :=
            mul_le_mul_of_nonneg_left (hC₁ u hus) hc.le
        _ ≤ c * (|C₁| * ε) := by
            apply mul_le_mul_of_nonneg_left _ hc.le
            calc C₁ * cNorm m u (-(K ^ q)) (K ^ q) ≤ |C₁| * cNorm m u (-(K ^ q)) (K ^ q) :=
                  mul_le_mul_of_nonneg_right (le_abs_self _) (cNorm_nonneg _ _ _ _)
              _ ≤ |C₁| * ε := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = c * |C₁| * ε := by ring
    rw [hsplit]
    calc |ν h - ν (h - g)| ≤ |ν h| + |ν (h - g)| := abs_sub _ _
      _ ≤ C * ε + c * |C₁| * ε := add_le_add hνh hrest
      _ = K0 * ε := by rw [hK0]; ring
  rw [← hνg]
  by_contra hne
  have hpos : 0 < |ν g| := abs_pos.mpr hne
  have := key (|ν g| / (2 * (K0 + 1))) (by positivity)
  have h3 : K0 * (|ν g| / (2 * (K0 + 1))) < |ν g| := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

end StrongConv.SV.PartV
end

section
open Polynomial Filter
namespace StrongConv.SV
/-! ## Part V: assembly -/

end StrongConv.SV
end

section
open Polynomial Filter
namespace StrongConv.SV.PartV
open StrongConv StrongConv.SV
theorem supp_subset_Icc_limsup (ν : smoothFun →ₗ[ℝ] ℝ) (hν : IsCSDistribution ν) :
    supp ν ⊆ Set.Icc (-limsup (fun p : ℕ => |ν (polyFun (X ^ p))| ^ (1 / (p : ℝ))) atTop)
      (limsup (fun p : ℕ => |ν (polyFun (X ^ p))| ^ (1 / (p : ℝ))) atTop) := by
  set ρ := limsup (fun p : ℕ => |ν (polyFun (X ^ p))| ^ (1 / (p : ℝ))) atTop with hρdef
  have hρ : 0 ≤ ρ := limsup_nonneg ν hν
  intro x hx
  refine Set.mem_sInter.mp hx (Set.Icc (-ρ) ρ) ⟨isClosed_Icc, ?_⟩
  intro f hfev
  obtain ⟨U, hUo, hIU, hUf⟩ := mem_nhdsSet_iff_exists.mp hfev
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_Icc (a := -ρ) (b := ρ)).exists_thickening_subset_open hUo hIU
  have hsub : Set.Ioo (-(ρ + δ)) (ρ + δ) ⊆ U := by
    intro y hy
    apply hδU
    rw [Metric.mem_thickening_iff]
    by_cases h1 : y < -ρ
    · refine ⟨-ρ, ⟨le_refl _, by linarith⟩, ?_⟩
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hy.1]
    · by_cases h2 : ρ < y
      · refine ⟨ρ, ⟨by linarith, le_refl _⟩, ?_⟩
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hy.2]
      · push Not at h1 h2
        exact ⟨y, ⟨h1, h2⟩, by simpa using hδ⟩
  obtain ⟨hs, C, hmom⟩ := mom_bound ν hν (ρ + δ / 2) (by rw [← hρdef]; linarith)
  exact vanish_core ν hν C (ρ + δ / 2) (ρ + δ) hs (by linarith) hmom f
    (fun y hy => hUf (hsub hy))

end StrongConv.SV.PartV
end

section
open Polynomial Filter
namespace StrongConv.SV
alias supp_subset_Icc_limsup := StrongConv.SV.PartV.supp_subset_Icc_limsup

end StrongConv.SV
end

alias StrongConv.supp_subset_Icc_limsup_dev := StrongConv.SV.supp_subset_Icc_limsup

end
end

section
open Filter Polynomial
open StrongConv

theorem solution (ν : smoothFun →ₗ[ℝ] ℝ) (hν : IsCSDistribution ν) :
    supp ν ⊆ Set.Icc (-limsup (fun p : ℕ => |ν (polyFun (X ^ p))| ^ (1 / (p : ℝ))) atTop)
      (limsup (fun p : ℕ => |ν (polyFun (X ^ p))| ^ (1 / (p : ℝ))) atTop) := by
  apply StrongConv.supp_subset_Icc_limsup_dev <;> assumption

end
