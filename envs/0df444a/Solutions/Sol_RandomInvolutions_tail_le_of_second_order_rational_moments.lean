-- Prove2me | solution 1 for RandomInvolutions.tail_le_of_second_order_rational_moments
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T11:49:31.307987+00:00
-- url     : https://prove2.me/submissions/196a9138-3de1-490f-941f-d4daaf572cd9

import Mathlib
import Definitions.Def_BordenaveCollins
import Definitions.Def_ZigZagStrong_ZigZag_Models
import Definitions.Def_RandomInvolutions
import Theorems.Thm_StrongConv_cNorm_iteratedDeriv_div_le
import Theorems.Thm_StrongConv_cNorm_le_two_mul_sSup_of_subset_add
import Theorems.Thm_StrongConv_abs_coeff_zero_le_and_sum_le_lpNormCircle
import Theorems.Thm_StrongConv_tfae_extends_csDistribution
import Theorems.Thm_StrongConv_supp_subset_Icc_limsup
import Theorems.Thm_StrongConv_vanishesNear_supp

section
/-!
# Strong convergence of uniform random involutions: definitions

Shared definitions for the proof of `ZigZagStrong.ZigZag.involution_strong_convergence`.
NEVER EDIT (the Blueprint and all Parts build on this file).

The group is `Γ_r = Z₂^{*r}`, in the encoding `BordenaveCollins.G 0 r` (no free generators, `r`
involutions `m_i = genL (Sum.inr i)`), so that the published Bordenave–Collins statements
(`exists_linearization`, `norm_sum_cfun_mul_trace_Bprod_le`, `tendsto_expFix`,
`tendsto_re_trTau_pow_rpow`) apply verbatim with `r := 0`, `s := r`.

* `homI τ : G 0 r →* Perm (Fin N)` for a tuple of involutions `τ`.
* The conditional model `OmK r N κ`: the `i`-th involution has exactly `κ i` fixed points;
  admissible sizes `AdmK N κ` (`κ i ≤ N`, `κ i ≡ N mod 2`), the filter `admF κ` of admissible
  sizes, the weight `lam κ = 1 + ∑ κ i`.
* Expected fixed points `expFixOn`, `expFixK`; the compressed model operator `perpOp`; the
  spectral functional `specE` of any finite family of representations.
* Colourings with loops of the closed path of a word, and their weights `wtF`, `wtK`.
* The coefficient counts `Bcount` (conjugates of `m_i`) and `C2count` (the two-loop shapes
  `a (ρ m_j ρ⁻¹ σ m_i σ⁻¹)^t a⁻¹`).
* `toAlg`: a scalar `*`-polynomial as an element of the group algebra.
-/

open Finset BordenaveCollins

noncomputable section

namespace RandomInvolutions.Dev

/-! ## The group `Γ_r = G 0 r` and its words -/

/-- The inverse letter. -/
def bar {r s : ℕ} : Lt r s → Lt r s
  | Sum.inl (i, b) => Sum.inl (i, !b)
  | Sum.inr j => Sum.inr j

/-- A reduced word: no letter is followed by its inverse. -/
def Red {r s : ℕ} (u : List (Lt r s)) : Prop := u.IsChain (fun a b => b ≠ bar a)

/-! ## Involutions and the representation they define -/

/-! ## The conditional model `M(N, κ)` -/

/-! ## Expected fixed points -/

/-! ## Operators -/

/-! ## Colourings with loops of the closed path of a word

A path is `x : Fin (u.length + 1) → α` with `x t = letter_t (x (t+1))` (so that
`x t = wordPermI τ (u.drop t) y`). Step `t` with letter `m_i` is a *loop* of colour `i` at
`x t` when `x t = x (t+1)` (that vertex is fixed by `τ_i`), and a *pair* `{x t, x (t+1)}` of
`τ_i` otherwise. -/

/-! ## The coefficient counts -/

/-! ## Scalar polynomials as group-algebra elements -/

end RandomInvolutions.Dev

end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartX
variable {r : ℕ}
/-!
# Part X: mixing over the fixed-point counts

* `mixture`: the uniform law on tuples of involutions is the mixture of the conditional models.
* `fixCount_exp_le`: `E[#fix] ≤ √N + 1`. In fact `E[#fix²] = N` exactly (`sum_fix_sq`): multiplying
  by the transposition `(x y)` is a bijection between involutions fixing `x ≠ y` and involutions
  swapping them, so `E[f (f - 1)] = E[N - f]`; then Cauchy–Schwarz gives `E[#fix] ≤ √N`.
* `mix_affine`: a conditional bound `a * lam κ + b` integrates to `a (1 + r (√N + 1)) + b`.
* `expFix_unif_le`, `upper_unif`.
-/
abbrev Inv (N : ℕ) := ZigZagStrong.ZigZag.Involution N

/-! ## Generic finite probability -/

/-! ## The mixture -/

end RandomInvolutions.Dev.PartX
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartX
variable {r : ℕ}
/-! ## The second moment of the number of fixed points -/

instance (N : ℕ) : Nonempty (Inv N) := ⟨⟨1, fun _ => rfl⟩⟩

end RandomInvolutions.Dev.PartX
end
end

section
open Polynomial Filter Topology StrongConv
open scoped Pointwise
namespace RandomInvolutions.Dev.PartA2
/-!
# Part A2, module 1: the analytic core of the second-order polynomial method

A sequence `F n = f(1/n)/g(1/n)` given, on a set `S` of sizes meeting every pair `{n, n+1}`, by a
rational function of bounded degree and bounded by `s`, has a second-order expansion in `1/n` with
explicit constants (CGTvH Lemmas 4.2, 4.3 and Taylor).
-/
lemma density_lemma2 (S : Set ℕ) (M : ℕ) (hM : 0 < M) (hS : ∀ n : ℕ, M ≤ n → n ∈ S ∨ n + 1 ∈ S)
    (q : ℝ) (hq0 : 0 < q) (hq : 4 * q ^ 2 ≤ M) :
    Set.Icc (0 : ℝ) (1 / M) ⊆ {x : ℝ | ∃ n : ℕ, n ∈ S ∧ M ≤ n ∧ x = 1 / (n : ℝ)} +
      Set.Icc (-((1 / (M : ℝ)) / (4 * q ^ 2))) ((1 / (M : ℝ)) / (4 * q ^ 2)) := by
  intro y hy
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  set δ : ℝ := (1 / (M : ℝ)) / (4 * q ^ 2) with hδ
  have hq2 : 0 < 4 * q ^ 2 := by positivity
  have hδD : 1 / (M : ℝ) ^ 2 ≤ δ := by
    rw [hδ, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hq hMp.le]
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have key : ∃ x ∈ {x : ℝ | ∃ n : ℕ, n ∈ S ∧ M ≤ n ∧ x = 1 / (n : ℝ)}, |y - x| ≤ δ := by
    rcases eq_or_lt_of_le hy.1 with h0 | hpos
    · subst h0
      obtain ⟨n, hn⟩ := exists_nat_ge (1 / δ)
      have hbig : ∀ k : ℕ, max n M ≤ k → |(0 : ℝ) - 1 / (k : ℝ)| ≤ δ := by
        intro k hk
        have hk1 : (1 / δ) ≤ (k : ℝ) :=
          hn.trans (by exact_mod_cast (le_max_left n M).trans hk)
        have hkp : (0 : ℝ) < k := lt_of_lt_of_le (by positivity) hk1
        rw [zero_sub, abs_neg, abs_of_pos (by positivity), div_le_iff₀ hkp]
        rw [div_le_iff₀ hδpos] at hk1
        linarith
      rcases hS (max n M) (le_max_right _ _) with h | h
      · exact ⟨_, ⟨_, h, le_max_right _ _, rfl⟩, hbig _ le_rfl⟩
      · exact ⟨_, ⟨_, h, (le_max_right n M).trans (Nat.le_succ _), rfl⟩, hbig _ (Nat.le_succ _)⟩
    · have hyM : (M : ℝ) ≤ 1 / y := by
        rw [le_div_iff₀ hpos]
        have := hy.2
        rw [le_div_iff₀ hMp] at this
        linarith
      set n := ⌊1 / y⌋₊ with hn
      have hnM : M ≤ n := Nat.le_floor hyM
      have hn1 : (n : ℝ) ≤ 1 / y := Nat.floor_le (by positivity)
      have hn2 : 1 / y < n + 1 := Nat.lt_floor_add_one _
      have hnp : (0 : ℝ) < n := by
        have : (M : ℝ) ≤ n := by exact_mod_cast hnM
        linarith
      have hy1 : y ≤ 1 / (n : ℝ) := by
        rw [le_div_iff₀ hnp]; rw [le_div_iff₀ hpos] at hn1; linarith
      have hy2 : 1 / ((n : ℝ) + 1) < y := by
        rw [div_lt_iff₀ (by positivity)]; rw [div_lt_iff₀ hpos] at hn2; linarith
      have hgap : 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) ≤ 1 / (M : ℝ) ^ 2 := by
        have : 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) = 1 / ((n : ℝ) * (n + 1)) := by
          field_simp; ring
        rw [this]
        have hnM' : (M : ℝ) ≤ n := by exact_mod_cast hnM
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith
      rcases hS n hnM with h | h
      · refine ⟨1 / (n : ℝ), ⟨n, h, hnM, rfl⟩, ?_⟩
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]
        linarith
      · refine ⟨1 / ((n + 1 : ℕ) : ℝ), ⟨n + 1, h, by omega, rfl⟩, ?_⟩
        push_cast
        rw [abs_of_nonneg (by linarith)]
        linarith
  obtain ⟨x, hx, hxy⟩ := key
  refine Set.mem_add.2 ⟨x, hx, y - x, ?_, by ring⟩
  rw [Set.mem_Icc]
  exact abs_le.1 hxy

lemma cNorm_zero_eq (h : ℝ → ℝ) (a b : ℝ) :
    cNorm 0 h a b = sSup ((fun x => |iteratedDeriv 0 h x|) '' Set.Icc a b) := by
  simp [cNorm, supOn]

lemma abs_le_cNorm_zero (h : ℝ → ℝ) (a b : ℝ) (hc : ContinuousOn (iteratedDeriv 0 h) (Set.Icc a b))
    (x : ℝ) (hx : x ∈ Set.Icc a b) : |iteratedDeriv 0 h x| ≤ cNorm 0 h a b := by
  rw [cNorm_zero_eq]
  exact le_csSup (isCompact_Icc.bddAbove_image hc.abs) ⟨x, hx, rfl⟩

lemma polyc {n : ℕ} (p : ℝ[X]) : ContDiff ℝ n (fun x => p.eval x) := by
  have := Polynomial.contDiff_aeval (𝕜 := ℝ) p (n : WithTop ℕ∞)
  simpa only [Polynomial.coe_aeval_eq_eval] using this

lemma poly_div_contDiffAt (f g : ℝ[X]) (n : ℕ) (y : ℝ) (hy : g.eval y ≠ 0) :
    ContDiffAt ℝ n (fun x => f.eval x / g.eval x) y :=
  (polyc f).contDiffAt.div (polyc g).contDiffAt hy

lemma poly_div_continuousOn_iteratedDeriv (f g : ℝ[X]) (b : ℝ) (hb : 0 < b)
    (hg0 : ∀ x ∈ Set.Icc 0 b, g.eval x ≠ 0) (m : ℕ) :
    ContinuousOn (iteratedDeriv m (fun x => f.eval x / g.eval x)) (Set.Icc 0 b) := by
  have hcd : ContDiffOn ℝ m (fun x => f.eval x / g.eval x) (Set.Icc 0 b) :=
    fun y hy => (poly_div_contDiffAt f g m y (hg0 y hy)).contDiffWithinAt
  have := hcd.continuousOn_iteratedDerivWithin le_rfl (uniqueDiffOn_Icc hb)
  refine this.congr fun y hy => ?_
  exact (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hb)
    (poly_div_contDiffAt f g m y (hg0 y hy)) hy).symm

lemma taylor_step (Ψ : ℝ → ℝ) (x : ℝ) (hx : 0 < x) (n : ℕ)
    (hcd : ∀ y ∈ Set.Icc 0 x, ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) Ψ y) (C : ℝ)
    (hC : ∀ y ∈ Set.Icc 0 x, |iteratedDeriv (n + 1) Ψ y| ≤ C) :
    |Ψ x - ∑ k ∈ Finset.range (n + 1), iteratedDeriv k Ψ 0 / (k.factorial : ℝ) * x ^ k| ≤
      C * x ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  have hu : Set.uIcc (0 : ℝ) x = Set.Icc 0 x := Set.uIcc_of_le hx.le
  have hcdOn : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) Ψ (Set.uIcc 0 x) := by
    rw [hu]; exact fun y hy => (hcd y hy).contDiffWithinAt
  obtain ⟨x', hx', hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hx.ne hcdOn
  have hx'I : x' ∈ Set.Icc 0 x := by
    rw [Set.uIoo_of_le hx.le] at hx'
    exact ⟨hx'.1.le, hx'.2.le⟩
  have htay : taylorWithinEval Ψ n (Set.uIcc 0 x) 0 x =
      ∑ k ∈ Finset.range (n + 1), iteratedDeriv k Ψ 0 / (k.factorial : ℝ) * x ^ k := by
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := by have := Finset.mem_range.1 hk; omega
    rw [hu, smul_eq_mul, iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hx)
      ((hcd 0 ⟨le_rfl, hx.le⟩).of_le (by exact_mod_cast (by omega : k ≤ n + 1))) ⟨le_rfl, hx.le⟩]
    rw [sub_zero]; field_simp
  rw [htay] at hrem
  rw [hrem, sub_zero, abs_div, abs_mul, abs_pow, abs_of_pos hx,
    abs_of_pos (by positivity : (0 : ℝ) < ((n + 1).factorial : ℝ))]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact mul_le_mul_of_nonneg_right (hC x' hx'I) (by positivity)

/-- The analytic core: a second-order expansion of `F n = f(1/n)/g(1/n)` along `S`. -/
lemma core_est2 (Q : ℕ) (hQ : 1 ≤ Q) (f g : ℝ[X]) (hfq : f.natDegree ≤ Q) (hgq : g.natDegree ≤ Q)
    (M : ℕ) (hM : 4 * Q ^ 2 ≤ M) (S : Set ℕ) (hS : ∀ n : ℕ, M ≤ n → n ∈ S ∨ n + 1 ∈ S)
    (hg : ∀ x ∈ Set.Icc (0 : ℝ) (1 / (M : ℝ)), 1 / 2 ≤ g.eval x ∧ g.eval x ≤ 1)
    (F : ℕ → ℝ) (s : ℝ)
    (hF : ∀ n : ℕ, n ∈ S → M ≤ n → F n = f.eval (1 / (n : ℝ)) / g.eval (1 / (n : ℝ)))
    (hs : ∀ n : ℕ, |F n| ≤ s) :
    ∃ l0 l1 l2 : ℝ, |l0| ≤ 4 * s ∧ |l1| ≤ 4 * (10 * (Q : ℝ) ^ 2 * M) * s ∧
      |l2| ≤ 4 * (10 * (Q : ℝ) ^ 2 * M) ^ 2 * s ∧
      ∀ n : ℕ, n ∈ S → M ≤ n →
        |F n - l0 - l1 / n - l2 / (n : ℝ) ^ 2| ≤
          4 * (10 * (Q : ℝ) ^ 2 * M) ^ 3 * s / (n : ℝ) ^ 3 := by
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ2 : 1 ≤ (Q : ℝ) ^ 2 := one_le_pow₀ hQ1
  have hMc : 4 * (Q : ℝ) ^ 2 ≤ M := by exact_mod_cast hM
  have hMp : (0 : ℝ) < M := by linarith
  have hMpos : 0 < M := by exact_mod_cast hMp
  set Ψ : ℝ → ℝ := fun x => f.eval x / g.eval x with hΨ
  have hs0 : 0 ≤ s := (abs_nonneg _).trans (hs 0)
  have hb : (0 : ℝ) < 1 / M := by positivity
  have hg0 : ∀ x ∈ Set.Icc (0 : ℝ) (1 / M), g.eval x ≠ 0 := fun x hx => by
    have := (hg x hx).1; intro h; rw [h] at this; norm_num at this
  have hfI : ∀ n : ℕ, n ∈ S → M ≤ n → |f.eval (1 / (n : ℝ))| ≤ s := by
    intro n hnS hn
    have hnp : (0 : ℝ) < n := lt_of_lt_of_le hMp (by exact_mod_cast hn)
    have hx1 : 1 / (n : ℝ) ≤ 1 / (M : ℝ) :=
      one_div_le_one_div_of_le hMp (by exact_mod_cast hn)
    obtain ⟨hg1, hg2⟩ := hg _ ⟨by positivity, hx1⟩
    have hFn := hF n hnS hn
    have : f.eval (1 / (n : ℝ)) = F n * g.eval (1 / (n : ℝ)) := by
      rw [hFn]; field_simp
    rw [this, abs_mul, abs_of_pos (by linarith : 0 < g.eval (1 / (n : ℝ)))]
    calc |F n| * g.eval (1 / (n : ℝ)) ≤ s * 1 :=
          mul_le_mul (hs n) hg2 (by linarith) hs0
      _ = s := mul_one s
  set I : Set ℝ := {x : ℝ | ∃ n : ℕ, n ∈ S ∧ M ≤ n ∧ x = 1 / (n : ℝ)} with hI
  have hIsub : I ⊆ Set.Icc 0 (1 / (M : ℝ)) := by
    rintro x ⟨n, -, hn, rfl⟩
    have hnp : (0 : ℝ) < n := lt_of_lt_of_le hMp (by exact_mod_cast hn)
    exact ⟨by positivity, one_div_le_one_div_of_le hMp (by exact_mod_cast hn)⟩
  have hIne : I.Nonempty := by
    rcases hS M le_rfl with h | h
    · exact ⟨_, M, h, le_rfl, rfl⟩
    · exact ⟨_, M + 1, h, Nat.le_succ _, rfl⟩
  have hdens := density_lemma2 S M hMpos hS (Q : ℝ) (by linarith) hMc
  have h42 := cNorm_le_two_mul_sSup_of_subset_add Q f hfq (1 / (M : ℝ)) hb I hIsub hdens
  have hsup : sSup ((fun x => |f.eval x|) '' I) ≤ s := by
    refine csSup_le (hIne.image _) ?_
    rintro _ ⟨x, ⟨n, hnS, hn, rfl⟩, rfl⟩
    exact hfI n hnS hn
  have hcf : cNorm 0 (fun x => f.eval x) 0 (1 / (M : ℝ)) ≤ 2 * s := by linarith
  have hfcont : ContinuousOn (iteratedDeriv 0 (fun x => f.eval x)) (Set.Icc 0 (1 / (M : ℝ))) := by
    rw [iteratedDeriv_zero]; exact (polyc (n := 0) f).continuous.continuousOn
  have hΨ4 : cNorm 0 Ψ 0 (1 / (M : ℝ)) ≤ 4 * s := by
    rw [cNorm_zero_eq]
    refine csSup_le ⟨_, 0, ⟨le_rfl, hb.le⟩, rfl⟩ ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hg1, hg2⟩ := hg x hx
    have h1 := abs_le_cNorm_zero (fun x => f.eval x) 0 (1 / (M : ℝ)) hfcont x hx
    rw [iteratedDeriv_zero] at h1 ⊢
    simp only [hΨ]
    rw [abs_div, abs_of_pos (by linarith : 0 < g.eval x), div_le_iff₀ (by linarith)]
    nlinarith [abs_nonneg (f.eval x)]
  set S' := sSup {t | ∃ x ∈ Set.Icc (0 : ℝ) (1 / M), ∃ y ∈ Set.Icc (0 : ℝ) (1 / M),
    t = |g.eval x / g.eval y|} with hS'
  have hS0 : 0 ≤ S' := by
    refine Real.sSup_nonneg ?_
    rintro _ ⟨x, hx, y, hy, rfl⟩; exact abs_nonneg _
  have hS2 : S' ≤ 2 := by
    refine csSup_le ⟨_, 0, ⟨le_rfl, hb.le⟩, 0, ⟨le_rfl, hb.le⟩, rfl⟩ ?_
    rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨hx1, hx2⟩ := hg x hx
    obtain ⟨hy1, hy2⟩ := hg y hy
    rw [abs_div, abs_of_pos (by linarith : 0 < g.eval x), abs_of_pos (by linarith : 0 < g.eval y),
      div_le_iff₀ (by linarith)]
    linarith
  set Λ : ℝ := 10 * (Q : ℝ) ^ 2 * M with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  have hbase : 5 * S' * (Q : ℝ) ^ 2 / (1 / (M : ℝ)) ≤ Λ := by
    have e : 5 * S' * (Q : ℝ) ^ 2 / (1 / (M : ℝ)) = 5 * S' * ((Q : ℝ) ^ 2 * M) := by
      field_simp
    rw [e, hΛ]
    nlinarith [mul_le_mul_of_nonneg_right hS2 (by positivity : (0 : ℝ) ≤ (Q : ℝ) ^ 2 * M)]
  have hbase0 : 0 ≤ 5 * S' * (Q : ℝ) ^ 2 / (1 / (M : ℝ)) := by positivity
  have hC : ∀ m : ℕ, cNorm 0 (iteratedDeriv m Ψ) 0 (1 / (M : ℝ)) ≤
      m.factorial * Λ ^ m * (4 * s) := by
    intro m
    refine (cNorm_iteratedDeriv_div_le Q m f g hfq hgq (1 / (M : ℝ)) hb hg0).trans ?_
    have hp := pow_le_pow_left₀ hbase0 hbase m
    have h4 : 0 ≤ cNorm 0 Ψ 0 (1 / (M : ℝ)) := by
      rw [cNorm_zero_eq]; exact Real.sSup_nonneg (by rintro _ ⟨x, _, rfl⟩; exact abs_nonneg _)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) hΨ4 h4 (by positivity)
  have hpt : ∀ m : ℕ, ∀ y ∈ Set.Icc (0 : ℝ) (1 / M),
      |iteratedDeriv m Ψ y| ≤ m.factorial * Λ ^ m * (4 * s) := by
    intro m y hy
    have := abs_le_cNorm_zero (iteratedDeriv m Ψ) 0 (1 / (M : ℝ))
      (by rw [iteratedDeriv_zero]; exact poly_div_continuousOn_iteratedDeriv f g _ hb hg0 _) y hy
    rw [iteratedDeriv_zero] at this
    exact this.trans (hC m)
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / M) := ⟨le_rfl, hb.le⟩
  have f1 : ((1 : ℕ).factorial : ℝ) = 1 := by norm_num [Nat.factorial]
  have f2 : ((2 : ℕ).factorial : ℝ) = 2 := by norm_num [Nat.factorial]
  have f3 : ((3 : ℕ).factorial : ℝ) = 6 := by norm_num [Nat.factorial]
  refine ⟨Ψ 0, iteratedDeriv 1 Ψ 0, iteratedDeriv 2 Ψ 0 / 2, ?_, ?_, ?_, ?_⟩
  · have := hpt 0 0 h0mem
    simpa using this
  · have := hpt 1 0 h0mem
    rw [f1] at this
    linarith
  · have := hpt 2 0 h0mem
    rw [f2] at this
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), div_le_iff₀ (by norm_num)]
    linarith
  · intro N hNS hMN
    have hNp : (0 : ℝ) < N := lt_of_lt_of_le hMp (by exact_mod_cast hMN)
    have hx : (0 : ℝ) < 1 / (N : ℝ) := by positivity
    have hxM : 1 / (N : ℝ) ≤ 1 / (M : ℝ) := one_div_le_one_div_of_le hMp (by exact_mod_cast hMN)
    have hT := taylor_step Ψ (1 / (N : ℝ)) hx 2
      (fun y hy => poly_div_contDiffAt f g _ y (hg0 y ⟨hy.1, hy.2.trans hxM⟩))
      (6 * Λ ^ 3 * (4 * s))
      (fun y hy => by
        have := hpt 3 y ⟨hy.1, hy.2.trans hxM⟩
        rw [f3] at this
        exact this)
    have hFN : F N = Ψ (1 / (N : ℝ)) := hF N hNS hMN
    have e1 : F N - Ψ 0 - iteratedDeriv 1 Ψ 0 / N - iteratedDeriv 2 Ψ 0 / 2 / (N : ℝ) ^ 2 =
        Ψ (1 / (N : ℝ)) - ∑ k ∈ Finset.range (2 + 1),
          iteratedDeriv k Ψ 0 / (k.factorial : ℝ) * (1 / (N : ℝ)) ^ k := by
      rw [hFN, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, f1, f2]
      simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, pow_zero, pow_one]
      field_simp
      ring
    rw [e1]
    refine hT.trans (le_of_eq ?_)
    have e3 : (((2 + 1 : ℕ)).factorial : ℝ) = 6 := f3
    rw [e3, one_div, inv_pow]
    field_simp

end RandomInvolutions.Dev.PartA2
end

section
open Polynomial Filter Topology StrongConv
namespace RandomInvolutions.Dev.PartA2
/-!
# Part A2, module 2: the second-order master inequality for polynomial test functions

For a family of positive functionals `E κ N` of mass at most one on `[-K, K]` whose polynomial
moments are rational in `1/N` along the admissible sizes of each ray `κ`, the coefficients
`T₀, T₁, T₂` of the expansion in `1/N` exist, are linear in the polynomial `h`, and
`|E κ N h - T₀ h - T₁ h / N - T₂ h / N²| ≤ (A q⁴ lam κ)³ sup_{[-K,K]} |h| / N³` for `deg h ≤ q`.
-/
/-- A sequence of positive functionals of mass at most one on `[-K, K]`. -/
structure PosFun (K : ℝ) (E : ℕ → (ℝ → ℝ) → ℝ) : Prop where
  hK : 0 < K
  hadd : ∀ n f g, E n (f + g) = E n f + E n g
  hsmul : ∀ n (a : ℝ) f, E n (a • f) = a * E n f
  hmono : ∀ n f g, (∀ x ∈ Set.Icc (-K) K, f x ≤ g x) → E n f ≤ E n g
  hone : ∀ n, E n (fun _ => 1) ≤ 1

end RandomInvolutions.Dev.PartA2
end

section
open Polynomial Filter Topology StrongConv
namespace RandomInvolutions.Dev.PartA2
namespace PosFun
variable {K : ℝ} {E : ℕ → (ℝ → ℝ) → ℝ}
lemma zero (hE : PosFun K E) (n : ℕ) : E n 0 = 0 := by
  have := hE.hsmul n 0 0
  simpa using this

lemma one_nonneg (hE : PosFun K E) (n : ℕ) : 0 ≤ E n (fun _ => 1) := by
  have := hE.hmono n 0 (fun _ => 1) (fun x _ => by simp)
  rwa [hE.zero] at this

lemma abs_le (hE : PosFun K E) (n : ℕ) (f : ℝ → ℝ) (B : ℝ)
    (h : ∀ x ∈ Set.Icc (-K) K, |f x| ≤ B) : |E n f| ≤ B := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (h 0 ⟨by linarith [hE.hK], hE.hK.le⟩)
  have h1 := hE.one_nonneg n
  have h2 := hE.hone n
  have hu := hE.hmono n f (B • fun _ => (1 : ℝ)) (fun x hx => by
    simpa using (_root_.abs_le.1 (h x hx)).2)
  have hl := hE.hmono n ((-B) • fun _ => (1 : ℝ)) f (fun x hx => by
    simpa using (_root_.abs_le.1 (h x hx)).1)
  rw [hE.hsmul] at hu hl
  rw [_root_.abs_le]
  constructor <;> nlinarith

/-- `E n` restricted to polynomials, as a linear map. -/
noncomputable def polyL (hE : PosFun K E) (n : ℕ) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun h := E n (fun x => h.eval x)
  map_add' h g := by
    have : (fun x => (h + g).eval x) = (fun x => h.eval x) + (fun x => g.eval x) := by
      ext x; simp
    rw [this, hE.hadd]
  map_smul' a h := by
    have : (fun x => (a • h).eval x) = a • (fun x => h.eval x) := by
      ext x; simp
    rw [this, hE.hsmul]; rfl

end PosFun
end RandomInvolutions.Dev.PartA2
end

section
open Polynomial Filter Topology StrongConv
namespace RandomInvolutions.Dev.PartA2
/-! ## Admissible sizes -/
lemma one_le_lam {r : ℕ} (κ : Fin r → ℕ) : 1 ≤ lam κ := by
  unfold lam
  have : (0 : ℝ) ≤ ∑ i, (κ i : ℝ) := Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
  linarith

lemma adm_dense {r : ℕ} (κ : Fin r → ℕ) (N₀ : ℕ) (h0 : AdmK N₀ κ) (n : ℕ)
    (hn : ∑ i, κ i ≤ n) : AdmK n κ ∨ AdmK (n + 1) κ := by
  have hle : ∀ i, κ i ≤ n := fun i =>
    (Finset.single_le_sum (fun j _ => Nat.zero_le (κ j)) (Finset.mem_univ i)).trans hn
  by_cases hp : n % 2 = N₀ % 2
  · exact Or.inl fun i => ⟨hle i, (h0 i).2.trans hp.symm⟩
  · exact Or.inr fun i => ⟨(hle i).trans (Nat.le_succ _), by have := (h0 i).2; omega⟩

lemma adm_add_two {r : ℕ} (κ : Fin r → ℕ) (N : ℕ) (h : AdmK N κ) (k : ℕ) :
    AdmK (N + 2 * k) κ :=
  fun i => ⟨(h i).1.trans (Nat.le_add_right _ _), by have := (h i).2; omega⟩

lemma admF_neBot {r : ℕ} (κ : Fin r → ℕ) (N₀ : ℕ) (h0 : AdmK N₀ κ) : (admF κ).NeBot := by
  unfold admF
  rw [Filter.inf_principal_neBot_iff]
  intro U hU
  obtain ⟨a, ha⟩ := Filter.mem_atTop_sets.1 hU
  exact ⟨N₀ + 2 * a, ha _ (by omega), adm_add_two κ N₀ h0 a⟩

lemma eventually_admF {r : ℕ} (κ : Fin r → ℕ) (M : ℕ) (P : ℕ → Prop)
    (h : ∀ N, M ≤ N → AdmK N κ → P N) : ∀ᶠ N in admF κ, P N := by
  unfold admF
  rw [Filter.eventually_inf_principal]
  filter_upwards [eventually_ge_atTop M] with N hN hA using h N hN hA

lemma admF_le {r : ℕ} (κ : Fin r → ℕ) : admF κ ≤ atTop := inf_le_left

/-! ## Second-order expansions along a filter -/
/-- `F N = l0 + l1/N + l2/N² + o(1/N²)` along `l`. -/
def Exp3 (l : Filter ℕ) (F : ℕ → ℝ) (l0 l1 l2 : ℝ) : Prop :=
  Tendsto F l (𝓝 l0) ∧ Tendsto (fun N : ℕ => (N : ℝ) * (F N - l0)) l (𝓝 l1) ∧
    Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * (F N - l0 - l1 / N)) l (𝓝 l2)

lemma Exp3.unique {l : Filter ℕ} [l.NeBot] {F : ℕ → ℝ} {a0 a1 a2 b0 b1 b2 : ℝ}
    (ha : Exp3 l F a0 a1 a2) (hb : Exp3 l F b0 b1 b2) : a0 = b0 ∧ a1 = b1 ∧ a2 = b2 := by
  obtain ⟨ha0, ha1, ha2⟩ := ha
  obtain ⟨hb0, hb1, hb2⟩ := hb
  obtain rfl := tendsto_nhds_unique ha0 hb0
  obtain rfl := tendsto_nhds_unique ha1 hb1
  exact ⟨rfl, rfl, tendsto_nhds_unique ha2 hb2⟩

lemma Exp3.add {l : Filter ℕ} {F G : ℕ → ℝ} {a0 a1 a2 b0 b1 b2 : ℝ}
    (ha : Exp3 l F a0 a1 a2) (hb : Exp3 l G b0 b1 b2) :
    Exp3 l (fun N => F N + G N) (a0 + b0) (a1 + b1) (a2 + b2) :=
  ⟨ha.1.add hb.1, (ha.2.1.add hb.2.1).congr fun N => by ring,
    (ha.2.2.add hb.2.2).congr fun N => by ring⟩

lemma Exp3.const_mul {l : Filter ℕ} {F : ℕ → ℝ} {a0 a1 a2 : ℝ} (ha : Exp3 l F a0 a1 a2)
    (c : ℝ) : Exp3 l (fun N => c * F N) (c * a0) (c * a1) (c * a2) :=
  ⟨ha.1.const_mul c, (ha.2.1.const_mul c).congr fun N => by ring,
    (ha.2.2.const_mul c).congr fun N => by ring⟩

lemma tendsto_inv_cast {l : Filter ℕ} (hl : l ≤ atTop) :
    Tendsto (fun N : ℕ => ((N : ℝ))⁻¹) l (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.mono_left hl)

lemma Exp3.of_bound {l : Filter ℕ} (hl : l ≤ atTop) {F : ℕ → ℝ} {l0 l1 l2 B : ℝ}
    (h : ∀ᶠ N in l, |F N - l0 - l1 / N - l2 / (N : ℝ) ^ 2| ≤ B / (N : ℝ) ^ 3) :
    Exp3 l F l0 l1 l2 := by
  have hinv := tendsto_inv_cast hl
  have hge : ∀ᶠ N : ℕ in l, 1 ≤ N := hl (eventually_ge_atTop 1)
  have h2 : Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * (F N - l0 - l1 / N)) l (𝓝 l2) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hB : Tendsto (fun N : ℕ => B * ((N : ℝ))⁻¹) l (𝓝 0) := by
      simpa using hinv.const_mul B
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hB
    filter_upwards [h, hge] with N hN hN1
    have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
    have e : (N : ℝ) ^ 2 * (F N - l0 - l1 / N) - l2 =
        (N : ℝ) ^ 2 * (F N - l0 - l1 / N - l2 / (N : ℝ) ^ 2) := by field_simp
    rw [Real.norm_eq_abs, e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) ^ 2)]
    calc (N : ℝ) ^ 2 * |F N - l0 - l1 / N - l2 / (N : ℝ) ^ 2|
        ≤ (N : ℝ) ^ 2 * (B / (N : ℝ) ^ 3) := mul_le_mul_of_nonneg_left hN (by positivity)
      _ = B * ((N : ℝ))⁻¹ := by field_simp
  have h1 : Tendsto (fun N : ℕ => (N : ℝ) * (F N - l0)) l (𝓝 l1) := by
    have h3 : Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * (F N - l0 - l1 / N) * ((N : ℝ))⁻¹ + l1) l
        (𝓝 (l2 * 0 + l1)) := (h2.mul hinv).add tendsto_const_nhds
    rw [mul_zero, zero_add] at h3
    refine h3.congr' ?_
    filter_upwards [hge] with N hN1
    have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
    field_simp
    ring
  refine ⟨?_, h1, h2⟩
  have h3 : Tendsto (fun N : ℕ => (N : ℝ) * (F N - l0) * ((N : ℝ))⁻¹ + l0) l
      (𝓝 (l1 * 0 + l0)) := (h1.mul hinv).add tendsto_const_nhds
  rw [mul_zero, zero_add] at h3
  refine h3.congr' ?_
  filter_upwards [hge] with N hN1
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  field_simp
  ring

/-! ## The rationality hypothesis and the expansion for large admissible sizes -/
/-- The rationality hypothesis along rays, with a denominator independent of the ray. -/
def RatHyp2 {r : ℕ} (E : (Fin r → ℕ) → ℕ → (ℝ → ℝ) → ℝ) (C : ℕ) : Prop :=
  ∀ q : ℕ, 1 ≤ q → ∃ gq : ℝ[X], gq.natDegree ≤ C * q ∧
    (∀ x ∈ Set.Icc (0 : ℝ) (1 / ((C : ℝ) * (q : ℝ) ^ 2)), 1 / 2 ≤ gq.eval x ∧ gq.eval x ≤ 1) ∧
    ∀ h : ℝ[X], h.natDegree ≤ q → ∀ κ : Fin r → ℕ, ∃ f : ℝ[X], f.natDegree ≤ C * q ∧
      ∀ N : ℕ, AdmK N κ → C * q ≤ N →
        E κ N (fun x => h.eval x) = f.eval (1 / (N : ℝ)) / gq.eval (1 / (N : ℝ))

lemma expansion_large2 {r : ℕ} {K : ℝ} {E : (Fin r → ℕ) → ℕ → (ℝ → ℝ) → ℝ} (C : ℕ)
    (hC : 1 ≤ C) (hR : RatHyp2 E C) (κ : Fin r → ℕ) (hE : PosFun K (E κ)) (N₀ : ℕ)
    (h0 : AdmK N₀ κ) (q : ℕ) (hq : 1 ≤ q) (h : ℝ[X]) (hh : h.natDegree ≤ q) (s : ℝ)
    (hs : ∀ x ∈ Set.Icc (-K) K, |h.eval x| ≤ s) :
    ∃ l0 l1 l2 : ℝ, |l0| ≤ 4 * s ∧
      |l1| ≤ 4 * (10 * ((C * q : ℕ) : ℝ) ^ 2 * ((4 * (C * q) ^ 2 + ∑ i, κ i : ℕ) : ℝ)) * s ∧
      |l2| ≤ 4 * (10 * ((C * q : ℕ) : ℝ) ^ 2 * ((4 * (C * q) ^ 2 + ∑ i, κ i : ℕ) : ℝ)) ^ 2 * s ∧
      ∀ N : ℕ, AdmK N κ → 4 * (C * q) ^ 2 + ∑ i, κ i ≤ N →
        |E κ N (fun x => h.eval x) - l0 - l1 / N - l2 / (N : ℝ) ^ 2| ≤
          4 * (10 * ((C * q : ℕ) : ℝ) ^ 2 * ((4 * (C * q) ^ 2 + ∑ i, κ i : ℕ) : ℝ)) ^ 3 * s /
            (N : ℝ) ^ 3 := by
  obtain ⟨gq, hgdeg, hgb, hrest⟩ := hR q hq
  obtain ⟨f, hfdeg, hf⟩ := hrest h hh κ
  have hQ : 1 ≤ C * q := Nat.mul_pos hC hq
  have hQ4 : C * q ≤ 4 * (C * q) ^ 2 := by nlinarith
  refine core_est2 (C * q) hQ f gq hfdeg hgdeg (4 * (C * q) ^ 2 + ∑ i, κ i)
    (Nat.le_add_right _ _) {N | AdmK N κ}
    (fun n hn => adm_dense κ N₀ h0 n ((Nat.le_add_left _ _).trans hn)) ?_
    (fun N => E κ N (fun x => h.eval x)) s
    (fun N hN hM => hf N hN (hQ4.trans ((Nat.le_add_right _ _).trans hM)))
    (fun N => hE.abs_le N _ s hs)
  intro x hx
  refine hgb x ⟨hx.1, hx.2.trans ?_⟩
  have hC1 : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  apply one_div_le_one_div_of_le (by positivity)
  have h1 : (C : ℝ) * (q : ℝ) ^ 2 ≤ ((4 * (C * q) ^ 2 : ℕ) : ℝ) := by
    push_cast
    have := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ 4 * C)
      (by positivity : (0 : ℝ) ≤ (C : ℝ) * (q : ℝ) ^ 2)
    nlinarith
  exact h1.trans (by exact_mod_cast Nat.le_add_right _ _)

lemma small_arith (s t e a b c : ℝ) (hs : 0 ≤ s) (ht : 1 ≤ t) (he : |e| ≤ s) (ha : |a| ≤ s)
    (hb : |b| ≤ 4 * t * s) (hc : |c| ≤ 4 * t ^ 2 * s) : |e - a - b - c| ≤ 10 * t ^ 3 * s := by
  have t1 : t ≤ t ^ 2 := by nlinarith
  have t2 : t ^ 2 ≤ t ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left ht (sq_nonneg t)]
  have h1 : 1 * s ≤ t ^ 3 * s := mul_le_mul_of_nonneg_right (by linarith) hs
  have h2 : t * s ≤ t ^ 3 * s := mul_le_mul_of_nonneg_right (by linarith) hs
  have h3 : t ^ 2 * s ≤ t ^ 3 * s := mul_le_mul_of_nonneg_right t2 hs
  rw [abs_le] at he ha hb hc ⊢
  constructor <;> linarith [he.1, he.2, ha.1, ha.2, hb.1, hb.2, hc.1, hc.2]

/-- The master inequality along a ray with at least one admissible size. -/
theorem master_adm {r : ℕ} {K : ℝ} {E : (Fin r → ℕ) → ℕ → (ℝ → ℝ) → ℝ} (C : ℕ) (hC : 1 ≤ C)
    (hR : RatHyp2 E C) (κ : Fin r → ℕ) (hE : PosFun K (E κ)) (N₀ : ℕ) (h0 : AdmK N₀ κ) :
    ∃ T : Fin 3 → (ℝ[X] →ₗ[ℝ] ℝ),
      ∀ q : ℕ, 1 ≤ q → ∀ h : ℝ[X], h.natDegree ≤ q → ∀ s : ℝ,
        (∀ x ∈ Set.Icc (-K) K, |h.eval x| ≤ s) →
        (∀ j : Fin 3, |T j h| ≤ (160 * (C : ℝ) ^ 4 * (q : ℝ) ^ 4 * lam κ) ^ (j : ℕ) * s) ∧
        ∀ N : ℕ, AdmK N κ → 1 ≤ N →
          |E κ N (fun x => h.eval x) - T 0 h - T 1 h / N - T 2 h / (N : ℝ) ^ 2| ≤
            (160 * (C : ℝ) ^ 4 * (q : ℝ) ^ 4 * lam κ) ^ 3 * s / (N : ℝ) ^ 3 := by
  have := admF_neBot κ N₀ h0
  have hbdd : ∀ h : ℝ[X], ∃ s : ℝ, ∀ x ∈ Set.Icc (-K) K, |h.eval x| ≤ s := by
    intro h
    obtain ⟨s, hs⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := fun x => h.eval x)
      (s := Set.Icc (-K) K) h.continuous.continuousOn
    exact ⟨s, fun x hx => by simpa using hs x hx⟩
  have hex : ∀ h : ℝ[X], ∃ l0 l1 l2 : ℝ,
      Exp3 (admF κ) (fun N => E κ N (fun x => h.eval x)) l0 l1 l2 := by
    intro h
    obtain ⟨s, hs⟩ := hbdd h
    obtain ⟨l0, l1, l2, -, -, -, hexp⟩ := expansion_large2 C hC hR κ hE N₀ h0
      (max h.natDegree 1) (le_max_right _ _) h (le_max_left _ _) s hs
    exact ⟨l0, l1, l2, Exp3.of_bound (admF_le κ)
      (eventually_admF κ _ _ fun N hN hA => hexp N hA hN)⟩
  choose n0 n1 n2 hn using hex
  have eadd : ∀ h g : ℝ[X], (fun N => E κ N (fun x => (h + g).eval x)) =
      fun N => E κ N (fun x => h.eval x) + E κ N (fun x => g.eval x) := fun h g =>
    funext fun N => (hE.polyL N).map_add h g
  have esmul : ∀ (a : ℝ) (h : ℝ[X]), (fun N => E κ N (fun x => (a • h).eval x)) =
      fun N => a * E κ N (fun x => h.eval x) := fun a h =>
    funext fun N => (hE.polyL N).map_smul a h
  have hadd3 : ∀ h g, n0 (h + g) = n0 h + n0 g ∧ n1 (h + g) = n1 h + n1 g ∧
      n2 (h + g) = n2 h + n2 g := by
    intro h g
    have := (hn h).add (hn g)
    rw [← eadd] at this
    exact Exp3.unique (hn (h + g)) this
  have hsmul3 : ∀ (a : ℝ) h, n0 (a • h) = a * n0 h ∧ n1 (a • h) = a * n1 h ∧
      n2 (a • h) = a * n2 h := by
    intro a h
    have := (hn h).const_mul a
    rw [← esmul] at this
    exact Exp3.unique (hn (a • h)) this
  let ν₀ : ℝ[X] →ₗ[ℝ] ℝ :=
    { toFun := n0, map_add' := fun h g => (hadd3 h g).1,
      map_smul' := fun a h => by simpa using (hsmul3 a h).1 }
  let ν₁ : ℝ[X] →ₗ[ℝ] ℝ :=
    { toFun := n1, map_add' := fun h g => (hadd3 h g).2.1,
      map_smul' := fun a h => by simpa using (hsmul3 a h).2.1 }
  let ν₂ : ℝ[X] →ₗ[ℝ] ℝ :=
    { toFun := n2, map_add' := fun h g => (hadd3 h g).2.2,
      map_smul' := fun a h => by simpa using (hsmul3 a h).2.2 }
  refine ⟨![ν₀, ν₁, ν₂], ?_⟩
  intro q hq h hh s hs
  have hC1 : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hs0 : 0 ≤ s := (abs_nonneg _).trans (hs 0 ⟨by linarith [hE.hK], hE.hK.le⟩)
  obtain ⟨l0, l1, l2, -, hl1, hl2, hexp⟩ := expansion_large2 C hC hR κ hE N₀ h0 q hq h hh s hs
  have hE3 : Exp3 (admF κ) (fun N => E κ N (fun x => h.eval x)) l0 l1 l2 :=
    Exp3.of_bound (admF_le κ) (eventually_admF κ _ _ fun N hN hA => hexp N hA hN)
  obtain ⟨e0, e1, e2⟩ := Exp3.unique hE3 (hn h)
  subst e0 e1 e2
  have hT0 : |n0 h| ≤ s :=
    le_of_tendsto (hn h).1.abs (Eventually.of_forall fun N => hE.abs_le N _ s hs)
  set Mth : ℕ := 4 * (C * q) ^ 2 + ∑ i, κ i with hMth
  set σ : ℝ := ∑ i, (κ i : ℝ) with hσ
  have hσ0 : 0 ≤ σ := Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
  set u : ℝ := (C : ℝ) * q with hu
  have hu1 : 1 ≤ u := by rw [hu]; nlinarith
  have hQu : ((C * q : ℕ) : ℝ) = u := by rw [hu]; push_cast; ring
  have hMR : (Mth : ℝ) = 4 * u ^ 2 + σ := by rw [hMth, hu, hσ]; push_cast; ring
  rw [hQu] at hl1 hl2 hexp
  set L : ℝ := 10 * u ^ 2 * (Mth : ℝ) with hL
  set Θ : ℝ := 160 * (C : ℝ) ^ 4 * (q : ℝ) ^ 4 * lam κ with hΘ
  have hΘe : Θ = 160 * u ^ 4 * (1 + σ) := by rw [hΘ, hu, hσ]; unfold lam; ring
  have hu2 : 1 ≤ u ^ 2 := one_le_pow₀ hu1
  have hML : (Mth : ℝ) ≤ L := by rw [hL]; nlinarith [hMR]
  have hM4 : 4 ≤ (Mth : ℝ) := by rw [hMR]; linarith
  have hL1 : 1 ≤ L := by linarith
  have h4L : 4 * L ≤ Θ := by
    rw [hΘe, hL, hMR]
    have h24 : u ^ 2 ≤ u ^ 4 := by nlinarith [mul_nonneg (sq_nonneg u) (by linarith : 0 ≤ u ^ 2 - 1)]
    have := mul_le_mul_of_nonneg_right h24 hσ0
    nlinarith
  have hΘ0 : 0 ≤ Θ := by linarith
  have h1 : |n1 h| ≤ Θ ^ 1 * s := by
    rw [pow_one]
    exact hl1.trans (mul_le_mul_of_nonneg_right h4L hs0)
  have h2 : |n2 h| ≤ Θ ^ 2 * s := by
    refine hl2.trans (mul_le_mul_of_nonneg_right ?_ hs0)
    have := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 4 * L) h4L 2
    nlinarith [sq_nonneg L]
  refine ⟨?_, ?_⟩
  · intro j
    match j with
    | 0 =>
      show |n0 h| ≤ Θ ^ 0 * s
      rw [pow_zero, one_mul]; exact hT0
    | 1 => exact h1
    | 2 => exact h2
  · intro N hA hN1
    show |E κ N (fun x => h.eval x) - n0 h - n1 h / N - n2 h / (N : ℝ) ^ 2| ≤ _
    have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
    have hΘ3 : (4 * L) ^ 3 ≤ Θ ^ 3 := pow_le_pow_left₀ (by linarith) h4L 3
    rcases le_or_gt Mth N with hbig | hsmall
    · refine (hexp N hA hbig).trans ?_
      refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hs0) (by positivity)
      nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ L) 3]
    · have hNL : (N : ℝ) ≤ L := by
        have : (N : ℝ) ≤ Mth := by exact_mod_cast hsmall.le
        linarith
      set t : ℝ := L / N with ht
      have ht1 : 1 ≤ t := by rw [ht, le_div_iff₀ hNp]; linarith
      have hb : |n1 h / N| ≤ 4 * t * s := by
        rw [abs_div, abs_of_pos hNp, show 4 * t * s = 4 * L * s / N by rw [ht]; ring]
        exact div_le_div_of_nonneg_right hl1 hNp.le
      have hc : |n2 h / (N : ℝ) ^ 2| ≤ 4 * t ^ 2 * s := by
        rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) ^ 2),
          show 4 * t ^ 2 * s = 4 * L ^ 2 * s / (N : ℝ) ^ 2 by rw [ht]; ring]
        exact div_le_div_of_nonneg_right hl2 (by positivity)
      refine (small_arith s t _ _ _ _ hs0 ht1 (hE.abs_le N _ s hs) hT0 hb hc).trans ?_
      have ht4 : 4 * t ≤ Θ / N := by
        rw [show 4 * t = 4 * L / N by rw [ht]; ring]
        exact div_le_div_of_nonneg_right h4L hNp.le
      have ht43 : (4 * t) ^ 3 ≤ (Θ / N) ^ 3 := pow_le_pow_left₀ (by linarith) ht4 3
      have ht30 : 0 ≤ t ^ 3 := by positivity
      calc 10 * t ^ 3 * s ≤ (4 * t) ^ 3 * s :=
            mul_le_mul_of_nonneg_right (by nlinarith) hs0
        _ ≤ (Θ / N) ^ 3 * s := mul_le_mul_of_nonneg_right ht43 hs0
        _ = Θ ^ 3 * s / (N : ℝ) ^ 3 := by ring

/-- The master inequality for polynomial test functions, with explicit dependence on the ray
(the statement of `RandomInvolutions.Dev.poly_master2`). -/
theorem poly_master2_aux (K : ℝ) (hK : 0 < K) (r : ℕ) (E : (Fin r → ℕ) → ℕ → (ℝ → ℝ) → ℝ)
    (hadd : ∀ κ N f g, E κ N (f + g) = E κ N f + E κ N g)
    (hsmul : ∀ κ N (a : ℝ) f, E κ N (a • f) = a * E κ N f)
    (hmono : ∀ κ N f g, (∀ x ∈ Set.Icc (-K) K, f x ≤ g x) → E κ N f ≤ E κ N g)
    (hone : ∀ κ N, E κ N (fun _ => 1) ≤ 1)
    (hrat : ∃ C : ℕ, 1 ≤ C ∧ ∀ q : ℕ, 1 ≤ q → ∃ gq : ℝ[X], gq.natDegree ≤ C * q ∧
      (∀ x ∈ Set.Icc (0 : ℝ) (1 / ((C : ℝ) * (q : ℝ) ^ 2)), 1 / 2 ≤ gq.eval x ∧ gq.eval x ≤ 1) ∧
      ∀ h : ℝ[X], h.natDegree ≤ q → ∀ κ : Fin r → ℕ, ∃ f : ℝ[X], f.natDegree ≤ C * q ∧
        ∀ N : ℕ, AdmK N κ → C * q ≤ N →
          E κ N (fun x => h.eval x) = f.eval (1 / (N : ℝ)) / gq.eval (1 / (N : ℝ))) :
    ∃ (A : ℝ) (M : ℕ), 0 ≤ A ∧ ∀ κ : Fin r → ℕ, ∃ T : Fin 3 → (ℝ[X] →ₗ[ℝ] ℝ),
      ∀ q : ℕ, 1 ≤ q → ∀ h : ℝ[X], h.natDegree ≤ q → ∀ s : ℝ,
        (∀ x ∈ Set.Icc (-K) K, |h.eval x| ≤ s) →
        (∀ j : Fin 3, |T j h| ≤ (A * (q : ℝ) ^ M * lam κ) ^ (j : ℕ) * s) ∧
        ∀ N : ℕ, AdmK N κ → 1 ≤ N →
          |E κ N (fun x => h.eval x) - T 0 h - T 1 h / N - T 2 h / (N : ℝ) ^ 2| ≤
            (A * (q : ℝ) ^ M * lam κ) ^ 3 * s / (N : ℝ) ^ 3 := by
  obtain ⟨C, hC, hR⟩ := hrat
  refine ⟨160 * (C : ℝ) ^ 4, 4, by positivity, fun κ => ?_⟩
  have hE : PosFun K (E κ) := ⟨hK, hadd κ, hsmul κ, hmono κ, hone κ⟩
  by_cases hadm : ∃ N₀, AdmK N₀ κ
  · obtain ⟨N₀, h0⟩ := hadm
    exact master_adm C hC hR κ hE N₀ h0
  · refine ⟨fun _ => 0, fun q hq h hh s hs => ⟨fun j => ?_, fun N hN _ => absurd ⟨N, hN⟩ hadm⟩⟩
    have hs0 : 0 ≤ s := (abs_nonneg _).trans (hs 0 ⟨by linarith, hK.le⟩)
    have := one_le_lam κ
    simp only [LinearMap.zero_apply, abs_zero]
    positivity

end RandomInvolutions.Dev.PartA2
end

section
open Polynomial Filter Topology StrongConv
namespace RandomInvolutions.Dev.PartA2
/-!
# Part A2, module 3: Chebyshev expansions and polynomial approximation (real analysis)

Generic lemmas: `Tⱼ(x/K)` as polynomials, the Chebyshev expansion of a polynomial, simultaneous
polynomial approximation of a smooth function and its derivatives, and the stability of the
`L^β` norm of derivatives of `θ ↦ h(K cos θ)`.
-/
/-- `Tⱼ(x/K)` as a polynomial. -/
noncomputable def chebK (K : ℝ) (j : ℕ) : ℝ[X] := (Chebyshev.T ℝ j).comp (Polynomial.C K⁻¹ * X)

lemma sum_range_succ_eq_add_Icc (f : ℕ → ℝ) (q : ℕ) :
    ∑ j ∈ Finset.range (q + 1), f j = f 0 + ∑ j ∈ Finset.Icc 1 q, f j := by
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  rfl

lemma natDegree_chebK_le (K : ℝ) (j : ℕ) : (chebK K j).natDegree ≤ j := by
  unfold chebK
  refine (natDegree_comp_le).trans ?_
  have h1 : (C K⁻¹ * X : ℝ[X]).natDegree ≤ 1 := by
    refine (natDegree_C_mul_le _ _).trans ?_
    simp
  simp only [Chebyshev.natDegree_T, Int.natAbs_natCast]
  nlinarith [h1]

lemma supOn_le_of_forall {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) {c : ℝ}
    (h : ∀ x ∈ Set.Icc a b, |f x| ≤ c) : supOn f a b ≤ c := by
  unfold supOn
  apply csSup_le ((Set.nonempty_Icc.mpr hab).image _)
  rintro _ ⟨x, hx, rfl⟩
  exact h x hx

lemma cNorm_le_of_abs_le (k : ℕ) (f : ℝ → ℝ) (R : ℝ) (hR : 0 ≤ R) (ε : ℝ)
    (hf : ∀ r ≤ k, ∀ x ∈ Set.Icc (-R) R, |iteratedDeriv r f x| ≤ ε) :
    cNorm k f (-R) R ≤ (k + 1) * ε := by
  unfold cNorm
  calc ∑ j ∈ Finset.range (k + 1), supOn (iteratedDeriv j f) (-R) R
      ≤ ∑ j ∈ Finset.range (k + 1), ε := by
        apply Finset.sum_le_sum
        intro j hj
        exact supOn_le_of_forall (by linarith) (hf j (by simp at hj; omega))
    _ = (k + 1) * ε := by simp

lemma iteratedDeriv_sub_of_contDiff (f g : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (r : ℕ) :
    iteratedDeriv r (fun x => f x - g x) = fun x => iteratedDeriv r f x - iteratedDeriv r g x := by
  funext x
  have hr : ((r : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  exact iteratedDeriv_fun_sub (hf.contDiffAt.of_le hr) (hg.contDiffAt.of_le hr)

lemma abs_iteratedDeriv_cos_le (i : ℕ) (θ : ℝ) : |iteratedDeriv i Real.cos θ| ≤ 1 := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' i
  · rw [Real.iteratedDeriv_even_cos]
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.one_apply, abs_mul, abs_pow,
      abs_neg, abs_one, one_pow, one_mul]
    exact Real.abs_cos_le_one θ
  · rw [Real.iteratedDeriv_odd_cos]
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.one_apply, abs_mul, abs_pow,
      abs_neg, abs_one, one_pow, one_mul]
    exact Real.abs_sin_le_one θ

lemma abs_iteratedDeriv_comp_cos_le (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (K : ℝ)
    (hK : 0 ≤ K) (r : ℕ) (ε : ℝ)
    (hε : ∀ i ≤ r, ∀ x ∈ Set.Icc (-K) K, |iteratedDeriv i g x| ≤ ε) (θ : ℝ) :
    |iteratedDeriv r (fun θ => g (K * Real.cos θ)) θ| ≤ (r.factorial : ℝ) * ε * (max K 1) ^ r := by
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fun θ => K * Real.cos θ) := contDiff_const.mul Real.contDiff_cos
  have hr : ((r : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hmem : K * Real.cos θ ∈ Set.Icc (-K) K := by
    have h1 := Real.neg_one_le_cos θ
    have h2 := Real.cos_le_one θ
    constructor <;> nlinarith
  have key := norm_iteratedFDeriv_comp_le (g := g) (f := fun θ => K * Real.cos θ) (n := r)
    hg hf hr θ (C := ε) (D := max K 1) ?_ ?_
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at key
    exact key
  · intro i hi
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    exact hε i hi _ hmem
  · intro i hi1 _
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs, iteratedDeriv_const_mul_field,
      abs_mul, abs_of_nonneg hK]
    calc K * |iteratedDeriv i Real.cos θ| ≤ K * 1 :=
          mul_le_mul_of_nonneg_left (abs_iteratedDeriv_cos_le i θ) hK
      _ ≤ max K 1 := by rw [mul_one]; exact le_max_left _ _
      _ ≤ max K 1 ^ i := le_self_pow₀ (le_max_right _ _) (by omega)

lemma lpNormCircle_le_add (β : ℝ) (hβ : 1 < β) (F G : ℝ → ℝ) (hF : Continuous F)
    (hG : Continuous G) (δ : ℝ) (hδ : ∀ θ, |F θ - G θ| ≤ δ) :
    lpNormCircle β F ≤ lpNormCircle β G + (2 * Real.pi + 1) * δ := by
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hδ 0)
  set μ := MeasureTheory.volume.restrict (Set.Icc 0 (2 * Real.pi))
  set p := ENNReal.ofReal β
  have hp1 : 1 ≤ p := by
    rw [show (1 : ENNReal) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal hβ.le
  have hptr : p.toReal = β := ENNReal.toReal_ofReal (by linarith)
  have hμ : μ Set.univ = ENNReal.ofReal (2 * Real.pi) := by
    simp [μ, Real.volume_Icc]
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  have hbound : ∀ (H : ℝ → ℝ) (C : ℝ), 0 ≤ C → (∀ x ∈ Set.Icc 0 (2 * Real.pi), ‖H x‖ ≤ C) →
      MeasureTheory.eLpNorm H p μ ≤ ENNReal.ofReal ((2 * Real.pi) ^ β⁻¹ * C) := by
    intro H C hC hH
    refine (MeasureTheory.eLpNorm_le_of_ae_bound
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hH)).trans (le_of_eq ?_)
    rw [hμ, hptr, ENNReal.ofReal_rpow_of_nonneg hpi (by positivity), ← ENNReal.ofReal_mul
      (by positivity)]
  have hFG : MeasureTheory.eLpNorm (fun x => F x - G x) p μ ≤
      ENNReal.ofReal ((2 * Real.pi) ^ β⁻¹ * δ) :=
    hbound _ δ hδ0 (fun x _ => by rw [Real.norm_eq_abs]; exact hδ x)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := G)
    (s := Set.Icc 0 (2 * Real.pi)) hG.continuousOn
  have hGfin : MeasureTheory.eLpNorm G p μ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (hbound G (max M 0) (le_max_right _ _) (fun x hx => (hM x hx).trans (le_max_left _ _)))
  have htri : MeasureTheory.eLpNorm F p μ ≤
      MeasureTheory.eLpNorm G p μ + MeasureTheory.eLpNorm (fun x => F x - G x) p μ := by
    have := MeasureTheory.eLpNorm_add_le (μ := μ) (p := p) (f := G) (g := fun x => F x - G x)
      hG.aestronglyMeasurable (hF.sub hG).aestronglyMeasurable hp1
    convert this using 2
    funext x; simp
  have hsum : MeasureTheory.eLpNorm F p μ ≤
      MeasureTheory.eLpNorm G p μ + ENNReal.ofReal ((2 * Real.pi) ^ β⁻¹ * δ) :=
    htri.trans (add_le_add_right hFG _)
  unfold lpNormCircle
  have h1 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hGfin, ENNReal.ofReal_ne_top⟩) hsum
  rw [ENNReal.toReal_add hGfin ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (by positivity)] at h1
  refine h1.trans (add_le_add_right ?_ _)
  apply mul_le_mul_of_nonneg_right _ hδ0
  have hpi1 : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  calc (2 * Real.pi) ^ β⁻¹ ≤ (2 * Real.pi) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hpi1 (inv_le_one_of_one_le₀ hβ.le)
    _ ≤ 2 * Real.pi + 1 := by rw [Real.rpow_one]; linarith

lemma natDegree_chebK (K : ℝ) (hK : 0 < K) (j : ℕ) : (chebK K j).natDegree = j := by
  unfold chebK
  rw [natDegree_comp, natDegree_C_mul_X _ (inv_ne_zero hK.ne')]
  simp

lemma chebK_coeff_ne_zero (K : ℝ) (hK : 0 < K) (j : ℕ) : (chebK K j).coeff j ≠ 0 := by
  have h := natDegree_chebK K hK j
  have hne : chebK K j ≠ 0 := by
    intro h0
    have h1 : (chebK K j).leadingCoeff ≠ 0 := by
      unfold chebK
      rw [leadingCoeff_comp (by rw [natDegree_C_mul_X _ (inv_ne_zero hK.ne')]; norm_num)]
      simp [hK.ne']
    rw [h0] at h1
    simp at h1
  have := leadingCoeff_ne_zero.mpr hne
  rwa [leadingCoeff, h] at this

lemma exists_chebyshev_expansion_aux (K : ℝ) (hK : 0 < K) (m : ℕ) :
    ∀ p : ℝ[X], p.natDegree ≤ m →
      ∃ a : ℕ → ℝ, p = ∑ j ∈ Finset.range (m + 1), Polynomial.C (a j) * chebK K j := by
  induction m with
  | zero =>
    intro p hp
    refine ⟨fun _ => p.coeff 0, ?_⟩
    rw [eq_C_of_natDegree_le_zero hp]
    simp [chebK]
  | succ m ih =>
    intro p hp
    set c := p.coeff (m + 1) / (chebK K (m + 1)).coeff (m + 1)
    have hc : c * (chebK K (m + 1)).coeff (m + 1) = p.coeff (m + 1) :=
      div_mul_cancel₀ _ (chebK_coeff_ne_zero K hK (m + 1))
    have hdeg : (p - Polynomial.C c * chebK K (m + 1)).natDegree ≤ m := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [coeff_sub, coeff_C_mul]
      rcases Nat.lt_or_ge (m + 1) N with h | h
      · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp h),
          coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_chebK_le K (m + 1)) h)]
        simp
      · obtain rfl : N = m + 1 := by omega
        rw [hc]; simp
    obtain ⟨a, ha⟩ := ih _ hdeg
    refine ⟨fun j => if j = m + 1 then c else a j, ?_⟩
    rw [Finset.sum_range_succ]
    simp only [if_true]
    have : ∑ j ∈ Finset.range (m + 1),
        Polynomial.C (if j = m + 1 then c else a j) * chebK K j =
        ∑ j ∈ Finset.range (m + 1), Polynomial.C (a j) * chebK K j := by
      apply Finset.sum_congr rfl
      intro j hj
      simp at hj
      rw [if_neg (by omega)]
    rw [this, ← ha]
    ring

lemma exists_chebyshev_expansion (p : ℝ[X]) (K : ℝ) (hK : 0 < K) :
    ∃ a : ℕ → ℝ,
      (∀ x : ℝ, p.eval x = ∑ j ∈ Finset.range (p.natDegree + 1),
        a j * (Chebyshev.T ℝ j).eval (x / K)) ∧
      p = ∑ j ∈ Finset.range (p.natDegree + 1), Polynomial.C (a j) * chebK K j := by
  obtain ⟨a, ha⟩ := exists_chebyshev_expansion_aux K hK p.natDegree p le_rfl
  refine ⟨a, ?_, ha⟩
  intro x
  conv_lhs => rw [ha]
  rw [eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j _
  simp [chebK, eval_comp, div_eq_inv_mul]

lemma exists_antiderivative (q : ℝ[X]) : ∃ Q : ℝ[X], derivative Q = q := by
  refine ⟨∑ i ∈ Finset.range (q.natDegree + 1),
    Polynomial.C (q.coeff i / ((i : ℝ) + 1)) * X ^ (i + 1), ?_⟩
  rw [derivative_sum]
  conv_rhs => rw [as_sum_range_C_mul_X_pow q]
  apply Finset.sum_congr rfl
  intro i _
  rw [derivative_C_mul_X_pow]
  congr 2
  · push_cast
    field_simp

lemma exists_poly_approx (h : ℝ → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) (k : ℕ) (R ε : ℝ)
    (hε : 0 < ε) :
    ∃ p : ℝ[X], ∀ r ≤ k, ∀ x ∈ Set.Icc (-R) R,
      |iteratedDeriv r h x - iteratedDeriv r (fun x => p.eval x) x| ≤ ε := by
  induction k generalizing h ε with
  | zero =>
    obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-R) R h
      hh.continuous.continuousOn ε hε
    refine ⟨p, fun r hr x hx => ?_⟩
    obtain rfl : r = 0 := by omega
    simp only [iteratedDeriv_zero]
    rw [abs_sub_comm]
    exact (hp x hx).le
  | succ k ih =>
    rcases lt_or_ge R 0 with hR | hR
    · refine ⟨0, fun r _ x hx => ?_⟩
      exfalso
      have := hx.1.trans hx.2
      linarith
    have hR1 : 0 < 2 * R + 1 := by linarith
    set ε' := ε / (2 * R + 1) with hε'
    have hε'pos : 0 < ε' := div_pos hε hR1
    have hε'mul : ε' * (2 * R + 1) = ε := div_mul_cancel₀ _ hR1.ne'
    have hε'le : ε' ≤ ε := by nlinarith
    obtain ⟨hdiff, hd⟩ := contDiff_infty_iff_deriv.mp hh
    obtain ⟨q, hq⟩ := ih (deriv h) hd ε' hε'pos
    obtain ⟨Q, hQ⟩ := exists_antiderivative q
    set p := Q + Polynomial.C (h (-R) - Q.eval (-R)) with hpdef
    have hpd : derivative p = q := by
      rw [hpdef, derivative_add, derivative_C, add_zero, hQ]
    have hderiv : deriv (fun x => p.eval x) = fun x => q.eval x := by
      funext x
      rw [Polynomial.deriv, hpd]
    refine ⟨p, fun r hr x hx => ?_⟩
    rcases r with _ | s
    · simp only [iteratedDeriv_zero]
      have hg0 : h (-R) - p.eval (-R) = 0 := by
        rw [hpdef]; simp
      have hmem : (-R) ∈ Set.Icc (-R) R := ⟨le_rfl, by linarith⟩
      have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ)
        (f := fun y => h y - p.eval y) (s := Set.Icc (-R) R) (C := ε')
        (fun y _ => (hdiff y).sub p.differentiableAt) ?_ (convex_Icc _ _) hmem hx
      · simp only [hg0, sub_zero, Real.norm_eq_abs] at hmvt
        have hxR : |x - -R| ≤ 2 * R := by
          rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
        calc |h x - eval x p| ≤ ε' * |x - -R| := hmvt
          _ ≤ ε' * (2 * R) := mul_le_mul_of_nonneg_left hxR hε'pos.le
          _ ≤ ε := by nlinarith
      · intro y hy
        rw [deriv_fun_sub (hdiff y) p.differentiableAt, Polynomial.deriv, hpd, Real.norm_eq_abs]
        have := hq 0 (Nat.zero_le _) y hy
        simpa only [iteratedDeriv_zero] using this
    · rw [iteratedDeriv_succ', iteratedDeriv_succ', hderiv]
      exact (hq s (by omega) x hx).trans hε'le

lemma lpNormCircle_nonneg (β : ℝ) (F : ℝ → ℝ) : 0 ≤ lpNormCircle β F :=
  ENNReal.toReal_nonneg

lemma conjExp_pos (β : ℝ) (hβ : 1 < β) : 0 < conjExp β := by
  unfold conjExp
  have : 1 / β < 1 := by rw [div_lt_one (by linarith)]; exact hβ
  exact inv_pos.mpr (by linarith)

/-! ## Assembly -/
/-- The constant of Lemma 4.4. -/
noncomputable def Czyg : ℝ := Classical.choose abs_coeff_zero_le_and_sum_le_lpNormCircle

lemma Czyg_spec : ∀ (q : ℕ) (a : ℕ → ℝ) (K : ℝ), 0 < K →
      |a 0| ≤ cNorm 0 (fun x => ∑ j ∈ Finset.range (q + 1),
          a j * (Chebyshev.T ℝ j).eval (x / K)) (-K) K ∧
      ∀ (m : ℕ) (β : ℝ), 1 < β →
        ∑ j ∈ Finset.Icc 1 q, (j : ℝ) ^ m * |a j| ≤
          Czyg * conjExp β * lpNormCircle β (iteratedDeriv (m + 1) (fun θ =>
            ∑ j ∈ Finset.range (q + 1), a j * (Chebyshev.T ℝ j).eval (K * Real.cos θ / K))) :=
  Classical.choose_spec abs_coeff_zero_le_and_sum_le_lpNormCircle

lemma smooth_coe (h : smoothFun) : ContDiff ℝ (⊤ : ℕ∞) (h : ℝ → ℝ) := h.2

lemma poly_smooth (p : ℝ[X]) : ContDiff ℝ (⊤ : ℕ∞) (fun x => p.eval x) := (polyFun p).2

/-- The `L^β` side passes to the limit: a polynomial close to `h` in `C^(r)[-K, K]`. -/
lemma lp_perturb (h : smoothFun) (p : ℝ[X]) (K : ℝ) (hK : 0 ≤ K) (r : ℕ) (β : ℝ) (hβ : 1 < β)
    (ε : ℝ) (hε : ∀ i ≤ r, ∀ x ∈ Set.Icc (-K) K,
      |iteratedDeriv i (fun x => (h : ℝ → ℝ) x - p.eval x) x| ≤ ε) :
    lpNormCircle β (iteratedDeriv r (fun θ => p.eval (K * Real.cos θ))) ≤
      lpNormCircle β (iteratedDeriv r (fun θ => (h : ℝ → ℝ) (K * Real.cos θ))) +
        (2 * Real.pi + 1) * ((r.factorial : ℝ) * ε * (max K 1) ^ r) := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun θ : ℝ => K * Real.cos θ) :=
    contDiff_const.mul Real.contDiff_cos
  have hhc : ContDiff ℝ (⊤ : ℕ∞) (fun θ => (h : ℝ → ℝ) (K * Real.cos θ)) :=
    (smooth_coe h).comp hc
  have hpc : ContDiff ℝ (⊤ : ℕ∞) (fun θ => p.eval (K * Real.cos θ)) := (poly_smooth p).comp hc
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun x => (h : ℝ → ℝ) x - p.eval x) :=
    (smooth_coe h).sub (poly_smooth p)
  refine lpNormCircle_le_add β hβ _ _ (hpc.continuous_iteratedDeriv r (WithTop.coe_le_coe.mpr le_top))
    (hhc.continuous_iteratedDeriv r (WithTop.coe_le_coe.mpr le_top)) _ fun θ => ?_
  have h1 := abs_iteratedDeriv_comp_cos_le _ hg K hK r ε hε θ
  have h2 := iteratedDeriv_sub_of_contDiff _ _ hhc hpc r
  have h3 : (fun θ => (fun x => (h : ℝ → ℝ) x - p.eval x) (K * Real.cos θ)) =
      fun θ => (fun θ => (h : ℝ → ℝ) (K * Real.cos θ)) θ - (fun θ => p.eval (K * Real.cos θ)) θ :=
    rfl
  rw [h3, h2] at h1
  rw [abs_sub_comm]
  exact h1

lemma abs_chebK_le (K : ℝ) (hK : 0 < K) (j : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (-K) K) :
    |(chebK K j).eval x| ≤ 1 := by
  simp only [chebK, eval_comp, eval_mul, eval_C, eval_X]
  apply Chebyshev.abs_eval_T_real_le_one
  rw [abs_mul, abs_inv, abs_of_pos hK, inv_mul_le_iff₀ hK, mul_one]
  exact abs_le.mpr ⟨hx.1, hx.2⟩

/-!
# Part A2, module 4: from polynomial to smooth test functions

A linear functional `Λ` on `C^∞(ℝ)` that is continuous for some `C^k[-R, R]` norm (`Tame`) and
satisfies `|Λ p| ≤ B q^m sup_{[-K,K]} |p|` on polynomials of degree `≤ q` is bounded on every
smooth `h` by `B (sup_{[-K,K]} |h| + c ‖(h(K cos θ))^{(m+1)}‖_{L²})`: Chebyshev expansion and
Zygmund's bound for polynomials, then approximation of `h` and its derivatives by polynomials.
-/
/-- Continuity for some `C^k[-R, R]` norm, in the form used for polynomial approximation. -/
def Tame (Λ : smoothFun →ₗ[ℝ] ℝ) : Prop :=
  ∃ (c R : ℝ) (k : ℕ), 0 ≤ c ∧ 0 ≤ R ∧ ∀ (g : smoothFun) (ε : ℝ),
    (∀ r ≤ k, ∀ x ∈ Set.Icc (-R) R, |iteratedDeriv r (g : ℝ → ℝ) x| ≤ ε) → |Λ g| ≤ c * ε

lemma Tame.zero : Tame 0 :=
  ⟨0, 0, 0, le_rfl, le_rfl, fun g ε _ => by simp⟩

lemma Tame.add {Λ₁ Λ₂ : smoothFun →ₗ[ℝ] ℝ} (h₁ : Tame Λ₁) (h₂ : Tame Λ₂) : Tame (Λ₁ + Λ₂) := by
  obtain ⟨c₁, R₁, k₁, hc₁, hR₁, H₁⟩ := h₁
  obtain ⟨c₂, R₂, k₂, hc₂, hR₂, H₂⟩ := h₂
  refine ⟨c₁ + c₂, max R₁ R₂, max k₁ k₂, by positivity, le_max_of_le_left hR₁, fun g ε hg => ?_⟩
  have a₁ := H₁ g ε fun r hr x hx => hg r (hr.trans (le_max_left _ _)) x
    ⟨by linarith [hx.1, le_max_left R₁ R₂], by linarith [hx.2, le_max_left R₁ R₂]⟩
  have a₂ := H₂ g ε fun r hr x hx => hg r (hr.trans (le_max_right _ _)) x
    ⟨by linarith [hx.1, le_max_right R₁ R₂], by linarith [hx.2, le_max_right R₁ R₂]⟩
  rw [LinearMap.add_apply, add_mul]
  exact (abs_add_le _ _).trans (add_le_add a₁ a₂)

lemma Tame.smul {Λ : smoothFun →ₗ[ℝ] ℝ} (h : Tame Λ) (a : ℝ) : Tame (a • Λ) := by
  obtain ⟨c, R, k, hc, hR, H⟩ := h
  refine ⟨|a| * c, R, k, by positivity, hR, fun g ε hg => ?_⟩
  rw [LinearMap.smul_apply, smul_eq_mul, abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (H g ε hg) (abs_nonneg _)

lemma Tame.sub {Λ₁ Λ₂ : smoothFun →ₗ[ℝ] ℝ} (h₁ : Tame Λ₁) (h₂ : Tame Λ₂) : Tame (Λ₁ - Λ₂) := by
  have e : Λ₁ - Λ₂ = Λ₁ + (-1 : ℝ) • Λ₂ := by
    ext g
    simp [sub_eq_add_neg]
  rw [e]
  exact h₁.add (h₂.smul (-1))

lemma Tame.sum {ι : Type*} (s : Finset ι) (Λ : ι → smoothFun →ₗ[ℝ] ℝ) (h : ∀ i, Tame (Λ i)) :
    Tame (∑ i ∈ s, Λ i) :=
  Finset.sum_induction Λ Tame (fun _ _ => Tame.add) Tame.zero fun i _ => h i

lemma Tame.of_csd {μ : smoothFun →ₗ[ℝ] ℝ} (hμ : IsCSDistribution μ) : Tame μ := by
  obtain ⟨c, K, m, hc, hK, H⟩ := hμ
  refine ⟨c * ((m : ℝ) + 1), K, m, by positivity, hK.le, fun g ε hg => ?_⟩
  rw [mul_assoc]
  exact (H g).trans (mul_le_mul_of_nonneg_left (cNorm_le_of_abs_le m g K hK.le ε hg) hc.le)

/-- `E n` restricted to smooth functions, as a linear map. -/
noncomputable def PosFun.smoothL {K : ℝ} {E : ℕ → (ℝ → ℝ) → ℝ} (hE : PosFun K E) (n : ℕ) :
    smoothFun →ₗ[ℝ] ℝ where
  toFun g := E n (g : ℝ → ℝ)
  map_add' f g := hE.hadd n f g
  map_smul' a f := hE.hsmul n a f

lemma PosFun.smoothL_apply {K : ℝ} {E : ℕ → (ℝ → ℝ) → ℝ} (hE : PosFun K E) (n : ℕ)
    (g : smoothFun) : hE.smoothL n g = E n (g : ℝ → ℝ) := rfl

lemma PosFun.tame {K : ℝ} {E : ℕ → (ℝ → ℝ) → ℝ} (hE : PosFun K E) (n : ℕ) :
    Tame (hE.smoothL n) := by
  refine ⟨1, K, 0, zero_le_one, hE.hK.le, fun g ε hg => ?_⟩
  rw [one_mul, PosFun.smoothL_apply]
  refine hE.abs_le n _ ε fun x hx => ?_
  have := hg 0 le_rfl x hx
  rwa [iteratedDeriv_zero] at this

/-- `polyFun` as a linear map. -/
noncomputable def polyFunL : ℝ[X] →ₗ[ℝ] smoothFun where
  toFun := polyFun
  map_add' h g := by
    apply Subtype.ext
    funext x
    show (h + g).eval x = h.eval x + g.eval x
    simp
  map_smul' a h := by
    apply Subtype.ext
    funext x
    show (a • h).eval x = a * h.eval x
    simp

/-- The bound for a polynomial, in terms of the derivatives of `p(K cos θ)`. -/
theorem cheb_bound (K : ℝ) (hK : 0 < K) (err : ℝ[X] →ₗ[ℝ] ℝ) (B : ℝ) (hB0 : 0 ≤ B) (m : ℕ)
    (hPM : ∀ q : ℕ, 1 ≤ q → ∀ h : ℝ[X], h.natDegree ≤ q → ∀ s : ℝ,
      (∀ x ∈ Set.Icc (-K) K, |h.eval x| ≤ s) → |err h| ≤ B * (q : ℝ) ^ m * s)
    (p : ℝ[X]) (β : ℝ) (hβ : 1 < β) :
    |err p| ≤
      B * (cNorm 0 (fun x => p.eval x) (-K) K + max Czyg 0 * conjExp β *
        lpNormCircle β (iteratedDeriv (m + 1) (fun θ => p.eval (K * Real.cos θ)))) := by
  obtain ⟨a, ha_eval, ha_poly⟩ := exists_chebyshev_expansion p K hK
  set q := p.natDegree with hq
  have key : err p = ∑ j ∈ Finset.range (q + 1), a j * err (chebK K j) := by
    conv_lhs => rw [ha_poly]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_eq_C_mul, map_smul, smul_eq_mul]
  have hE0 : |err (chebK K 0)| ≤ B := by
    have := hPM 1 le_rfl (chebK K 0) ((natDegree_chebK_le K 0).trans zero_le_one) 1
      (abs_chebK_le K hK 0)
    refine this.trans (le_of_eq ?_)
    simp
  have hEj : ∀ j ∈ Finset.Icc 1 q, |a j * err (chebK K j)| ≤ B * ((j : ℝ) ^ m * |a j|) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have := hPM j hj1 (chebK K j) (natDegree_chebK_le K j) 1 (abs_chebK_le K hK j)
    rw [abs_mul]
    calc |a j| * |err (chebK K j)| ≤ |a j| * (B * (j : ℝ) ^ m * 1) :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = B * ((j : ℝ) ^ m * |a j|) := by ring
  obtain ⟨hz0, hzyg⟩ := Czyg_spec q a K hK
  have hfun : (fun θ => ∑ j ∈ Finset.range (q + 1),
      a j * (Chebyshev.T ℝ j).eval (K * Real.cos θ / K)) = fun θ => p.eval (K * Real.cos θ) := by
    funext θ; rw [ha_eval]
  have hfun0 : (fun x => ∑ j ∈ Finset.range (q + 1), a j * (Chebyshev.T ℝ j).eval (x / K)) =
      fun x => p.eval x := by
    funext x; rw [ha_eval]
  rw [hfun0] at hz0
  have hZ := hzyg m β hβ
  rw [hfun] at hZ
  set lp := lpNormCircle β (iteratedDeriv (m + 1) (fun θ => p.eval (K * Real.cos θ))) with hlp
  have hlp0 : 0 ≤ lp := lpNormCircle_nonneg _ _
  have hβs := conjExp_pos β hβ
  have hZ' : ∑ j ∈ Finset.Icc 1 q, (j : ℝ) ^ m * |a j| ≤ max Czyg 0 * conjExp β * lp := by
    refine hZ.trans ?_
    have : 0 ≤ conjExp β * lp := by positivity
    calc Czyg * conjExp β * lp = Czyg * (conjExp β * lp) := by ring
      _ ≤ max Czyg 0 * (conjExp β * lp) := mul_le_mul_of_nonneg_right (le_max_left _ _) this
      _ = _ := by ring
  rw [key, sum_range_succ_eq_add_Icc]
  have h0 : |a 0 * err (chebK K 0)| ≤ B * cNorm 0 (fun x => p.eval x) (-K) K := by
    rw [abs_mul, mul_comm]
    exact mul_le_mul hE0 hz0 (abs_nonneg _) hB0
  have hsum : |∑ j ∈ Finset.Icc 1 q, a j * err (chebK K j)| ≤
      B * (max Czyg 0 * conjExp β * lp) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hEj).trans ?_)
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hZ' hB0
  calc |a 0 * err (chebK K 0) + ∑ j ∈ Finset.Icc 1 q, a j * err (chebK K j)|
      ≤ |a 0 * err (chebK K 0)| + |∑ j ∈ Finset.Icc 1 q, a j * err (chebK K j)| :=
        abs_add_le _ _
    _ ≤ _ := by rw [mul_add]; linarith

/-- The bound for smooth test functions. -/
theorem smooth_bound (K : ℝ) (hK : 0 < K) (Λ : smoothFun →ₗ[ℝ] ℝ) (hΛ : Tame Λ) (B : ℝ)
    (hB0 : 0 ≤ B) (m : ℕ)
    (hPM : ∀ q : ℕ, 1 ≤ q → ∀ h : ℝ[X], h.natDegree ≤ q → ∀ s : ℝ,
      (∀ x ∈ Set.Icc (-K) K, |h.eval x| ≤ s) → |Λ (polyFun h)| ≤ B * (q : ℝ) ^ m * s)
    (h : smoothFun) (S : ℝ) (hS : ∀ x ∈ Set.Icc (-K) K, |(h : ℝ → ℝ) x| ≤ S) :
    |Λ h| ≤ B * (S + max Czyg 0 * conjExp 2 *
      lpNormCircle 2 (iteratedDeriv (m + 1) (fun θ => (h : ℝ → ℝ) (K * Real.cos θ)))) := by
  obtain ⟨c, R₀, k₀, hc, hR₀, hck⟩ := hΛ
  set Cz : ℝ := max Czyg 0 * conjExp 2 with hCz
  have hCz0 : 0 ≤ Cz := by
    have := conjExp_pos 2 (by norm_num)
    have := le_max_right Czyg 0
    positivity
  set lph := lpNormCircle 2 (iteratedDeriv (m + 1) (fun θ => (h : ℝ → ℝ) (K * Real.cos θ)))
    with hlph
  set R := K + R₀ with hR
  set kk := (m + 1) + k₀ with hkk
  set G : ℝ := (2 * Real.pi + 1) * (((m + 1).factorial : ℝ) * (max K 1) ^ (m + 1)) with hG
  have hG0 : 0 ≤ G := by
    have : (0 : ℝ) ≤ max K 1 := le_trans zero_le_one (le_max_right _ _)
    have := Real.pi_pos
    positivity
  set Mc : ℝ := B * (1 + Cz * G) + 1 + c with hMc
  have hM0 : 0 < Mc := by
    have : 0 ≤ B * (1 + Cz * G) := by positivity
    linarith
  have main : ∀ ε > 0, |Λ h| ≤ B * (S + Cz * lph) + ε * Mc := by
    intro ε hε
    obtain ⟨p, hp⟩ := exists_poly_approx (h : ℝ → ℝ) (smooth_coe h) kk R ε hε
    set g : ℝ → ℝ := fun x => (h : ℝ → ℝ) x - p.eval x with hgdef
    have hg : ∀ r ≤ kk, ∀ x ∈ Set.Icc (-R) R, |iteratedDeriv r g x| ≤ ε := by
      intro r hr x hx
      rw [hgdef, iteratedDeriv_sub_of_contDiff _ _ (smooth_coe h) (poly_smooth p) r]
      exact hp r hr x hx
    have hsubK : ∀ x ∈ Set.Icc (-K) K, x ∈ Set.Icc (-R) R := fun x hx =>
      ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hg0 : ∀ x ∈ Set.Icc (-K) K, |(h : ℝ → ℝ) x - p.eval x| ≤ ε := by
      intro x hx
      have := hg 0 (Nat.zero_le _) x (hsubK x hx)
      simpa [hgdef] using this
    have e2 : ((h - polyFun p : smoothFun) : ℝ → ℝ) = g := rfl
    have hb : |Λ h - Λ (polyFun p)| ≤ c * ε := by
      rw [← map_sub]
      refine hck _ ε ?_
      rw [e2]
      exact fun r hr x hx => hg r (by omega) x ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hc' := cheb_bound K hK (Λ ∘ₗ polyFunL) B hB0 m hPM p 2 (by norm_num)
    have hlp := lp_perturb h p K hK.le (m + 1) 2 (by norm_num) ε fun i hi x hx =>
      hg i (by omega) x (hsubK x hx)
    have hsup : cNorm 0 (fun x => p.eval x) (-K) K ≤ S + ε := by
      unfold cNorm
      simp only [zero_add, Finset.range_one, Finset.sum_singleton, iteratedDeriv_zero]
      apply supOn_le_of_forall (by linarith)
      intro x hx
      have h1 := hS x hx
      have h2 := hg0 x hx
      have h3 : |p.eval x| ≤ |(h : ℝ → ℝ) x| + |(h : ℝ → ℝ) x - p.eval x| := by
        have := abs_sub_abs_le_abs_sub (p.eval x) ((h : ℝ → ℝ) x)
        rw [abs_sub_comm] at this
        linarith
      linarith
    have hc'' : |Λ (polyFun p)| ≤ B * (S + Cz * lph) + ε * (B * (1 + Cz * G)) := by
      refine hc'.trans ?_
      have hin : cNorm 0 (fun x => p.eval x) (-K) K + max Czyg 0 * conjExp 2 *
          lpNormCircle 2 (iteratedDeriv (m + 1) (fun θ => p.eval (K * Real.cos θ))) ≤
          (S + ε) + Cz * (lph + (2 * Real.pi + 1) * (((m + 1).factorial : ℝ) * ε *
            (max K 1) ^ (m + 1))) :=
        add_le_add hsup (mul_le_mul_of_nonneg_left hlp hCz0)
      refine (mul_le_mul_of_nonneg_left hin hB0).trans (le_of_eq ?_)
      rw [hG]; ring
    have t1 : |Λ h| ≤ |Λ (polyFun p)| + |Λ h - Λ (polyFun p)| := by
      have := abs_add_le (Λ (polyFun p)) (Λ h - Λ (polyFun p))
      rwa [add_sub_cancel] at this
    have : ε * Mc = ε * (B * (1 + Cz * G)) + ε + c * ε := by rw [hMc]; ring
    linarith
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have := main (δ / Mc) (div_pos hδ hM0)
  rwa [div_mul_cancel₀ δ hM0.ne'] at this

/-!
# Part A2, module 5: the tail bound

Assembly: the polynomial master inequality along every ray (`poly_master2_aux`), identification
of the coefficients `T₀ = a`, `T₁ = A + ∑ κᵢ Bᵢ`, `T₂ = C₀ + ∑ κᵢ C₁ᵢ + ∑ κᵢ κⱼ C₂ᵢⱼ` on monomials,
interpolation at the even rays `0`, `2eᵢ`, `2eᵢ + 2eⱼ` to express `Bᵢ`, `C₁ᵢ`, `C₂ᵢⱼ + C₂ⱼᵢ` through
finitely many `T`'s (hence with ray-free constants), extension to compactly supported
distributions, supports from the moment growth, and the smooth bound applied to a cutoff.
-/
/-- Moment growth `|u p| ≤ C (ρ + δ)^p` for all `δ > 0` bounds the limsup of `|u p|^(1/p)`. -/
lemma limsup_rpow_le (u : ℕ → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hu : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ p : ℕ, |u p| ≤ C * (ρ + δ) ^ p) (η : ℝ) (hη : 0 < η) :
    limsup (fun p : ℕ => |u p| ^ (1 / (p : ℝ))) atTop ≤ ρ + η := by
  set δ : ℝ := min 1 (η / (ρ + 2)) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδη : δ * (ρ + 2) ≤ η := by
    have : δ ≤ η / (ρ + 2) := min_le_right _ _
    rwa [le_div_iff₀ (by linarith)] at this
  obtain ⟨C, hC⟩ := hu δ hδ0
  set C' : ℝ := max C 1 with hC'
  have hC'1 : 1 ≤ C' := le_max_right _ _
  have hC'pos : 0 < C' := by linarith
  have hlim : Tendsto (fun p : ℕ => C' ^ (1 / (p : ℝ))) atTop (𝓝 1) := by
    have : Tendsto ((fun x : ℝ => C' ^ x) ∘ fun n : ℕ => 1 / (n : ℝ)) atTop
        (𝓝 (C' ^ (0 : ℝ))) :=
      (Real.continuousAt_const_rpow (b := 0) hC'pos.ne').tendsto.comp
        tendsto_one_div_atTop_nhds_zero_nat
    rw [Real.rpow_zero] at this
    exact this
  have hev : ∀ᶠ p : ℕ in atTop, C' ^ (1 / (p : ℝ)) < 1 + δ :=
    (tendsto_order.1 hlim).2 (1 + δ) (by linarith)
  refine limsup_le_of_le ?_ ?_
  · exact (isBoundedUnder_of ⟨0, fun p => Real.rpow_nonneg (abs_nonneg _) _⟩).isCoboundedUnder_le
  · filter_upwards [hev, eventually_ge_atTop 1] with p hp hp1
    have hp0 : p ≠ 0 := by omega
    have hρδ : 0 ≤ ρ + δ := by linarith
    have h1 : |u p| ≤ C' * (ρ + δ) ^ p :=
      (hC p).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hρδ p))
    have hexp : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
    calc |u p| ^ (1 / (p : ℝ)) ≤ (C' * (ρ + δ) ^ p) ^ (1 / (p : ℝ)) :=
          Real.rpow_le_rpow (abs_nonneg _) h1 hexp
      _ = C' ^ (1 / (p : ℝ)) * (ρ + δ) := by
          rw [Real.mul_rpow hC'pos.le (pow_nonneg hρδ p), one_div,
            Real.pow_rpow_inv_natCast hρδ hp0]
      _ ≤ (1 + δ) * (ρ + δ) := mul_le_mul_of_nonneg_right hp.le hρδ
      _ ≤ ρ + η := by nlinarith

/-- A compactly supported distribution with moment growth `(ρ + δ)^p` kills smooth functions
vanishing on `|x| ≤ ρ + ε/2`. -/
lemma csd_eq_zero (μ : smoothFun →ₗ[ℝ] ℝ) (hμ : IsCSDistribution μ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hu : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ p : ℕ, |μ (polyFun (X ^ p))| ≤ C * (ρ + δ) ^ p)
    (ε : ℝ) (hε : 0 < ε) (χ : smoothFun)
    (hχ : ∀ x : ℝ, |x| ≤ ρ + ε / 2 → (χ : ℝ → ℝ) x = 0) : μ χ = 0 := by
  have hL := limsup_rpow_le (fun p => μ (polyFun (X ^ p))) ρ hρ hu (ε / 4) (by positivity)
  have hsupp := supp_subset_Icc_limsup μ hμ
  refine vanishesNear_supp μ hμ χ ?_
  have hopen : IsOpen {x : ℝ | |x| < ρ + ε / 2} := isOpen_lt continuous_abs continuous_const
  have hsub : supp μ ⊆ {x : ℝ | |x| < ρ + ε / 2} := by
    intro x hx
    have := hsupp hx
    show |x| < ρ + ε / 2
    rw [abs_lt]
    constructor <;> linarith [this.1, this.2]
  exact Filter.eventually_of_mem (hopen.mem_nhdsSet.2 hsub) fun x hx => hχ x (le_of_lt hx)

/-- A smooth test function with values in `[0, 1]`, zero on `|x| ≤ r₁`, one on `|x| ≥ r₂`. -/
lemma exists_cutoff (r₁ r₂ : ℝ) (h0 : 0 ≤ r₁) (h12 : r₁ < r₂) :
    ∃ χ : smoothFun, (∀ x, 0 ≤ (χ : ℝ → ℝ) x) ∧ (∀ x, (χ : ℝ → ℝ) x ≤ 1) ∧
      (∀ x, |x| ≤ r₁ → (χ : ℝ → ℝ) x = 0) ∧ (∀ x, r₂ ≤ |x| → (χ : ℝ → ℝ) x = 1) := by
  have hd : 0 < r₂ ^ 2 - r₁ ^ 2 := by nlinarith
  refine ⟨⟨fun x => Real.smoothTransition ((x ^ 2 - r₁ ^ 2) / (r₂ ^ 2 - r₁ ^ 2)), ?_⟩,
    fun x => Real.smoothTransition.nonneg _, fun x => Real.smoothTransition.le_one _, ?_, ?_⟩
  · show ContDiff ℝ (⊤ : ℕ∞) _
    exact Real.smoothTransition.contDiff.comp
      (((contDiff_id.pow 2).sub contDiff_const).div_const _)
  · intro x hx
    apply Real.smoothTransition.zero_of_nonpos
    have : x ^ 2 ≤ r₁ ^ 2 := by
      rw [← sq_abs x]; exact pow_le_pow_left₀ (abs_nonneg x) hx 2
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
  · intro x hx
    apply Real.smoothTransition.one_of_one_le
    have : r₂ ^ 2 ≤ x ^ 2 := by
      rw [← sq_abs x]; exact pow_le_pow_left₀ (by linarith) hx 2
    rw [le_div_iff₀ hd]; linarith

/-! ## Functionals on polynomials with a Markov-type bound -/
/-- `|ν h| ≤ c q^m sup_{[-K,K]} |h|` for `deg h ≤ q`. -/
def PolyBdd (K : ℝ) (ν : ℝ[X] →ₗ[ℝ] ℝ) : Prop :=
  ∃ (c : ℝ) (m : ℕ), 0 ≤ c ∧ ∀ q : ℕ, 1 ≤ q → ∀ h : ℝ[X], h.natDegree ≤ q → ∀ s : ℝ,
    (∀ x ∈ Set.Icc (-K) K, |h.eval x| ≤ s) → |ν h| ≤ c * (q : ℝ) ^ m * s

lemma PolyBdd.add {K : ℝ} (hK : 0 < K) {ν₁ ν₂ : ℝ[X] →ₗ[ℝ] ℝ} (h₁ : PolyBdd K ν₁)
    (h₂ : PolyBdd K ν₂) : PolyBdd K (ν₁ + ν₂) := by
  obtain ⟨c₁, m₁, hc₁, H₁⟩ := h₁
  obtain ⟨c₂, m₂, hc₂, H₂⟩ := h₂
  refine ⟨c₁ + c₂, m₁ + m₂, by positivity, fun q hq h hh s hs => ?_⟩
  have hs0 : 0 ≤ s := (abs_nonneg _).trans (hs 0 ⟨by linarith, hK.le⟩)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have e₁ : (q : ℝ) ^ m₁ ≤ (q : ℝ) ^ (m₁ + m₂) := pow_le_pow_right₀ hq1 (Nat.le_add_right _ _)
  have e₂ : (q : ℝ) ^ m₂ ≤ (q : ℝ) ^ (m₁ + m₂) := pow_le_pow_right₀ hq1 (Nat.le_add_left _ _)
  have a₁ : c₁ * (q : ℝ) ^ m₁ * s ≤ c₁ * (q : ℝ) ^ (m₁ + m₂) * s :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e₁ hc₁) hs0
  have a₂ : c₂ * (q : ℝ) ^ m₂ * s ≤ c₂ * (q : ℝ) ^ (m₁ + m₂) * s :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e₂ hc₂) hs0
  rw [LinearMap.add_apply]
  have := abs_add_le (ν₁ h) (ν₂ h)
  have b₁ := H₁ q hq h hh s hs
  have b₂ := H₂ q hq h hh s hs
  calc |ν₁ h + ν₂ h| ≤ c₁ * (q : ℝ) ^ (m₁ + m₂) * s + c₂ * (q : ℝ) ^ (m₁ + m₂) * s := by linarith
    _ = (c₁ + c₂) * (q : ℝ) ^ (m₁ + m₂) * s := by ring

lemma PolyBdd.smul {K : ℝ} {ν : ℝ[X] →ₗ[ℝ] ℝ} (h : PolyBdd K ν) (a : ℝ) :
    PolyBdd K (a • ν) := by
  obtain ⟨c, m, hc, H⟩ := h
  refine ⟨|a| * c, m, by positivity, fun q hq h hh s hs => ?_⟩
  rw [LinearMap.smul_apply, smul_eq_mul, abs_mul, mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [← mul_assoc]
  exact H q hq h hh s hs

lemma PolyBdd.sub {K : ℝ} (hK : 0 < K) {ν₁ ν₂ : ℝ[X] →ₗ[ℝ] ℝ} (h₁ : PolyBdd K ν₁)
    (h₂ : PolyBdd K ν₂) : PolyBdd K (ν₁ - ν₂) := by
  have e : ν₁ - ν₂ = ν₁ + (-1 : ℝ) • ν₂ := by
    ext g
    simp [sub_eq_add_neg]
  rw [e]
  exact h₁.add hK (h₂.smul (-1))

/-- Extension of a functional on polynomials with a Markov-type bound to a compactly supported
distribution. -/
lemma exists_csExt (K : ℝ) (hK : 0 < K) (ν : ℝ[X] →ₗ[ℝ] ℝ) (hν : PolyBdd K ν) :
    ∃ μ : smoothFun →ₗ[ℝ] ℝ, IsCSDistribution μ ∧ ∀ h : ℝ[X], μ (polyFun h) = ν h := by
  obtain ⟨A, m, hA, hν⟩ := hν
  have h1 : ∃ c m K : ℝ, 0 ≤ c ∧ 0 ≤ m ∧ 0 ≤ K ∧ ∀ q : ℕ, 1 ≤ q → ∀ h : ℝ[X],
      h.natDegree ≤ q → |ν h| ≤ c * (q : ℝ) ^ m * cNorm 0 (fun x => h.eval x) (-K) K := by
    refine ⟨A, ((m : ℕ) : ℝ), K, hA, by positivity, hK.le, fun q hq h hh => ?_⟩
    rw [Real.rpow_natCast]
    refine hν q hq h hh _ fun x hx => ?_
    have := abs_le_cNorm_zero (fun x => h.eval x) (-K) K
      (by rw [iteratedDeriv_zero]; exact h.continuous.continuousOn) x hx
    rwa [iteratedDeriv_zero] at this
  obtain ⟨μ, hμ, -⟩ := ((tfae_extends_csDistribution ν).out 0 2).mp h1
  exact ⟨μ, hμ.1, hμ.2⟩

lemma lin_ext (f g : ℝ[X] →ₗ[ℝ] ℝ) (h : ∀ p : ℕ, f (X ^ p) = g (X ^ p)) : f = g := by
  refine Polynomial.lhom_ext' fun n => LinearMap.ext_ring ?_
  show f (monomial n 1) = g (monomial n 1)
  rw [monomial_one_right_eq_X_pow]
  exact h n

/-! ## Identification of the coefficients -/
lemma Exp3.of_last {l : Filter ℕ} (hl : l ≤ atTop) {F : ℕ → ℝ} {l0 l1 l2 : ℝ}
    (h2 : Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * (F N - l0 - l1 / N)) l (𝓝 l2)) :
    Exp3 l F l0 l1 l2 := by
  have hinv := tendsto_inv_cast hl
  have hge : ∀ᶠ N : ℕ in l, 1 ≤ N := hl (eventually_ge_atTop 1)
  have h1 : Tendsto (fun N : ℕ => (N : ℝ) * (F N - l0)) l (𝓝 l1) := by
    have h3 : Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * (F N - l0 - l1 / N) * ((N : ℝ))⁻¹ + l1) l
        (𝓝 (l2 * 0 + l1)) := (h2.mul hinv).add tendsto_const_nhds
    rw [mul_zero, zero_add] at h3
    refine h3.congr' ?_
    filter_upwards [hge] with N hN1
    have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
    field_simp
    ring
  refine ⟨?_, h1, h2⟩
  have h3 : Tendsto (fun N : ℕ => (N : ℝ) * (F N - l0) * ((N : ℝ))⁻¹ + l0) l
      (𝓝 (l1 * 0 + l0)) := (h1.mul hinv).add tendsto_const_nhds
  rw [mul_zero, zero_add] at h3
  refine h3.congr' ?_
  filter_upwards [hge] with N hN1
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  field_simp
  ring

lemma ident {r : ℕ} (κ : Fin r → ℕ) (N₀ : ℕ) (h0 : AdmK N₀ κ) (F : ℕ → ℝ)
    (t0 t1 t2 a b L Bd : ℝ)
    (hb : ∀ N : ℕ, AdmK N κ → 1 ≤ N →
      |F N - t0 - t1 / N - t2 / (N : ℝ) ^ 2| ≤ Bd / (N : ℝ) ^ 3)
    (hL : Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * (F N - a - b / N)) (admF κ) (𝓝 L)) :
    t0 = a ∧ t1 = b ∧ t2 = L := by
  have := admF_neBot κ N₀ h0
  exact Exp3.unique
    (Exp3.of_bound (admF_le κ) (eventually_admF κ 1 _ fun N hN hA => hb N hA hN))
    (Exp3.of_last (admF_le κ) hL)

/-! ## The even rays used for interpolation -/
/-- The ray `κ = 0`. -/
def ray0 (r : ℕ) : Fin r → ℕ := fun _ => 0

/-- The ray `κ = 2 eᵢ`. -/
def ray1 {r : ℕ} (i : Fin r) : Fin r → ℕ := fun k => if k = i then 2 else 0

/-- The ray `κ = 2 eᵢ + 2 eⱼ`. -/
def ray2 {r : ℕ} (i j : Fin r) : Fin r → ℕ :=
  fun k => (if k = i then 2 else 0) + (if k = j then 2 else 0)

lemma adm_ray0 (r : ℕ) : AdmK 4 (ray0 r) := fun k => ⟨by simp [ray0], by simp [ray0]⟩

lemma adm_ray1 {r : ℕ} (i : Fin r) : AdmK 4 (ray1 i) := fun k => by
  unfold ray1; split_ifs <;> exact ⟨by norm_num, by norm_num⟩

lemma adm_ray2 {r : ℕ} (i j : Fin r) : AdmK 4 (ray2 i j) := fun k => by
  unfold ray2; split_ifs <;> exact ⟨by norm_num, by norm_num⟩

lemma sum_ray0 {r : ℕ} (f : Fin r → ℝ) : ∑ k, ((ray0 r k : ℕ) : ℝ) * f k = 0 := by
  simp [ray0]

lemma sum_ray1 {r : ℕ} (i : Fin r) (f : Fin r → ℝ) :
    ∑ k, ((ray1 i k : ℕ) : ℝ) * f k = 2 * f i := by
  simp [ray1, Nat.cast_ite, ite_mul]

lemma sum_ray2 {r : ℕ} (i j : Fin r) (f : Fin r → ℝ) :
    ∑ k, ((ray2 i j k : ℕ) : ℝ) * f k = 2 * f i + 2 * f j := by
  simp [ray2, Nat.cast_ite, ite_mul, add_mul, Finset.sum_add_distrib]

/-- The second-order coefficient as a function of the ray. -/
def Qf {r : ℕ} (c0 : ℝ) (c1 : Fin r → ℝ) (c2 : Fin r → Fin r → ℝ) (κ : Fin r → ℕ) : ℝ :=
  c0 + ∑ i, (κ i : ℝ) * c1 i + ∑ i, ∑ j, (κ i : ℝ) * κ j * c2 i j

lemma Qf_ray0 {r : ℕ} (c0 : ℝ) (c1 : Fin r → ℝ) (c2 : Fin r → Fin r → ℝ) :
    Qf c0 c1 c2 (ray0 r) = c0 := by
  simp [Qf, ray0]

lemma Qf_ray1 {r : ℕ} (c0 : ℝ) (c1 : Fin r → ℝ) (c2 : Fin r → Fin r → ℝ) (i : Fin r) :
    Qf c0 c1 c2 (ray1 i) = c0 + 2 * c1 i + 4 * c2 i i := by
  unfold Qf
  simp_rw [mul_assoc, ← Finset.mul_sum, sum_ray1]
  ring

lemma Qf_ray2 {r : ℕ} (c0 : ℝ) (c1 : Fin r → ℝ) (c2 : Fin r → Fin r → ℝ) (i j : Fin r) :
    Qf c0 c1 c2 (ray2 i j) =
      c0 + 2 * c1 i + 2 * c1 j + 4 * c2 i i + 4 * c2 i j + 4 * c2 j i + 4 * c2 j j := by
  unfold Qf
  simp_rw [mul_assoc, ← Finset.mul_sum, sum_ray2]
  ring

lemma le_lam {r : ℕ} (κ : Fin r → ℕ) (i : Fin r) : (κ i : ℝ) ≤ lam κ := by
  unfold lam
  have : (κ i : ℝ) ≤ ∑ j, (κ j : ℝ) :=
    Finset.single_le_sum (f := fun j => (κ j : ℝ)) (fun j _ => Nat.cast_nonneg _)
      (Finset.mem_univ i)
  linarith

/-! ## The tail bound -/
theorem tail_core (K : ℝ) (hK : 0 < K) (r : ℕ) (E : (Fin r → ℕ) → ℕ → (ℝ → ℝ) → ℝ)
    (hadd : ∀ κ N f g, E κ N (f + g) = E κ N f + E κ N g)
    (hsmul : ∀ κ N (a : ℝ) f, E κ N (a • f) = a * E κ N f)
    (hmono : ∀ κ N f g, (∀ x ∈ Set.Icc (-K) K, f x ≤ g x) → E κ N f ≤ E κ N g)
    (hone : ∀ κ N, E κ N (fun _ => 1) ≤ 1)
    (hrat : ∃ C : ℕ, 1 ≤ C ∧ ∀ q : ℕ, 1 ≤ q → ∃ gq : ℝ[X], gq.natDegree ≤ C * q ∧
      (∀ x ∈ Set.Icc (0 : ℝ) (1 / ((C : ℝ) * (q : ℝ) ^ 2)), 1 / 2 ≤ gq.eval x ∧ gq.eval x ≤ 1) ∧
      ∀ h : ℝ[X], h.natDegree ≤ q → ∀ κ : Fin r → ℕ, ∃ f : ℝ[X], f.natDegree ≤ C * q ∧
        ∀ N : ℕ, AdmK N κ → C * q ≤ N →
          E κ N (fun x => h.eval x) = f.eval (1 / (N : ℝ)) / gq.eval (1 / (N : ℝ)))
    (ρ : ℝ) (hρ : 0 ≤ ρ) (a A : ℕ → ℝ) (B : Fin r → ℕ → ℝ) (C2 : Fin r → Fin r → ℕ → ℝ)
    (hexp : ∃ (C0 : ℕ → ℝ) (C1 : Fin r → ℕ → ℝ), ∀ (κ : Fin r → ℕ) (p : ℕ),
      Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * (E κ N (fun x => x ^ p) - a p -
          (A p + ∑ i, (κ i : ℝ) * B i p) / N)) (admF κ)
        (𝓝 (C0 p + ∑ i, (κ i : ℝ) * C1 i p + ∑ i, ∑ j, (κ i : ℝ) * κ j * C2 i j p)))
    (hagrow : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ p : ℕ, |a p| ≤ C * (ρ + δ) ^ p)
    (hAgrow : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ p : ℕ, |A p| ≤ C * (ρ + δ) ^ p)
    (hBgrow : ∀ i, ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ p : ℕ, |B i p| ≤ C * (ρ + δ) ^ p)
    (hC2grow : ∀ i j, ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ p : ℕ, |C2 i j p| ≤ C * (ρ + δ) ^ p)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ (κ : Fin r → ℕ) (N : ℕ), AdmK N κ → 1 ≤ N → ∀ f : ℝ → ℝ, (∀ x, f x ≤ 1) →
      (∀ x, |x| < ρ + ε → f x ≤ 0) →
      E κ N f ≤ C * lam κ / (N : ℝ) ^ 2 + C * lam κ ^ 3 / (N : ℝ) ^ 3 := by
  obtain ⟨A0, M, hA0, hT⟩ := poly_master2_aux K hK r E hadd hsmul hmono hone hrat
  choose T hT using hT
  obtain ⟨C0, C1, hexp⟩ := hexp
  have hE : ∀ κ, PosFun K (E κ) := fun κ => ⟨hK, hadd κ, hsmul κ, hmono κ, hone κ⟩
  have hPB : ∀ κ (j : Fin 3), PolyBdd K (T κ j) := by
    intro κ j
    have := one_le_lam κ
    refine ⟨(A0 * lam κ) ^ (j : ℕ), M * j, by positivity, fun q hq h hh s hs => ?_⟩
    refine ((hT κ q hq h hh s hs).1 j).trans (le_of_eq ?_)
    rw [pow_mul, mul_pow, mul_pow, mul_pow]
    ring
  -- identification on monomials
  have hid : ∀ κ N₀, AdmK N₀ κ → ∀ p : ℕ, T κ 0 (X ^ p) = a p ∧
      T κ 1 (X ^ p) = A p + ∑ i, (κ i : ℝ) * B i p ∧
      T κ 2 (X ^ p) = Qf (C0 p) (fun i => C1 i p) (fun i j => C2 i j p) κ := by
    intro κ N₀ h0 p
    have hsb : ∀ x ∈ Set.Icc (-K) K, |(X ^ p : ℝ[X]).eval x| ≤ K ^ p := by
      intro x hx
      rw [eval_pow, eval_X, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_le.2 ⟨hx.1, hx.2⟩) p
    have hb := (hT κ (max p 1) (le_max_right _ _) (X ^ p)
      ((natDegree_X_pow_le p).trans (le_max_left _ _)) (K ^ p) hsb).2
    simp only [eval_pow, eval_X] at hb
    exact ident κ N₀ h0 (fun N => E κ N (fun x => x ^ p)) _ _ _ _ _ _ _ hb (hexp κ p)
  set z := ray0 r with hz
  have hz0 := adm_ray0 r
  set νB : Fin r → ℝ[X] →ₗ[ℝ] ℝ := fun i => (1 / 2 : ℝ) • (T (ray1 i) 1 - T z 1) with hνB
  set νS : Fin r → Fin r → ℝ[X] →ₗ[ℝ] ℝ := fun i j =>
    (1 / 4 : ℝ) • (T (ray2 i j) 2 - T (ray1 i) 2 - T (ray1 j) 2 + T z 2) with hνS
  set νC1 : Fin r → ℝ[X] →ₗ[ℝ] ℝ := fun i =>
    (1 / 2 : ℝ) • (T (ray1 i) 2 - T z 2) - νS i i with hνC1
  have va : ∀ p, T z 0 (X ^ p) = a p := fun p => (hid z 4 hz0 p).1
  have vA : ∀ p, T z 1 (X ^ p) = A p := fun p => by
    rw [(hid z 4 hz0 p).2.1, sum_ray0, add_zero]
  have vC0 : ∀ p, T z 2 (X ^ p) = C0 p := fun p => by
    rw [(hid z 4 hz0 p).2.2, Qf_ray0]
  have vB : ∀ i p, νB i (X ^ p) = B i p := by
    intro i p
    simp only [hνB, LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul, vA,
      (hid (ray1 i) 4 (adm_ray1 i) p).2.1, sum_ray1]
    ring
  have vS : ∀ i j p, νS i j (X ^ p) = C2 i j p + C2 j i p := by
    intro i j p
    simp only [hνS, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.add_apply, smul_eq_mul,
      vC0, (hid (ray2 i j) 4 (adm_ray2 i j) p).2.2, (hid (ray1 i) 4 (adm_ray1 i) p).2.2,
      (hid (ray1 j) 4 (adm_ray1 j) p).2.2, Qf_ray1, Qf_ray2]
    ring
  have vC1 : ∀ i p, νC1 i (X ^ p) = C1 i p := by
    intro i p
    simp only [hνC1, LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul, vC0, vS,
      (hid (ray1 i) 4 (adm_ray1 i) p).2.2, Qf_ray1]
    ring
  -- the coefficients along any admissible ray
  have gen : ∀ κ N₀, AdmK N₀ κ → T κ 0 = T z 0 ∧ T κ 1 = T z 1 + ∑ i, (κ i : ℝ) • νB i ∧
      T κ 2 = T z 2 + ∑ i, (κ i : ℝ) • νC1 i +
        (1 / 2 : ℝ) • ∑ i, ∑ j, ((κ i : ℝ) * κ j) • νS i j := by
    intro κ N₀ h0
    refine ⟨lin_ext _ _ fun p => ?_, lin_ext _ _ fun p => ?_, lin_ext _ _ fun p => ?_⟩
    · rw [(hid κ N₀ h0 p).1, va]
    · rw [(hid κ N₀ h0 p).2.1]
      simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        vB, vA]
    · rw [(hid κ N₀ h0 p).2.2]
      simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        vC1, vS, vC0]
      unfold Qf
      have hsw : ∑ i, ∑ j, (κ i : ℝ) * κ j * C2 j i p = ∑ i, ∑ j, (κ i : ℝ) * κ j * C2 i j p := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      simp only [mul_add, Finset.sum_add_distrib, hsw]
      ring
  -- extension to compactly supported distributions
  obtain ⟨μa, hμa, ea⟩ := exists_csExt K hK (T z 0) (hPB z 0)
  obtain ⟨μA, hμA, eA⟩ := exists_csExt K hK (T z 1) (hPB z 1)
  obtain ⟨μC0, hμC0, eC0⟩ := exists_csExt K hK (T z 2) (hPB z 2)
  have pbB : ∀ i, PolyBdd K (νB i) := fun i => ((hPB _ 1).sub hK (hPB _ 1)).smul _
  have pbS : ∀ i j, PolyBdd K (νS i j) := fun i j =>
    ((((hPB _ 2).sub hK (hPB _ 2)).sub hK (hPB _ 2)).add hK (hPB _ 2)).smul _
  have pbC1 : ∀ i, PolyBdd K (νC1 i) := fun i =>
    (((hPB _ 2).sub hK (hPB _ 2)).smul _).sub hK (pbS i i)
  choose μB hμB eB using fun i => exists_csExt K hK (νB i) (pbB i)
  choose μS hμS eS using fun i j => exists_csExt K hK (νS i j) (pbS i j)
  choose μC1 hμC1 eC1 using fun i => exists_csExt K hK (νC1 i) (pbC1 i)
  obtain ⟨χ, hχ0, hχ1, hχz, hχo⟩ :=
    exists_cutoff (ρ + ε / 2) (ρ + ε) (by linarith) (by linarith)
  have za : μa χ = 0 := by
    refine csd_eq_zero μa hμa ρ hρ (fun δ hδ => ?_) ε hε χ hχz
    obtain ⟨c, hc⟩ := hagrow δ hδ
    exact ⟨c, fun p => by rw [ea, va]; exact hc p⟩
  have zA : μA χ = 0 := by
    refine csd_eq_zero μA hμA ρ hρ (fun δ hδ => ?_) ε hε χ hχz
    obtain ⟨c, hc⟩ := hAgrow δ hδ
    exact ⟨c, fun p => by rw [eA, vA]; exact hc p⟩
  have zB : ∀ i, μB i χ = 0 := by
    intro i
    refine csd_eq_zero (μB i) (hμB i) ρ hρ (fun δ hδ => ?_) ε hε χ hχz
    obtain ⟨c, hc⟩ := hBgrow i δ hδ
    exact ⟨c, fun p => by rw [eB, vB]; exact hc p⟩
  have zS : ∀ i j, μS i j χ = 0 := by
    intro i j
    refine csd_eq_zero (μS i j) (hμS i j) ρ hρ (fun δ hδ => ?_) ε hε χ hχz
    obtain ⟨c, hc⟩ := hC2grow i j δ hδ
    obtain ⟨c', hc'⟩ := hC2grow j i δ hδ
    refine ⟨c + c', fun p => ?_⟩
    rw [eS, vS, add_mul]
    exact (abs_add_le _ _).trans (add_le_add (hc p) (hc' p))
  set W : ℝ := 1 + max Czyg 0 * conjExp 2 *
    lpNormCircle 2 (iteratedDeriv (M * 3 + 1) (fun θ => (χ : ℝ → ℝ) (K * Real.cos θ))) with hW
  have hW0 : 0 ≤ W := by
    have h1 := conjExp_pos 2 (by norm_num)
    have h2 := le_max_right Czyg 0
    have h3 := lpNormCircle_nonneg 2
      (iteratedDeriv (M * 3 + 1) (fun θ => (χ : ℝ → ℝ) (K * Real.cos θ)))
    rw [hW]
    positivity
  set D : ℝ := |μC0 χ| + ∑ i, |μC1 i χ| with hD
  have hD0 : 0 ≤ D := by
    have : 0 ≤ ∑ i, |μC1 i χ| := Finset.sum_nonneg fun i _ => abs_nonneg _
    have := abs_nonneg (μC0 χ)
    linarith
  refine ⟨D + A0 ^ 3 * W, fun κ N hA hN f hf1 hf0 => ?_⟩
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hlam := one_le_lam κ
  obtain ⟨g0, g1, g2⟩ := gen κ N hA
  set Λ₁ : smoothFun →ₗ[ℝ] ℝ := μA + ∑ i, (κ i : ℝ) • μB i with hΛ₁
  set Λ₂ : smoothFun →ₗ[ℝ] ℝ :=
    μC0 + ∑ i, (κ i : ℝ) • μC1 i + (1 / 2 : ℝ) • ∑ i, ∑ j, ((κ i : ℝ) * κ j) • μS i j with hΛ₂
  set Λ : smoothFun →ₗ[ℝ] ℝ :=
    (hE κ).smoothL N - μa - (1 / (N : ℝ)) • Λ₁ - (1 / (N : ℝ) ^ 2) • Λ₂ with hΛ
  have t₁ : Tame Λ₁ :=
    (Tame.of_csd hμA).add (Tame.sum _ _ fun i => (Tame.of_csd (hμB i)).smul _)
  have t₂ : Tame Λ₂ :=
    ((Tame.of_csd hμC0).add (Tame.sum _ _ fun i => (Tame.of_csd (hμC1 i)).smul _)).add
      ((Tame.sum _ _ fun i => Tame.sum _ _ fun j => (Tame.of_csd (hμS i j)).smul _).smul _)
  have tΛ : Tame Λ := ((((hE κ).tame N).sub (Tame.of_csd hμa)).sub (t₁.smul _)).sub (t₂.smul _)
  have hpoly : ∀ h : ℝ[X], Λ (polyFun h) =
      E κ N (fun x => h.eval x) - T κ 0 h - T κ 1 h / N - T κ 2 h / (N : ℝ) ^ 2 := by
    intro h
    have hcoe : ((polyFun h : smoothFun) : ℝ → ℝ) = fun x => h.eval x := rfl
    rw [g0, g1, g2]
    simp only [hΛ, hΛ₁, hΛ₂, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.sum_apply, smul_eq_mul, PosFun.smoothL_apply, ea, eA, eC0, eB, eC1, eS, hcoe]
    ring
  have hPM : ∀ q : ℕ, 1 ≤ q → ∀ h : ℝ[X], h.natDegree ≤ q → ∀ s : ℝ,
      (∀ x ∈ Set.Icc (-K) K, |h.eval x| ≤ s) →
      |Λ (polyFun h)| ≤ (A0 * lam κ) ^ 3 / (N : ℝ) ^ 3 * (q : ℝ) ^ (M * 3) * s := by
    intro q hq h hh s hs
    rw [hpoly]
    refine ((hT κ q hq h hh s hs).2 N hA hN).trans (le_of_eq ?_)
    rw [pow_mul]
    ring
  have hχS : ∀ x ∈ Set.Icc (-K) K, |(χ : ℝ → ℝ) x| ≤ 1 := fun x _ => by
    rw [abs_of_nonneg (hχ0 x)]; exact hχ1 x
  have hmain : |Λ χ| ≤ (A0 * lam κ) ^ 3 / (N : ℝ) ^ 3 * W :=
    smooth_bound K hK Λ tΛ ((A0 * lam κ) ^ 3 / (N : ℝ) ^ 3) (by positivity) (M * 3) hPM χ 1 hχS
  have hΛχ : Λ χ = E κ N (χ : ℝ → ℝ) -
      (1 / (N : ℝ) ^ 2) * (μC0 χ + ∑ i, (κ i : ℝ) * μC1 i χ) := by
    simp only [hΛ, hΛ₁, hΛ₂, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.sum_apply, smul_eq_mul, PosFun.smoothL_apply, za, zA, zB, zS, mul_zero,
      Finset.sum_const_zero, add_zero, sub_zero]
  have h1 : E κ N f ≤ E κ N (χ : ℝ → ℝ) := hmono κ N _ _ fun x _ => by
    by_cases hx : |x| < ρ + ε
    · exact (hf0 x hx).trans (hχ0 x)
    · rw [hχo x (not_lt.1 hx)]; exact hf1 x
  have h3 : |μC0 χ + ∑ i, (κ i : ℝ) * μC1 i χ| ≤ lam κ * D := by
    have s1 : |∑ i, (κ i : ℝ) * μC1 i χ| ≤ ∑ i, lam κ * |μC1 i χ| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_right (le_lam κ i) (abs_nonneg _)
    have s0 : |μC0 χ| ≤ lam κ * |μC0 χ| := by nlinarith [abs_nonneg (μC0 χ)]
    rw [hD, mul_add, Finset.mul_sum]
    exact (abs_add_le _ _).trans (add_le_add s0 s1)
  have h2 : E κ N (χ : ℝ → ℝ) ≤
      lam κ * D / (N : ℝ) ^ 2 + (A0 * lam κ) ^ 3 * W / (N : ℝ) ^ 3 := by
    have e : E κ N (χ : ℝ → ℝ) =
        Λ χ + (μC0 χ + ∑ i, (κ i : ℝ) * μC1 i χ) / (N : ℝ) ^ 2 := by rw [hΛχ]; ring
    have b1 : (μC0 χ + ∑ i, (κ i : ℝ) * μC1 i χ) / (N : ℝ) ^ 2 ≤ lam κ * D / (N : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right ((le_abs_self _).trans h3) (by positivity)
    have b2 : Λ χ ≤ (A0 * lam κ) ^ 3 * W / (N : ℝ) ^ 3 := by
      refine (le_abs_self _).trans (hmain.trans (le_of_eq ?_))
      ring
    rw [e]
    linarith
  have e1 : (D + A0 ^ 3 * W) * lam κ / (N : ℝ) ^ 2 + (D + A0 ^ 3 * W) * lam κ ^ 3 / (N : ℝ) ^ 3 =
      lam κ * D / (N : ℝ) ^ 2 + (A0 * lam κ) ^ 3 * W / (N : ℝ) ^ 3 +
        (A0 ^ 3 * W * lam κ / (N : ℝ) ^ 2 + D * lam κ ^ 3 / (N : ℝ) ^ 3) := by ring
  have e2 : 0 ≤ A0 ^ 3 * W * lam κ / (N : ℝ) ^ 2 + D * lam κ ^ 3 / (N : ℝ) ^ 3 := by positivity
  rw [e1]
  linarith

end RandomInvolutions.Dev.PartA2
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartA2
variable {r : ℕ}
/-- The tail bound: if the first-order coefficient is `A + ∑ κᵢ Bᵢ`, the quadratic part of the
second-order coefficient is `∑ κᵢ κⱼ C₂ᵢⱼ`, and the moments of `a`, `A`, `Bᵢ`, `C₂ᵢⱼ` grow at most
like `(ρ + δ)^p`, then the mass outside `(-ρ-ε, ρ+ε)` is `O(lam κ / N² + lam κ³ / N³)`, uniformly
in `κ`. -/
theorem tail_le_of_second_order_rational_moments (K : ℝ) (hK : 0 < K) (r : ℕ) (E : (Fin r → ℕ) → ℕ → (ℝ → ℝ) → ℝ)
    (hadd : ∀ κ N f g, E κ N (f + g) = E κ N f + E κ N g)
    (hsmul : ∀ κ N (a : ℝ) f, E κ N (a • f) = a * E κ N f)
    (hmono : ∀ κ N f g, (∀ x ∈ Set.Icc (-K) K, f x ≤ g x) → E κ N f ≤ E κ N g)
    (hone : ∀ κ N, E κ N (fun _ => 1) ≤ 1)
    (hrat : ∃ C : ℕ, 1 ≤ C ∧ ∀ q : ℕ, 1 ≤ q → ∃ gq : ℝ[X], gq.natDegree ≤ C * q ∧
      (∀ x ∈ Set.Icc (0 : ℝ) (1 / ((C : ℝ) * (q : ℝ) ^ 2)), 1 / 2 ≤ gq.eval x ∧ gq.eval x ≤ 1) ∧
      ∀ h : ℝ[X], h.natDegree ≤ q → ∀ κ : Fin r → ℕ, ∃ f : ℝ[X], f.natDegree ≤ C * q ∧
        ∀ N : ℕ, AdmK N κ → C * q ≤ N →
          E κ N (fun x => h.eval x) = f.eval (1 / (N : ℝ)) / gq.eval (1 / (N : ℝ)))
    (ρ : ℝ) (hρ : 0 ≤ ρ) (a A : ℕ → ℝ) (B : Fin r → ℕ → ℝ) (C2 : Fin r → Fin r → ℕ → ℝ)
    (hexp : ∃ (C0 : ℕ → ℝ) (C1 : Fin r → ℕ → ℝ), ∀ (κ : Fin r → ℕ) (p : ℕ),
      Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * (E κ N (fun x => x ^ p) - a p -
          (A p + ∑ i, (κ i : ℝ) * B i p) / N)) (admF κ)
        (𝓝 (C0 p + ∑ i, (κ i : ℝ) * C1 i p + ∑ i, ∑ j, (κ i : ℝ) * κ j * C2 i j p)))
    (hagrow : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ p : ℕ, |a p| ≤ C * (ρ + δ) ^ p)
    (hAgrow : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ p : ℕ, |A p| ≤ C * (ρ + δ) ^ p)
    (hBgrow : ∀ i, ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ p : ℕ, |B i p| ≤ C * (ρ + δ) ^ p)
    (hC2grow : ∀ i j, ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ p : ℕ, |C2 i j p| ≤ C * (ρ + δ) ^ p)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ (κ : Fin r → ℕ) (N : ℕ), AdmK N κ → 1 ≤ N →
      E κ N (fun x => if ρ + ε ≤ |x| then 1 else 0) ≤
        C * lam κ / (N : ℝ) ^ 2 + C * lam κ ^ 3 / (N : ℝ) ^ 3 := by
  obtain ⟨C, hC⟩ := tail_core K hK r E hadd hsmul hmono hone hrat ρ hρ a A B C2 hexp hagrow hAgrow
    hBgrow hC2grow ε hε
  refine ⟨C, fun κ N hA hN => hC κ N hA hN _ (fun x => ?_) (fun x hx => ?_)⟩
  · split_ifs <;> norm_num
  · rw [if_neg (not_le.2 hx)]

end RandomInvolutions.Dev.PartA2
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
alias tail_le_of_second_order_rational_moments := RandomInvolutions.Dev.PartA2.tail_le_of_second_order_rational_moments

end RandomInvolutions.Dev
end
end

section
open Finset BordenaveCollins
noncomputable section
namespace RandomInvolutions.Dev.PartF
variable {r s : ℕ}
/-!
# Part F, toolkit: normal forms in `F_r * Γ_s` (van der Waerden's trick) and reduced words

Stated for `G r s`, `Lt r s` with the `RandomInvolutions.Dev` versions of `bar`, `Red`, `CycRed`; Part F uses it at
`G 0 r`.
-/
/-! ## Group lemmas for `G r s`

(`rw`/`simp` with the generic group lemmas fail on `G r s` because of an instance diamond in
`Monoid.Coprod (…) (Gam s)`; these restatements are syntactically in the form of the Blueprint.) -/
theorem g_mul_inv_cancel (a : G r s) : a * a⁻¹ = 1 := mul_inv_cancel a

theorem g_inv_mul_cancel (a : G r s) : a⁻¹ * a = 1 := inv_mul_cancel a

theorem g_inv_inv (a : G r s) : a⁻¹⁻¹ = a := inv_inv a

theorem g_inv_eq_of_mul_eq_one_right {a b : G r s} (h : a * b = 1) : a⁻¹ = b := by
  have h2 : a⁻¹ * (a * b) = a⁻¹ := by rw [h, mul_one]
  rw [← mul_assoc, g_inv_mul_cancel, one_mul] at h2
  exact h2.symm

theorem g_map_inv {H : Type*} [Group H] (f : G r s →* H) (a : G r s) : f a⁻¹ = (f a)⁻¹ :=
  map_inv f a

/-! ## Letters -/
@[simp] theorem bar_bar (a : Lt r s) : bar (bar a) = a := by
  rcases a with ⟨i, b⟩ | j <;> simp [bar]

theorem genL_bar (a : Lt r s) : genL (bar a) = (genL a)⁻¹ := by
  rcases a with ⟨i, b⟩ | j
  · cases b
    · exact (g_inv_inv _).symm
    · rfl
  · simp only [bar, genL]
    refine (g_inv_eq_of_mul_eq_one_right ?_).symm
    rw [← map_mul, DerandSq.mGen_mul_self, map_one]

theorem genL_mul_genL_bar (a : Lt r s) : genL a * genL (bar a) = 1 := by
  rw [genL_bar, g_mul_inv_cancel]

/-! ## Word products -/
@[simp] theorem wprod_nil : wprod ([] : List (Lt r s)) = 1 := rfl

@[simp] theorem wprod_cons (a : Lt r s) (u : List (Lt r s)) :
    wprod (a :: u) = genL a * wprod u := by
  simp [wprod]

@[simp] theorem wprod_append (u v : List (Lt r s)) : wprod (u ++ v) = wprod u * wprod v := by
  simp [wprod]

/-! ## The push action on reduced words -/
/-- Cancel the head if it is the inverse letter, otherwise push. -/
def push (a : Lt r s) : List (Lt r s) → List (Lt r s)
  | [] => [a]
  | b :: t => if b = bar a then t else a :: b :: t

@[simp] theorem push_nil (a : Lt r s) : push a [] = [a] := rfl

theorem push_cons_bar (a : Lt r s) (t : List (Lt r s)) : push a (bar a :: t) = t := by
  simp [push]

theorem push_cons_ne (a b : Lt r s) (t : List (Lt r s)) (h : b ≠ bar a) :
    push a (b :: t) = a :: b :: t := by
  simp [push, h]

theorem red_nil : Red ([] : List (Lt r s)) := List.isChain_nil

theorem red_cons_cons {a b : Lt r s} {t : List (Lt r s)} :
    Red (a :: b :: t) ↔ b ≠ bar a ∧ Red (b :: t) := List.isChain_cons_cons

theorem Red.tail' {a : Lt r s} {t : List (Lt r s)} (h : Red (a :: t)) : Red t :=
  List.IsChain.tail h

theorem red_push (a : Lt r s) (u : List (Lt r s)) (h : Red u) : Red (push a u) := by
  cases u with
  | nil => exact List.isChain_singleton _
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb; rw [push_cons_bar]; exact Red.tail' h
    · rw [push_cons_ne _ _ _ hb]; exact red_cons_cons.2 ⟨hb, h⟩

theorem push_bar_push (a : Lt r s) (u : List (Lt r s)) (h : Red u) :
    push (bar a) (push a u) = u := by
  cases u with
  | nil => simp [push]
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb
      rw [push_cons_bar]
      cases t with
      | nil => rfl
      | cons c t =>
        have hc : c ≠ bar (bar a) := (red_cons_cons.1 h).1
        rw [push_cons_ne _ _ _ hc]
    · rw [push_cons_ne _ _ _ hb]
      simp [push]

theorem push_push_bar (a : Lt r s) (u : List (Lt r s)) (h : Red u) :
    push a (push (bar a) u) = u := by
  simpa using push_bar_push (bar a) u h

theorem length_push_le (a : Lt r s) (u : List (Lt r s)) :
    (push a u).length ≤ u.length + 1 := by
  cases u with
  | nil => simp
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb; rw [push_cons_bar]; simp; omega
    · rw [push_cons_ne _ _ _ hb]; simp

theorem wprod_push (a : Lt r s) (u : List (Lt r s)) : wprod (push a u) = genL a * wprod u := by
  cases u with
  | nil => simp
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb
      rw [push_cons_bar, wprod_cons, ← mul_assoc, genL_mul_genL_bar, one_mul]
    · rw [push_cons_ne _ _ _ hb]; simp

/-- Reduced words. -/
abbrev RL (r s : ℕ) := {u : List (Lt r s) // Red u}

/-- The permutation of reduced words given by a letter. -/
def pushP (a : Lt r s) : Equiv.Perm (RL r s) where
  toFun u := ⟨push a u.1, red_push a u.1 u.2⟩
  invFun u := ⟨push (bar a) u.1, red_push (bar a) u.1 u.2⟩
  left_inv u := Subtype.ext (push_bar_push a u.1 u.2)
  right_inv u := Subtype.ext (push_push_bar a u.1 u.2)

@[simp] theorem pushP_apply (a : Lt r s) (u : RL r s) : (pushP a u).1 = push a u.1 := rfl

theorem pushP_inv (a : Lt r s) : (pushP a)⁻¹ = pushP (bar a) := by
  ext u : 2
  rfl

theorem pushP_inr_sq (j : Fin s) :
    pushP (Sum.inr j : Lt r s) * pushP (Sum.inr j : Lt r s) = 1 := by
  have h := pushP_inv (Sum.inr j : Lt r s)
  have hb : bar (Sum.inr j : Lt r s) = Sum.inr j := rfl
  rw [hb] at h
  nth_rewrite 1 [← h]
  exact inv_mul_cancel _

/-- The homomorphism `Z₂ → Perm α` of an involution. -/
def invHomP {α : Type*} (σ : Equiv.Perm α) (hσ : σ * σ = 1) :
    Multiplicative (ZMod 2) →* Equiv.Perm α where
  toFun a := σ ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    have key : ∀ a b : ZMod 2, σ ^ (a + b).val = σ ^ a.val * σ ^ b.val := by
      intro a b
      fin_cases a <;> fin_cases b
      · show σ ^ (0 : ZMod 2).val = σ ^ (0 : ZMod 2).val * σ ^ (0 : ZMod 2).val
        simp
      · show σ ^ (1 : ZMod 2).val = σ ^ (0 : ZMod 2).val * σ ^ (1 : ZMod 2).val
        simp
      · show σ ^ (1 : ZMod 2).val = σ ^ (1 : ZMod 2).val * σ ^ (0 : ZMod 2).val
        simp
      · show σ ^ ((1 : ZMod 2) + 1).val = σ ^ (1 : ZMod 2).val * σ ^ (1 : ZMod 2).val
        have h11 : ((1 : ZMod 2) + 1) = 0 := by decide
        rw [h11]; simp [ZMod.val_one, hσ]
    exact key _ _

theorem invHomP_gen {α : Type*} (σ : Equiv.Perm α) (hσ : σ * σ = 1) :
    invHomP σ hσ (Multiplicative.ofAdd (1 : ZMod 2)) = σ := by
  show σ ^ (1 : ZMod 2).val = σ
  simp [ZMod.val_one]

/-- The action of `G r s` on reduced words. -/
def hom (r s : ℕ) : G r s →* Equiv.Perm (RL r s) :=
  Monoid.Coprod.lift (FreeGroup.lift fun i => pushP (Sum.inl (i, true)))
    (Monoid.CoprodI.lift fun j => invHomP (pushP (Sum.inr j)) (pushP_inr_sq j))

theorem hom_genL (a : Lt r s) : hom r s (genL a) = pushP a := by
  rcases a with ⟨i, b⟩ | j
  · cases b
    · have : hom r s (genL (Sum.inl (i, true))) = pushP (Sum.inl (i, true)) := by
        simp [hom, genL]
      show hom r s (genL (Sum.inl (i, true)))⁻¹ = _
      rw [g_map_inv, this, pushP_inv]; rfl
    · simp [hom, genL]
  · simp only [hom, genL, Monoid.Coprod.lift_apply_inr, DerandSq.mGen]
    rw [Monoid.CoprodI.lift_of]
    exact invHomP_gen _ _

/-- The normal form: the reduced word of `g`. -/
def nf (g : G r s) : List (Lt r s) := (hom r s g ⟨[], red_nil⟩).1

@[simp] theorem nf_one : nf (1 : G r s) = [] := by simp [nf]

theorem hom_genL_mul (a : Lt r s) (g : G r s) (v : RL r s) :
    (hom r s (genL a * g) v).1 = push a (hom r s g v).1 := by
  rw [map_mul, hom_genL]; rfl

theorem wprod_hom (g : G r s) : ∀ v : RL r s, wprod (hom r s g v).1 = g * wprod v.1 := by
  have hone : ∀ v : RL r s, wprod (hom r s 1 v).1 = 1 * wprod v.1 := by intro v; simp
  have hmul : ∀ x y : G r s, (∀ v : RL r s, wprod (hom r s x v).1 = x * wprod v.1) →
      (∀ v : RL r s, wprod (hom r s y v).1 = y * wprod v.1) →
      ∀ v : RL r s, wprod (hom r s (x * y) v).1 = x * y * wprod v.1 := by
    intro x y hx hy v
    rw [map_mul, Equiv.Perm.mul_apply, hx, hy, mul_assoc]
  have hgen : ∀ (a : Lt r s) (v : RL r s),
      wprod (hom r s (genL a) v).1 = genL a * wprod v.1 := by
    intro a v
    rw [hom_genL, pushP_apply, wprod_push]
  induction g using Monoid.Coprod.induction_on with
  | inl x =>
    induction x using FreeGroup.induction_on with
    | C1 => simp
    | of i => exact hgen (Sum.inl (i, true))
    | inv_of i _ => exact hgen (Sum.inl (i, false))
    | mul x y hx hy => rw [map_mul]; exact hmul _ _ hx hy
  | inr y =>
    induction y using Monoid.CoprodI.induction_on with
    | one => simp
    | of j m =>
      have hm : ∀ z : Multiplicative (ZMod 2), z = 1 ∨ z = Multiplicative.ofAdd 1 := by decide
      rcases hm m with rfl | rfl
      · simp
      · exact hgen (Sum.inr j)
    | mul x y hx hy => rw [map_mul]; exact hmul _ _ hx hy
  | mul x y hx hy => exact hmul x y hx hy

theorem wprod_nf (g : G r s) : wprod (nf g) = g := by
  have := wprod_hom g ⟨[], red_nil⟩
  simpa [nf] using this

theorem length_hom_wprod_le (u : List (Lt r s)) (v : RL r s) :
    (hom r s (wprod u) v).1.length ≤ u.length + v.1.length := by
  induction u with
  | nil => simp
  | cons a t ih =>
    rw [wprod_cons, hom_genL_mul]
    have := length_push_le a (hom r s (wprod t) v).1
    simp only [List.length_cons]
    omega

theorem length_nf_wprod_le (u : List (Lt r s)) : (nf (wprod u)).length ≤ u.length := by
  have := length_hom_wprod_le u ⟨[], red_nil⟩
  simp only [List.length_nil, add_zero] at this
  exact this

/-- Any word for `g` bounds `len g`. -/
theorem len_le_of_wprod {u : List (Lt r s)} {g : G r s} (h : wprod u = g) : len g ≤ u.length :=
  Nat.sInf_le ⟨u, rfl, h⟩

theorem len_eq_length_nf (g : G r s) : len g = (nf g).length := by
  apply le_antisymm (len_le_of_wprod (wprod_nf g))
  have hne : {n | ∃ u : List (Lt r s), u.length = n ∧ wprod u = g}.Nonempty :=
    ⟨_, nf g, rfl, wprod_nf g⟩
  obtain ⟨u, hu, hg⟩ := Nat.sInf_mem hne
  show _ ≤ len g
  unfold len
  rw [← hu, ← hg]
  exact length_nf_wprod_le u

@[simp] theorem len_one : len (1 : G r s) = 0 := by rw [len_eq_length_nf, nf_one]; rfl

/-! ## Aliases -/

/-! ## Generic group identities

(`simp`, `rw` and `group` do not see through the instance path of `G r s`, so identities are
proved in a generic group and applied with `exact`.) -/

/-! ## The inverse word -/
/-- The inverse word: reversed, with `bar` applied. -/
def ibar (u : List (Lt r s)) : List (Lt r s) := (u.map bar).reverse

end RandomInvolutions.Dev.PartF
end
end

section
open Finset BordenaveCollins
noncomputable section
namespace RandomInvolutions.Dev.PartF
variable {r s : ℕ}
@[simp] theorem ibar_nil : ibar ([] : List (Lt r s)) = [] := rfl

end RandomInvolutions.Dev.PartF
end
end

section
open Finset BordenaveCollins
noncomputable section
namespace RandomInvolutions.Dev.PartF
variable {r s : ℕ}
@[simp] theorem length_ibar (u : List (Lt r s)) : (ibar u).length = u.length := by simp [ibar]

end RandomInvolutions.Dev.PartF
end
end

section
open Finset BordenaveCollins
noncomputable section
namespace RandomInvolutions.Dev.PartF
variable {r s : ℕ}
/-! ## Repeated words -/
/-- `Z` repeated `k` times. -/
def rep (Z : List (Lt r s)) (k : ℕ) : List (Lt r s) := (List.replicate k Z).flatten

@[simp] theorem rep_zero (Z : List (Lt r s)) : rep Z 0 = [] := by simp [rep]

theorem rep_succ (Z : List (Lt r s)) (k : ℕ) : rep Z (k + 1) = Z ++ rep Z k := by
  simp [rep, List.replicate_succ]

@[simp] theorem rep_nil (k : ℕ) : rep ([] : List (Lt r s)) k = [] := by simp [rep]

@[simp] theorem length_rep (Z : List (Lt r s)) (k : ℕ) : (rep Z k).length = k * Z.length := by
  induction k with
  | zero => simp
  | succ k ih => rw [rep_succ, List.length_append, ih]; ring

end RandomInvolutions.Dev.PartF
end
end

section
open Finset
noncomputable section
namespace RandomInvolutions.Dev.PartP3a.F1
open BordenaveCollins RandomInvolutions RandomInvolutions.Dev
variable {r s : ℕ}
/-!
# Part P3a, module 0: normal forms in `F_r * Γ_s` (van der Waerden's trick)

Copy of bc214's Part F1 (general `G r s`), so that the first-passage modules below do not depend
on the Part F stubs.
-/
/-! ## Group lemmas for `G r s`

(`rw`/`simp` with the generic group lemmas fail on `G r s` because of an instance diamond in
`Monoid.Coprod (…) (Gam s)`; these restatements are syntactically in the form of the Blueprint.) -/
theorem g_mul_inv_cancel (a : G r s) : a * a⁻¹ = 1 := mul_inv_cancel a

theorem g_inv_mul_cancel (a : G r s) : a⁻¹ * a = 1 := inv_mul_cancel a

theorem g_inv_inv (a : G r s) : a⁻¹⁻¹ = a := inv_inv a

theorem g_inv_eq_of_mul_eq_one_right {a b : G r s} (h : a * b = 1) : a⁻¹ = b := by
  have h2 : a⁻¹ * (a * b) = a⁻¹ := by rw [h, mul_one]
  rw [← mul_assoc, g_inv_mul_cancel, one_mul] at h2
  exact h2.symm

theorem g_map_inv {H : Type*} [Group H] (f : G r s →* H) (a : G r s) : f a⁻¹ = (f a)⁻¹ :=
  map_inv f a

/-! ## Letters -/
@[simp] theorem bar_bar (a : Lt r s) : bar (bar a) = a := by
  rcases a with ⟨i, b⟩ | j <;> simp [bar]

theorem genL_bar (a : Lt r s) : genL (bar a) = (genL a)⁻¹ := by
  rcases a with ⟨i, b⟩ | j
  · cases b
    · exact (g_inv_inv _).symm
    · rfl
  · simp only [bar, genL]
    refine (g_inv_eq_of_mul_eq_one_right ?_).symm
    rw [← map_mul, DerandSq.mGen_mul_self, map_one]

theorem genL_mul_genL_bar (a : Lt r s) : genL a * genL (bar a) = 1 := by
  rw [genL_bar, g_mul_inv_cancel]

/-! ## Word products -/
@[simp] theorem wprod_nil : wprod ([] : List (Lt r s)) = 1 := rfl

@[simp] theorem wprod_cons (a : Lt r s) (u : List (Lt r s)) :
    wprod (a :: u) = genL a * wprod u := by
  simp [wprod]

@[simp] theorem wprod_append (u v : List (Lt r s)) : wprod (u ++ v) = wprod u * wprod v := by
  simp [wprod]

/-! ## The push action on reduced words -/
/-- Cancel the head if it is the inverse letter, otherwise push. -/
def push (a : Lt r s) : List (Lt r s) → List (Lt r s)
  | [] => [a]
  | b :: t => if b = bar a then t else a :: b :: t

@[simp] theorem push_nil (a : Lt r s) : push a [] = [a] := rfl

theorem push_cons_bar (a : Lt r s) (t : List (Lt r s)) : push a (bar a :: t) = t := by
  simp [push]

theorem push_cons_ne (a b : Lt r s) (t : List (Lt r s)) (h : b ≠ bar a) :
    push a (b :: t) = a :: b :: t := by
  simp [push, h]

theorem red_nil : Red ([] : List (Lt r s)) := List.isChain_nil

theorem red_cons_cons {a b : Lt r s} {t : List (Lt r s)} :
    Red (a :: b :: t) ↔ b ≠ bar a ∧ Red (b :: t) := List.isChain_cons_cons

theorem Red.tail' {a : Lt r s} {t : List (Lt r s)} (h : Red (a :: t)) : Red t :=
  List.IsChain.tail h

theorem red_push (a : Lt r s) (u : List (Lt r s)) (h : Red u) : Red (push a u) := by
  cases u with
  | nil => exact List.isChain_singleton _
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb; rw [push_cons_bar]; exact Red.tail' h
    · rw [push_cons_ne _ _ _ hb]; exact red_cons_cons.2 ⟨hb, h⟩

theorem push_bar_push (a : Lt r s) (u : List (Lt r s)) (h : Red u) :
    push (bar a) (push a u) = u := by
  cases u with
  | nil => simp [push]
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb
      rw [push_cons_bar]
      cases t with
      | nil => rfl
      | cons c t =>
        have hc : c ≠ bar (bar a) := (red_cons_cons.1 h).1
        rw [push_cons_ne _ _ _ hc]
    · rw [push_cons_ne _ _ _ hb]
      simp [push]

theorem push_push_bar (a : Lt r s) (u : List (Lt r s)) (h : Red u) :
    push a (push (bar a) u) = u := by
  simpa using push_bar_push (bar a) u h

theorem length_push_le (a : Lt r s) (u : List (Lt r s)) :
    (push a u).length ≤ u.length + 1 := by
  cases u with
  | nil => simp
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb; rw [push_cons_bar]; simp; omega
    · rw [push_cons_ne _ _ _ hb]; simp

theorem wprod_push (a : Lt r s) (u : List (Lt r s)) : wprod (push a u) = genL a * wprod u := by
  cases u with
  | nil => simp
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb
      rw [push_cons_bar, wprod_cons, ← mul_assoc, genL_mul_genL_bar, one_mul]
    · rw [push_cons_ne _ _ _ hb]; simp

/-- Reduced words. -/
abbrev RL (r s : ℕ) := {u : List (Lt r s) // Red u}

/-- The permutation of reduced words given by a letter. -/
def pushP (a : Lt r s) : Equiv.Perm (RL r s) where
  toFun u := ⟨push a u.1, red_push a u.1 u.2⟩
  invFun u := ⟨push (bar a) u.1, red_push (bar a) u.1 u.2⟩
  left_inv u := Subtype.ext (push_bar_push a u.1 u.2)
  right_inv u := Subtype.ext (push_push_bar a u.1 u.2)

@[simp] theorem pushP_apply (a : Lt r s) (u : RL r s) : (pushP a u).1 = push a u.1 := rfl

theorem pushP_inv (a : Lt r s) : (pushP a)⁻¹ = pushP (bar a) := by
  ext u : 2
  rfl

theorem pushP_inr_sq (j : Fin s) :
    pushP (Sum.inr j : Lt r s) * pushP (Sum.inr j : Lt r s) = 1 := by
  have h := pushP_inv (Sum.inr j : Lt r s)
  have hb : bar (Sum.inr j : Lt r s) = Sum.inr j := rfl
  rw [hb] at h
  nth_rewrite 1 [← h]
  exact inv_mul_cancel _

/-- The homomorphism `Z₂ → Perm α` of an involution. -/
def invHomP {α : Type*} (σ : Equiv.Perm α) (hσ : σ * σ = 1) :
    Multiplicative (ZMod 2) →* Equiv.Perm α where
  toFun a := σ ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    have key : ∀ a b : ZMod 2, σ ^ (a + b).val = σ ^ a.val * σ ^ b.val := by
      intro a b
      fin_cases a <;> fin_cases b
      · show σ ^ (0 : ZMod 2).val = σ ^ (0 : ZMod 2).val * σ ^ (0 : ZMod 2).val
        simp
      · show σ ^ (1 : ZMod 2).val = σ ^ (0 : ZMod 2).val * σ ^ (1 : ZMod 2).val
        simp
      · show σ ^ (1 : ZMod 2).val = σ ^ (1 : ZMod 2).val * σ ^ (0 : ZMod 2).val
        simp
      · show σ ^ ((1 : ZMod 2) + 1).val = σ ^ (1 : ZMod 2).val * σ ^ (1 : ZMod 2).val
        have h11 : ((1 : ZMod 2) + 1) = 0 := by decide
        rw [h11]; simp [ZMod.val_one, hσ]
    exact key _ _

theorem invHomP_gen {α : Type*} (σ : Equiv.Perm α) (hσ : σ * σ = 1) :
    invHomP σ hσ (Multiplicative.ofAdd (1 : ZMod 2)) = σ := by
  show σ ^ (1 : ZMod 2).val = σ
  simp [ZMod.val_one]

/-- The action of `G r s` on reduced words. -/
def hom (r s : ℕ) : G r s →* Equiv.Perm (RL r s) :=
  Monoid.Coprod.lift (FreeGroup.lift fun i => pushP (Sum.inl (i, true)))
    (Monoid.CoprodI.lift fun j => invHomP (pushP (Sum.inr j)) (pushP_inr_sq j))

theorem hom_genL (a : Lt r s) : hom r s (genL a) = pushP a := by
  rcases a with ⟨i, b⟩ | j
  · cases b
    · have : hom r s (genL (Sum.inl (i, true))) = pushP (Sum.inl (i, true)) := by
        simp [hom, genL]
      show hom r s (genL (Sum.inl (i, true)))⁻¹ = _
      rw [g_map_inv, this, pushP_inv]; rfl
    · simp [hom, genL]
  · simp only [hom, genL, Monoid.Coprod.lift_apply_inr, DerandSq.mGen]
    rw [Monoid.CoprodI.lift_of]
    exact invHomP_gen _ _

/-- The normal form: the reduced word of `g`. -/
def nf (g : G r s) : List (Lt r s) := (hom r s g ⟨[], red_nil⟩).1

@[simp] theorem nf_one : nf (1 : G r s) = [] := by simp [nf]

theorem hom_genL_mul (a : Lt r s) (g : G r s) (v : RL r s) :
    (hom r s (genL a * g) v).1 = push a (hom r s g v).1 := by
  rw [map_mul, hom_genL]; rfl

theorem wprod_hom (g : G r s) : ∀ v : RL r s, wprod (hom r s g v).1 = g * wprod v.1 := by
  have hone : ∀ v : RL r s, wprod (hom r s 1 v).1 = 1 * wprod v.1 := by intro v; simp
  have hmul : ∀ x y : G r s, (∀ v : RL r s, wprod (hom r s x v).1 = x * wprod v.1) →
      (∀ v : RL r s, wprod (hom r s y v).1 = y * wprod v.1) →
      ∀ v : RL r s, wprod (hom r s (x * y) v).1 = x * y * wprod v.1 := by
    intro x y hx hy v
    rw [map_mul, Equiv.Perm.mul_apply, hx, hy, mul_assoc]
  have hgen : ∀ (a : Lt r s) (v : RL r s),
      wprod (hom r s (genL a) v).1 = genL a * wprod v.1 := by
    intro a v
    rw [hom_genL, pushP_apply, wprod_push]
  induction g using Monoid.Coprod.induction_on with
  | inl x =>
    induction x using FreeGroup.induction_on with
    | C1 => simp
    | of i => exact hgen (Sum.inl (i, true))
    | inv_of i _ => exact hgen (Sum.inl (i, false))
    | mul x y hx hy => rw [map_mul]; exact hmul _ _ hx hy
  | inr y =>
    induction y using Monoid.CoprodI.induction_on with
    | one => simp
    | of j m =>
      have hm : ∀ z : Multiplicative (ZMod 2), z = 1 ∨ z = Multiplicative.ofAdd 1 := by decide
      rcases hm m with rfl | rfl
      · simp
      · exact hgen (Sum.inr j)
    | mul x y hx hy => rw [map_mul]; exact hmul _ _ hx hy
  | mul x y hx hy => exact hmul x y hx hy

theorem wprod_nf (g : G r s) : wprod (nf g) = g := by
  have := wprod_hom g ⟨[], red_nil⟩
  simpa [nf] using this

theorem length_hom_wprod_le (u : List (Lt r s)) (v : RL r s) :
    (hom r s (wprod u) v).1.length ≤ u.length + v.1.length := by
  induction u with
  | nil => simp
  | cons a t ih =>
    rw [wprod_cons, hom_genL_mul]
    have := length_push_le a (hom r s (wprod t) v).1
    simp only [List.length_cons]
    omega

theorem length_nf_wprod_le (u : List (Lt r s)) : (nf (wprod u)).length ≤ u.length := by
  have := length_hom_wprod_le u ⟨[], red_nil⟩
  simp only [List.length_nil, add_zero] at this
  exact this

/-- Any word for `g` bounds `len g`. -/
theorem len_le_of_wprod {u : List (Lt r s)} {g : G r s} (h : wprod u = g) : len g ≤ u.length :=
  Nat.sInf_le ⟨u, rfl, h⟩

theorem len_eq_length_nf (g : G r s) : len g = (nf g).length := by
  apply le_antisymm (len_le_of_wprod (wprod_nf g))
  have hne : {n | ∃ u : List (Lt r s), u.length = n ∧ wprod u = g}.Nonempty :=
    ⟨_, nf g, rfl, wprod_nf g⟩
  obtain ⟨u, hu, hg⟩ := Nat.sInf_mem hne
  show _ ≤ len g
  unfold len
  rw [← hu, ← hg]
  exact length_nf_wprod_le u

@[simp] theorem len_one : len (1 : G r s) = 0 := by rw [len_eq_length_nf, nf_one]; rfl

/-! ## The stubs -/

end RandomInvolutions.Dev.PartP3a.F1
end
end

section
open Finset
noncomputable section
namespace RandomInvolutions.Dev.PartP3b.F1
open BordenaveCollins RandomInvolutions RandomInvolutions.Dev
variable {r s : ℕ}
/-!
# Part P3a, module 0: normal forms in `F_r * Γ_s` (van der Waerden's trick)

Copy of bc214's Part F1 (general `G r s`), so that the first-passage modules below do not depend
on the Part F stubs.
-/
/-! ## Group lemmas for `G r s`

(`rw`/`simp` with the generic group lemmas fail on `G r s` because of an instance diamond in
`Monoid.Coprod (…) (Gam s)`; these restatements are syntactically in the form of the Blueprint.) -/
theorem g_mul_inv_cancel (a : G r s) : a * a⁻¹ = 1 := mul_inv_cancel a

theorem g_inv_mul_cancel (a : G r s) : a⁻¹ * a = 1 := inv_mul_cancel a

theorem g_inv_inv (a : G r s) : a⁻¹⁻¹ = a := inv_inv a

theorem g_inv_eq_of_mul_eq_one_right {a b : G r s} (h : a * b = 1) : a⁻¹ = b := by
  have h2 : a⁻¹ * (a * b) = a⁻¹ := by rw [h, mul_one]
  rw [← mul_assoc, g_inv_mul_cancel, one_mul] at h2
  exact h2.symm

theorem g_map_inv {H : Type*} [Group H] (f : G r s →* H) (a : G r s) : f a⁻¹ = (f a)⁻¹ :=
  map_inv f a

/-! ## Letters -/
@[simp] theorem bar_bar (a : Lt r s) : bar (bar a) = a := by
  rcases a with ⟨i, b⟩ | j <;> simp [bar]

theorem genL_bar (a : Lt r s) : genL (bar a) = (genL a)⁻¹ := by
  rcases a with ⟨i, b⟩ | j
  · cases b
    · exact (g_inv_inv _).symm
    · rfl
  · simp only [bar, genL]
    refine (g_inv_eq_of_mul_eq_one_right ?_).symm
    rw [← map_mul, DerandSq.mGen_mul_self, map_one]

theorem genL_mul_genL_bar (a : Lt r s) : genL a * genL (bar a) = 1 := by
  rw [genL_bar, g_mul_inv_cancel]

/-! ## Word products -/
@[simp] theorem wprod_nil : wprod ([] : List (Lt r s)) = 1 := rfl

@[simp] theorem wprod_cons (a : Lt r s) (u : List (Lt r s)) :
    wprod (a :: u) = genL a * wprod u := by
  simp [wprod]

@[simp] theorem wprod_append (u v : List (Lt r s)) : wprod (u ++ v) = wprod u * wprod v := by
  simp [wprod]

/-! ## The push action on reduced words -/
/-- Cancel the head if it is the inverse letter, otherwise push. -/
def push (a : Lt r s) : List (Lt r s) → List (Lt r s)
  | [] => [a]
  | b :: t => if b = bar a then t else a :: b :: t

@[simp] theorem push_nil (a : Lt r s) : push a [] = [a] := rfl

theorem push_cons_bar (a : Lt r s) (t : List (Lt r s)) : push a (bar a :: t) = t := by
  simp [push]

theorem push_cons_ne (a b : Lt r s) (t : List (Lt r s)) (h : b ≠ bar a) :
    push a (b :: t) = a :: b :: t := by
  simp [push, h]

theorem red_nil : Red ([] : List (Lt r s)) := List.isChain_nil

theorem red_cons_cons {a b : Lt r s} {t : List (Lt r s)} :
    Red (a :: b :: t) ↔ b ≠ bar a ∧ Red (b :: t) := List.isChain_cons_cons

theorem Red.tail' {a : Lt r s} {t : List (Lt r s)} (h : Red (a :: t)) : Red t :=
  List.IsChain.tail h

theorem red_push (a : Lt r s) (u : List (Lt r s)) (h : Red u) : Red (push a u) := by
  cases u with
  | nil => exact List.isChain_singleton _
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb; rw [push_cons_bar]; exact Red.tail' h
    · rw [push_cons_ne _ _ _ hb]; exact red_cons_cons.2 ⟨hb, h⟩

theorem push_bar_push (a : Lt r s) (u : List (Lt r s)) (h : Red u) :
    push (bar a) (push a u) = u := by
  cases u with
  | nil => simp [push]
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb
      rw [push_cons_bar]
      cases t with
      | nil => rfl
      | cons c t =>
        have hc : c ≠ bar (bar a) := (red_cons_cons.1 h).1
        rw [push_cons_ne _ _ _ hc]
    · rw [push_cons_ne _ _ _ hb]
      simp [push]

theorem push_push_bar (a : Lt r s) (u : List (Lt r s)) (h : Red u) :
    push a (push (bar a) u) = u := by
  simpa using push_bar_push (bar a) u h

theorem length_push_le (a : Lt r s) (u : List (Lt r s)) :
    (push a u).length ≤ u.length + 1 := by
  cases u with
  | nil => simp
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb; rw [push_cons_bar]; simp; omega
    · rw [push_cons_ne _ _ _ hb]; simp

theorem wprod_push (a : Lt r s) (u : List (Lt r s)) : wprod (push a u) = genL a * wprod u := by
  cases u with
  | nil => simp
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb
      rw [push_cons_bar, wprod_cons, ← mul_assoc, genL_mul_genL_bar, one_mul]
    · rw [push_cons_ne _ _ _ hb]; simp

/-- Reduced words. -/
abbrev RL (r s : ℕ) := {u : List (Lt r s) // Red u}

/-- The permutation of reduced words given by a letter. -/
def pushP (a : Lt r s) : Equiv.Perm (RL r s) where
  toFun u := ⟨push a u.1, red_push a u.1 u.2⟩
  invFun u := ⟨push (bar a) u.1, red_push (bar a) u.1 u.2⟩
  left_inv u := Subtype.ext (push_bar_push a u.1 u.2)
  right_inv u := Subtype.ext (push_push_bar a u.1 u.2)

@[simp] theorem pushP_apply (a : Lt r s) (u : RL r s) : (pushP a u).1 = push a u.1 := rfl

theorem pushP_inv (a : Lt r s) : (pushP a)⁻¹ = pushP (bar a) := by
  ext u : 2
  rfl

theorem pushP_inr_sq (j : Fin s) :
    pushP (Sum.inr j : Lt r s) * pushP (Sum.inr j : Lt r s) = 1 := by
  have h := pushP_inv (Sum.inr j : Lt r s)
  have hb : bar (Sum.inr j : Lt r s) = Sum.inr j := rfl
  rw [hb] at h
  nth_rewrite 1 [← h]
  exact inv_mul_cancel _

/-- The homomorphism `Z₂ → Perm α` of an involution. -/
def invHomP {α : Type*} (σ : Equiv.Perm α) (hσ : σ * σ = 1) :
    Multiplicative (ZMod 2) →* Equiv.Perm α where
  toFun a := σ ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    have key : ∀ a b : ZMod 2, σ ^ (a + b).val = σ ^ a.val * σ ^ b.val := by
      intro a b
      fin_cases a <;> fin_cases b
      · show σ ^ (0 : ZMod 2).val = σ ^ (0 : ZMod 2).val * σ ^ (0 : ZMod 2).val
        simp
      · show σ ^ (1 : ZMod 2).val = σ ^ (0 : ZMod 2).val * σ ^ (1 : ZMod 2).val
        simp
      · show σ ^ (1 : ZMod 2).val = σ ^ (1 : ZMod 2).val * σ ^ (0 : ZMod 2).val
        simp
      · show σ ^ ((1 : ZMod 2) + 1).val = σ ^ (1 : ZMod 2).val * σ ^ (1 : ZMod 2).val
        have h11 : ((1 : ZMod 2) + 1) = 0 := by decide
        rw [h11]; simp [ZMod.val_one, hσ]
    exact key _ _

theorem invHomP_gen {α : Type*} (σ : Equiv.Perm α) (hσ : σ * σ = 1) :
    invHomP σ hσ (Multiplicative.ofAdd (1 : ZMod 2)) = σ := by
  show σ ^ (1 : ZMod 2).val = σ
  simp [ZMod.val_one]

/-- The action of `G r s` on reduced words. -/
def hom (r s : ℕ) : G r s →* Equiv.Perm (RL r s) :=
  Monoid.Coprod.lift (FreeGroup.lift fun i => pushP (Sum.inl (i, true)))
    (Monoid.CoprodI.lift fun j => invHomP (pushP (Sum.inr j)) (pushP_inr_sq j))

theorem hom_genL (a : Lt r s) : hom r s (genL a) = pushP a := by
  rcases a with ⟨i, b⟩ | j
  · cases b
    · have : hom r s (genL (Sum.inl (i, true))) = pushP (Sum.inl (i, true)) := by
        simp [hom, genL]
      show hom r s (genL (Sum.inl (i, true)))⁻¹ = _
      rw [g_map_inv, this, pushP_inv]; rfl
    · simp [hom, genL]
  · simp only [hom, genL, Monoid.Coprod.lift_apply_inr, DerandSq.mGen]
    rw [Monoid.CoprodI.lift_of]
    exact invHomP_gen _ _

/-- The normal form: the reduced word of `g`. -/
def nf (g : G r s) : List (Lt r s) := (hom r s g ⟨[], red_nil⟩).1

@[simp] theorem nf_one : nf (1 : G r s) = [] := by simp [nf]

theorem hom_genL_mul (a : Lt r s) (g : G r s) (v : RL r s) :
    (hom r s (genL a * g) v).1 = push a (hom r s g v).1 := by
  rw [map_mul, hom_genL]; rfl

theorem wprod_hom (g : G r s) : ∀ v : RL r s, wprod (hom r s g v).1 = g * wprod v.1 := by
  have hone : ∀ v : RL r s, wprod (hom r s 1 v).1 = 1 * wprod v.1 := by intro v; simp
  have hmul : ∀ x y : G r s, (∀ v : RL r s, wprod (hom r s x v).1 = x * wprod v.1) →
      (∀ v : RL r s, wprod (hom r s y v).1 = y * wprod v.1) →
      ∀ v : RL r s, wprod (hom r s (x * y) v).1 = x * y * wprod v.1 := by
    intro x y hx hy v
    rw [map_mul, Equiv.Perm.mul_apply, hx, hy, mul_assoc]
  have hgen : ∀ (a : Lt r s) (v : RL r s),
      wprod (hom r s (genL a) v).1 = genL a * wprod v.1 := by
    intro a v
    rw [hom_genL, pushP_apply, wprod_push]
  induction g using Monoid.Coprod.induction_on with
  | inl x =>
    induction x using FreeGroup.induction_on with
    | C1 => simp
    | of i => exact hgen (Sum.inl (i, true))
    | inv_of i _ => exact hgen (Sum.inl (i, false))
    | mul x y hx hy => rw [map_mul]; exact hmul _ _ hx hy
  | inr y =>
    induction y using Monoid.CoprodI.induction_on with
    | one => simp
    | of j m =>
      have hm : ∀ z : Multiplicative (ZMod 2), z = 1 ∨ z = Multiplicative.ofAdd 1 := by decide
      rcases hm m with rfl | rfl
      · simp
      · exact hgen (Sum.inr j)
    | mul x y hx hy => rw [map_mul]; exact hmul _ _ hx hy
  | mul x y hx hy => exact hmul x y hx hy

theorem wprod_nf (g : G r s) : wprod (nf g) = g := by
  have := wprod_hom g ⟨[], red_nil⟩
  simpa [nf] using this

theorem length_hom_wprod_le (u : List (Lt r s)) (v : RL r s) :
    (hom r s (wprod u) v).1.length ≤ u.length + v.1.length := by
  induction u with
  | nil => simp
  | cons a t ih =>
    rw [wprod_cons, hom_genL_mul]
    have := length_push_le a (hom r s (wprod t) v).1
    simp only [List.length_cons]
    omega

theorem length_nf_wprod_le (u : List (Lt r s)) : (nf (wprod u)).length ≤ u.length := by
  have := length_hom_wprod_le u ⟨[], red_nil⟩
  simp only [List.length_nil, add_zero] at this
  exact this

/-- Any word for `g` bounds `len g`. -/
theorem len_le_of_wprod {u : List (Lt r s)} {g : G r s} (h : wprod u = g) : len g ≤ u.length :=
  Nat.sInf_le ⟨u, rfl, h⟩

theorem len_eq_length_nf (g : G r s) : len g = (nf g).length := by
  apply le_antisymm (len_le_of_wprod (wprod_nf g))
  have hne : {n | ∃ u : List (Lt r s), u.length = n ∧ wprod u = g}.Nonempty :=
    ⟨_, nf g, rfl, wprod_nf g⟩
  obtain ⟨u, hu, hg⟩ := Nat.sInf_mem hne
  show _ ≤ len g
  unfold len
  rw [← hu, ← hg]
  exact length_nf_wprod_le u

@[simp] theorem len_one : len (1 : G r s) = 0 := by rw [len_eq_length_nf, nf_one]; rfl

/-! ## The stubs -/

end RandomInvolutions.Dev.PartP3b.F1
end
end

section
open Finset BordenaveCollins
noncomputable section
namespace RandomInvolutions.Dev.PartW
variable {r s : ℕ}
/-!
# Part W, words: the two-loop factorizations of a cyclically reduced word and `C2count`

The first half is the reduced-word toolkit of Part F (normal forms by van der Waerden's trick),
copied here because Parts do not import each other.  The second half identifies the folds
`Par u j i` with the tuples counted by `C2count i j (a * wprod u * a⁻¹)`.
-/
/-! ## Group lemmas for `G r s`

(`rw`/`simp` with the generic group lemmas fail on `G r s` because of an instance diamond in
`Monoid.Coprod (…) (Gam s)`; these restatements are syntactically in the form of the Blueprint.) -/
theorem g_mul_inv_cancel (a : G r s) : a * a⁻¹ = 1 := mul_inv_cancel a

theorem g_inv_mul_cancel (a : G r s) : a⁻¹ * a = 1 := inv_mul_cancel a

theorem g_inv_inv (a : G r s) : a⁻¹⁻¹ = a := inv_inv a

theorem g_inv_eq_of_mul_eq_one_right {a b : G r s} (h : a * b = 1) : a⁻¹ = b := by
  have h2 : a⁻¹ * (a * b) = a⁻¹ := by rw [h, mul_one]
  rw [← mul_assoc, g_inv_mul_cancel, one_mul] at h2
  exact h2.symm

theorem g_map_inv {H : Type*} [Group H] (f : G r s →* H) (a : G r s) : f a⁻¹ = (f a)⁻¹ :=
  map_inv f a

/-! ## Letters -/
@[simp] theorem bar_bar (a : Lt r s) : bar (bar a) = a := by
  rcases a with ⟨i, b⟩ | j <;> simp [bar]

theorem genL_bar (a : Lt r s) : genL (bar a) = (genL a)⁻¹ := by
  rcases a with ⟨i, b⟩ | j
  · cases b
    · exact (g_inv_inv _).symm
    · rfl
  · simp only [bar, genL]
    refine (g_inv_eq_of_mul_eq_one_right ?_).symm
    rw [← map_mul, DerandSq.mGen_mul_self, map_one]

theorem genL_mul_genL_bar (a : Lt r s) : genL a * genL (bar a) = 1 := by
  rw [genL_bar, g_mul_inv_cancel]

/-! ## Word products -/
@[simp] theorem wprod_nil : wprod ([] : List (Lt r s)) = 1 := rfl

@[simp] theorem wprod_cons (a : Lt r s) (u : List (Lt r s)) :
    wprod (a :: u) = genL a * wprod u := by
  simp [wprod]

@[simp] theorem wprod_append (u v : List (Lt r s)) : wprod (u ++ v) = wprod u * wprod v := by
  simp [wprod]

/-! ## The push action on reduced words -/
/-- Cancel the head if it is the inverse letter, otherwise push. -/
def push (a : Lt r s) : List (Lt r s) → List (Lt r s)
  | [] => [a]
  | b :: t => if b = bar a then t else a :: b :: t

@[simp] theorem push_nil (a : Lt r s) : push a [] = [a] := rfl

theorem push_cons_bar (a : Lt r s) (t : List (Lt r s)) : push a (bar a :: t) = t := by
  simp [push]

theorem push_cons_ne (a b : Lt r s) (t : List (Lt r s)) (h : b ≠ bar a) :
    push a (b :: t) = a :: b :: t := by
  simp [push, h]

theorem red_nil : Red ([] : List (Lt r s)) := List.isChain_nil

theorem red_cons_cons {a b : Lt r s} {t : List (Lt r s)} :
    Red (a :: b :: t) ↔ b ≠ bar a ∧ Red (b :: t) := List.isChain_cons_cons

theorem Red.tail' {a : Lt r s} {t : List (Lt r s)} (h : Red (a :: t)) : Red t :=
  List.IsChain.tail h

theorem red_push (a : Lt r s) (u : List (Lt r s)) (h : Red u) : Red (push a u) := by
  cases u with
  | nil => exact List.isChain_singleton _
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb; rw [push_cons_bar]; exact Red.tail' h
    · rw [push_cons_ne _ _ _ hb]; exact red_cons_cons.2 ⟨hb, h⟩

theorem push_bar_push (a : Lt r s) (u : List (Lt r s)) (h : Red u) :
    push (bar a) (push a u) = u := by
  cases u with
  | nil => simp [push]
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb
      rw [push_cons_bar]
      cases t with
      | nil => rfl
      | cons c t =>
        have hc : c ≠ bar (bar a) := (red_cons_cons.1 h).1
        rw [push_cons_ne _ _ _ hc]
    · rw [push_cons_ne _ _ _ hb]
      simp [push]

theorem push_push_bar (a : Lt r s) (u : List (Lt r s)) (h : Red u) :
    push a (push (bar a) u) = u := by
  simpa using push_bar_push (bar a) u h

theorem length_push_le (a : Lt r s) (u : List (Lt r s)) :
    (push a u).length ≤ u.length + 1 := by
  cases u with
  | nil => simp
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb; rw [push_cons_bar]; simp; omega
    · rw [push_cons_ne _ _ _ hb]; simp

theorem wprod_push (a : Lt r s) (u : List (Lt r s)) : wprod (push a u) = genL a * wprod u := by
  cases u with
  | nil => simp
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb
      rw [push_cons_bar, wprod_cons, ← mul_assoc, genL_mul_genL_bar, one_mul]
    · rw [push_cons_ne _ _ _ hb]; simp

/-- Reduced words. -/
abbrev RL (r s : ℕ) := {u : List (Lt r s) // Red u}

/-- The permutation of reduced words given by a letter. -/
def pushP (a : Lt r s) : Equiv.Perm (RL r s) where
  toFun u := ⟨push a u.1, red_push a u.1 u.2⟩
  invFun u := ⟨push (bar a) u.1, red_push (bar a) u.1 u.2⟩
  left_inv u := Subtype.ext (push_bar_push a u.1 u.2)
  right_inv u := Subtype.ext (push_push_bar a u.1 u.2)

@[simp] theorem pushP_apply (a : Lt r s) (u : RL r s) : (pushP a u).1 = push a u.1 := rfl

theorem pushP_inv (a : Lt r s) : (pushP a)⁻¹ = pushP (bar a) := by
  ext u : 2
  rfl

theorem pushP_inr_sq (j : Fin s) :
    pushP (Sum.inr j : Lt r s) * pushP (Sum.inr j : Lt r s) = 1 := by
  have h := pushP_inv (Sum.inr j : Lt r s)
  have hb : bar (Sum.inr j : Lt r s) = Sum.inr j := rfl
  rw [hb] at h
  nth_rewrite 1 [← h]
  exact inv_mul_cancel _

/-- The homomorphism `Z₂ → Perm α` of an involution. -/
def invHomP {α : Type*} (σ : Equiv.Perm α) (hσ : σ * σ = 1) :
    Multiplicative (ZMod 2) →* Equiv.Perm α where
  toFun a := σ ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    have key : ∀ a b : ZMod 2, σ ^ (a + b).val = σ ^ a.val * σ ^ b.val := by
      intro a b
      fin_cases a <;> fin_cases b
      · show σ ^ (0 : ZMod 2).val = σ ^ (0 : ZMod 2).val * σ ^ (0 : ZMod 2).val
        simp
      · show σ ^ (1 : ZMod 2).val = σ ^ (0 : ZMod 2).val * σ ^ (1 : ZMod 2).val
        simp
      · show σ ^ (1 : ZMod 2).val = σ ^ (1 : ZMod 2).val * σ ^ (0 : ZMod 2).val
        simp
      · show σ ^ ((1 : ZMod 2) + 1).val = σ ^ (1 : ZMod 2).val * σ ^ (1 : ZMod 2).val
        have h11 : ((1 : ZMod 2) + 1) = 0 := by decide
        rw [h11]; simp [ZMod.val_one, hσ]
    exact key _ _

theorem invHomP_gen {α : Type*} (σ : Equiv.Perm α) (hσ : σ * σ = 1) :
    invHomP σ hσ (Multiplicative.ofAdd (1 : ZMod 2)) = σ := by
  show σ ^ (1 : ZMod 2).val = σ
  simp [ZMod.val_one]

/-- The action of `G r s` on reduced words. -/
def hom (r s : ℕ) : G r s →* Equiv.Perm (RL r s) :=
  Monoid.Coprod.lift (FreeGroup.lift fun i => pushP (Sum.inl (i, true)))
    (Monoid.CoprodI.lift fun j => invHomP (pushP (Sum.inr j)) (pushP_inr_sq j))

theorem hom_genL (a : Lt r s) : hom r s (genL a) = pushP a := by
  rcases a with ⟨i, b⟩ | j
  · cases b
    · have : hom r s (genL (Sum.inl (i, true))) = pushP (Sum.inl (i, true)) := by
        simp [hom, genL]
      show hom r s (genL (Sum.inl (i, true)))⁻¹ = _
      rw [g_map_inv, this, pushP_inv]; rfl
    · simp [hom, genL]
  · simp only [hom, genL, Monoid.Coprod.lift_apply_inr, DerandSq.mGen]
    rw [Monoid.CoprodI.lift_of]
    exact invHomP_gen _ _

/-- The normal form: the reduced word of `g`. -/
def nf (g : G r s) : List (Lt r s) := (hom r s g ⟨[], red_nil⟩).1

@[simp] theorem nf_one : nf (1 : G r s) = [] := by simp [nf]

theorem hom_genL_mul (a : Lt r s) (g : G r s) (v : RL r s) :
    (hom r s (genL a * g) v).1 = push a (hom r s g v).1 := by
  rw [map_mul, hom_genL]; rfl

theorem wprod_hom (g : G r s) : ∀ v : RL r s, wprod (hom r s g v).1 = g * wprod v.1 := by
  have hone : ∀ v : RL r s, wprod (hom r s 1 v).1 = 1 * wprod v.1 := by intro v; simp
  have hmul : ∀ x y : G r s, (∀ v : RL r s, wprod (hom r s x v).1 = x * wprod v.1) →
      (∀ v : RL r s, wprod (hom r s y v).1 = y * wprod v.1) →
      ∀ v : RL r s, wprod (hom r s (x * y) v).1 = x * y * wprod v.1 := by
    intro x y hx hy v
    rw [map_mul, Equiv.Perm.mul_apply, hx, hy, mul_assoc]
  have hgen : ∀ (a : Lt r s) (v : RL r s),
      wprod (hom r s (genL a) v).1 = genL a * wprod v.1 := by
    intro a v
    rw [hom_genL, pushP_apply, wprod_push]
  induction g using Monoid.Coprod.induction_on with
  | inl x =>
    induction x using FreeGroup.induction_on with
    | C1 => simp
    | of i => exact hgen (Sum.inl (i, true))
    | inv_of i _ => exact hgen (Sum.inl (i, false))
    | mul x y hx hy => rw [map_mul]; exact hmul _ _ hx hy
  | inr y =>
    induction y using Monoid.CoprodI.induction_on with
    | one => simp
    | of j m =>
      have hm : ∀ z : Multiplicative (ZMod 2), z = 1 ∨ z = Multiplicative.ofAdd 1 := by decide
      rcases hm m with rfl | rfl
      · simp
      · exact hgen (Sum.inr j)
    | mul x y hx hy => rw [map_mul]; exact hmul _ _ hx hy
  | mul x y hx hy => exact hmul x y hx hy

theorem wprod_nf (g : G r s) : wprod (nf g) = g := by
  have := wprod_hom g ⟨[], red_nil⟩
  simpa [nf] using this

theorem length_hom_wprod_le (u : List (Lt r s)) (v : RL r s) :
    (hom r s (wprod u) v).1.length ≤ u.length + v.1.length := by
  induction u with
  | nil => simp
  | cons a t ih =>
    rw [wprod_cons, hom_genL_mul]
    have := length_push_le a (hom r s (wprod t) v).1
    simp only [List.length_cons]
    omega

theorem length_nf_wprod_le (u : List (Lt r s)) : (nf (wprod u)).length ≤ u.length := by
  have := length_hom_wprod_le u ⟨[], red_nil⟩
  simp only [List.length_nil, add_zero] at this
  exact this

/-- Any word for `g` bounds `len g`. -/
theorem len_le_of_wprod {u : List (Lt r s)} {g : G r s} (h : wprod u = g) : len g ≤ u.length :=
  Nat.sInf_le ⟨u, rfl, h⟩

theorem len_eq_length_nf (g : G r s) : len g = (nf g).length := by
  apply le_antisymm (len_le_of_wprod (wprod_nf g))
  have hne : {n | ∃ u : List (Lt r s), u.length = n ∧ wprod u = g}.Nonempty :=
    ⟨_, nf g, rfl, wprod_nf g⟩
  obtain ⟨u, hu, hg⟩ := Nat.sInf_mem hne
  show _ ≤ len g
  unfold len
  rw [← hu, ← hg]
  exact length_nf_wprod_le u

@[simp] theorem len_one : len (1 : G r s) = 0 := by rw [len_eq_length_nf, nf_one]; rfl

/-! ## Aliases -/

/-! ## Generic group identities

(`simp`, `rw` and `group` do not see through the instance path of `G r s`, so identities are
proved in a generic group and applied with `exact`.) -/

/-! ## The inverse word -/
/-- The inverse word: reversed, with `bar` applied. -/
def ibar (u : List (Lt r s)) : List (Lt r s) := (u.map bar).reverse

@[simp] theorem ibar_nil : ibar ([] : List (Lt r s)) = [] := rfl

@[simp] theorem length_ibar (u : List (Lt r s)) : (ibar u).length = u.length := by simp [ibar]

/-! ## Non-reduced words are not shortest -/

/-! ## Repeated words -/
/-- `Z` repeated `k` times. -/
def rep (Z : List (Lt r s)) (k : ℕ) : List (Lt r s) := (List.replicate k Z).flatten

@[simp] theorem rep_zero (Z : List (Lt r s)) : rep Z 0 = [] := by simp [rep]

theorem rep_succ (Z : List (Lt r s)) (k : ℕ) : rep Z (k + 1) = Z ++ rep Z k := by
  simp [rep, List.replicate_succ]

@[simp] theorem rep_nil (k : ℕ) : rep ([] : List (Lt r s)) k = [] := by simp [rep]

@[simp] theorem length_rep (Z : List (Lt r s)) (k : ℕ) : (rep Z k).length = k * Z.length := by
  induction k with
  | zero => simp
  | succ k ih => rw [rep_succ, List.length_append, ih]; ring

end RandomInvolutions.Dev.PartW
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
open RandomInvolutions
open RandomInvolutions.Dev
theorem solution (K : ℝ) (hK : 0 < K) (r : ℕ) (E : (Fin r → ℕ) → ℕ → (ℝ → ℝ) → ℝ)
    (hadd : ∀ κ N f g, E κ N (f + g) = E κ N f + E κ N g)
    (hsmul : ∀ κ N (a : ℝ) f, E κ N (a • f) = a * E κ N f)
    (hmono : ∀ κ N f g, (∀ x ∈ Set.Icc (-K) K, f x ≤ g x) → E κ N f ≤ E κ N g)
    (hone : ∀ κ N, E κ N (fun _ => 1) ≤ 1)
    (hrat : ∃ C : ℕ, 1 ≤ C ∧ ∀ q : ℕ, 1 ≤ q → ∃ gq : ℝ[X], gq.natDegree ≤ C * q ∧
      (∀ x ∈ Set.Icc (0 : ℝ) (1 / ((C : ℝ) * (q : ℝ) ^ 2)), 1 / 2 ≤ gq.eval x ∧ gq.eval x ≤ 1) ∧
      ∀ h : ℝ[X], h.natDegree ≤ q → ∀ κ : Fin r → ℕ, ∃ f : ℝ[X], f.natDegree ≤ C * q ∧
        ∀ N : ℕ, AdmK N κ → C * q ≤ N →
          E κ N (fun x => h.eval x) = f.eval (1 / (N : ℝ)) / gq.eval (1 / (N : ℝ)))
    (ρ : ℝ) (hρ : 0 ≤ ρ) (a A : ℕ → ℝ) (B : Fin r → ℕ → ℝ) (C2 : Fin r → Fin r → ℕ → ℝ)
    (hexp : ∃ (C0 : ℕ → ℝ) (C1 : Fin r → ℕ → ℝ), ∀ (κ : Fin r → ℕ) (p : ℕ),
      Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * (E κ N (fun x => x ^ p) - a p -
          (A p + ∑ i, (κ i : ℝ) * B i p) / N)) (admF κ)
        (𝓝 (C0 p + ∑ i, (κ i : ℝ) * C1 i p + ∑ i, ∑ j, (κ i : ℝ) * κ j * C2 i j p)))
    (hagrow : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ p : ℕ, |a p| ≤ C * (ρ + δ) ^ p)
    (hAgrow : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ p : ℕ, |A p| ≤ C * (ρ + δ) ^ p)
    (hBgrow : ∀ i, ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ p : ℕ, |B i p| ≤ C * (ρ + δ) ^ p)
    (hC2grow : ∀ i j, ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ p : ℕ, |C2 i j p| ≤ C * (ρ + δ) ^ p)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ (κ : Fin r → ℕ) (N : ℕ), AdmK N κ → 1 ≤ N →
      E κ N (fun x => if ρ + ε ≤ |x| then 1 else 0) ≤
        C * lam κ / (N : ℝ) ^ 2 + C * lam κ ^ 3 / (N : ℝ) ^ 3 := by
  exact RandomInvolutions.Dev.tail_le_of_second_order_rational_moments K hK r E hadd hsmul hmono hone hrat ρ hρ a A B C2 hexp hagrow hAgrow hBgrow hC2grow ε hε
end
end
