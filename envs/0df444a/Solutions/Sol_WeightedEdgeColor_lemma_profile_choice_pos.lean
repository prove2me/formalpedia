-- Prove2me | solution 1 for WeightedEdgeColor.lemma_profile_choice_pos
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T09:42:22.810946+00:00
-- url     : https://prove2.me/submissions/6b875336-918d-43da-b0b1-028b6c4b9947
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WeightedEdgeColor_WGraph
import Theorems.Thm_WeightedEdgeColor_proposition_A_4

set_option autoImplicit false
set_option maxHeartbeats 0

namespace WECProb

variable {C Ω : Type} [Fintype C] [DecidableEq C] [Fintype Ω]

/-- product weight of a list -/
noncomputable def pw (lam : C → Ω → ℝ) (L : C → Ω) : ℝ := ∏ c, lam c (L c)

theorem pw_nonneg (lam : C → Ω → ℝ) (h0 : ∀ c m, 0 ≤ lam c m) (L : C → Ω) : 0 ≤ pw lam L :=
  Finset.prod_nonneg (fun c _ => h0 c (L c))

theorem sum_prod_lists (h : C → Ω → ℝ) : ∑ L : C → Ω, ∏ c, h c (L c) = ∏ c, ∑ m, h c m :=
  (Fintype.prod_sum h).symm

theorem pw_sum (lam : C → Ω → ℝ) (h1 : ∀ c, ∑ m, lam c m = 1) : ∑ L, pw lam L = 1 := by
  unfold pw; rw [sum_prod_lists]; simp [h1]

/-- expectation of a product of coordinate functions (general factorization) -/
theorem pw_prod (lam : C → Ω → ℝ) (g : C → Ω → ℝ) :
    ∑ L, pw lam L * ∏ c, g c (L c) = ∏ c, ∑ m, lam c m * g c m := by
  unfold pw
  simp_rw [← Finset.prod_mul_distrib]
  exact sum_prod_lists (fun c m => lam c m * g c m)

theorem pw_marg (lam : C → Ω → ℝ) (h1 : ∀ c, ∑ m, lam c m = 1) (c₀ : C) (g : Ω → ℝ) :
    ∑ L, pw lam L * g (L c₀) = ∑ m, lam c₀ m * g m := by
  have h := pw_prod lam (fun c m => if c = c₀ then g m else 1)
  have e1 : ∀ L : C → Ω, (∏ c, (if c = c₀ then g (L c) else 1)) = g (L c₀) := by
    intro L; rw [Finset.prod_ite_eq']; simp
  simp_rw [e1] at h
  rw [h, Finset.prod_eq_single c₀]
  · simp
  · intro c _ hc; simp [hc, h1 c]
  · simp

theorem pw_marg2 (lam : C → Ω → ℝ) (h1 : ∀ c, ∑ m, lam c m = 1) (c₁ c₂ : C) (hne : c₁ ≠ c₂)
    (g g' : Ω → ℝ) :
    ∑ L, pw lam L * (g (L c₁) * g' (L c₂)) = (∑ m, lam c₁ m * g m) * (∑ m, lam c₂ m * g' m) := by
  have h := pw_prod lam (fun c m => (if c = c₁ then g m else 1) * (if c = c₂ then g' m else 1))
  have e1 : ∀ L : C → Ω, (∏ c, ((if c = c₁ then g (L c) else 1) * (if c = c₂ then g' (L c) else 1)))
      = g (L c₁) * g' (L c₂) := by
    intro L; rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']; simp
  simp_rw [e1] at h
  rw [h, ← Finset.mul_prod_erase _ _ (Finset.mem_univ c₁)]
  have h2 : c₂ ∈ Finset.univ.erase c₁ := Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩
  rw [← Finset.mul_prod_erase _ _ h2]
  rw [Finset.prod_eq_one]
  · simp [hne, hne.symm]
  · intro c hc
    have hc1 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hc)
    have hc2 := Finset.ne_of_mem_erase hc
    simp [hc1, hc2, h1 c]

/-- expectation of a sum of coordinate functions -/
theorem pw_sum_fun (lam : C → Ω → ℝ) (h1 : ∀ c, ∑ m, lam c m = 1) (g : C → Ω → ℝ) :
    ∑ L, pw lam L * ∑ c, g c (L c) = ∑ c, ∑ m, lam c m * g c m := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun c _ => pw_marg lam h1 c (g c))

theorem pw_var (lam : C → Ω → ℝ) (h1 : ∀ c, ∑ m, lam c m = 1) (g : C → Ω → ℝ) :
    ∑ L, pw lam L * (∑ c, g c (L c) - ∑ c, ∑ m, lam c m * g c m) ^ 2
      = ∑ c, ∑ m, lam c m * (g c m - ∑ m', lam c m' * g c m') ^ 2 := by
  set gb : C → ℝ := fun c => ∑ m', lam c m' * g c m'
  have hrw : ∀ L : C → Ω, (∑ c, g c (L c) - ∑ c, gb c) ^ 2
      = ∑ c, ∑ d, (g c (L c) - gb c) * (g d (L d) - gb d) := by
    intro L
    rw [← Finset.sum_sub_distrib, sq, Finset.sum_mul_sum]
  simp_rw [hrw, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro c _
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single c]
  · rw [show (∑ L : C → Ω, pw lam L * ((g c (L c) - gb c) * (g c (L c) - gb c)))
        = ∑ L, pw lam L * ((fun m => (g c m - gb c) ^ 2) (L c)) by
      apply Finset.sum_congr rfl; intro L _; ring]
    exact pw_marg lam h1 c (fun m => (g c m - gb c) ^ 2)
  · intro d _ hdc
    rw [pw_marg2 lam h1 c d (Ne.symm hdc) (fun m => g c m - gb c) (fun m => g d m - gb d)]
    have : ∑ m, lam c m * (g c m - gb c) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h1 c, one_mul, gb]; ring
    rw [this, zero_mul]
  · simp

/-- Cauchy–Schwarz for an expectation -/
theorem exp_abs_le_sqrt {α : Type} [Fintype α] (p Y : α → ℝ) (h0 : ∀ a, 0 ≤ p a)
    (h1 : ∑ a, p a = 1) : ∑ a, p a * |Y a| ≤ Real.sqrt (∑ a, p a * Y a ^ 2) := by
  apply Real.le_sqrt_of_sq_le
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun a => Real.sqrt (p a))
    (fun a => Real.sqrt (p a) * |Y a|)
  have e1 : ∀ a, Real.sqrt (p a) * (Real.sqrt (p a) * |Y a|) = p a * |Y a| := by
    intro a; rw [← mul_assoc, Real.mul_self_sqrt (h0 a)]
  have e2 : ∀ a, Real.sqrt (p a) ^ 2 = p a := fun a => Real.sq_sqrt (h0 a)
  have e3 : ∀ a, (Real.sqrt (p a) * |Y a|) ^ 2 = p a * Y a ^ 2 := by
    intro a; rw [mul_pow, Real.sq_sqrt (h0 a), sq_abs]
  simp only [e1, e2, e3, h1, one_mul] at this
  exact this

/-- Markov's inequality -/
theorem markov {α : Type} [Fintype α] (p Y : α → ℝ) (h0 : ∀ a, 0 ≤ p a) (hY : ∀ a, 0 ≤ Y a)
    (t : ℝ) (ht : 0 < t) :
    ∑ a ∈ Finset.univ.filter (fun a => t < Y a), p a ≤ (∑ a, p a * Y a) / t := by
  rw [le_div_iff₀ ht, Finset.sum_mul]
  calc ∑ a ∈ Finset.univ.filter (fun a => t < Y a), p a * t
      ≤ ∑ a ∈ Finset.univ.filter (fun a => t < Y a), p a * Y a :=
        Finset.sum_le_sum (fun a ha => mul_le_mul_of_nonneg_left (Finset.mem_filter.mp ha).2.le (h0 a))
    _ ≤ ∑ a, p a * Y a := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun a _ _ => mul_nonneg (h0 a) (hY a))

/-- variance is at most the bound times the mean, for values in `[0, G]` -/
theorem var_le {α : Type} [Fintype α] (p g : α → ℝ) (Gm : ℝ) (h0 : ∀ a, 0 ≤ p a)
    (h1 : ∑ a, p a = 1) (hg0 : ∀ a, 0 ≤ g a) (hgG : ∀ a, g a ≤ Gm) :
    ∑ a, p a * (g a - ∑ b, p b * g b) ^ 2 ≤ Gm * ∑ b, p b * g b := by
  set gb := ∑ b, p b * g b
  have e : ∑ a, p a * (g a - gb) ^ 2 = ∑ a, p a * g a ^ 2 - gb ^ 2 := by
    have : ∀ a, p a * (g a - gb) ^ 2 = p a * g a ^ 2 - 2 * gb * (p a * g a) + gb ^ 2 * p a := by
      intro a; ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h1]
    ring
  rw [e]
  have : ∑ a, p a * g a ^ 2 ≤ Gm * gb := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro a _
    have := mul_le_mul_of_nonneg_left (hgG a) (hg0 a)
    nlinarith [h0 a]
  nlinarith [sq_nonneg gb]

end WECProb


namespace WECEdge

/-- The coupled fraction for one edge, one color, labels `Ps`, `Pt` at the two ends. -/
noncomputable def Xc {M Ks : ℕ} (Ls Lt : Fin M → Fin Ks → ℝ) (Ss St : Fin M → ℝ)
    (ls lt : Fin M → ℝ) (y : ℝ) (Ps Pt : Fin M) : ℝ :=
  ((∑ i, Ls Ps i) * (∑ j, Lt Pt j) + Ss Ps * St Pt) / (y * ls Ps * lt Pt)

variable {M Ks : ℕ} (Ls Lt : Fin M → Fin Ks → ℝ) (Ss St : Fin M → ℝ) (ls lt : Fin M → ℝ)
  (y θ : ℝ)

/-- the total fraction at one end and one label -/
noncomputable def At (L : Fin M → Fin Ks → ℝ) (S : Fin M → ℝ) (P : Fin M) : ℝ := ∑ i, L P i + S P

theorem Xc_nonneg (hL : ∀ P i, 0 ≤ Ls P i) (hL' : ∀ P i, 0 ≤ Lt P i) (hS : ∀ P, 0 ≤ Ss P)
    (hS' : ∀ P, 0 ≤ St P) (hls : ∀ P, 0 < ls P) (hlt : ∀ P, 0 < lt P) (hy : 0 ≤ y) (Ps Pt : Fin M) :
    0 ≤ Xc Ls Lt Ss St ls lt y Ps Pt := by
  unfold Xc
  apply div_nonneg
  · exact add_nonneg (mul_nonneg (Finset.sum_nonneg (fun i _ => hL Ps i))
      (Finset.sum_nonneg (fun j _ => hL' Pt j))) (mul_nonneg (hS Ps) (hS' Pt))
  · exact mul_nonneg (mul_nonneg hy (hls Ps).le) (hlt Pt).le

theorem Xc_le (hL : ∀ P i, 0 ≤ Ls P i) (hL' : ∀ P i, 0 ≤ Lt P i) (hS : ∀ P, 0 ≤ Ss P)
    (hS' : ∀ P, 0 ≤ St P) (hθ : 0 < θ) (hls : ∀ P, θ / M ≤ ls P) (hlt : ∀ P, θ / M ≤ lt P)
    (hy : 0 ≤ y) (hAs : ∀ P, At Ls Ss P ≤ y) (hAt : ∀ P, At Lt St P ≤ y) (hM : 0 < (M : ℝ))
    (Ps Pt : Fin M) :
    Xc Ls Lt Ss St ls lt y Ps Pt ≤ y * ((M : ℝ) / θ) ^ 2 := by
  unfold Xc
  rcases hy.lt_or_eq with hy0 | hy0
  · have hθM : 0 < θ / M := div_pos hθ hM
    have h1 : (∑ i, Ls Ps i) * (∑ j, Lt Pt j) + Ss Ps * St Pt ≤ y * y := by
      have a1 := hAs Ps; have a2 := hAt Pt
      unfold At at a1 a2
      have b1 : 0 ≤ ∑ i, Ls Ps i := Finset.sum_nonneg (fun i _ => hL Ps i)
      have b2 : 0 ≤ ∑ j, Lt Pt j := Finset.sum_nonneg (fun j _ => hL' Pt j)
      have := mul_le_mul a1 a2 (add_nonneg b2 (hS' Pt)) hy
      nlinarith only [this, b1, b2, hS Ps, hS' Pt]
    have h2 : y * (θ / M) * (θ / M) ≤ y * ls Ps * lt Pt := by
      have := mul_le_mul (hls Ps) (hlt Pt) hθM.le (le_trans hθM.le (hls Ps))
      nlinarith only [this, hy0]
    calc ((∑ i, Ls Ps i) * (∑ j, Lt Pt j) + Ss Ps * St Pt) / (y * ls Ps * lt Pt)
        ≤ (y * y) / (y * (θ / M) * (θ / M)) :=
          div_le_div₀ (by positivity) h1 (by positivity) h2
      _ = y * ((M : ℝ) / θ) ^ 2 := by field_simp
  · rw [← hy0]; simp

/-- conditional mean over the label at the target end -/
theorem Xc_mean_t (hlt : ∀ P, 0 < lt P) (hy : 0 < y)
    (hmt : ∑ P, At Lt St P = y) (Ps : Fin M) :
    ∑ Pt, lt Pt * Xc Ls Lt Ss St ls lt y Ps Pt
      = ((∑ i, Ls Ps i) * (∑ P, ∑ j, Lt P j) + Ss Ps * (∑ P, St P)) / (y * ls Ps) := by
  unfold Xc
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl; intro P _
  have := hlt P
  field_simp

theorem Xc_swap (Ps Pt : Fin M) :
    Xc Ls Lt Ss St ls lt y Ps Pt = Xc Lt Ls St Ss lt ls y Pt Ps := by
  unfold Xc; ring_nf

theorem Xc_mean_le (hL : ∀ P i, 0 ≤ Ls P i) (hL' : ∀ P i, 0 ≤ Lt P i) (hS : ∀ P, 0 ≤ Ss P)
    (hS' : ∀ P, 0 ≤ St P) (hθ : 0 < θ) (hM : 0 < (M : ℝ)) (hls : ∀ P, θ / M ≤ ls P)
    (hlt : ∀ P, 0 < lt P) (hy : 0 ≤ y) (hAs : ∀ P, At Ls Ss P ≤ y)
    (hmt : ∑ P, At Lt St P = y) (Ps : Fin M) :
    ∑ Pt, lt Pt * Xc Ls Lt Ss St ls lt y Ps Pt ≤ y * ((M : ℝ) / θ) := by
  rcases hy.lt_or_eq with hy0 | hy0
  · rw [Xc_mean_t Ls Lt Ss St ls lt y hlt hy0 hmt]
    have hLt : ∑ P', ∑ j, Lt P' j ≤ y := by
      rw [← hmt]; exact Finset.sum_le_sum (fun P' _ => le_add_of_nonneg_right (hS' P'))
    have hSt : ∑ P', St P' ≤ y := by
      rw [← hmt]; exact Finset.sum_le_sum (fun P' _ => le_add_of_nonneg_left
        (Finset.sum_nonneg (fun j _ => hL' P' j)))
    have hA := hAs Ps
    unfold At at hA
    have hS0 : 0 ≤ ∑ i, Ls Ps i := Finset.sum_nonneg (fun i _ => hL Ps i)
    have hnum : (∑ i, Ls Ps i) * (∑ P', ∑ j, Lt P' j) + Ss Ps * ∑ P', St P'
        ≤ (∑ i, Ls Ps i + Ss Ps) * y := by
      have := mul_le_mul_of_nonneg_left hLt hS0
      have := mul_le_mul_of_nonneg_left hSt (hS Ps)
      nlinarith
    have hlo := hls Ps
    have hlp : 0 < ls Ps := lt_of_lt_of_le (div_pos hθ hM) hlo
    rw [div_le_iff₀ (by positivity)]
    calc (∑ i, Ls Ps i) * (∑ P', ∑ j, Lt P' j) + Ss Ps * ∑ P', St P'
        ≤ (∑ i, Ls Ps i + Ss Ps) * y := hnum
      _ ≤ y * y := mul_le_mul_of_nonneg_right hA hy0.le
      _ ≤ y * ((M : ℝ) / θ) * (y * ls Ps) := by
          have : 1 ≤ (M : ℝ) / θ * ls Ps := by
            have := mul_le_mul_of_nonneg_left hlo (by positivity : (0 : ℝ) ≤ M / θ)
            have h1 : (M : ℝ) / θ * (θ / M) = 1 := by field_simp
            linarith
          nlinarith
  · have : ∀ Q, Xc Ls Lt Ss St ls lt y Ps Q = 0 := fun Q => by unfold Xc; rw [← hy0]; simp
    rw [Finset.sum_eq_zero (fun Q _ => by rw [this Q, mul_zero]), ← hy0, zero_mul]

/-- generic contribution of one edge to one place, given the other end's label -/
noncomputable def capg {M : ℕ} (a lv y : ℝ) (B lt : Fin M → ℝ) (P : Fin M) : ℝ :=
  a * B P / (y * lv * lt P)

theorem capg_nonneg {M : ℕ} (a lv y : ℝ) (B lt : Fin M → ℝ) (P : Fin M) (ha : 0 ≤ a) (hlv : 0 ≤ lv)
    (hy : 0 ≤ y) (hB : 0 ≤ B P) (hlt : 0 ≤ lt P) : 0 ≤ capg a lv y B lt P := by
  unfold capg; positivity

theorem capg_le {M : ℕ} (a lv y θ : ℝ) (B lt : Fin M → ℝ) (P : Fin M) (hθ : 0 < θ) (hM : 0 < (M : ℝ))
    (ha0 : 0 ≤ a) (ha : a ≤ y) (hB0 : 0 ≤ B P) (hB : B P ≤ y) (hlv : θ / M ≤ lv) (hlt : θ / M ≤ lt P) :
    capg a lv y B lt P ≤ y * ((M : ℝ) / θ) ^ 2 := by
  unfold capg
  have hθM : 0 < θ / M := div_pos hθ hM
  rcases (le_trans ha0 ha).lt_or_eq with hy0 | hy0
  · have h1 : a * B P ≤ y * y := mul_le_mul ha hB hB0 hy0.le
    have h2 : y * (θ / M) * (θ / M) ≤ y * lv * lt P := by
      have := mul_le_mul hlv hlt hθM.le (le_trans hθM.le hlv)
      nlinarith only [this, hy0]
    calc a * B P / (y * lv * lt P) ≤ (y * y) / (y * (θ / M) * (θ / M)) :=
          div_le_div₀ (by positivity) h1 (by positivity) h2
      _ = y * ((M : ℝ) / θ) ^ 2 := by field_simp
  · rw [← hy0]; simp

theorem capg_mean {M : ℕ} (a lv y : ℝ) (B lt : Fin M → ℝ) (ha : 0 ≤ a) (hlv : 0 < lv) (hy : 0 ≤ y)
    (hB0 : ∀ P, 0 ≤ B P) (hB : ∑ P, B P ≤ y) (hlt : ∀ P, 0 < lt P) :
    ∑ P, lt P * capg a lv y B lt P ≤ a / lv := by
  unfold capg
  rcases hy.lt_or_eq with hy0 | hy0
  · have : ∀ P, lt P * (a * B P / (y * lv * lt P)) = a / (y * lv) * B P := by
      intro P; have := hlt P; field_simp
    simp_rw [this]
    rw [← Finset.mul_sum]
    calc a / (y * lv) * ∑ P, B P ≤ a / (y * lv) * y := mul_le_mul_of_nonneg_left hB (by positivity)
      _ = a / lv := by field_simp
  · simp only [← hy0, zero_mul, div_zero, mul_zero, Finset.sum_const_zero]; positivity

end WECEdge

namespace WECErr

theorem err_bound (K₄ cR cD n ρ : ℝ) (hn : 1 ≤ n) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 2)
    (hcR : 0 < cR) (hcD : 0 < cD) :
    K₄ * (Real.sqrt (cR * n / (1 - ρ) * Real.log (max 2 (max (cR * n / (1 - ρ)) (cD * n ^ 2)) + 2))
      + Real.log (max 2 (max (cR * n / (1 - ρ)) (cD * n ^ 2)) + 2))
      ≤ |K₄| * (Real.sqrt (2 * cR * (8 * (2 * cR + cD + 4) ^ (1 / 8 : ℝ))) +
          8 * (2 * cR + cD + 4) ^ (1 / 8 : ℝ)) * n ^ (3 / 4 : ℝ) := by
  have hn0 : 0 < n := by linarith
  have h1ρ : 1 / 2 ≤ 1 - ρ := by linarith
  set c := 2 * cR + cD + 4
  have hc0 : 0 < c := by positivity
  set X := max 2 (max (cR * n / (1 - ρ)) (cD * n ^ 2)) + 2
  have hRn : cR * n / (1 - ρ) ≤ 2 * cR * n := by
    rw [div_le_iff₀ (by linarith)]
    have h := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 2 * (1 - ρ) by linarith)
      (le_of_lt (mul_pos hcR hn0))
    linarith [h]
  have hn2 : n ≤ n ^ 2 := by nlinarith
  have hX : X ≤ c * n ^ 2 := by
    simp only [X, c]
    have h2 : (2 : ℝ) ≤ 2 * n ^ 2 := by nlinarith
    have : max 2 (max (cR * n / (1 - ρ)) (cD * n ^ 2)) ≤ (2 * cR + cD + 2) * n ^ 2 := by
      apply max_le
      · nlinarith
      · apply max_le
        · nlinarith
        · nlinarith
    nlinarith
  have hX0 : 0 < X := by simp only [X]; positivity
  have hX1 : 1 ≤ X := by simp only [X]; have := le_max_left 2 (max (cR * n / (1 - ρ)) (cD * n ^ 2)); linarith
  have hlog : Real.log X ≤ 8 * c ^ (1 / 8 : ℝ) * n ^ (1 / 4 : ℝ) := by
    have h1 := Real.log_le_rpow_div hX0.le (by norm_num : (0 : ℝ) < 1 / 8)
    have h2 : X ^ (1 / 8 : ℝ) ≤ (c * n ^ 2) ^ (1 / 8 : ℝ) := Real.rpow_le_rpow hX0.le hX (by norm_num)
    have h3 : (c * n ^ 2) ^ (1 / 8 : ℝ) = c ^ (1 / 8 : ℝ) * n ^ (1 / 4 : ℝ) := by
      rw [Real.mul_rpow hc0.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
      norm_num
    rw [h3] at h2
    calc Real.log X ≤ X ^ (1 / 8 : ℝ) / (1 / 8) := h1
      _ = 8 * X ^ (1 / 8 : ℝ) := by ring
      _ ≤ 8 * (c ^ (1 / 8 : ℝ) * n ^ (1 / 4 : ℝ)) := by linarith
      _ = 8 * c ^ (1 / 8 : ℝ) * n ^ (1 / 4 : ℝ) := by ring
  have hlog0 : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hp14 : n ^ (1 / 4 : ℝ) ≤ n ^ (3 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
  have hsq : Real.sqrt (cR * n / (1 - ρ) * Real.log X)
      ≤ Real.sqrt (2 * cR * (8 * c ^ (1 / 8 : ℝ))) * n ^ (3 / 4 : ℝ) := by
    have h1 : cR * n / (1 - ρ) * Real.log X ≤ (2 * cR * (8 * c ^ (1 / 8 : ℝ))) * (n * n ^ (1 / 4 : ℝ)) := by
      have := mul_le_mul hRn hlog hlog0 (by positivity)
      nlinarith [this]
    have h2 : n * n ^ (1 / 4 : ℝ) ≤ (n ^ (3 / 4 : ℝ)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
      have : n * n ^ (1 / 4 : ℝ) = n ^ (5 / 4 : ℝ) := by
        rw [← Real.rpow_one_add' hn0.le (by norm_num)]; norm_num
      rw [this]
      exact Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
    calc Real.sqrt (cR * n / (1 - ρ) * Real.log X)
        ≤ Real.sqrt ((2 * cR * (8 * c ^ (1 / 8 : ℝ))) * (n ^ (3 / 4 : ℝ)) ^ 2) := by
          apply Real.sqrt_le_sqrt
          refine le_trans h1 ?_
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = Real.sqrt (2 * cR * (8 * c ^ (1 / 8 : ℝ))) * n ^ (3 / 4 : ℝ) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hsum : Real.sqrt (cR * n / (1 - ρ) * Real.log X) + Real.log X
      ≤ (Real.sqrt (2 * cR * (8 * c ^ (1 / 8 : ℝ))) + 8 * c ^ (1 / 8 : ℝ)) * n ^ (3 / 4 : ℝ) := by
    have : 8 * c ^ (1 / 8 : ℝ) * n ^ (1 / 4 : ℝ) ≤ 8 * c ^ (1 / 8 : ℝ) * n ^ (3 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left hp14 (by positivity)
    nlinarith
  have hnn : 0 ≤ Real.sqrt (cR * n / (1 - ρ) * Real.log X) + Real.log X := by positivity
  calc K₄ * (Real.sqrt (cR * n / (1 - ρ) * Real.log X) + Real.log X)
      ≤ |K₄| * (Real.sqrt (cR * n / (1 - ρ) * Real.log X) + Real.log X) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hnn
    _ ≤ |K₄| * ((Real.sqrt (2 * cR * (8 * c ^ (1 / 8 : ℝ))) + 8 * c ^ (1 / 8 : ℝ)) * n ^ (3 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ = _ := by ring

end WECErr

namespace WECA4

/-- Proposition A.4 after conditioning every variable on a good set of probability `≥ 1 - ρ`. -/
theorem a4_cond (K₄ : ℝ)
    (hK₄ : ∀ (I T : Type) [Fintype I] [Fintype T] (Ω : I → Type) [∀ i, Fintype (Ω i)]
      (p : ∀ i, Ω i → ℝ) (f : T → ∀ i, Ω i → ℝ) (R D : ℝ),
      (∀ i ω, 0 < p i ω) → (∀ i, ∑ ω, p i ω = 1) →
      (∀ t i ω, 0 ≤ f t i ω ∧ f t i ω ≤ 1) →
      (∀ t, ∑ i, ∑ ω, p i ω * f t i ω ≤ R) →
      (∀ i ω, ∑ t, f t i ω ≤ D) →
      ∃ z : ∀ i, Ω i, ∀ t, ∑ i, f t i (z i) ≤ ∑ i, ∑ ω, p i ω * f t i ω +
        K₄ * (Real.sqrt (R * Real.log (max 2 (max R D) + 2)) + Real.log (max 2 (max R D) + 2)))
    {I T Ω : Type} [Fintype I] [Fintype T] [Fintype Ω] [DecidableEq Ω]
    (π : I → Ω → ℝ) (good : I → Ω → Prop) [∀ i, DecidablePred (good i)]
    (f : T → I → Ω → ℝ) (m : T → ℝ) (ρ R₀ D₀ : ℝ)
    (hπ : ∀ i ω, 0 < π i ω) (hπ1 : ∀ i, ∑ ω, π i ω = 1) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hgood : ∀ i, 1 - ρ ≤ ∑ ω ∈ Finset.univ.filter (good i), π i ω)
    (hf : ∀ t i ω, 0 ≤ f t i ω ∧ f t i ω ≤ 1)
    (hm : ∀ t, ∑ i, ∑ ω, π i ω * f t i ω ≤ m t) (hmR : ∀ t, m t ≤ R₀)
    (hD : ∀ i ω, ∑ t, f t i ω ≤ D₀) :
    ∃ z : I → Ω, (∀ i, good i (z i)) ∧ ∀ t, ∑ i, f t i (z i) ≤ m t / (1 - ρ) +
      K₄ * (Real.sqrt (R₀ / (1 - ρ) * Real.log (max 2 (max (R₀ / (1 - ρ)) D₀) + 2)) +
        Real.log (max 2 (max (R₀ / (1 - ρ)) D₀) + 2)) := by
  classical
  have h1ρ : 0 < 1 - ρ := by linarith
  -- the conditioned distributions
  let Z : I → ℝ := fun i => ∑ ω ∈ Finset.univ.filter (good i), π i ω
  have hZ : ∀ i, 1 - ρ ≤ Z i := hgood
  have hZpos : ∀ i, 0 < Z i := fun i => lt_of_lt_of_le h1ρ (hZ i)
  let Ω' : I → Type := fun i => {ω : Ω // good i ω}
  let p : ∀ i, Ω' i → ℝ := fun i ω => π i ω.1 / Z i
  let f' : T → ∀ i, Ω' i → ℝ := fun t i ω => f t i ω.1
  have hsub : ∀ i (F : Ω → ℝ), ∑ ω : Ω' i, F ω.1 = ∑ ω ∈ Finset.univ.filter (good i), F ω := by
    intro i F
    exact (Finset.sum_subtype (Finset.univ.filter (good i)) (by simp) F).symm
  have hp : ∀ i ω, 0 < p i ω := fun i ω => div_pos (hπ i ω.1) (hZpos i)
  have hp1 : ∀ i, ∑ ω, p i ω = 1 := by
    intro i
    simp only [p]
    rw [← Finset.sum_div, hsub i (fun ω => π i ω)]
    exact div_self (hZpos i).ne'
  have hmean : ∀ t, ∑ i, ∑ ω, p i ω * f' t i ω ≤ m t / (1 - ρ) := by
    intro t
    have : ∀ i, ∑ ω, p i ω * f' t i ω ≤ (∑ ω, π i ω * f t i ω) / (1 - ρ) := by
      intro i
      simp only [p, f']
      rw [hsub i (fun ω => π i ω / Z i * f t i ω)]
      calc ∑ ω ∈ Finset.univ.filter (good i), π i ω / Z i * f t i ω
          = (∑ ω ∈ Finset.univ.filter (good i), π i ω * f t i ω) / Z i := by
            rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro ω _; ring
        _ ≤ (∑ ω, π i ω * f t i ω) / Z i := by
            apply div_le_div_of_nonneg_right _ (hZpos i).le
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun ω _ _ => mul_nonneg (hπ i ω).le (hf t i ω).1)
        _ ≤ (∑ ω, π i ω * f t i ω) / (1 - ρ) := by
            apply div_le_div_of_nonneg_left _ h1ρ (hZ i)
            exact Finset.sum_nonneg (fun ω _ => mul_nonneg (hπ i ω).le (hf t i ω).1)
    calc ∑ i, ∑ ω, p i ω * f' t i ω ≤ ∑ i, (∑ ω, π i ω * f t i ω) / (1 - ρ) :=
          Finset.sum_le_sum (fun i _ => this i)
      _ = (∑ i, ∑ ω, π i ω * f t i ω) / (1 - ρ) := by rw [Finset.sum_div]
      _ ≤ m t / (1 - ρ) := div_le_div_of_nonneg_right (hm t) h1ρ.le
  obtain ⟨z, hz⟩ := hK₄ I T Ω' p f' (R₀ / (1 - ρ)) D₀ hp hp1
    (fun t i ω => hf t i ω.1)
    (fun t => le_trans (hmean t) (div_le_div_of_nonneg_right (hmR t) h1ρ.le))
    (fun i ω => hD i ω.1)
  refine ⟨fun i => (z i).1, fun i => (z i).2, fun t => ?_⟩
  have := hz t
  have h2 := hmean t
  simp only [f'] at this h2 ⊢
  linarith

end WECA4

open WeightedEdgeColor WeightedEdgeColor.WGraph

theorem pc_oriented (C₀ C₁ θ σ r₀ β : ℝ) (M Ks r : ℕ)
    (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) (hθ : 0 < θ) (hσ0 : 0 < σ) (hσ1 : σ < 1) (hr₀ : 0 < r₀)
    (hβ : 0 < β) :
    ∃ n₀ K : ℝ, ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      (G : WGraph V E), G.IsSimple → ∀ g : V → Fin r,
      (∀ (e : E) (u v : V), G.ends e = s(u, v) → g u ≠ g v) →
      ∀ (src tgt : E → V), (∀ e, G.ends e = s(src e, tgt e)) → (∀ e, g (src e) < g (tgt e)) →
      ∀ n : ℝ, n₀ ≤ n → (∀ v, G.W v ≤ n) →
      ∀ (𝒞 : Type) [Fintype 𝒞] [DecidableEq 𝒞], (Fintype.card 𝒞 : ℝ) ≤ C₁ * n →
      ∀ (y : E → 𝒞 → ℝ) (lam : V → 𝒞 → Fin M → ℝ) (R : V → 𝒞 → Fin M → ℝ)
        (aL : V → 𝒞 → E → Fin M → Fin Ks → ℝ) (aS : V → 𝒞 → E → Fin M → ℝ),
      (∀ e c, 0 ≤ y e c ∧ y e c ≤ C₀ / n) →
      (∀ v c P, θ / M ≤ lam v c P) → (∀ v c, ∑ P, lam v c P = 1) →
      (∀ v c P, R v c P = 0 ∨ r₀ ≤ R v c P) →
      (∀ v c e P i, 0 ≤ aL v c e P i) → (∀ v c e P, 0 ≤ aS v c e P) →
      (∀ v c e P, aS v c e P ≠ 0 → 0 < R v c P) →
      -- every edge is either large (slot fractions only) or small (reserve fractions only)
      (∀ v c e P i, aL v c e P i ≠ 0 → β ≤ G.w e) → (∀ v c e P, aS v c e P ≠ 0 → G.w e < β) →
      -- the fractions of `e` at each of its ends add up to `y e c`
      (∀ v c e, v ∈ G.ends e → ∑ P, (∑ i, aL v c e P i + aS v c e P) = y e c) →
      -- capacities hold in expectation, with slack `σ`
      (∀ v c P i, ∑ e ∈ G.inc v, aL v c e P i ≤ (1 - σ) * lam v c P) →
      (∀ v c P, ∑ e ∈ G.inc v, G.w e * aS v c e P ≤ (1 - σ) * lam v c P * R v c P) →
      ∃ Pc : V → 𝒞 → Fin M, ∀ (XL : E → 𝒞 → Fin Ks → Fin Ks → ℝ) (XS : E → 𝒞 → ℝ),
        (∀ e c i j, XL e c i j = aL (src e) c e (Pc (src e) c) i * aL (tgt e) c e (Pc (tgt e) c) j /
            (y e c * lam (src e) c (Pc (src e) c) * lam (tgt e) c (Pc (tgt e) c))) →
        (∀ e c, XS e c = aS (src e) c e (Pc (src e) c) * aS (tgt e) c e (Pc (tgt e) c) /
            (y e c * lam (src e) c (Pc (src e) c) * lam (tgt e) c (Pc (tgt e) c))) →
        -- every slot of a chosen profile keeps slack `σ / 2`
        (∀ v c i, ∑ e ∈ Finset.univ.filter (fun e => src e = v), ∑ j, XL e c i j
           + ∑ e ∈ Finset.univ.filter (fun e => tgt e = v), ∑ j, XL e c j i ≤ 1 - σ / 2) ∧
        (∀ v c, ∑ e ∈ G.inc v, G.w e * XS e c ≤ (1 - σ / 2) * R v c (Pc v c)) ∧
        -- small weighted discrepancy at every vertex
        ∀ v, ∑ e ∈ G.inc v, G.w e *
          |∑ c, (∑ i, ∑ j, XL e c i j + XS e c) - ∑ c, y e c| ≤ K * n ^ (3 / 4 : ℝ) := by
  classical
  obtain ⟨K₄, hK₄⟩ := proposition_A_4
  obtain ⟨Mθ, hMθ⟩ : ∃ x : ℝ, x = (M : ℝ) / θ := ⟨_, rfl⟩
  have hMθ0 : 0 ≤ Mθ := by rw [hMθ]; positivity
  obtain ⟨κ, hκ⟩ : ∃ x : ℝ, x = C₀ * Mθ ^ 2 := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
  obtain ⟨κ₁, hκ₁⟩ : ∃ x : ℝ, x = κ * Mθ * (C₀ * C₁) + C₀ * Mθ * (C₀ * C₁) + 1 := ⟨_, rfl⟩
  have hκ₁0 : 0 < κ₁ := by rw [hκ₁]; positivity
  obtain ⟨Bd, hBd⟩ : ∃ x : ℝ, x = 2 * (C₀ * C₁ * Mθ ^ 2 + C₀ * C₁) + 1 := ⟨_, rfl⟩
  have hBd0 : 0 < Bd := by rw [hBd]; positivity
  -- asymptotic constants
  obtain ⟨cR, hcR⟩ : ∃ x : ℝ, x = 2 + r₀ + Real.sqrt κ₁ := ⟨_, rfl⟩
  have hcR0 : 0 < cR := by rw [hcR]; positivity
  obtain ⟨cD, hcD⟩ : ∃ x : ℝ, x = C₁ * M * (1 / β + 1) + 1 := ⟨_, rfl⟩
  have hcD0 : 0 < cD := by rw [hcD]; positivity
  obtain ⟨cE, hcE⟩ : ∃ x : ℝ, x = |K₄| * (Real.sqrt (2 * cR * (8 * (2 * cR + cD + 4) ^ (1 / 8 : ℝ))) +
      8 * (2 * cR + cD + 4) ^ (1 / 8 : ℝ)) := ⟨_, rfl⟩
  have hcE0 : 0 ≤ cE := by rw [hcE]; positivity
  obtain ⟨Tn, hTn⟩ : ∃ x : ℝ, x = 16 * Real.sqrt κ₁ / σ + 8 * r * cE * (κ + 1) / σ +
      8 * r * cE * (κ + 1) / (σ * r₀) + 1 := ⟨_, rfl⟩
  have hTn1 : 1 ≤ Tn := by
    have h0 : 0 ≤ 16 * Real.sqrt κ₁ / σ + 8 * r * cE * (κ + 1) / σ +
        8 * r * cE * (κ + 1) / (σ * r₀) := by positivity
    rw [hTn]; linarith
  refine ⟨Tn ^ 4, 2 + 2 * Real.sqrt κ₁ + r * cE * Bd, ?_⟩
  intro V E _ _ _ _ G hG g hg src tgt hst hor n hn hW 𝒞 _ _ hcard y lam R aL aS hy hlamlo hlam1 hR
    haL0 haS0 haSR htypL htypS hmarg hcapL hcapS
  have hn1 : 1 ≤ n := le_trans (one_le_pow₀ hTn1) hn
  have hn0 : 0 < n := by linarith
  have hn14 : Tn ≤ n ^ (1 / 4 : ℝ) := by
    have h := Real.rpow_le_rpow (by positivity) hn (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have e : (Tn ^ 4) ^ (1 / 4 : ℝ) = Tn := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
    rwa [e] at h
  have hn14pos : 0 < n ^ (1 / 4 : ℝ) := by positivity
  -- basic facts about the data
  have hMpos : ∀ (v : V) (c : 𝒞), (0 : ℝ) < M := by
    intro v c
    have := hlam1 v c
    rcases Nat.eq_zero_or_pos M with h0 | h0
    · subst h0; simp at this
    · exact_mod_cast h0
  have hlampos : ∀ v c P, 0 < lam v c P := fun v c P =>
    lt_of_lt_of_le (div_pos hθ (hMpos v c)) (hlamlo v c P)
  have hysum : ∀ e, ∑ c, y e c ≤ C₀ * C₁ := by
    intro e
    calc ∑ c, y e c ≤ ∑ _c : 𝒞, C₀ / n := Finset.sum_le_sum (fun c _ => (hy e c).2)
      _ = Fintype.card 𝒞 * (C₀ / n) := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      _ ≤ C₁ * n * (C₀ / n) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = C₀ * C₁ := by field_simp
  have hsrc_mem : ∀ e, src e ∈ G.ends e := fun e => by rw [hst e]; exact Sym2.mem_mk_left _ _
  have htgt_mem : ∀ e, tgt e ∈ G.ends e := fun e => by rw [hst e]; exact Sym2.mem_mk_right _ _
  -- the total fraction at an end and a label is at most `y`
  have hAt : ∀ v c e, v ∈ G.ends e → ∀ P, WECEdge.At (fun P i => aL v c e P i) (fun P => aS v c e P) P ≤ y e c := by
    intro v c e hv P
    rw [← hmarg v c e hv]
    exact Finset.single_le_sum (f := fun P => ∑ i, aL v c e P i + aS v c e P)
      (fun P _ => add_nonneg (Finset.sum_nonneg (fun i _ => haL0 v c e P i)) (haS0 v c e P))
      (Finset.mem_univ P)
  -- the coupled fractions
  obtain ⟨X, hX⟩ : ∃ X : E → 𝒞 → Fin M → Fin M → ℝ, ∀ e c P Q, X e c P Q =
      WECEdge.Xc (fun P i => aL (src e) c e P i) (fun P j => aL (tgt e) c e P j)
        (fun P => aS (src e) c e P) (fun P => aS (tgt e) c e P) (lam (src e) c) (lam (tgt e) c)
        (y e c) P Q := ⟨_, fun _ _ _ _ => rfl⟩
  have hX0 : ∀ e c P Q, 0 ≤ X e c P Q := fun e c P Q => by
    rw [hX]; exact WECEdge.Xc_nonneg _ _ _ _ _ _ _ (fun P i => haL0 _ _ _ P i) (fun P i => haL0 _ _ _ P i)
      (fun P => haS0 _ _ _ P) (fun P => haS0 _ _ _ P) (fun P => hlampos _ _ P) (fun P => hlampos _ _ P)
      (hy e c).1 P Q
  have hXle : ∀ e c P Q, X e c P Q ≤ y e c * Mθ ^ 2 := fun e c P Q => by
    rw [hX, hMθ]
    exact WECEdge.Xc_le _ _ _ _ _ _ _ θ (fun P i => haL0 _ _ _ P i) (fun P i => haL0 _ _ _ P i)
      (fun P => haS0 _ _ _ P) (fun P => haS0 _ _ _ P) hθ (fun P => hlamlo _ _ P) (fun P => hlamlo _ _ P)
      (hy e c).1 (hAt _ c e (hsrc_mem e)) (hAt _ c e (htgt_mem e)) (hMpos (src e) c) P Q
  have hXκ : ∀ e c P Q, X e c P Q ≤ κ / n := fun e c P Q => by
    refine le_trans (hXle e c P Q) ?_
    rw [hκ, show C₀ * Mθ ^ 2 / n = C₀ / n * Mθ ^ 2 by ring]
    exact mul_le_mul_of_nonneg_right (hy e c).2 (by positivity)
  -- conditional means of the coupled fractions
  have hXmt : ∀ e c P, ∑ Q, lam (tgt e) c Q * X e c P Q ≤ y e c * Mθ := by
    intro e c P
    simp_rw [hX]; rw [hMθ]
    exact WECEdge.Xc_mean_le _ _ _ _ _ _ _ θ (fun P i => haL0 _ _ _ P i) (fun P i => haL0 _ _ _ P i)
      (fun P => haS0 _ _ _ P) (fun P => haS0 _ _ _ P) hθ (hMpos (src e) c) (fun P => hlamlo _ _ P)
      (fun P => hlampos _ _ P) (hy e c).1 (hAt _ c e (hsrc_mem e)) (hmarg _ c e (htgt_mem e)) P
  have hXms : ∀ e c Q, ∑ P, lam (src e) c P * X e c P Q ≤ y e c * Mθ := by
    intro e c Q
    have hsw : ∀ P, X e c P Q = WECEdge.Xc (fun P j => aL (tgt e) c e P j) (fun P i => aL (src e) c e P i)
        (fun P => aS (tgt e) c e P) (fun P => aS (src e) c e P) (lam (tgt e) c) (lam (src e) c)
        (y e c) Q P := fun P => by rw [hX, WECEdge.Xc_swap]
    simp_rw [hsw]; rw [hMθ]
    exact WECEdge.Xc_mean_le _ _ _ _ _ _ _ θ (fun P i => haL0 _ _ _ P i) (fun P i => haL0 _ _ _ P i)
      (fun P => haS0 _ _ _ P) (fun P => haS0 _ _ _ P) hθ (hMpos (src e) c) (fun P => hlamlo _ _ P)
      (fun P => hlampos _ _ P) (hy e c).1 (hAt _ c e (htgt_mem e)) (hmarg _ c e (hsrc_mem e)) Q
  -- the exact mean (here the large/small typing is used)
  have hXmean : ∀ e c, ∑ P, lam (src e) c P * ∑ Q, lam (tgt e) c Q * X e c P Q = y e c := by
    intro e c
    rcases (hy e c).1.lt_or_eq with hy0 | hy0
    · have h1 : ∀ P, ∑ Q, lam (tgt e) c Q * X e c P Q = ((∑ i, aL (src e) c e P i) *
          (∑ P', ∑ j, aL (tgt e) c e P' j) + aS (src e) c e P * (∑ P', aS (tgt e) c e P')) /
          (y e c * lam (src e) c P) := by
        intro P; simp_rw [hX]
        exact WECEdge.Xc_mean_t _ _ _ _ _ _ _ (fun Q => hlampos _ _ Q) hy0 (hmarg _ c e (htgt_mem e)) P
      simp_rw [h1]
      have h2 : ∀ P, lam (src e) c P * (((∑ i, aL (src e) c e P i) * (∑ P', ∑ j, aL (tgt e) c e P' j) +
          aS (src e) c e P * (∑ P', aS (tgt e) c e P')) / (y e c * lam (src e) c P))
          = ((∑ i, aL (src e) c e P i) * (∑ P', ∑ j, aL (tgt e) c e P' j) +
          aS (src e) c e P * (∑ P', aS (tgt e) c e P')) / y e c := by
        intro P; have := hlampos (src e) c P; field_simp
      simp_rw [h2]
      rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
      have hms := hmarg _ c e (hsrc_mem e)
      have hmt := hmarg _ c e (htgt_mem e)
      simp only [Finset.sum_add_distrib] at hms hmt
      by_cases hl : β ≤ G.w e
      · have z1 : ∀ v P, aS v c e P = 0 := fun v P => by
          by_contra h; exact absurd (htypS v c e P h) (not_lt.mpr hl)
        simp only [z1, Finset.sum_const_zero, add_zero] at hms hmt ⊢
        rw [hms, hmt]; field_simp; ring
      · have z1 : ∀ v P i, aL v c e P i = 0 := fun v P i => by
          by_contra h; exact hl (htypL v c e P i h)
        simp only [z1, Finset.sum_const_zero, zero_add] at hms hmt ⊢
        rw [hms, hmt]; field_simp; ring
    · have : ∀ P Q, X e c P Q = 0 := fun P Q => by rw [hX]; unfold WECEdge.Xc; rw [← hy0]; simp
      simp [this, ← hy0]
  -- totals over all colors
  let π : V → (𝒞 → Fin M) → ℝ := fun v L => WECProb.pw (lam v) L
  have hπ0 : ∀ v L, 0 < π v L := fun v L => Finset.prod_pos (fun c _ => hlampos v c (L c))
  have hπ1 : ∀ v, ∑ L, π v L = 1 := fun v => WECProb.pw_sum (lam v) (hlam1 v)
  obtain ⟨Se, hSe⟩ : ∃ F : E → (𝒞 → Fin M) → (𝒞 → Fin M) → ℝ, ∀ e Ls Lt,
      F e Ls Lt = ∑ c, X e c (Ls c) (Lt c) := ⟨_, fun _ _ _ => rfl⟩
  obtain ⟨ms, hms⟩ : ∃ F : E → (𝒞 → Fin M) → ℝ, ∀ e Ls,
      F e Ls = ∑ c, ∑ Q, lam (tgt e) c Q * X e c (Ls c) Q := ⟨_, fun _ _ => rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ F : E → ℝ, ∀ e, F e = ∑ c, y e c := ⟨_, fun _ => rfl⟩
  have hms_mean : ∀ e Ls, ∑ Lt, π (tgt e) Lt * Se e Ls Lt = ms e Ls := by
    intro e Ls
    simp only [hSe, hms, π]
    exact WECProb.pw_sum_fun (lam (tgt e)) (hlam1 _) (fun c m => X e c (Ls c) m)
  have hVar1 : ∀ e Ls, ∑ Lt, π (tgt e) Lt * (Se e Ls Lt - ms e Ls) ^ 2 ≤ κ₁ / n := by
    intro e Ls
    simp only [hSe, hms, π]
    rw [WECProb.pw_var (lam (tgt e)) (hlam1 _) (fun c m => X e c (Ls c) m)]
    calc ∑ c, ∑ m, lam (tgt e) c m * (X e c (Ls c) m - ∑ m', lam (tgt e) c m' * X e c (Ls c) m') ^ 2
        ≤ ∑ c, κ / n * ∑ m', lam (tgt e) c m' * X e c (Ls c) m' :=
          Finset.sum_le_sum (fun c _ => WECProb.var_le _ _ _ (fun m => (hlampos _ _ m).le) (hlam1 _ c)
            (fun m => hX0 _ _ _ _) (fun m => hXκ _ _ _ _))
      _ ≤ ∑ c, κ / n * (y e c * Mθ) :=
          Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left (hXmt e c (Ls c)) (by positivity))
      _ = κ / n * Mθ * ∑ c, y e c := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro c _; ring
      _ ≤ κ / n * Mθ * (C₀ * C₁) := mul_le_mul_of_nonneg_left (hysum e) (by positivity)
      _ ≤ κ₁ / n := by
          rw [hκ₁, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hn0]
          have : 0 ≤ C₀ * Mθ * (C₀ * C₁) := by positivity
          linarith
  have hVar2 : ∀ e, ∑ Ls, π (src e) Ls * (ms e Ls - μ e) ^ 2 ≤ κ₁ / n := by
    intro e
    have hmean : μ e = ∑ c, ∑ m, lam (src e) c m * ∑ Q, lam (tgt e) c Q * X e c m Q := by
      rw [hμ]; apply Finset.sum_congr rfl; intro c _; rw [hXmean]
    simp only [hms, π]
    rw [hmean, WECProb.pw_var (lam (src e)) (hlam1 _) (fun c m => ∑ Q, lam (tgt e) c Q * X e c m Q)]
    have hb : ∀ c m, ∑ Q, lam (tgt e) c Q * X e c m Q ≤ C₀ / n * Mθ := fun c m =>
      le_trans (hXmt e c m) (mul_le_mul_of_nonneg_right (hy e c).2 hMθ0)
    have hb0 : ∀ c m, 0 ≤ ∑ Q, lam (tgt e) c Q * X e c m Q := fun c m =>
      Finset.sum_nonneg (fun Q _ => mul_nonneg (hlampos _ _ Q).le (hX0 _ _ _ _))
    calc ∑ c, ∑ m, lam (src e) c m * (∑ Q, lam (tgt e) c Q * X e c m Q -
          ∑ m', lam (src e) c m' * ∑ Q, lam (tgt e) c Q * X e c m' Q) ^ 2
        ≤ ∑ c, C₀ / n * Mθ * ∑ m', lam (src e) c m' * ∑ Q, lam (tgt e) c Q * X e c m' Q :=
          Finset.sum_le_sum (fun c _ => WECProb.var_le _ _ _ (fun m => (hlampos _ _ m).le) (hlam1 _ c)
            (hb0 c) (hb c))
      _ = C₀ / n * Mθ * ∑ c, y e c := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro c _; rw [hXmean]
      _ ≤ C₀ / n * Mθ * (C₀ * C₁) := mul_le_mul_of_nonneg_left (hysum e) (by positivity)
      _ ≤ κ₁ / n := by
          rw [hκ₁, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hn0]
          have : 0 ≤ κ * Mθ * (C₀ * C₁) := by positivity
          linarith
  -- expected absolute deviations
  have hκn : 0 ≤ κ₁ / n := by positivity
  have hE1 : ∀ e Ls, ∑ Lt, π (tgt e) Lt * |Se e Ls Lt - ms e Ls| ≤ Real.sqrt (κ₁ / n) := fun e Ls =>
    le_trans (WECProb.exp_abs_le_sqrt _ _ (fun L => (hπ0 _ L).le) (hπ1 _))
      (Real.sqrt_le_sqrt (hVar1 e Ls))
  have hE2 : ∀ e, ∑ Ls, π (src e) Ls * |ms e Ls - μ e| ≤ Real.sqrt (κ₁ / n) := fun e =>
    le_trans (WECProb.exp_abs_le_sqrt _ _ (fun L => (hπ0 _ L).le) (hπ1 _))
      (Real.sqrt_le_sqrt (hVar2 e))
  -- sizes
  have hSe0 : ∀ e Ls Lt, 0 ≤ Se e Ls Lt := fun e Ls Lt => by
    rw [hSe]; exact Finset.sum_nonneg (fun c _ => hX0 _ _ _ _)
  have hSe1 : ∀ e Ls Lt, Se e Ls Lt ≤ C₀ * C₁ * Mθ ^ 2 := fun e Ls Lt => by
    rw [hSe]
    calc ∑ c, X e c (Ls c) (Lt c) ≤ ∑ c, y e c * Mθ ^ 2 := Finset.sum_le_sum (fun c _ => hXle _ _ _ _)
      _ = (∑ c, y e c) * Mθ ^ 2 := by rw [Finset.sum_mul]
      _ ≤ C₀ * C₁ * Mθ ^ 2 := mul_le_mul_of_nonneg_right (hysum e) (by positivity)
  have hms0 : ∀ e Ls, 0 ≤ ms e Ls := fun e Ls => by
    rw [hms]; exact Finset.sum_nonneg (fun c _ => Finset.sum_nonneg (fun Q _ =>
      mul_nonneg (hlampos _ _ Q).le (hX0 _ _ _ _)))
  have hms1 : ∀ e Ls, ms e Ls ≤ C₀ * C₁ * Mθ ^ 2 := fun e Ls => by
    rw [← hms_mean e Ls]
    calc ∑ Lt, π (tgt e) Lt * Se e Ls Lt ≤ ∑ Lt, π (tgt e) Lt * (C₀ * C₁ * Mθ ^ 2) :=
          Finset.sum_le_sum (fun Lt _ => mul_le_mul_of_nonneg_left (hSe1 _ _ _) (hπ0 _ _).le)
      _ = C₀ * C₁ * Mθ ^ 2 := by rw [← Finset.sum_mul, hπ1, one_mul]
  have hμ0 : ∀ e, 0 ≤ μ e := fun e => by rw [hμ]; exact Finset.sum_nonneg (fun c _ => (hy e c).1)
  have hμ1 : ∀ e, μ e ≤ C₀ * C₁ := fun e => by rw [hμ]; exact hysum e
  have hdisc1 : ∀ e Ls Lt, |Se e Ls Lt - ms e Ls| ≤ Bd := fun e Ls Lt => by
    rw [abs_le, hBd]
    have := hSe0 e Ls Lt; have := hSe1 e Ls Lt; have := hms0 e Ls; have := hms1 e Ls
    have : 0 ≤ C₀ * C₁ := by positivity
    constructor <;> linarith
  have hdisc2 : ∀ e Ls, |ms e Ls - μ e| ≤ Bd := fun e Ls => by
    rw [abs_le, hBd]
    have := hms0 e Ls; have := hms1 e Ls; have := hμ0 e; have := hμ1 e
    have : 0 ≤ C₀ * C₁ * Mθ ^ 2 := by positivity
    constructor <;> linarith
  -- the rejection threshold and probability
  obtain ⟨t, ht⟩ : ∃ x : ℝ, x = n ^ (3 / 4 : ℝ) := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [ht]; positivity
  obtain ⟨ρ, hρ⟩ : ∃ x : ℝ, x = 2 * Real.sqrt κ₁ / n ^ (1 / 4 : ℝ) := ⟨_, rfl⟩
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hρσ : ρ ≤ σ / 8 := by
    rw [hρ, div_le_iff₀ hn14pos]
    have h1 : 16 * Real.sqrt κ₁ / σ ≤ n ^ (1 / 4 : ℝ) := by
      refine le_trans ?_ hn14
      rw [hTn]
      have : 0 ≤ 8 * r * cE * (κ + 1) / σ + 8 * r * cE * (κ + 1) / (σ * r₀) := by positivity
      linarith
    rw [div_le_iff₀ hσ0] at h1
    linarith
  have hρ1 : ρ < 1 := by linarith
  -- the key scale relation: `√(n κ₁) / t = ρ / 2`
  have hsqrt_t : n * Real.sqrt (κ₁ / n) / t = ρ / 2 := by
    obtain ⟨a, ha⟩ : ∃ a : ℝ, a = n ^ (1 / 4 : ℝ) := ⟨_, rfl⟩
    have ha0 : 0 < a := by rw [ha]; exact hn14pos
    have h4 : a ^ 4 = n := by
      rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; norm_num
    have h2 : Real.sqrt n = a ^ 2 := by
      rw [← h4, show a ^ 4 = (a ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    have h3 : n ^ (3 / 4 : ℝ) = a ^ 3 := by
      rw [← h4, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
    rw [ht, hρ, Real.sqrt_div' _ hn0.le, h2, h3, ← ha, ← h4]
    field_simp
  -- the vertex's own conditions
  obtain ⟨O1, hO1⟩ : ∃ F : V → (𝒞 → Fin M) → ℝ, ∀ u L,
      F u L = ∑ e ∈ Finset.univ.filter (fun e => src e = u), G.w e * |ms e L - μ e| :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨O2, hO2⟩ : ∃ F : (V → 𝒞 → Fin M) → V → (𝒞 → Fin M) → ℝ, ∀ Pp u L,
      F Pp u L = ∑ e ∈ Finset.univ.filter (fun e => tgt e = u),
        G.w e * |Se e (Pp (src e)) L - ms e (Pp (src e))| := ⟨_, fun _ _ _ => rfl⟩
  have hWsrc : ∀ u, ∑ e ∈ Finset.univ.filter (fun e => src e = u), G.w e ≤ n := by
    intro u
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun e _ _ => (G.w_pos e).le)) (hW u)
    intro e he
    simp only [Finset.mem_filter] at he
    simp only [WGraph.inc, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← he.2]; exact hsrc_mem e
  have hWtgt : ∀ u, ∑ e ∈ Finset.univ.filter (fun e => tgt e = u), G.w e ≤ n := by
    intro u
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun e _ _ => (G.w_pos e).le)) (hW u)
    intro e he
    simp only [Finset.mem_filter] at he
    simp only [WGraph.inc, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← he.2]; exact htgt_mem e
  have hO1mean : ∀ u, ∑ L, π u L * O1 u L ≤ n * Real.sqrt (κ₁ / n) := by
    intro u
    simp_rw [hO1, Finset.mul_sum]
    rw [Finset.sum_comm]
    calc ∑ e ∈ Finset.univ.filter (fun e => src e = u), ∑ L, π u L * (G.w e * |ms e L - μ e|)
        ≤ ∑ e ∈ Finset.univ.filter (fun e => src e = u), G.w e * Real.sqrt (κ₁ / n) := by
          apply Finset.sum_le_sum; intro e he
          have hsu : src e = u := (Finset.mem_filter.mp he).2
          have := hE2 e
          rw [hsu] at this
          calc ∑ L, π u L * (G.w e * |ms e L - μ e|) = G.w e * ∑ L, π u L * |ms e L - μ e| := by
                rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro L _; ring
            _ ≤ G.w e * Real.sqrt (κ₁ / n) := mul_le_mul_of_nonneg_left this (G.w_pos e).le
      _ = (∑ e ∈ Finset.univ.filter (fun e => src e = u), G.w e) * Real.sqrt (κ₁ / n) := by
          rw [Finset.sum_mul]
      _ ≤ n * Real.sqrt (κ₁ / n) := mul_le_mul_of_nonneg_right (hWsrc u) (Real.sqrt_nonneg _)
  have hO2mean : ∀ Pp u, ∑ L, π u L * O2 Pp u L ≤ n * Real.sqrt (κ₁ / n) := by
    intro Pp u
    simp_rw [hO2, Finset.mul_sum]
    rw [Finset.sum_comm]
    calc ∑ e ∈ Finset.univ.filter (fun e => tgt e = u),
          ∑ L, π u L * (G.w e * |Se e (Pp (src e)) L - ms e (Pp (src e))|)
        ≤ ∑ e ∈ Finset.univ.filter (fun e => tgt e = u), G.w e * Real.sqrt (κ₁ / n) := by
          apply Finset.sum_le_sum; intro e he
          have htu : tgt e = u := (Finset.mem_filter.mp he).2
          have := hE1 e (Pp (src e))
          rw [htu] at this
          calc ∑ L, π u L * (G.w e * |Se e (Pp (src e)) L - ms e (Pp (src e))|)
              = G.w e * ∑ L, π u L * |Se e (Pp (src e)) L - ms e (Pp (src e))| := by
                rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro L _; ring
            _ ≤ G.w e * Real.sqrt (κ₁ / n) := mul_le_mul_of_nonneg_left this (G.w_pos e).le
      _ = (∑ e ∈ Finset.univ.filter (fun e => tgt e = u), G.w e) * Real.sqrt (κ₁ / n) := by
          rw [Finset.sum_mul]
      _ ≤ n * Real.sqrt (κ₁ / n) := mul_le_mul_of_nonneg_right (hWtgt u) (Real.sqrt_nonneg _)
  have hO10 : ∀ u L, 0 ≤ O1 u L := fun u L => by
    rw [hO1]; exact Finset.sum_nonneg (fun e _ => mul_nonneg (G.w_pos e).le (abs_nonneg _))
  have hO20 : ∀ Pp u L, 0 ≤ O2 Pp u L := fun Pp u L => by
    rw [hO2]; exact Finset.sum_nonneg (fun e _ => mul_nonneg (G.w_pos e).le (abs_nonneg _))
  have hgood : ∀ Pp u, 1 - ρ ≤ ∑ L ∈ Finset.univ.filter (fun L => O1 u L ≤ t ∧ O2 Pp u L ≤ t), π u L := by
    intro Pp u
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun L => O1 u L ≤ t ∧ O2 Pp u L ≤ t) (π u)
    rw [hπ1] at hsplit
    have hbad : ∑ L ∈ Finset.univ.filter (fun L => ¬ (O1 u L ≤ t ∧ O2 Pp u L ≤ t)), π u L ≤ ρ := by
      have h1 := WECProb.markov (π u) (O1 u) (fun L => (hπ0 u L).le) (hO10 u) t ht0
      have h2 := WECProb.markov (π u) (O2 Pp u) (fun L => (hπ0 u L).le) (hO20 Pp u) t ht0
      have h1' : (∑ L, π u L * O1 u L) / t ≤ ρ / 2 := by
        rw [← hsqrt_t]; exact div_le_div_of_nonneg_right (hO1mean u) ht0.le
      have h2' : (∑ L, π u L * O2 Pp u L) / t ≤ ρ / 2 := by
        rw [← hsqrt_t]; exact div_le_div_of_nonneg_right (hO2mean Pp u) ht0.le
      calc ∑ L ∈ Finset.univ.filter (fun L => ¬ (O1 u L ≤ t ∧ O2 Pp u L ≤ t)), π u L
          ≤ ∑ L ∈ Finset.univ.filter (fun L => t < O1 u L) ∪ Finset.univ.filter (fun L => t < O2 Pp u L),
              π u L := by
            apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun L _ _ => (hπ0 u L).le)
            intro L hL
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, not_and_or,
              not_le] at hL ⊢
            exact hL
        _ ≤ ∑ L ∈ Finset.univ.filter (fun L => t < O1 u L), π u L +
            ∑ L ∈ Finset.univ.filter (fun L => t < O2 Pp u L), π u L := by
            have hui := Finset.sum_union_inter (s₁ := Finset.univ.filter (fun L => t < O1 u L))
              (s₂ := Finset.univ.filter (fun L => t < O2 Pp u L)) (f := π u)
            have hint : 0 ≤ ∑ L ∈ Finset.univ.filter (fun L => t < O1 u L) ∩
                Finset.univ.filter (fun L => t < O2 Pp u L), π u L :=
              Finset.sum_nonneg (fun L _ => (hπ0 u L).le)
            linarith
        _ ≤ ρ := by linarith
    linarith
  -- the other endpoint
  let oth : E → V → V := fun e v => if src e = v then tgt e else src e
  have hst_ne : ∀ e, src e ≠ tgt e := fun e h => by
    have := G.loopless e; rw [hst e, Sym2.mk_isDiag_iff] at this; exact this h
  have hmem : ∀ e v, v ∈ G.ends e ↔ v = src e ∨ v = tgt e := fun e v => by rw [hst e, Sym2.mem_iff]
  have hoth_mem : ∀ e v, oth e v ∈ G.ends e := fun e v => by
    simp only [oth]; split_ifs
    · exact htgt_mem e
    · exact hsrc_mem e
  -- contributions to the places of a profile
  obtain ⟨cap, hcap⟩ : ∃ F : E → V → 𝒞 → Fin M → Option (Fin Ks) → Fin M → ℝ, ∀ e v c P' pl P'',
      F e v c P' pl P'' = pl.elim (G.w e) (fun _ => 1) *
        WECEdge.capg (pl.elim (aS v c e P') (fun i => aL v c e P' i)) (lam v c P') (y e c)
          (fun Q => pl.elim (aS (oth e v) c e Q) (fun _ => ∑ j, aL (oth e v) c e Q j))
          (lam (oth e v) c) P'' := ⟨_, fun _ _ _ _ _ _ => rfl⟩
  have hcap0 : ∀ e v c P' pl P'', 0 ≤ cap e v c P' pl P'' := by
    intro e v c P' pl P''
    rw [hcap]
    cases pl with
    | none =>
      exact mul_nonneg (G.w_pos e).le (WECEdge.capg_nonneg _ _ _ _ _ _ (haS0 _ _ _ _)
        (hlampos _ _ _).le (hy e c).1 (haS0 _ _ _ _) (hlampos _ _ _).le)
    | some i =>
      simp only [Option.elim, one_mul]
      exact WECEdge.capg_nonneg _ _ _ _ _ _ (haL0 _ _ _ _ _)
        (hlampos _ _ _).le (hy e c).1 (Finset.sum_nonneg (fun j _ => haL0 _ _ _ _ j)) (hlampos _ _ _).le
  have hySum_le : ∀ v c e, v ∈ G.ends e → ∀ P', ∑ i, aL v c e P' i ≤ y e c := fun v c e hv P' =>
    le_trans (le_add_of_nonneg_right (haS0 v c e P')) (hAt v c e hv P')
  have hySS_le : ∀ v c e, v ∈ G.ends e → ∀ P', aS v c e P' ≤ y e c := fun v c e hv P' =>
    le_trans (le_add_of_nonneg_left (Finset.sum_nonneg (fun i _ => haL0 v c e P' i))) (hAt v c e hv P')
  have haL_le : ∀ v c e, v ∈ G.ends e → ∀ P' i, aL v c e P' i ≤ y e c := fun v c e hv P' i =>
    le_trans (Finset.single_le_sum (f := fun i => aL v c e P' i) (fun i _ => haL0 v c e P' i)
      (Finset.mem_univ i)) (hySum_le v c e hv P')
  have hyMθ : ∀ e c, y e c * Mθ ^ 2 ≤ κ / n := fun e c => by
    rw [hκ, show C₀ * Mθ ^ 2 / n = C₀ / n * Mθ ^ 2 by ring]
    exact mul_le_mul_of_nonneg_right (hy e c).2 (by positivity)
  have hcb1 : ∀ e v c P' i P'', v ∈ G.ends e → cap e v c P' (some i) P'' ≤ κ / n := by
    intro e v c P' i P'' hv
    rw [hcap]; simp only [Option.elim, one_mul]
    refine le_trans ?_ (hyMθ e c)
    rw [hMθ]
    exact WECEdge.capg_le _ _ _ θ _ _ _ hθ (hMpos v c) (haL0 _ _ _ _ _) (haL_le v c e hv P' i)
      (Finset.sum_nonneg (fun j _ => haL0 _ _ _ _ j)) (hySum_le _ c e (hoth_mem e v) P'')
      (hlamlo v c P') (hlamlo _ c P'')
  have hcb2 : ∀ e v c P' P'', v ∈ G.ends e → cap e v c P' none P'' ≤ G.w e * (κ / n) := by
    intro e v c P' P'' hv
    rw [hcap]; simp only [Option.elim]
    apply mul_le_mul_of_nonneg_left _ (G.w_pos e).le
    refine le_trans ?_ (hyMθ e c)
    rw [hMθ]
    exact WECEdge.capg_le _ _ _ θ _ _ _ hθ (hMpos v c) (haS0 _ _ _ _) (hySS_le v c e hv P')
      (haS0 _ _ _ _) (hySS_le _ c e (hoth_mem e v) P'') (hlamlo v c P') (hlamlo _ c P'')
  have hcm1 : ∀ e v c P' i, v ∈ G.ends e →
      ∑ P'', lam (oth e v) c P'' * cap e v c P' (some i) P'' ≤ aL v c e P' i / lam v c P' := by
    intro e v c P' i hv
    simp_rw [hcap]; simp only [Option.elim, one_mul]
    apply WECEdge.capg_mean _ _ _ _ _ (haL0 _ _ _ _ _) (hlampos v c P') (hy e c).1
      (fun Q => Finset.sum_nonneg (fun j _ => haL0 _ _ _ _ j)) _ (fun Q => hlampos _ c Q)
    rw [← hmarg _ c e (hoth_mem e v)]
    exact Finset.sum_le_sum (fun Q _ => le_add_of_nonneg_right (haS0 _ _ _ _))
  have hcm2 : ∀ e v c P', v ∈ G.ends e →
      ∑ P'', lam (oth e v) c P'' * cap e v c P' none P'' ≤ G.w e * aS v c e P' / lam v c P' := by
    intro e v c P' hv
    simp_rw [hcap]; simp only [Option.elim]
    have h := WECEdge.capg_mean (aS v c e P') (lam v c P') (y e c) (fun Q => aS (oth e v) c e Q)
      (lam (oth e v) c) (haS0 _ _ _ _) (hlampos v c P') (hy e c).1 (fun Q => haS0 _ _ _ _) (by
        rw [← hmarg _ c e (hoth_mem e v)]
        exact Finset.sum_le_sum (fun Q _ => le_add_of_nonneg_left
          (Finset.sum_nonneg (fun j _ => haL0 _ _ _ _ j)))) (fun Q => hlampos _ c Q)
    calc ∑ P'', lam (oth e v) c P'' * (G.w e * WECEdge.capg (aS v c e P') (lam v c P') (y e c)
          (fun Q => aS (oth e v) c e Q) (lam (oth e v) c) P'')
        = G.w e * ∑ P'', lam (oth e v) c P'' * WECEdge.capg (aS v c e P') (lam v c P') (y e c)
          (fun Q => aS (oth e v) c e Q) (lam (oth e v) c) P'' := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro Q _; ring
      _ ≤ G.w e * (aS v c e P' / lam v c P') := mul_le_mul_of_nonneg_left h (G.w_pos e).le
      _ = G.w e * aS v c e P' / lam v c P' := by ring
  have hcs1 : ∀ e v c P'', v ∈ G.ends e →
      ∑ P', ∑ i, cap e v c P' (some i) P'' ≤ (if β ≤ G.w e then (M : ℝ) * (κ / n) else 0) := by
    intro e v c P'' hv
    split_ifs with hl
    · calc ∑ P', ∑ i, cap e v c P' (some i) P'' ≤ ∑ _P' : Fin M, κ / n := by
            apply Finset.sum_le_sum; intro P' _
            simp_rw [hcap]; simp only [Option.elim, one_mul]
            have : ∑ i, WECEdge.capg (aL v c e P' i) (lam v c P') (y e c)
                (fun Q => ∑ j, aL (oth e v) c e Q j) (lam (oth e v) c) P''
                = WECEdge.capg (∑ i, aL v c e P' i) (lam v c P') (y e c)
                (fun Q => ∑ j, aL (oth e v) c e Q j) (lam (oth e v) c) P'' := by
              unfold WECEdge.capg; rw [← Finset.sum_div, ← Finset.sum_mul]
            rw [this]
            refine le_trans ?_ (hyMθ e c)
            rw [hMθ]
            exact WECEdge.capg_le _ _ _ θ _ _ _ hθ (hMpos v c)
              (Finset.sum_nonneg (fun i _ => haL0 _ _ _ _ i)) (hySum_le v c e hv P')
              (Finset.sum_nonneg (fun j _ => haL0 _ _ _ _ j)) (hySum_le _ c e (hoth_mem e v) P'')
              (hlamlo v c P') (hlamlo _ c P'')
        _ = (M : ℝ) * (κ / n) := by simp
    · have hz : ∀ P' i, aL v c e P' i = 0 := fun P' i => by
        by_contra h; exact hl (htypL v c e P' i h)
      apply le_of_eq
      apply Finset.sum_eq_zero; intro P' _; apply Finset.sum_eq_zero; intro i _
      rw [hcap]; simp [Option.elim, WECEdge.capg, hz]
  have hcs2 : ∀ e v c P'', v ∈ G.ends e → ∑ P', cap e v c P' none P'' ≤ G.w e * ((M : ℝ) * (κ / n)) := by
    intro e v c P'' hv
    calc ∑ P', cap e v c P' none P'' ≤ ∑ _P' : Fin M, G.w e * (κ / n) :=
          Finset.sum_le_sum (fun P' _ => hcb2 e v c P' P'' hv)
      _ = G.w e * ((M : ℝ) * (κ / n)) := by simp; ring
  -- geometry of the other endpoint
  have hoth_ne : ∀ e v, v ∈ G.ends e → oth e v ≠ v := by
    intro e v hv h
    simp only [oth] at h
    split_ifs at h with hs
    · exact hst_ne e (hs.trans h.symm)
    · exact hs h
  have hends_oth : ∀ e v, v ∈ G.ends e → G.ends e = s(v, oth e v) := by
    intro e v hv
    simp only [oth]
    split_ifs with hs
    · rw [hst e, hs]
    · rcases (hmem e v).mp hv with h' | h'
      · exact absurd h'.symm hs
      · rw [hst e, h', Sym2.eq_swap]
  have hoth_oth : ∀ e v, v ∈ G.ends e → oth e (oth e v) = v := by
    intro e v hv
    simp only [oth]
    rcases (hmem e v).mp hv with h' | h'
    · rw [if_pos h'.symm, if_neg (hst_ne e)]; exact h'.symm
    · rw [if_neg (show ¬ src e = v by rw [h']; exact hst_ne e)]
      rw [if_pos rfl]; exact h'.symm
  have hinc : ∀ e v, e ∈ G.inc v ↔ v ∈ G.ends e := fun e v => by simp [WGraph.inc]
  -- at most one edge joins two vertices
  have huniq : ∀ v u e e', e ∈ G.inc v → e' ∈ G.inc v → oth e v = u → oth e' v = u → e = e' := by
    intro v u e e' he he' h1 h2
    apply hG
    rw [hends_oth e v ((hinc e v).mp he), hends_oth e' v ((hinc e' v).mp he'), h1, h2]
  have hsum_one : ∀ v u (φ : E → ℝ) (B : ℝ), (∀ e, 0 ≤ φ e) → (∀ e ∈ G.inc v, oth e v = u → φ e ≤ B) →
      ∑ e ∈ (G.inc v).filter (fun e => oth e v = u), φ e ≤ max B 0 := by
    intro v u φ B hφ hB
    set S := (G.inc v).filter (fun e => oth e v = u)
    rcases S.eq_empty_or_nonempty with h0 | ⟨e₀, he₀⟩
    · rw [h0, Finset.sum_empty]; exact le_max_right _ _
    · have hS : S = {e₀} := by
        ext e
        simp only [Finset.mem_singleton]
        constructor
        · intro he
          have h1 := Finset.mem_filter.mp he
          have h2 := Finset.mem_filter.mp he₀
          exact huniq v u e e₀ h1.1 h2.1 h1.2 h2.2
        · rintro rfl; exact he₀
      rw [hS, Finset.sum_singleton]
      have h2 := Finset.mem_filter.mp he₀
      exact le_trans (hB e₀ h2.1 h2.2) (le_max_left _ _)
  -- exchanging vertices and edges
  have hexch2 : ∀ (u : V) (ψ : V → E → ℝ),
      ∑ v, ∑ e ∈ (G.inc v).filter (fun e => oth e v = u), ψ v e = ∑ e ∈ G.inc u, ψ (oth e u) e := by
    intro u ψ
    have h1 : ∀ v, ∑ e ∈ (G.inc v).filter (fun e => oth e v = u), ψ v e
        = ∑ e, if e ∈ G.inc v ∧ oth e v = u then ψ v e else 0 := by
      intro v; rw [Finset.sum_filter]
      unfold WGraph.inc; rw [Finset.sum_filter]
      apply Finset.sum_congr rfl; intro e _
      by_cases h1 : v ∈ G.ends e <;> simp [h1]
    simp_rw [h1]
    rw [Finset.sum_comm]
    have h2 : ∀ e, (∑ v, if e ∈ G.inc v ∧ oth e v = u then ψ v e else 0)
        = if e ∈ G.inc u then ψ (oth e u) e else 0 := by
      intro e
      have hiff : ∀ v, (e ∈ G.inc v ∧ oth e v = u) ↔ (v = oth e u ∧ e ∈ G.inc u) := by
        intro v
        constructor
        · rintro ⟨hv, hvu⟩
          have hv' := (hinc e v).mp hv
          refine ⟨?_, (hinc e u).mpr (hvu ▸ hoth_mem e v)⟩
          rw [← hvu, hoth_oth e v hv']
        · rintro ⟨rfl, hu⟩
          have hu' := (hinc e u).mp hu
          exact ⟨(hinc e _).mpr (hoth_mem e u), hoth_oth e u hu'⟩
      simp_rw [hiff]
      by_cases hu : e ∈ G.inc u
      · simp only [hu, and_true, if_true]
        rw [Finset.sum_ite_eq']; simp
      · simp [hu]
    simp_rw [h2]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hexch : ∀ (k : Fin r) (S : Finset E) (v : V) (φ : E → ℝ),
      ∑ u : {u // g u = k}, ∑ e ∈ S.filter (fun e => oth e v = u.1), φ e
        = ∑ e ∈ S.filter (fun e => g (oth e v) = k), φ e := by
    intro k S v φ
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro e _
    by_cases h : g (oth e v) = k
    · rw [if_pos h, Finset.sum_eq_single ⟨oth e v, h⟩]
      · simp
      · intro u _ hu
        rw [if_neg]; intro h'; apply hu; exact Subtype.ext h'.symm
      · simp
    · rw [if_neg h]
      apply Finset.sum_eq_zero; intro u _
      rw [if_neg]; intro h'; apply h; rw [h']; exact u.2
  -- discrepancy terms
  obtain ⟨disc, hdisc⟩ : ∃ F : E → V → (𝒞 → Fin M) → (𝒞 → Fin M) → ℝ, ∀ e v Lv Lo,
      F e v Lv Lo = if src e = v then |Se e Lv Lo - ms e Lv| else |ms e Lo - μ e| :=
    ⟨_, fun _ _ _ _ => rfl⟩
  have hdisc0 : ∀ e v Lv Lo, 0 ≤ disc e v Lv Lo := fun e v Lv Lo => by
    rw [hdisc]; split_ifs <;> exact abs_nonneg _
  have hdiscB : ∀ e v Lv Lo, disc e v Lv Lo ≤ Bd := fun e v Lv Lo => by
    rw [hdisc]; split_ifs
    · exact hdisc1 _ _ _
    · exact hdisc2 _ _
  have hdiscE : ∀ e v Lv, v ∈ G.ends e →
      ∑ Lo, π (oth e v) Lo * disc e v Lv Lo ≤ Real.sqrt (κ₁ / n) := by
    intro e v Lv hv
    by_cases hs : src e = v
    · have hoth : oth e v = tgt e := by simp only [oth, if_pos hs]
      rw [hoth]; simp_rw [hdisc, if_pos hs]; exact hE1 e _
    · have hoth : oth e v = src e := by simp only [oth, if_neg hs]
      rw [hoth]; simp_rw [hdisc, if_neg hs]; exact hE2 e
  -- the error term of Proposition A.4
  obtain ⟨Err, hErr⟩ : ∃ x : ℝ, x = K₄ * (Real.sqrt (cR * n / (1 - ρ) *
      Real.log (max 2 (max (cR * n / (1 - ρ)) (cD * n ^ 2)) + 2)) +
      Real.log (max 2 (max (cR * n / (1 - ρ)) (cD * n ^ 2)) + 2)) := ⟨_, rfl⟩
  have hErrle : Err ≤ cE * n ^ (3 / 4 : ℝ) := by
    rw [hErr, hcE]
    exact WECErr.err_bound K₄ cR cD n ρ hn1 hρ0 (by linarith) hcR0 hcD0
  -- large edges at a vertex
  have hlarge : ∀ u, ∑ e ∈ G.inc u, (if β ≤ G.w e then (1 : ℝ) else 0) ≤ n / β := by
    intro u
    calc ∑ e ∈ G.inc u, (if β ≤ G.w e then (1 : ℝ) else 0) ≤ ∑ e ∈ G.inc u, G.w e / β := by
          apply Finset.sum_le_sum; intro e _
          split_ifs with h
          · rw [le_div_iff₀ hβ]; linarith
          · exact div_nonneg (G.w_pos e).le hβ.le
      _ = G.W u / β := by unfold WGraph.W; rw [Finset.sum_div]
      _ ≤ n / β := div_le_div_of_nonneg_right (hW u) hβ.le
  -- scales of the rows
  obtain ⟨sc, hsc⟩ : ∃ F : V → 𝒞 → Fin M → Option (Fin Ks) → ℝ, ∀ v c P' pl,
      F v c P' pl = pl.elim (if 0 < R v c P' then n * r₀ / ((κ + 1) * R v c P') else 0)
        (fun _ => n / (κ + 1)) := ⟨_, fun _ _ _ _ => rfl⟩
  have hsc0 : ∀ v c P' pl, 0 ≤ sc v c P' pl := by
    intro v c P' pl; rw [hsc]; cases pl with
    | none => simp only [Option.elim]; split_ifs with h
              · positivity
              · exact le_refl _
    | some i => simp only [Option.elim]; positivity
  have hsc_le : ∀ v c P' pl, sc v c P' pl ≤ n / (κ + 1) := by
    intro v c P' pl; rw [hsc]; cases pl with
    | none =>
      simp only [Option.elim]; split_ifs with h
      · have hr := (hR v c P').resolve_left h.ne'
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have := mul_le_mul_of_nonneg_left hr (by positivity : (0 : ℝ) ≤ n * (κ + 1))
        nlinarith only [this]
      · positivity
    | some i => simp only [Option.elim]; exact le_refl _
  -- one group step
  have step : ∀ (k : Fin r) (Pp : V → 𝒞 → Fin M), ∃ Q : V → 𝒞 → Fin M,
      (∀ v, g v ≠ k → Q v = Pp v) ∧
      (∀ u, g u = k → O1 u (Q u) ≤ t ∧ O2 Pp u (Q u) ≤ t) ∧
      (∀ v c P' pl, sc v c P' pl * ∑ e ∈ (G.inc v).filter (fun e => g (oth e v) = k),
          cap e v c P' pl (Q (oth e v) c)
        ≤ sc v c P' pl * (∑ e ∈ (G.inc v).filter (fun e => g (oth e v) = k),
            ∑ P'', lam (oth e v) c P'' * cap e v c P' pl P'') / (1 - ρ) + Err) ∧
      (∀ v, (1 / Bd) * ∑ e ∈ (G.inc v).filter (fun e => g (oth e v) = k),
          G.w e * disc e v (Pp v) (Q (oth e v))
        ≤ (1 / Bd) * (∑ e ∈ (G.inc v).filter (fun e => g (oth e v) = k),
            G.w e * Real.sqrt (κ₁ / n)) / (1 - ρ) + Err) := by
    intro k Pp
    let I := {u : V // g u = k}
    let T := (V × 𝒞 × Fin M × Option (Fin Ks)) ⊕ V
    let F : T → I → (𝒞 → Fin M) → ℝ := fun row u L => Sum.elim
      (fun q : V × 𝒞 × Fin M × Option (Fin Ks) => sc q.1 q.2.1 q.2.2.1 q.2.2.2 *
        ∑ e ∈ (G.inc q.1).filter (fun e => oth e q.1 = u.1), cap e q.1 q.2.1 q.2.2.1 q.2.2.2 (L q.2.1))
      (fun v => (1 / Bd) * ∑ e ∈ (G.inc v).filter (fun e => oth e v = u.1),
        G.w e * disc e v (Pp v) L) row
    have hcapκ : ∀ e v c P' pl P'', v ∈ G.ends e → cap e v c P' pl P'' ≤ κ / n := by
      intro e v c P' pl P'' hv
      cases pl with
      | some i => exact hcb1 e v c P' i P'' hv
      | none =>
        refine le_trans (hcb2 e v c P' P'' hv) ?_
        have := G.w_le_one e
        have : 0 ≤ κ / n := by positivity
        exact mul_le_of_le_one_left this (G.w_le_one e)
    have hF01 : ∀ row u L, 0 ≤ F row u L ∧ F row u L ≤ 1 := by
      intro row u L
      rcases row with ⟨v, c, P', pl⟩ | v
      · simp only [F, Sum.elim_inl]
        have hs := hsum_one v u.1 (fun e => cap e v c P' pl (L c)) (κ / n)
          (fun e => hcap0 _ _ _ _ _ _) (fun e he _ => hcapκ e v c P' pl _ ((hinc e v).mp he))
        rw [max_eq_left (by positivity)] at hs
        have hs0 : 0 ≤ ∑ e ∈ (G.inc v).filter (fun e => oth e v = u.1), cap e v c P' pl (L c) :=
          Finset.sum_nonneg (fun e _ => hcap0 _ _ _ _ _ _)
        refine ⟨mul_nonneg (hsc0 _ _ _ _) hs0, ?_⟩
        calc sc v c P' pl * ∑ e ∈ (G.inc v).filter (fun e => oth e v = u.1), cap e v c P' pl (L c)
            ≤ n / (κ + 1) * (κ / n) := mul_le_mul (hsc_le _ _ _ _) hs hs0 (by positivity)
          _ ≤ 1 := by
              rw [div_mul_div_comm, div_le_one (by positivity)]
              nlinarith only [hn0]
      · simp only [F, Sum.elim_inr]
        have hs := hsum_one v u.1 (fun e => G.w e * disc e v (Pp v) L) Bd
          (fun e => mul_nonneg (G.w_pos e).le (hdisc0 _ _ _ _))
          (fun e _ _ => le_trans (mul_le_of_le_one_left (hdisc0 e v (Pp v) L) (G.w_le_one e))
            (hdiscB e v (Pp v) L))
        rw [max_eq_left hBd0.le] at hs
        have hs0 : 0 ≤ ∑ e ∈ (G.inc v).filter (fun e => oth e v = u.1), G.w e * disc e v (Pp v) L :=
          Finset.sum_nonneg (fun e _ => mul_nonneg (G.w_pos e).le (hdisc0 _ _ _ _))
        refine ⟨mul_nonneg (by positivity) hs0, ?_⟩
        calc 1 / Bd * ∑ e ∈ (G.inc v).filter (fun e => oth e v = u.1), G.w e * disc e v (Pp v) L
            ≤ 1 / Bd * Bd := mul_le_mul_of_nonneg_left hs (by positivity)
          _ = 1 := by field_simp
    -- exact means
    have hmeanC : ∀ v c P' pl, ∑ u : I, ∑ L, π u.1 L *
        (∑ e ∈ (G.inc v).filter (fun e => oth e v = u.1), cap e v c P' pl (L c))
        = ∑ e ∈ (G.inc v).filter (fun e => g (oth e v) = k),
            ∑ P'', lam (oth e v) c P'' * cap e v c P' pl P'' := by
      intro v c P' pl
      have h1 : ∀ u : I, ∑ L, π u.1 L * (∑ e ∈ (G.inc v).filter (fun e => oth e v = u.1),
          cap e v c P' pl (L c)) = ∑ e ∈ (G.inc v).filter (fun e => oth e v = u.1),
            ∑ P'', lam (oth e v) c P'' * cap e v c P' pl P'' := by
        intro u
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro e he
        have hoe : oth e v = u.1 := (Finset.mem_filter.mp he).2
        rw [hoe]
        exact WECProb.pw_marg (lam u.1) (hlam1 _) c (fun P'' => cap e v c P' pl P'')
      rw [Finset.sum_congr rfl (fun u _ => h1 u)]
      exact hexch k (G.inc v) v _
    have hmeanD : ∀ v, ∑ u : I, ∑ L, π u.1 L *
        (∑ e ∈ (G.inc v).filter (fun e => oth e v = u.1), G.w e * disc e v (Pp v) L)
        = ∑ e ∈ (G.inc v).filter (fun e => g (oth e v) = k),
            G.w e * ∑ Lo, π (oth e v) Lo * disc e v (Pp v) Lo := by
      intro v
      have h1 : ∀ u : I, ∑ L, π u.1 L * (∑ e ∈ (G.inc v).filter (fun e => oth e v = u.1),
          G.w e * disc e v (Pp v) L) = ∑ e ∈ (G.inc v).filter (fun e => oth e v = u.1),
            G.w e * ∑ Lo, π (oth e v) Lo * disc e v (Pp v) Lo := by
        intro u
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro e he
        have hoe : oth e v = u.1 := (Finset.mem_filter.mp he).2
        rw [hoe]
        apply Finset.sum_congr rfl; intro L _; ring
      rw [Finset.sum_congr rfl (fun u _ => h1 u)]
      exact hexch k (G.inc v) v _
    -- the means are at most `cR * n`
    have hsubEk : ∀ v (φ : E → ℝ), (∀ e, 0 ≤ φ e) →
        ∑ e ∈ (G.inc v).filter (fun e => g (oth e v) = k), φ e ≤ ∑ e ∈ G.inc v, φ e := fun v φ hφ =>
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun e _ _ => hφ e)
    have hsqκ : Real.sqrt (κ₁ / n) ≤ Real.sqrt κ₁ :=
      Real.sqrt_le_sqrt (div_le_self hκ₁0.le hn1)
    have hmR : ∀ row, ∑ u : I, ∑ L, π u.1 L * F row u L ≤ cR * n := by
      intro row
      rcases row with ⟨v, c, P', pl⟩ | v
      · simp only [F, Sum.elim_inl]
        have e1 : ∑ u : I, ∑ L, π u.1 L * (sc v c P' pl *
            ∑ e ∈ (G.inc v).filter (fun e => oth e v = u.1), cap e v c P' pl (L c))
            = sc v c P' pl * ∑ e ∈ (G.inc v).filter (fun e => g (oth e v) = k),
                ∑ P'', lam (oth e v) c P'' * cap e v c P' pl P'' := by
          rw [← hmeanC, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro u _
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro L _; ring
        rw [e1]
        cases pl with
        | some i =>
          have h1 : ∑ e ∈ (G.inc v).filter (fun e => g (oth e v) = k),
              ∑ P'', lam (oth e v) c P'' * cap e v c P' (some i) P'' ≤ 1 - σ := by
            calc _ ≤ ∑ e ∈ (G.inc v).filter (fun e => g (oth e v) = k), aL v c e P' i / lam v c P' :=
                  Finset.sum_le_sum (fun e he => hcm1 e v c P' i
                    ((hinc e v).mp (Finset.mem_filter.mp he).1))
              _ ≤ ∑ e ∈ G.inc v, aL v c e P' i / lam v c P' :=
                  hsubEk v _ (fun e => div_nonneg (haL0 _ _ _ _ _) (hlampos _ _ _).le)
              _ = (∑ e ∈ G.inc v, aL v c e P' i) / lam v c P' := by rw [Finset.sum_div]
              _ ≤ 1 - σ := by
                  rw [div_le_iff₀ (hlampos _ _ _)]; exact hcapL v c P' i
          have h2 : sc v c P' (some i) = n / (κ + 1) := by rw [hsc]; rfl
          rw [h2]
          have h3 : n / (κ + 1) ≤ n := div_le_self hn0.le (by linarith)
          have h4 : 0 ≤ ∑ e ∈ (G.inc v).filter (fun e => g (oth e v) = k),
              ∑ P'', lam (oth e v) c P'' * cap e v c P' (some i) P'' :=
            Finset.sum_nonneg (fun e _ => Finset.sum_nonneg (fun P'' _ =>
              mul_nonneg (hlampos _ _ _).le (hcap0 _ _ _ _ _ _)))
          calc n / (κ + 1) * _ ≤ n * 1 := mul_le_mul h3 (by linarith) h4 hn0.le
            _ ≤ cR * n := by rw [hcR]; nlinarith only [hn0, mul_nonneg hr₀.le hn0.le, mul_nonneg (Real.sqrt_nonneg κ₁) hn0.le]
        | none =>
          by_cases hRp : 0 < R v c P'
          · have hr := (hR v c P').resolve_left hRp.ne'
            have h1 : ∑ e ∈ (G.inc v).filter (fun e => g (oth e v) = k),
                ∑ P'', lam (oth e v) c P'' * cap e v c P' none P'' ≤ (1 - σ) * R v c P' := by
              calc _ ≤ ∑ e ∈ (G.inc v).filter (fun e => g (oth e v) = k),
                      G.w e * aS v c e P' / lam v c P' :=
                    Finset.sum_le_sum (fun e he => hcm2 e v c P'
                      ((hinc e v).mp (Finset.mem_filter.mp he).1))
                _ ≤ ∑ e ∈ G.inc v, G.w e * aS v c e P' / lam v c P' :=
                    hsubEk v _ (fun e => div_nonneg (mul_nonneg (G.w_pos e).le (haS0 _ _ _ _))
                      (hlampos _ _ _).le)
                _ = (∑ e ∈ G.inc v, G.w e * aS v c e P') / lam v c P' := by rw [Finset.sum_div]
                _ ≤ (1 - σ) * R v c P' := by
                    rw [div_le_iff₀ (hlampos _ _ _)]
                    have := hcapS v c P'
                    linarith [show (1 - σ) * lam v c P' * R v c P' = (1 - σ) * R v c P' * lam v c P'
                      by ring]
            have h2 : sc v c P' none = n * r₀ / ((κ + 1) * R v c P') := by
              rw [hsc]; simp only [Option.elim, if_pos hRp]
            rw [h2]
            have h4 : 0 ≤ ∑ e ∈ (G.inc v).filter (fun e => g (oth e v) = k),
                ∑ P'', lam (oth e v) c P'' * cap e v c P' none P'' :=
              Finset.sum_nonneg (fun e _ => Finset.sum_nonneg (fun P'' _ =>
                mul_nonneg (hlampos _ _ _).le (hcap0 _ _ _ _ _ _)))
            calc n * r₀ / ((κ + 1) * R v c P') * _ ≤ n * r₀ / ((κ + 1) * R v c P') * ((1 - σ) * R v c P') :=
                  mul_le_mul_of_nonneg_left h1 (by positivity)
              _ = n * r₀ * (1 - σ) / (κ + 1) := by field_simp
              _ ≤ n * r₀ := by
                  rw [div_le_iff₀ (by linarith)]
                  have : 0 ≤ n * r₀ := by positivity
                  nlinarith only [this, hσ0, hκ0, mul_nonneg this hκ0, mul_nonneg this hσ0.le]
              _ ≤ cR * n := by rw [hcR]; nlinarith only [hn0, mul_nonneg hr₀.le hn0.le, mul_nonneg (Real.sqrt_nonneg κ₁) hn0.le]
          · have h2 : sc v c P' none = 0 := by rw [hsc]; simp only [Option.elim, if_neg hRp]
            rw [h2, zero_mul]; positivity
      · simp only [F, Sum.elim_inr]
        have e1 : ∑ u : I, ∑ L, π u.1 L * (1 / Bd *
            ∑ e ∈ (G.inc v).filter (fun e => oth e v = u.1), G.w e * disc e v (Pp v) L)
            = 1 / Bd * ∑ e ∈ (G.inc v).filter (fun e => g (oth e v) = k),
                G.w e * ∑ Lo, π (oth e v) Lo * disc e v (Pp v) Lo := by
          rw [← hmeanD, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro u _
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro L _; ring
        rw [e1]
        have h1 : ∑ e ∈ (G.inc v).filter (fun e => g (oth e v) = k),
            G.w e * ∑ Lo, π (oth e v) Lo * disc e v (Pp v) Lo ≤ n * Real.sqrt κ₁ := by
          calc _ ≤ ∑ e ∈ (G.inc v).filter (fun e => g (oth e v) = k), G.w e * Real.sqrt κ₁ := by
                apply Finset.sum_le_sum; intro e he
                apply mul_le_mul_of_nonneg_left _ (G.w_pos e).le
                exact le_trans (hdiscE e v (Pp v) ((hinc e v).mp (Finset.mem_filter.mp he).1)) hsqκ
            _ ≤ ∑ e ∈ G.inc v, G.w e * Real.sqrt κ₁ :=
                hsubEk v _ (fun e => mul_nonneg (G.w_pos e).le (Real.sqrt_nonneg _))
            _ = G.W v * Real.sqrt κ₁ := by unfold WGraph.W; rw [Finset.sum_mul]
            _ ≤ n * Real.sqrt κ₁ := mul_le_mul_of_nonneg_right (hW v) (Real.sqrt_nonneg _)
        have h0 : 0 ≤ ∑ e ∈ (G.inc v).filter (fun e => g (oth e v) = k),
            G.w e * ∑ Lo, π (oth e v) Lo * disc e v (Pp v) Lo :=
          Finset.sum_nonneg (fun e _ => mul_nonneg (G.w_pos e).le (Finset.sum_nonneg (fun Lo _ =>
            mul_nonneg (hπ0 _ _).le (hdisc0 _ _ _ _))))
        have hB1 : 1 / Bd ≤ 1 := by
          rw [div_le_one hBd0, hBd]; have : 0 ≤ C₀ * C₁ * Mθ ^ 2 + C₀ * C₁ := by positivity
          linarith
        calc 1 / Bd * _ ≤ 1 * (n * Real.sqrt κ₁) := mul_le_mul hB1 h1 h0 (by norm_num)
          _ ≤ cR * n := by rw [hcR]; nlinarith only [hn0, mul_nonneg hr₀.le hn0.le, mul_nonneg (Real.sqrt_nonneg κ₁) hn0.le]
    -- column sums
    have hD : ∀ (u : I) L, ∑ row, F row u L ≤ cD * n ^ 2 := by
      intro u L
      rw [Fintype.sum_sum_type]
      simp only [F, Sum.elim_inl, Sum.elim_inr]
      -- capacity part
      have hcapsum : ∑ q : V × 𝒞 × Fin M × Option (Fin Ks), sc q.1 q.2.1 q.2.2.1 q.2.2.2 *
          ∑ e ∈ (G.inc q.1).filter (fun e => oth e q.1 = u.1), cap e q.1 q.2.1 q.2.2.1 q.2.2.2 (L q.2.1)
          ≤ C₁ * M * (1 / β + 1) * n ^ 2 := by
        rw [Fintype.sum_prod_type]
        have h1 : ∀ v, ∑ y' : 𝒞 × Fin M × Option (Fin Ks), sc v y'.1 y'.2.1 y'.2.2 *
            ∑ e ∈ (G.inc v).filter (fun e => oth e v = u.1), cap e v y'.1 y'.2.1 y'.2.2 (L y'.1)
            = ∑ e ∈ (G.inc v).filter (fun e => oth e v = u.1),
                ∑ y' : 𝒞 × Fin M × Option (Fin Ks), sc v y'.1 y'.2.1 y'.2.2 *
                  cap e v y'.1 y'.2.1 y'.2.2 (L y'.1) := by
          intro v; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
        simp only [h1]
        rw [hexch2 u.1 (fun v e => ∑ y' : 𝒞 × Fin M × Option (Fin Ks), sc v y'.1 y'.2.1 y'.2.2 *
          cap e v y'.1 y'.2.1 y'.2.2 (L y'.1))]
        have h2 : ∀ e ∈ G.inc u.1, ∑ y' : 𝒞 × Fin M × Option (Fin Ks), sc (oth e u.1) y'.1 y'.2.1 y'.2.2 *
            cap e (oth e u.1) y'.1 y'.2.1 y'.2.2 (L y'.1)
            ≤ C₁ * n * M * ((if β ≤ G.w e then (1 : ℝ) else 0) + G.w e) := by
          intro e he
          have hv : oth e u.1 ∈ G.ends e := hoth_mem e u.1
          set v := oth e u.1
          rw [Fintype.sum_prod_type]
          have h3 : ∀ c, ∑ y'' : Fin M × Option (Fin Ks), sc v c y''.1 y''.2 * cap e v c y''.1 y''.2 (L c)
              ≤ M * ((if β ≤ G.w e then (1 : ℝ) else 0) + G.w e) := by
            intro c
            rw [Fintype.sum_prod_type]
            have h4 : ∀ P', ∑ pl : Option (Fin Ks), sc v c P' pl * cap e v c P' pl (L c)
                ≤ n / (κ + 1) * (∑ i, cap e v c P' (some i) (L c) + cap e v c P' none (L c)) := by
              intro P'
              rw [Fintype.sum_option]
              rw [mul_add, Finset.mul_sum]
              rw [add_comm]
              apply add_le_add
              · apply Finset.sum_le_sum; intro i _
                exact mul_le_mul_of_nonneg_right (hsc_le _ _ _ _) (hcap0 _ _ _ _ _ _)
              · exact mul_le_mul_of_nonneg_right (hsc_le _ _ _ _) (hcap0 _ _ _ _ _ _)
            calc ∑ P', ∑ pl : Option (Fin Ks), sc v c P' pl * cap e v c P' pl (L c)
                ≤ ∑ P', n / (κ + 1) * (∑ i, cap e v c P' (some i) (L c) + cap e v c P' none (L c)) :=
                  Finset.sum_le_sum (fun P' _ => h4 P')
              _ = n / (κ + 1) * (∑ P', ∑ i, cap e v c P' (some i) (L c) + ∑ P', cap e v c P' none (L c)) := by
                  rw [← Finset.mul_sum, Finset.sum_add_distrib]
              _ ≤ n / (κ + 1) * ((if β ≤ G.w e then (M : ℝ) * (κ / n) else 0) +
                    G.w e * ((M : ℝ) * (κ / n))) :=
                  mul_le_mul_of_nonneg_left (add_le_add (hcs1 e v c (L c) hv) (hcs2 e v c (L c) hv))
                    (by positivity)
              _ ≤ M * ((if β ≤ G.w e then (1 : ℝ) else 0) + G.w e) := by
                  have hκk : n / (κ + 1) * (κ / n) ≤ 1 := by
                    rw [div_mul_div_comm, div_le_one (by positivity)]; nlinarith only [hn0]
                  have hw0 := (G.w_pos e).le
                  split_ifs
                  · have : n / (κ + 1) * ((M : ℝ) * (κ / n) + G.w e * ((M : ℝ) * (κ / n)))
                        = (M * (1 + G.w e)) * (n / (κ + 1) * (κ / n)) := by ring
                    rw [this]
                    have : (0 : ℝ) ≤ M * (1 + G.w e) := by positivity
                    nlinarith only [this, hκk, mul_le_mul_of_nonneg_left hκk this]
                  · have : n / (κ + 1) * (0 + G.w e * ((M : ℝ) * (κ / n)))
                        = (M * G.w e) * (n / (κ + 1) * (κ / n)) := by ring
                    rw [this, zero_add]
                    have : (0 : ℝ) ≤ M * G.w e := by positivity
                    nlinarith only [this, hκk, mul_le_mul_of_nonneg_left hκk this]
          calc ∑ c, ∑ y'' : Fin M × Option (Fin Ks), sc v c y''.1 y''.2 * cap e v c y''.1 y''.2 (L c)
              ≤ ∑ _c : 𝒞, (M : ℝ) * ((if β ≤ G.w e then (1 : ℝ) else 0) + G.w e) :=
                Finset.sum_le_sum (fun c _ => h3 c)
            _ = Fintype.card 𝒞 * ((M : ℝ) * ((if β ≤ G.w e then (1 : ℝ) else 0) + G.w e)) := by
                rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
            _ ≤ C₁ * n * ((M : ℝ) * ((if β ≤ G.w e then (1 : ℝ) else 0) + G.w e)) :=
                mul_le_mul_of_nonneg_right hcard (mul_nonneg (Nat.cast_nonneg _)
                  (add_nonneg (by split_ifs <;> norm_num) (G.w_pos e).le))
            _ = C₁ * n * M * ((if β ≤ G.w e then (1 : ℝ) else 0) + G.w e) := by ring
        calc ∑ e ∈ G.inc u.1, ∑ y' : 𝒞 × Fin M × Option (Fin Ks), sc (oth e u.1) y'.1 y'.2.1 y'.2.2 *
              cap e (oth e u.1) y'.1 y'.2.1 y'.2.2 (L y'.1)
            ≤ ∑ e ∈ G.inc u.1, C₁ * n * M * ((if β ≤ G.w e then (1 : ℝ) else 0) + G.w e) :=
              Finset.sum_le_sum h2
          _ = C₁ * n * M * (∑ e ∈ G.inc u.1, (if β ≤ G.w e then (1 : ℝ) else 0) + G.W u.1) := by
              rw [← Finset.mul_sum, Finset.sum_add_distrib]; rfl
          _ ≤ C₁ * n * M * (n / β + n) :=
              mul_le_mul_of_nonneg_left (add_le_add (hlarge u.1) (hW u.1)) (by positivity)
          _ = C₁ * M * (1 / β + 1) * n ^ 2 := by ring
      have hdiscsum : ∑ v, 1 / Bd * ∑ e ∈ (G.inc v).filter (fun e => oth e v = u.1),
          G.w e * disc e v (Pp v) L ≤ n := by
        simp_rw [← Finset.mul_sum]
        rw [hexch2 u.1 (fun v e => G.w e * disc e v (Pp v) L)]
        calc 1 / Bd * ∑ e ∈ G.inc u.1, G.w e * disc e (oth e u.1) (Pp (oth e u.1)) L
            ≤ 1 / Bd * ∑ e ∈ G.inc u.1, G.w e * Bd :=
              mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun e _ =>
                mul_le_mul_of_nonneg_left (hdiscB _ _ _ _) (G.w_pos e).le)) (by positivity)
          _ = G.W u.1 := by unfold WGraph.W; rw [← Finset.sum_mul]; field_simp
          _ ≤ n := hW u.1
      have hn2 : n ≤ n ^ 2 := by nlinarith only [hn1]
      rw [hcD]
      nlinarith only [hcapsum, hdiscsum, hn2]
    have hmmC : ∀ v c P' pl, ∑ u : I, ∑ L, π u.1 L * F (Sum.inl (v, c, P', pl)) u L
        = sc v c P' pl * ∑ e ∈ (G.inc v).filter (fun e => g (oth e v) = k),
            ∑ P'', lam (oth e v) c P'' * cap e v c P' pl P'' := by
      intro v c P' pl
      simp only [F, Sum.elim_inl]
      rw [← hmeanC, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro u _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro L _; ring
    have hmmD : ∀ v, ∑ u : I, ∑ L, π u.1 L * F (Sum.inr v) u L
        = 1 / Bd * ∑ e ∈ (G.inc v).filter (fun e => g (oth e v) = k),
            G.w e * ∑ Lo, π (oth e v) Lo * disc e v (Pp v) Lo := by
      intro v
      simp only [F, Sum.elim_inr]
      rw [← hmeanD, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro u _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro L _; ring
    obtain ⟨z, hzgood, hz⟩ := WECA4.a4_cond K₄ hK₄ (I := I) (T := T) (Ω := 𝒞 → Fin M)
      (fun u L => π u.1 L) (fun u L => O1 u.1 L ≤ t ∧ O2 Pp u.1 L ≤ t) F
      (fun row => ∑ u : I, ∑ L, π u.1 L * F row u L) ρ (cR * n) (cD * n ^ 2)
      (fun u L => hπ0 _ _) (fun u => hπ1 _) hρ0 hρ1 (fun u => hgood Pp u.1) hF01
      (fun row => le_refl _) hmR hD
    rw [← hErr] at hz
    let Q : V → 𝒞 → Fin M := fun v => if h : g v = k then z ⟨v, h⟩ else Pp v
    have hQz : ∀ u : I, Q u.1 = z u := fun u => by simp only [Q, dif_pos u.2]; rfl
    have hconv : ∀ v (H : E → (𝒞 → Fin M) → ℝ),
        ∑ u : I, ∑ e ∈ (G.inc v).filter (fun e => oth e v = u.1), H e (z u)
          = ∑ e ∈ (G.inc v).filter (fun e => g (oth e v) = k), H e (Q (oth e v)) := by
      intro v H
      have : ∀ u : I, ∑ e ∈ (G.inc v).filter (fun e => oth e v = u.1), H e (z u)
          = ∑ e ∈ (G.inc v).filter (fun e => oth e v = u.1), H e (Q (oth e v)) := by
        intro u
        apply Finset.sum_congr rfl; intro e he
        rw [(Finset.mem_filter.mp he).2, hQz]
      rw [Finset.sum_congr rfl (fun u _ => this u)]
      exact hexch k (G.inc v) v _
    refine ⟨Q, fun v hv => by simp only [Q, dif_neg hv], fun u hu => ?_, fun v c P' pl => ?_,
      fun v => ?_⟩
    · have := hzgood ⟨u, hu⟩
      have hq : Q u = z ⟨u, hu⟩ := hQz ⟨u, hu⟩
      rw [hq]; exact this
    · have h1 := hz (Sum.inl (v, c, P', pl))
      rw [hmmC] at h1
      simp only [F, Sum.elim_inl] at h1
      rw [← Finset.mul_sum, hconv v (fun e L => cap e v c P' pl (L c))] at h1
      exact h1
    · have h1 := hz (Sum.inr v)
      rw [hmmD] at h1
      simp only [F, Sum.elim_inr] at h1
      rw [← Finset.mul_sum, hconv v (fun e L => G.w e * disc e v (Pp v) L)] at h1
      refine le_trans h1 ?_
      refine add_le_add ?_ (le_refl _)
      apply div_le_div_of_nonneg_right _ (by linarith)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum; intro e he
      exact mul_le_mul_of_nonneg_left (hdiscE e v (Pp v) ((hinc e v).mp (Finset.mem_filter.mp he).1))
        (G.w_pos e).le
  -- iterate over the groups
  choose Qf hQ1 hQ2 hQ3 hQ4 using step
  have hne : ∀ v : V, Nonempty (𝒞 → Fin M) := by
    intro v
    by_contra h
    rw [not_nonempty_iff] at h
    have := hπ1 v
    rw [Finset.univ_eq_empty, Finset.sum_empty] at this
    exact zero_ne_one this
  let P₀ : V → 𝒞 → Fin M := fun v => Classical.choice (hne v)
  let seq : ℕ → V → 𝒞 → Fin M := fun j =>
    Nat.rec P₀ (fun j P => if h : j < r then Qf ⟨j, h⟩ P else P) j
  have hseq_succ : ∀ j (h : j < r), seq (j + 1) = Qf ⟨j, h⟩ (seq j) := by
    intro j h; simp only [seq, dif_pos h]
  set Pc := seq r with hPc
  have hfix : ∀ v (m : ℕ), (g v).val + 1 + m ≤ r → seq ((g v).val + 1 + m) v = seq ((g v).val + 1) v := by
    intro v m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      have hlt : (g v).val + 1 + m < r := by omega
      rw [show (g v).val + 1 + (m + 1) = (g v).val + 1 + m + 1 by ring, hseq_succ _ hlt,
        hQ1 _ _ v (by intro h; have := congrArg Fin.val h; simp at this; omega)]
      exact ih (by omega)
  have hfinal : ∀ v j, (g v).val < j → j ≤ r → seq j v = Pc v := by
    intro v j hj hjr
    have h1 := hfix v (j - ((g v).val + 1)) (by omega)
    have h2 := hfix v (r - ((g v).val + 1)) (by have := (g v).isLt; omega)
    rw [show (g v).val + 1 + (j - ((g v).val + 1)) = j by omega] at h1
    rw [show (g v).val + 1 + (r - ((g v).val + 1)) = r by have := (g v).isLt; omega] at h2
    rw [hPc, h1, h2]
  -- the step at group `k` in terms of `Pc`
  have hstepP : ∀ k : Fin r, seq (k.val + 1) = Qf k (seq k.val) := fun k => by
    rw [hseq_succ k.val k.isLt]
  have hQ_P : ∀ (k : Fin r) v, g v = k → Qf k (seq k.val) v = Pc v := by
    intro k v hv
    rw [← hstepP k]
    exact hfinal v (k.val + 1) (by rw [hv]; exact Nat.lt_succ_self _) k.isLt
  have hPp_P : ∀ (k : Fin r) v, (g v).val < k.val → seq k.val v = Pc v := fun k v hv =>
    hfinal v _ hv k.isLt.le
  refine ⟨Pc, fun XL XS hXL hXS => ?_⟩
  have hpart : ∀ v (φ : E → ℝ), ∑ k : Fin r, ∑ e ∈ (G.inc v).filter (fun e => g (oth e v) = k), φ e
      = ∑ e ∈ G.inc v, φ e := fun v φ => Finset.sum_fiberwise (G.inc v) (fun e => g (oth e v)) φ
  have hgoth : ∀ e v k, e ∈ (G.inc v).filter (fun e => g (oth e v) = k) → Qf k (seq k.val) (oth e v) = Pc (oth e v) :=
    fun e v k he => hQ_P k _ (Finset.mem_filter.mp he).2
  -- capacity bounds summed over the groups
  have hcapAll : ∀ v c P' pl, sc v c P' pl * ∑ e ∈ G.inc v, cap e v c P' pl (Pc (oth e v) c)
      ≤ sc v c P' pl * (∑ e ∈ G.inc v, ∑ P'', lam (oth e v) c P'' * cap e v c P' pl P'') / (1 - ρ)
        + r * Err := by
    intro v c P' pl
    have h1 : ∀ k : Fin r, sc v c P' pl * ∑ e ∈ (G.inc v).filter (fun e => g (oth e v) = k),
        cap e v c P' pl (Pc (oth e v) c)
        ≤ sc v c P' pl * (∑ e ∈ (G.inc v).filter (fun e => g (oth e v) = k),
            ∑ P'', lam (oth e v) c P'' * cap e v c P' pl P'') / (1 - ρ) + Err := by
      intro k
      have := hQ3 k (seq k.val) v c P' pl
      rwa [Finset.sum_congr rfl (fun e he => by rw [hgoth e v k he])] at this
    have h2 := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => h1 k)
    rw [← Finset.mul_sum, hpart, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at h2
    have h3 : ∑ k : Fin r, sc v c P' pl * (∑ e ∈ (G.inc v).filter (fun e => g (oth e v) = k),
        ∑ P'', lam (oth e v) c P'' * cap e v c P' pl P'') / (1 - ρ)
        = sc v c P' pl * (∑ e ∈ G.inc v, ∑ P'', lam (oth e v) c P'' * cap e v c P' pl P'') / (1 - ρ) := by
      rw [← Finset.sum_div, ← Finset.mul_sum, hpart]
    rw [h3] at h2
    exact h2
  -- arithmetic of the slack
  have hρfrac : (1 - σ) / (1 - ρ) ≤ 1 - σ + σ / 4 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith only [hρσ, hρ0, hσ0, hσ1, mul_nonneg hρ0 hσ0.le]
  have hErrsl : r * Err * (κ + 1) / n ≤ σ / 8 := by
    have h1 : r * Err * (κ + 1) / n ≤ r * (cE * n ^ (3 / 4 : ℝ)) * (κ + 1) / n := by
      apply div_le_div_of_nonneg_right _ hn0.le
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      exact mul_le_mul_of_nonneg_left hErrle (Nat.cast_nonneg _)
    have h2 : r * (cE * n ^ (3 / 4 : ℝ)) * (κ + 1) / n = r * cE * (κ + 1) / n ^ (1 / 4 : ℝ) := by
      have e : n ^ (3 / 4 : ℝ) = n / n ^ (1 / 4 : ℝ) := by
        rw [show (3 / 4 : ℝ) = 1 - 1 / 4 by norm_num, Real.rpow_sub hn0, Real.rpow_one]
      rw [e]
      field_simp
    have h3 : r * cE * (κ + 1) / n ^ (1 / 4 : ℝ) ≤ σ / 8 := by
      rw [div_le_iff₀ hn14pos]
      have h4 : 8 * r * cE * (κ + 1) / σ ≤ n ^ (1 / 4 : ℝ) := by
        refine le_trans ?_ hn14
        rw [hTn]
        have : 0 ≤ 16 * Real.sqrt κ₁ / σ + 8 * r * cE * (κ + 1) / (σ * r₀) := by positivity
        linarith
      rw [div_le_iff₀ hσ0] at h4
      linarith
    linarith
  have hErrres : r * Err * (κ + 1) / (n * r₀) ≤ σ / 8 := by
    have h1 : r * Err * (κ + 1) / (n * r₀) ≤ r * (cE * n ^ (3 / 4 : ℝ)) * (κ + 1) / (n * r₀) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      exact mul_le_mul_of_nonneg_left hErrle (Nat.cast_nonneg _)
    have h2 : r * (cE * n ^ (3 / 4 : ℝ)) * (κ + 1) / (n * r₀) = r * cE * (κ + 1) / (r₀ * n ^ (1 / 4 : ℝ)) := by
      have e : n ^ (3 / 4 : ℝ) = n / n ^ (1 / 4 : ℝ) := by
        rw [show (3 / 4 : ℝ) = 1 - 1 / 4 by norm_num, Real.rpow_sub hn0, Real.rpow_one]
      rw [e]
      field_simp
    have h3 : r * cE * (κ + 1) / (r₀ * n ^ (1 / 4 : ℝ)) ≤ σ / 8 := by
      rw [div_le_iff₀ (by positivity)]
      have h4 : 8 * r * cE * (κ + 1) / (σ * r₀) ≤ n ^ (1 / 4 : ℝ) := by
        refine le_trans ?_ hn14
        rw [hTn]
        have : 0 ≤ 16 * Real.sqrt κ₁ / σ + 8 * r * cE * (κ + 1) / σ := by positivity
        linarith
      rw [div_le_iff₀ (by positivity)] at h4
      nlinarith only [h4]
    linarith
  -- the inc set splits into the two orientations
  have hsplit_inc : ∀ v (A B : E → ℝ),
      ∑ e ∈ Finset.univ.filter (fun e => src e = v), A e + ∑ e ∈ Finset.univ.filter (fun e => tgt e = v), B e
        = ∑ e ∈ G.inc v, (if src e = v then A e else B e) := by
    intro v A B
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    unfold WGraph.inc
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl; intro e _
    by_cases hs : src e = v
    · have ht : ¬ tgt e = v := fun h => hst_ne e (hs.trans h.symm)
      have hv : v ∈ G.ends e := by rw [← hs]; exact hsrc_mem e
      simp [hs, ht, hv]
    · by_cases ht : tgt e = v
      · have hv : v ∈ G.ends e := by rw [← ht]; exact htgt_mem e
        simp [hs, ht, hv]
      · have hv : v ∉ G.ends e := by
          intro hv; rcases (hmem e v).mp hv with h | h
          · exact hs h.symm
          · exact ht h.symm
        simp [hs, ht, hv]
  refine ⟨?_, ?_, ?_⟩
  · -- slots
    intro v c i
    have hrw : ∑ e ∈ Finset.univ.filter (fun e => src e = v), ∑ j, XL e c i j
        + ∑ e ∈ Finset.univ.filter (fun e => tgt e = v), ∑ j, XL e c j i
        = ∑ e ∈ G.inc v, cap e v c (Pc v c) (some i) (Pc (oth e v) c) := by
      rw [hsplit_inc]
      apply Finset.sum_congr rfl; intro e he
      rw [hcap]; simp only [Option.elim, one_mul, WECEdge.capg]
      by_cases hs : src e = v
      · simp only [if_pos hs, oth]
        simp_rw [hXL]
        rw [← Finset.sum_div, ← Finset.mul_sum, hs]
      · simp only [if_neg hs, oth]
        have ht : tgt e = v := by
          rcases (hmem e v).mp ((hinc e v).mp he) with h | h
          · exact absurd h.symm hs
          · exact h.symm
        simp_rw [hXL]
        rw [← Finset.sum_div, ← Finset.sum_mul, ht]
        ring
    rw [hrw]
    have h1 := hcapAll v c (Pc v c) (some i)
    have hsc : sc v c (Pc v c) (some i) = n / (κ + 1) := by rw [hsc]; rfl
    rw [hsc] at h1
    have h2 : ∑ e ∈ G.inc v, ∑ P'', lam (oth e v) c P'' * cap e v c (Pc v c) (some i) P'' ≤ 1 - σ := by
      calc _ ≤ ∑ e ∈ G.inc v, aL v c e (Pc v c) i / lam v c (Pc v c) :=
            Finset.sum_le_sum (fun e he => hcm1 e v c _ i ((hinc e v).mp he))
        _ = (∑ e ∈ G.inc v, aL v c e (Pc v c) i) / lam v c (Pc v c) := by rw [Finset.sum_div]
        _ ≤ 1 - σ := by rw [div_le_iff₀ (hlampos _ _ _)]; exact hcapL v c _ i
    have hκn : 0 < n / (κ + 1) := by positivity
    have h3 : ∑ e ∈ G.inc v, cap e v c (Pc v c) (some i) (Pc (oth e v) c)
        ≤ (∑ e ∈ G.inc v, ∑ P'', lam (oth e v) c P'' * cap e v c (Pc v c) (some i) P'') / (1 - ρ)
          + r * Err * (κ + 1) / n := by
      have e1 : r * Err * (κ + 1) / n = r * Err / (n / (κ + 1)) := by field_simp
      rw [e1, ← sub_le_iff_le_add', le_div_iff₀ hκn]
      have e2 : (∑ e ∈ G.inc v, cap e v c (Pc v c) (some i) (Pc (oth e v) c) -
          (∑ e ∈ G.inc v, ∑ P'', lam (oth e v) c P'' * cap e v c (Pc v c) (some i) P'') / (1 - ρ)) *
          (n / (κ + 1)) = n / (κ + 1) * ∑ e ∈ G.inc v, cap e v c (Pc v c) (some i) (Pc (oth e v) c) -
          n / (κ + 1) * (∑ e ∈ G.inc v, ∑ P'', lam (oth e v) c P'' * cap e v c (Pc v c) (some i) P'') / (1 - ρ) := by
        ring
      rw [e2]; linarith
    have h4 : (∑ e ∈ G.inc v, ∑ P'', lam (oth e v) c P'' * cap e v c (Pc v c) (some i) P'') / (1 - ρ)
        ≤ (1 - σ) / (1 - ρ) := div_le_div_of_nonneg_right h2 (by linarith)
    linarith
  · -- reserves
    intro v c
    have hrw : ∑ e ∈ G.inc v, G.w e * XS e c = ∑ e ∈ G.inc v, cap e v c (Pc v c) none (Pc (oth e v) c) := by
      apply Finset.sum_congr rfl; intro e he
      rw [hcap, hXS]; simp only [Option.elim, WECEdge.capg]
      by_cases hs : src e = v
      · simp only [oth, if_pos hs]; rw [hs]
      · have ht : tgt e = v := by
          rcases (hmem e v).mp ((hinc e v).mp he) with h | h
          · exact absurd h.symm hs
          · exact h.symm
        simp only [oth, if_neg hs]; rw [ht]; ring
    rw [hrw]
    rcases (hR v c (Pc v c)) with hR0 | hRr
    · have hz : ∀ e, aS v c e (Pc v c) = 0 := fun e => by
        by_contra h; have := haSR v c e _ h; rw [hR0] at this; exact lt_irrefl _ this
      have : ∀ e, cap e v c (Pc v c) none (Pc (oth e v) c) = 0 := fun e => by
        rw [hcap]; simp [Option.elim, WECEdge.capg, hz]
      simp [this, hR0]
    · have hRp : 0 < R v c (Pc v c) := lt_of_lt_of_le hr₀ hRr
      have h1 := hcapAll v c (Pc v c) none
      have hsc : sc v c (Pc v c) none = n * r₀ / ((κ + 1) * R v c (Pc v c)) := by
        rw [hsc]; simp only [Option.elim, if_pos hRp]
      rw [hsc] at h1
      have h2 : ∑ e ∈ G.inc v, ∑ P'', lam (oth e v) c P'' * cap e v c (Pc v c) none P''
          ≤ (1 - σ) * R v c (Pc v c) := by
        calc _ ≤ ∑ e ∈ G.inc v, G.w e * aS v c e (Pc v c) / lam v c (Pc v c) :=
              Finset.sum_le_sum (fun e he => hcm2 e v c _ ((hinc e v).mp he))
          _ = (∑ e ∈ G.inc v, G.w e * aS v c e (Pc v c)) / lam v c (Pc v c) := by rw [Finset.sum_div]
          _ ≤ (1 - σ) * R v c (Pc v c) := by
              rw [div_le_iff₀ (hlampos _ _ _)]
              have := hcapS v c (Pc v c)
              linarith [show (1 - σ) * lam v c (Pc v c) * R v c (Pc v c)
                = (1 - σ) * R v c (Pc v c) * lam v c (Pc v c) by ring]
      have hscp : 0 < n * r₀ / ((κ + 1) * R v c (Pc v c)) := by positivity
      have h3 : ∑ e ∈ G.inc v, cap e v c (Pc v c) none (Pc (oth e v) c)
          ≤ (∑ e ∈ G.inc v, ∑ P'', lam (oth e v) c P'' * cap e v c (Pc v c) none P'') / (1 - ρ)
            + r * Err * (κ + 1) / (n * r₀) * R v c (Pc v c) := by
        have e1 : r * Err * (κ + 1) / (n * r₀) * R v c (Pc v c)
            = r * Err / (n * r₀ / ((κ + 1) * R v c (Pc v c))) := by field_simp
        rw [e1, ← sub_le_iff_le_add', le_div_iff₀ hscp]
        have e2 : (∑ e ∈ G.inc v, cap e v c (Pc v c) none (Pc (oth e v) c) -
            (∑ e ∈ G.inc v, ∑ P'', lam (oth e v) c P'' * cap e v c (Pc v c) none P'') / (1 - ρ)) *
            (n * r₀ / ((κ + 1) * R v c (Pc v c)))
            = n * r₀ / ((κ + 1) * R v c (Pc v c)) * ∑ e ∈ G.inc v, cap e v c (Pc v c) none (Pc (oth e v) c) -
            n * r₀ / ((κ + 1) * R v c (Pc v c)) *
              (∑ e ∈ G.inc v, ∑ P'', lam (oth e v) c P'' * cap e v c (Pc v c) none P'') / (1 - ρ) := by
          ring
        rw [e2]; linarith
      have h4 : (∑ e ∈ G.inc v, ∑ P'', lam (oth e v) c P'' * cap e v c (Pc v c) none P'') / (1 - ρ)
          ≤ (1 - σ) / (1 - ρ) * R v c (Pc v c) := by
        rw [div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_right (by linarith [h2]) (by linarith)
      have h5 : r * Err * (κ + 1) / (n * r₀) * R v c (Pc v c) ≤ σ / 8 * R v c (Pc v c) :=
        mul_le_mul_of_nonneg_right hErrres hRp.le
      have h6 : (1 - σ) / (1 - ρ) * R v c (Pc v c) ≤ (1 - σ + σ / 4) * R v c (Pc v c) :=
        mul_le_mul_of_nonneg_right hρfrac hRp.le
      nlinarith only [h3, h4, h5, h6, mul_nonneg hσ0.le hRp.le]
  · -- discrepancy
    intro v
    have hSrw : ∀ e, ∑ c, (∑ i, ∑ j, XL e c i j + XS e c) = Se e (Pc (src e)) (Pc (tgt e)) := by
      intro e
      rw [hSe]; apply Finset.sum_congr rfl; intro c _
      rw [hX]; unfold WECEdge.Xc
      simp_rw [hXL, hXS]
      rw [add_div, Finset.sum_mul_sum, Finset.sum_div]
      congr 1
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_div]
    simp_rw [hSrw, ← hμ]
    -- pointwise triangle inequality
    have hpt : ∀ e ∈ G.inc v, G.w e * |Se e (Pc (src e)) (Pc (tgt e)) - μ e|
        ≤ G.w e * disc e v (Pc v) (Pc (oth e v)) +
          (if src e = v then G.w e * |ms e (Pc v) - μ e|
           else G.w e * |Se e (Pc (src e)) (Pc v) - ms e (Pc (src e))|) := by
      intro e he
      have hw := (G.w_pos e).le
      by_cases hs : src e = v
      · simp only [hdisc, oth, if_pos hs]
        rw [← hs]
        rw [← mul_add]
        apply mul_le_mul_of_nonneg_left _ hw
        calc |Se e (Pc (src e)) (Pc (tgt e)) - μ e|
            = |(Se e (Pc (src e)) (Pc (tgt e)) - ms e (Pc (src e))) + (ms e (Pc (src e)) - μ e)| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      · have ht : tgt e = v := by
          rcases (hmem e v).mp ((hinc e v).mp he) with h | h
          · exact absurd h.symm hs
          · exact h.symm
        simp only [hdisc, oth, if_neg hs]
        rw [← ht, ← mul_add]
        apply mul_le_mul_of_nonneg_left _ hw
        calc |Se e (Pc (src e)) (Pc (tgt e)) - μ e|
            = |(ms e (Pc (src e)) - μ e) + (Se e (Pc (src e)) (Pc (tgt e)) - ms e (Pc (src e)))| := by ring_nf
          _ ≤ _ := abs_add_le _ _
    have hsum1 := Finset.sum_le_sum hpt
    rw [Finset.sum_add_distrib, ← hsplit_inc v (fun e => G.w e * |ms e (Pc v) - μ e|)
      (fun e => G.w e * |Se e (Pc (src e)) (Pc v) - ms e (Pc (src e))|)] at hsum1
    -- the own conditions
    have hO1v : O1 v (Pc v) ≤ t := by
      have := (hQ2 (g v) (seq (g v).val) v rfl).1
      rwa [hQ_P (g v) v rfl] at this
    have hO2v : O2 Pc v (Pc v) ≤ t := by
      have h1 := (hQ2 (g v) (seq (g v).val) v rfl).2
      rw [hQ_P (g v) v rfl] at h1
      have h2 : O2 Pc v (Pc v) = O2 (seq (g v).val) v (Pc v) := by
        rw [hO2, hO2]
        apply Finset.sum_congr rfl; intro e he
        have ht : tgt e = v := (Finset.mem_filter.mp he).2
        have hlt : (g (src e)).val < (g v).val := by rw [← ht]; exact hor e
        rw [hPp_P (g v) (src e) hlt]
      rw [h2]; exact h1
    have hO1e : ∑ e ∈ Finset.univ.filter (fun e => src e = v), G.w e * |ms e (Pc v) - μ e| = O1 v (Pc v) := by
      rw [hO1]
    have hO2e : ∑ e ∈ Finset.univ.filter (fun e => tgt e = v),
        G.w e * |Se e (Pc (src e)) (Pc v) - ms e (Pc (src e))| = O2 Pc v (Pc v) := by
      rw [hO2]
    rw [hO1e, hO2e] at hsum1
    -- the discrepancy rows
    have hdisc_indep : ∀ e Lv Lv' Lo, ¬ src e = v → disc e v Lv Lo = disc e v Lv' Lo := by
      intro e Lv Lv' Lo hs; rw [hdisc, hdisc, if_neg hs, if_neg hs]
    have hdk : ∀ k : Fin r, (1 / Bd) * ∑ e ∈ (G.inc v).filter (fun e => g (oth e v) = k),
        G.w e * disc e v (Pc v) (Pc (oth e v))
        ≤ (1 / Bd) * (∑ e ∈ (G.inc v).filter (fun e => g (oth e v) = k), G.w e * Real.sqrt (κ₁ / n))
          / (1 - ρ) + Err := by
      intro k
      have h1 := hQ4 k (seq k.val) v
      refine le_trans (le_of_eq ?_) h1
      congr 1
      apply Finset.sum_congr rfl; intro e he
      rw [hgoth e v k he]
      by_cases hs : src e = v
      · have hk : g (oth e v) = k := (Finset.mem_filter.mp he).2
        have hlt : (g v).val < k.val := by
          rw [← hk]; simp only [oth, if_pos hs]; rw [← hs]; exact hor e
        rw [hPp_P k v hlt]
      · rw [hdisc_indep e (Pc v) (seq k.val v) _ hs]
    have hdall := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hdk k)
    rw [← Finset.mul_sum, hpart, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_div, ← Finset.mul_sum, hpart] at hdall
    have hwsum : ∑ e ∈ G.inc v, G.w e * Real.sqrt (κ₁ / n) ≤ n * Real.sqrt (κ₁ / n) := by
      rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (hW v) (Real.sqrt_nonneg _)
    have hnsq : n * Real.sqrt (κ₁ / n) ≤ Real.sqrt κ₁ * n ^ (3 / 4 : ℝ) := by
      rw [Real.sqrt_div' _ hn0.le, Real.sqrt_eq_rpow n]
      have e1 : n * (Real.sqrt κ₁ / n ^ (1 / 2 : ℝ)) = Real.sqrt κ₁ * n ^ (1 / 2 : ℝ) := by
        have e : n = n ^ (1 / 2 : ℝ) * n ^ (1 / 2 : ℝ) := by rw [← Real.rpow_add hn0]; norm_num
        have : 0 < n ^ (1 / 2 : ℝ) := by positivity
        rw [div_eq_mul_inv]; nth_rewrite 1 [e]; field_simp
      rw [e1]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num))
        (Real.sqrt_nonneg _)
    have hρ2 : 1 / (1 - ρ) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    have hdisc_tot : ∑ e ∈ G.inc v, G.w e * disc e v (Pc v) (Pc (oth e v))
        ≤ 2 * Real.sqrt κ₁ * n ^ (3 / 4 : ℝ) + r * Bd * (cE * n ^ (3 / 4 : ℝ)) := by
      have h1 : ∑ e ∈ G.inc v, G.w e * disc e v (Pc v) (Pc (oth e v))
          ≤ (∑ e ∈ G.inc v, G.w e * Real.sqrt (κ₁ / n)) / (1 - ρ) + r * Bd * Err := by
        have e1 : (1 / Bd) * (∑ e ∈ G.inc v, G.w e * Real.sqrt (κ₁ / n)) / (1 - ρ)
            = (1 / Bd) * ((∑ e ∈ G.inc v, G.w e * Real.sqrt (κ₁ / n)) / (1 - ρ)) := by ring
        rw [e1] at hdall
        have := mul_le_mul_of_nonneg_left hdall hBd0.le
        rw [mul_add, ← mul_assoc, ← mul_assoc, mul_one_div_cancel hBd0.ne', one_mul, one_mul] at this
        linarith
      have h2 : (∑ e ∈ G.inc v, G.w e * Real.sqrt (κ₁ / n)) / (1 - ρ) ≤ 2 * Real.sqrt κ₁ * n ^ (3 / 4 : ℝ) := by
        rw [div_eq_mul_one_div]
        have h3 : 0 ≤ ∑ e ∈ G.inc v, G.w e * Real.sqrt (κ₁ / n) :=
          Finset.sum_nonneg (fun e _ => mul_nonneg (G.w_pos e).le (Real.sqrt_nonneg _))
        calc (∑ e ∈ G.inc v, G.w e * Real.sqrt (κ₁ / n)) * (1 / (1 - ρ))
            ≤ (Real.sqrt κ₁ * n ^ (3 / 4 : ℝ)) * 2 := mul_le_mul (le_trans hwsum hnsq) hρ2
              (by positivity) (by positivity)
          _ = 2 * Real.sqrt κ₁ * n ^ (3 / 4 : ℝ) := by ring
      have h4 : r * Bd * Err ≤ r * Bd * (cE * n ^ (3 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hErrle (by positivity)
      linarith
    rw [ht] at hO1v hO2v
    have hK : (2 + 2 * Real.sqrt κ₁ + r * cE * Bd) * n ^ (3 / 4 : ℝ)
        = 2 * Real.sqrt κ₁ * n ^ (3 / 4 : ℝ) + r * Bd * (cE * n ^ (3 / 4 : ℝ)) +
          n ^ (3 / 4 : ℝ) + n ^ (3 / 4 : ℝ) := by ring
    rw [hK]
    linarith

theorem solution (C₀ C₁ θ σ r₀ β : ℝ) (M Ks r : ℕ)
    (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) (hθ : 0 < θ) (hσ0 : 0 < σ) (hσ1 : σ < 1) (hr₀ : 0 < r₀)
    (hβ : 0 < β) :
    ∃ n₀ K : ℝ, ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      (G : WGraph V E), G.IsSimple → ∀ g : V → Fin r,
      (∀ (e : E) (u v : V), G.ends e = s(u, v) → g u ≠ g v) →
      ∀ (src tgt : E → V), (∀ e, G.ends e = s(src e, tgt e)) →
      ∀ n : ℝ, n₀ ≤ n → (∀ v, G.W v ≤ n) →
      ∀ (𝒞 : Type) [Fintype 𝒞] [DecidableEq 𝒞], (Fintype.card 𝒞 : ℝ) ≤ C₁ * n →
      ∀ (y : E → 𝒞 → ℝ) (lam : V → 𝒞 → Fin M → ℝ) (R : V → 𝒞 → Fin M → ℝ)
        (aL : V → 𝒞 → E → Fin M → Fin Ks → ℝ) (aS : V → 𝒞 → E → Fin M → ℝ),
      (∀ e c, 0 ≤ y e c ∧ y e c ≤ C₀ / n) →
      (∀ v c P, θ / M ≤ lam v c P) → (∀ v c, ∑ P, lam v c P = 1) →
      (∀ v c P, R v c P = 0 ∨ r₀ ≤ R v c P) →
      (∀ v c e P i, 0 ≤ aL v c e P i) → (∀ v c e P, 0 ≤ aS v c e P) →
      (∀ v c e P, aS v c e P ≠ 0 → 0 < R v c P) →
      -- every edge is either large (slot fractions only) or small (reserve fractions only)
      (∀ v c e P i, aL v c e P i ≠ 0 → β ≤ G.w e) → (∀ v c e P, aS v c e P ≠ 0 → G.w e < β) →
      -- the fractions of `e` at each of its ends add up to `y e c`
      (∀ v c e, v ∈ G.ends e → ∑ P, (∑ i, aL v c e P i + aS v c e P) = y e c) →
      -- capacities hold in expectation, with slack `σ`
      (∀ v c P i, ∑ e ∈ G.inc v, aL v c e P i ≤ (1 - σ) * lam v c P) →
      (∀ v c P, ∑ e ∈ G.inc v, G.w e * aS v c e P ≤ (1 - σ) * lam v c P * R v c P) →
      ∃ Pc : V → 𝒞 → Fin M, ∀ (XL : E → 𝒞 → Fin Ks → Fin Ks → ℝ) (XS : E → 𝒞 → ℝ),
        (∀ e c i j, XL e c i j = aL (src e) c e (Pc (src e) c) i * aL (tgt e) c e (Pc (tgt e) c) j /
            (y e c * lam (src e) c (Pc (src e) c) * lam (tgt e) c (Pc (tgt e) c))) →
        (∀ e c, XS e c = aS (src e) c e (Pc (src e) c) * aS (tgt e) c e (Pc (tgt e) c) /
            (y e c * lam (src e) c (Pc (src e) c) * lam (tgt e) c (Pc (tgt e) c))) →
        -- every slot of a chosen profile keeps slack `σ / 2`
        (∀ v c i, ∑ e ∈ Finset.univ.filter (fun e => src e = v), ∑ j, XL e c i j
           + ∑ e ∈ Finset.univ.filter (fun e => tgt e = v), ∑ j, XL e c j i ≤ 1 - σ / 2) ∧
        (∀ v c, ∑ e ∈ G.inc v, G.w e * XS e c ≤ (1 - σ / 2) * R v c (Pc v c)) ∧
        -- small weighted discrepancy at every vertex
        ∀ v, ∑ e ∈ G.inc v, G.w e *
          |∑ c, (∑ i, ∑ j, XL e c i j + XS e c) - ∑ c, y e c| ≤ K * n ^ (3 / 4 : ℝ) := by
  classical
  obtain ⟨n₀, K, hor⟩ := pc_oriented C₀ C₁ θ σ r₀ β M Ks r hC₀ hC₁ hθ hσ0 hσ1 hr₀ hβ
  refine ⟨n₀, K, ?_⟩
  intro V E _ _ _ _ G hG g hg src tgt hst n hn hW 𝒞 _ _ hcard y lam R aL aS hy hlamlo hlam1 hR
    haL0 haS0 haSR htypL htypS hmarg hcapL hcapS
  have hne : ∀ e, g (src e) ≠ g (tgt e) := fun e => hg e (src e) (tgt e) (hst e)
  let sw : E → Prop := fun e => g (tgt e) < g (src e)
  let src' : E → V := fun e => if sw e then tgt e else src e
  let tgt' : E → V := fun e => if sw e then src e else tgt e
  have hst' : ∀ e, G.ends e = s(src' e, tgt' e) := by
    intro e; simp only [src', tgt']; split_ifs
    · rw [hst e, Sym2.eq_swap]
    · exact hst e
  have hor' : ∀ e, g (src' e) < g (tgt' e) := by
    intro e; simp only [src', tgt', sw]; split_ifs with h
    · exact h
    · exact lt_of_le_of_ne (not_lt.mp h) (hne e)
  obtain ⟨Pc, hPc⟩ := hor V E G hG g hg src' tgt' hst' hor' n hn hW 𝒞 hcard y lam R aL aS hy
    hlamlo hlam1 hR haL0 haS0 haSR htypL htypS hmarg hcapL hcapS
  refine ⟨Pc, fun XL XS hXL hXS => ?_⟩
  -- the options for the reoriented edges
  obtain ⟨hload, hres, hdisc⟩ := hPc
    (fun e c i j => aL (src' e) c e (Pc (src' e) c) i * aL (tgt' e) c e (Pc (tgt' e) c) j /
      (y e c * lam (src' e) c (Pc (src' e) c) * lam (tgt' e) c (Pc (tgt' e) c)))
    (fun e c => aS (src' e) c e (Pc (src' e) c) * aS (tgt' e) c e (Pc (tgt' e) c) /
      (y e c * lam (src' e) c (Pc (src' e) c) * lam (tgt' e) c (Pc (tgt' e) c)))
    (fun _ _ _ _ => rfl) (fun _ _ => rfl)
  have hXSsym : ∀ e c, XS e c = aS (src' e) c e (Pc (src' e) c) * aS (tgt' e) c e (Pc (tgt' e) c) /
      (y e c * lam (src' e) c (Pc (src' e) c) * lam (tgt' e) c (Pc (tgt' e) c)) := by
    intro e c; rw [hXS]; simp only [src', tgt']; split_ifs <;> ring
  have hXLsym : ∀ e c i j, XL e c i j = if sw e then
      aL (src' e) c e (Pc (src' e) c) j * aL (tgt' e) c e (Pc (tgt' e) c) i /
        (y e c * lam (src' e) c (Pc (src' e) c) * lam (tgt' e) c (Pc (tgt' e) c))
      else aL (src' e) c e (Pc (src' e) c) i * aL (tgt' e) c e (Pc (tgt' e) c) j /
        (y e c * lam (src' e) c (Pc (src' e) c) * lam (tgt' e) c (Pc (tgt' e) c)) := by
    intro e c i j; rw [hXL]; simp only [src', tgt']; split_ifs <;> ring
  refine ⟨?_, ?_, ?_⟩
  · intro v c i
    refine le_trans (le_of_eq ?_) (hload v c i)
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro e _
    simp_rw [hXLsym]
    by_cases hs : sw e
    · simp only [src', tgt', if_pos hs]
      rw [add_comm]
    · simp only [src', tgt', if_neg hs]
  · intro v c
    refine le_trans (le_of_eq ?_) (hres v c)
    apply Finset.sum_congr rfl; intro e _
    rw [hXSsym]
  · intro v
    refine le_trans (le_of_eq ?_) (hdisc v)
    apply Finset.sum_congr rfl; intro e _
    congr 3
    apply Finset.sum_congr rfl; intro c _
    rw [hXSsym]
    congr 1
    simp_rw [hXLsym]
    by_cases hs : sw e
    · simp only [if_pos hs]; rw [Finset.sum_comm]
    · simp only [if_neg hs]
