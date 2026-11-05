-- Prove2me | solution 1 for QualityEncroach.FixedCost.proposition_6_i
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T04:22:51.852569+00:00
-- url     : https://prove2.me/submissions/09f192b1-652a-431b-b7ea-5d29b711dd77

import Mathlib
import Definitions.Def_QualityEncroach_FixedCost_Game
import Definitions.Def_QualityEncroach_FixedCost_Reduced
import Theorems.Thm_QualityEncroach_FixedCost_claim_3
import Theorems.Thm_QualityEncroach_FixedCost_lemma_2

open Filter Topology

namespace QE3Main

open QualityEncroach.FixedCost

/-- A concave quadratic cannot have a local maximum away from its vertex. -/
lemma quad_locmax (f : ℝ → ℝ) (R α xs x0 : ℝ) (hα : 0 < α)
    (hf : ∀ x, f x = R - α * (x - xs) ^ 2) (S : Set ℝ) (hS : S ∈ 𝓝 x0)
    (hmax : ∀ x ∈ S, f x ≤ f x0) : x0 = xs := by
  by_contra hne
  have hcont : Tendsto (fun θ : ℝ => x0 + θ * (xs - x0)) (𝓝[>] 0) (𝓝 x0) := by
    have : Tendsto (fun θ : ℝ => x0 + θ * (xs - x0)) (𝓝 0) (𝓝 (x0 + 0 * (xs - x0))) :=
      ((continuous_const.add (continuous_id.mul continuous_const)).tendsto 0)
    simpa using this.mono_left nhdsWithin_le_nhds
  have h1 : ∀ᶠ θ in 𝓝[>] (0:ℝ), x0 + θ * (xs - x0) ∈ S := hcont hS
  have h2 : ∀ᶠ θ in 𝓝[>] (0:ℝ), θ ∈ Set.Ioo (0:ℝ) 1 := Ioo_mem_nhdsGT one_pos
  obtain ⟨θ, hθS, hθ0, hθ1⟩ := (h1.and h2).exists
  have hle := hmax _ hθS
  rw [hf, hf] at hle
  have hd : (x0 - xs) ≠ 0 := sub_ne_zero.mpr hne
  have hsq : 0 < (x0 - xs) ^ 2 := by positivity
  have e : x0 + θ * (xs - x0) - xs = (1 - θ) * (x0 - xs) := by ring
  rw [e] at hle
  have h3 : (1 - θ) ^ 2 < 1 := by nlinarith
  have h4 : (1 - θ) ^ 2 * (x0 - xs) ^ 2 < (x0 - xs) ^ 2 := by nlinarith
  have h5 := mul_lt_mul_of_pos_left h4 hα
  nlinarith

variable {k c : ℝ} {σ : Profile}

/-- Stage 3: the manufacturer's direct quantity is the unique best reply. -/
lemma direct_eq (hσ : IsSPE k c σ) (w u t q a : ℝ) (hu : 0 < u) (ht : 0 < t) (hq : 0 ≤ q)
    (hpM : ∀ qM, QualityEncroach.Differ.priceM u t qM q = u * (1 - qM - a * q)) :
    σ.direct w u t q = max 0 ((1 - a * q - c / u) / 2) := by
  set m := (1 - a * q - c / u) / 2 with hm
  have hcu : u * (c / u) = c := mul_div_cancel₀ c hu.ne'
  have hF : ∀ x, mfrPayoff k c ⟨w, u, t, q, x⟩ =
      w * q + (2 * u * m - u * x) * x - max (k * u ^ 2) (k * (t * u) ^ 2) := by
    intro x
    simp only [mfrPayoff, hpM, hm]
    linear_combination x * hcu
  have hd0 := hσ.direct_nonneg w u t q hu ht hq
  have hopt := hσ.direct_optimal w u t q (max 0 m) hu ht hq (le_max_left _ _)
  simp only [Profile.outcomeAtDirect] at hopt
  rw [hF, hF] at hopt
  set d := σ.direct w u t q
  have key : u * (d - max 0 m) ^ 2 ≤ 0 := by
    rcases le_total 0 m with h | h
    · rw [max_eq_right h] at hopt ⊢; nlinarith
    · rw [max_eq_left h] at hopt ⊢
      nlinarith [mul_nonneg (mul_nonneg hu.le hd0) (neg_nonneg.mpr h)]
  have h2 : (d - max 0 m) ^ 2 ≤ 0 := by
    by_contra h; push Not at h; nlinarith [mul_pos hu h]
  have h3 := le_antisymm h2 (sq_nonneg _)
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3)

/-- Stage 2: the retailer's order is the unique best reply when it induces positive direct
sales. The wholesale price is parametrized by the induced order `q`. -/
lemma order_eq (hσ : IsSPE k c σ) (u t q a γ : ℝ) (hu : 0 < u) (ht : 0 < t) (hq : 0 ≤ q)
    (hpM : ∀ qM x, QualityEncroach.Differ.priceM u t qM x = u * (1 - qM - a * x))
    (hpR : ∀ qM x, QualityEncroach.Differ.priceR u t qM x = t * u * (1 - x) - γ * qM)
    (hA : 0 < t * u - γ * a / 2) (hγ : 0 < γ)
    (hm : 0 < (1 - a * q - c / u) / 2) :
    σ.order (t * u - γ * (1 - c / u) / 2 - 2 * (t * u - γ * a / 2) * q) u t = q := by
  set w := t * u - γ * (1 - c / u) / 2 - 2 * (t * u - γ * a / 2) * q with hw
  have hdir : ∀ x, 0 ≤ x → σ.direct w u t x = max 0 ((1 - a * x - c / u) / 2) :=
    fun x hx => direct_eq hσ w u t x a hu ht hx (fun qM => hpM qM x)
  have hq' := hσ.order_nonneg w u t hu ht
  have hopt := hσ.order_optimal w u t q hu ht hq
  simp only [Profile.outcomeAtOrder, Profile.outcomeAtDirect,
    QualityEncroach.Differ.retailerPayoff, hpR] at hopt
  set q' := σ.order w u t
  rw [hdir q hq, hdir q' hq', max_eq_right hm.le] at hopt
  have hle : (t * u * (1 - q') - γ * max 0 ((1 - a * q' - c / u) / 2) - w) * q' ≤
      (t * u * (1 - q') - γ * ((1 - a * q' - c / u) / 2) - w) * q' := by
    have := le_max_right 0 ((1 - a * q' - c / u) / 2)
    nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hγ.le hq')]
  have key : (t * u - γ * a / 2) * (q' - q) ^ 2 ≤ 0 := by
    rw [hw] at hopt hle; nlinarith
  have h2 : (q' - q) ^ 2 ≤ 0 := by
    by_contra h; push Not at h; nlinarith [mul_pos hA h]
  have h3 := le_antisymm h2 (sq_nonneg _)
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3)

/-- Manufacturer's payoff after the wholesale price inducing the order `q`. -/
lemma payoff_dev (hσ : IsSPE k c σ) (u t q a γ : ℝ) (hu : 0 < u) (ht : 0 < t) (hq : 0 ≤ q)
    (hpM : ∀ qM x, QualityEncroach.Differ.priceM u t qM x = u * (1 - qM - a * x))
    (hpR : ∀ qM x, QualityEncroach.Differ.priceR u t qM x = t * u * (1 - x) - γ * qM)
    (hA : 0 < t * u - γ * a / 2) (hγ : 0 < γ)
    (hm : 0 < (1 - a * q - c / u) / 2) :
    mfrPayoff k c (σ.outcomeAtOrder
      (t * u - γ * (1 - c / u) / 2 - 2 * (t * u - γ * a / 2) * q) u t) =
      (t * u - γ * (1 - c / u) / 2 - 2 * (t * u - γ * a / 2) * q) * q +
        u * ((1 - a * q - c / u) / 2) ^ 2 - max (k * u ^ 2) (k * (t * u) ^ 2) := by
  have ho := order_eq hσ u t q a γ hu ht hq hpM hpR hA hγ hm
  simp only [Profile.outcomeAtOrder, Profile.outcomeAtDirect, ho]
  rw [direct_eq hσ _ u t q a hu ht hq (fun qM => hpM qM q), max_eq_right hm.le]
  simp only [mfrPayoff, hpM]
  have hu0 : u ≠ 0 := hu.ne'
  field_simp
  ring

/-- Stage 2 at the path: an interior order satisfies the retailer's first-order condition. -/
lemma path_foc (hσ : IsSPE k c σ) (w u t q a γ : ℝ) (hu : 0 < u) (ht : 0 < t) (hq : 0 < q)
    (ha : 0 ≤ a)
    (hpR : ∀ qM x, QualityEncroach.Differ.priceR u t qM x = t * u * (1 - x) - γ * qM)
    (hpM : ∀ qM x, QualityEncroach.Differ.priceM u t qM x = u * (1 - qM - a * x))
    (hA : 0 < t * u - γ * a / 2)
    (hm : 0 < (1 - a * q - c / u) / 2) (hord : σ.order w u t = q) :
    w = t * u - γ * (1 - c / u) / 2 - 2 * (t * u - γ * a / 2) * q := by
  set A := t * u - γ * a / 2 with hAdef
  set B := t * u - γ * (1 - c / u) / 2 - w with hB
  have hdir : ∀ x, 0 ≤ x → σ.direct w u t x = max 0 ((1 - a * x - c / u) / 2) :=
    fun x hx => direct_eq hσ w u t x a hu ht hx (fun qM => hpM qM x)
  let S : Set ℝ := {x | 0 < x ∧ 0 < (1 - a * x - c / u) / 2}
  have hSopen : IsOpen S := by
    apply IsOpen.inter (isOpen_lt continuous_const continuous_id)
    exact isOpen_lt continuous_const
      (show Continuous (fun x : ℝ => (1 - a * x - c / u) / 2) by fun_prop)
  have hqS : q ∈ S := ⟨hq, hm⟩
  have hfeq : ∀ x, (B - A * x) * x = B ^ 2 / (4 * A) - A * (x - B / (2 * A)) ^ 2 := by
    intro x; field_simp; ring
  have hmax : ∀ x ∈ S, (B - A * x) * x ≤ (B - A * q) * q := by
    intro x hx
    have hopt := hσ.order_optimal w u t x hu ht hx.1.le
    simp only [Profile.outcomeAtOrder, Profile.outcomeAtDirect,
      QualityEncroach.Differ.retailerPayoff, hpR, hord] at hopt
    rw [hdir x hx.1.le, hdir q hq.le, max_eq_right hx.2.le, max_eq_right hm.le] at hopt
    have e1 : (t * u * (1 - x) - γ * ((1 - a * x - c / u) / 2) - w) * x = (B - A * x) * x := by
      rw [hB, hAdef]; ring
    have e2 : (t * u * (1 - q) - γ * ((1 - a * q - c / u) / 2) - w) * q = (B - A * q) * q := by
      rw [hB, hAdef]; ring
    linarith
  have := quad_locmax (fun x => (B - A * x) * x) (B ^ 2 / (4 * A)) A (B / (2 * A)) q hA hfeq S
    (hSopen.mem_nhds hqS) hmax
  have hA0 : A ≠ 0 := hA.ne'
  have : B = 2 * A * q := by rw [this]; field_simp
  rw [hB] at this
  linarith

/-- Price formulas on the high-direct-quality branch. -/
lemma hi_pM (u t : ℝ) (ht1 : t ≤ 1) :
    ∀ qM x, QualityEncroach.Differ.priceM u t qM x = u * (1 - qM - t * x) := by
  intro qM x; unfold QualityEncroach.Differ.priceM; rw [if_pos ht1]

lemma hi_pR (u t : ℝ) (ht1 : t ≤ 1) :
    ∀ qM x, QualityEncroach.Differ.priceR u t qM x = t * u * (1 - x) - (t * u) * qM := by
  intro qM x; unfold QualityEncroach.Differ.priceR; rw [if_pos ht1]; ring

lemma lo_pM (u t : ℝ) (ht1 : 1 ≤ t) :
    ∀ qM x, QualityEncroach.Differ.priceM u t qM x = u * (1 - qM - 1 * x) := by
  intro qM x; unfold QualityEncroach.Differ.priceM
  split_ifs with h
  · have : t = 1 := le_antisymm h ht1
    subst this; ring
  · ring

lemma lo_pR (u t : ℝ) (ht1 : 1 ≤ t) :
    ∀ qM x, QualityEncroach.Differ.priceR u t qM x = t * u * (1 - x) - u * qM := by
  intro qM x; unfold QualityEncroach.Differ.priceR
  split_ifs with h
  · have : t = 1 := le_antisymm h ht1
    subst this; ring
  · ring

lemma hi_cost (k u t : ℝ) (hk : 0 < k) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    max (k * u ^ 2) (k * (t * u) ^ 2) = k * u ^ 2 := by
  apply max_eq_left
  have : (t * u) ^ 2 ≤ u ^ 2 := by
    have ht2 : t ^ 2 ≤ 1 := by nlinarith
    rw [mul_pow]; nlinarith [mul_le_mul_of_nonneg_right ht2 (sq_nonneg u)]
  nlinarith

lemma lo_cost (k u t : ℝ) (hk : 0 < k) (ht1 : 1 ≤ t) :
    max (k * u ^ 2) (k * (t * u) ^ 2) = k * t ^ 2 * u ^ 2 := by
  rw [max_eq_right]
  · ring
  · have : u ^ 2 ≤ (t * u) ^ 2 := by
      have ht2 : 1 ≤ t ^ 2 := by nlinarith
      rw [mul_pow]; nlinarith [mul_le_mul_of_nonneg_right ht2 (sq_nonneg u)]
    nlinarith

/-- The induced manufacturer revenue on the high branch as a concave quadratic. -/
lemma hi_psi (c u t x : ℝ) (hu : 0 < u) (ht1 : t ≤ 1) :
    (t * u - (t * u) * (1 - c / u) / 2 - 2 * (t * u - (t * u) * t / 2) * x) * x +
      u * ((1 - t * x - c / u) / 2) ^ 2 =
      (u + (8 - t) * c ^ 2 / ((8 - 5 * t) * u) - 2 * c) / 4 -
        (t * u * (8 - 5 * t) / 4) * (x - 2 * c / ((8 - 5 * t) * u)) ^ 2 := by
  have h85 : 8 - 5 * t ≠ 0 := by intro h; linarith
  have hu0 : u ≠ 0 := hu.ne'
  generalize hD : 8 - 5 * t = D at *
  field_simp
  have ht : t = (8 - D) / 5 := by linarith
  subst ht
  ring

lemma lo_psi (c u t x : ℝ) (hu : 0 < u) (ht1 : 1 ≤ t) :
    (t * u - u * (1 - c / u) / 2 - 2 * (t * u - u * 1 / 2) * x) * x +
      u * ((1 - 1 * x - c / u) / 2) ^ 2 =
      ((4 * t ^ 2 - 1) * u / (4 * (8 * t - 5)) + (1 - 4 * t) * c / (2 * (8 * t - 5)) +
        (8 * t - 1) * c ^ 2 / (4 * (8 * t - 5) * u)) -
        (u * (8 * t - 5) / 4) * (x - (2 * c / ((8 * t - 5) * u) + 2 * (t - 1) / (8 * t - 5))) ^ 2 := by
  have h85 : 8 * t - 5 ≠ 0 := by intro h; linarith
  have hu0 : u ≠ 0 := hu.ne'
  generalize hD : 8 * t - 5 = D at *
  field_simp
  have ht : t = (D + 5) / 8 := by linarith
  subst ht
  ring

lemma hi_m (c u t : ℝ) (hu : 0 < u) (ht1 : t ≤ 1) :
    (1 - t * (2 * c / ((8 - 5 * t) * u)) - c / u) / 2 =
      ((8 - 5 * t) * u - (8 - 3 * t) * c) / (2 * (8 - 5 * t) * u) := by
  have h85 : 8 - 5 * t ≠ 0 := by intro h; linarith
  have hu0 : u ≠ 0 := hu.ne'
  generalize hD : 8 - 5 * t = D at *
  field_simp
  have ht : t = (8 - D) / 5 := by linarith
  subst ht
  ring

lemma lo_m (c u t : ℝ) (hu : 0 < u) (ht1 : 1 ≤ t) :
    (1 - 1 * (2 * c / ((8 * t - 5) * u) + 2 * (t - 1) / (8 * t - 5)) - c / u) / 2 =
      ((6 * t - 3) * u - (8 * t - 3) * c) / (2 * (8 * t - 5) * u) := by
  have h85 : 8 * t - 5 ≠ 0 := by intro h; linarith
  have hu0 : u ≠ 0 := hu.ne'
  generalize hD : 8 * t - 5 = D at *
  field_simp
  have ht : t = (D + 5) / 8 := by linarith
  subst ht
  ring

end QE3Main

open QE3Main QualityEncroach.FixedCost in
theorem solution (k c : ℝ) (hk : 0 < k) (hc : 0 < c)
    (σ : QualityEncroach.FixedCost.Profile) (hσ : QualityEncroach.FixedCost.IsSPE k c σ)
    (henc : 0 < σ.path.qM) :
    σ.t = 1 := by
  -- the equilibrium payoff
  set P := mfrPayoff k c σ.path with hP
  have hfo : ∀ w u t : ℝ, 0 < u → 0 < t → mfrPayoff k c (σ.outcomeAtOrder w u t) ≤ P :=
    fun w u t hu ht => hσ.first_optimal w u t hu ht
  -- lower bound from the high branch
  have lbHi : ∀ t' u' : ℝ, 0 < t' → t' ≤ 1 → (8 - 3 * t') * c / (8 - 5 * t') < u' →
      PiHi k c t' u' ≤ P := by
    intro t' u' ht0 ht1 hfe
    have h85 : 0 < 8 - 5 * t' := by linarith
    have hu' : 0 < u' := by
      have : 0 < (8 - 3 * t') * c / (8 - 5 * t') := div_pos (by nlinarith) h85
      linarith
    have hm : 0 < (1 - t' * (2 * c / ((8 - 5 * t') * u')) - c / u') / 2 := by
      rw [hi_m c u' t' hu' ht1]
      apply div_pos _ (by positivity)
      rw [div_lt_iff₀ h85] at hfe; linarith
    have hA : 0 < t' * u' - (t' * u') * t' / 2 := by nlinarith [mul_pos ht0 hu']
    have hq : 0 ≤ 2 * c / ((8 - 5 * t') * u') := by positivity
    have := payoff_dev hσ u' t' _ t' (t' * u') hu' ht0 hq (hi_pM u' t' ht1) (hi_pR u' t' ht1)
      hA (mul_pos ht0 hu') hm
    rw [hi_psi c u' t' _ hu' ht1, hi_cost k u' t' hk ht0 ht1, sub_self, zero_pow two_ne_zero,
      mul_zero, sub_zero] at this
    have h2 := hfo (t' * u' - t' * u' * (1 - c / u') / 2 - 2 * (t' * u' - t' * u' * t' / 2) *
      (2 * c / ((8 - 5 * t') * u'))) u' t' hu' ht0
    rw [this] at h2
    unfold PiHi; linarith
  -- lower bound from the low branch
  have lbLo : ∀ t' u' : ℝ, 1 ≤ t' → (8 * t' - 3) * c < (6 * t' - 3) * u' →
      PiLo k c t' u' ≤ P := by
    intro t' u' ht1 hfe
    have ht0 : 0 < t' := by linarith
    have h85 : 0 < 8 * t' - 5 := by linarith
    have hu' : 0 < u' := by
      by_contra hh; push Not at hh; nlinarith
    have hm : 0 < (1 - 1 * (2 * c / ((8 * t' - 5) * u') + 2 * (t' - 1) / (8 * t' - 5)) - c / u') / 2 := by
      rw [lo_m c u' t' hu' ht1]
      apply div_pos _ (by positivity)
      linarith
    have hA : 0 < t' * u' - u' * 1 / 2 := by nlinarith
    have hq : 0 ≤ 2 * c / ((8 * t' - 5) * u') + 2 * (t' - 1) / (8 * t' - 5) := by
      have : 0 ≤ 2 * (t' - 1) / (8 * t' - 5) := div_nonneg (by linarith) h85.le
      positivity
    have := payoff_dev hσ u' t' _ 1 u' hu' ht0 hq (lo_pM u' t' ht1) (lo_pR u' t' ht1)
      hA hu' hm
    rw [lo_psi c u' t' _ hu' ht1, lo_cost k u' t' hk ht1, sub_self, zero_pow two_ne_zero,
      mul_zero, sub_zero] at this
    have h2 := hfo (t' * u' - u' * (1 - c / u') / 2 - 2 * (t' * u' - u' * 1 / 2) *
      (2 * c / ((8 * t' - 5) * u') + 2 * (t' - 1) / (8 * t' - 5))) u' t' hu' ht0
    rw [this] at h2
    have e : PiLo k c t' u' = (4 * t' ^ 2 - 1) * u' / (4 * (8 * t' - 5)) + (1 - 4 * t') * c / (2 * (8 * t' - 5)) +
        (8 * t' - 1) * c ^ 2 / (4 * (8 * t' - 5) * u') - k * t' ^ 2 * u' ^ 2 := rfl
    linarith
  -- the path
  have hu0 := hσ.u_pos
  have ht0 := hσ.t_pos
  set w0 := σ.w
  set u0 := σ.u
  set t0 := σ.t
  set q0 := σ.order w0 u0 t0 with hq0
  have hq0nn : 0 ≤ q0 := hσ.order_nonneg w0 u0 t0 hu0 ht0
  have hpath : σ.path = ⟨w0, u0, t0, q0, σ.direct w0 u0 t0 q0⟩ := rfl
  rw [hpath] at henc
  simp only at henc
  -- generic path-structure facts
  rcases eq_or_lt_of_le hq0nn with hz | hqpos
  · -- no retailer sales: a contradiction
    exfalso
    have hpM0 : ∀ qM, QualityEncroach.Differ.priceM u0 t0 qM q0 = u0 * (1 - qM - 0 * q0) := by
      intro qM; rw [← hz]; unfold QualityEncroach.Differ.priceM; split_ifs <;> ring
    have hd := direct_eq hσ w0 u0 t0 q0 0 hu0 ht0 hq0nn hpM0
    rw [hd] at henc
    have hm0 : 0 < (1 - 0 * q0 - c / u0) / 2 := by
      by_contra h; push Not at h; rw [max_eq_left h] at henc; exact lt_irrefl _ henc
    have hPv : P = u0 * ((1 - c / u0) / 2) ^ 2 - max (k * u0 ^ 2) (k * (t0 * u0) ^ 2) := by
      rw [hP, hpath]
      simp only [mfrPayoff]
      rw [hd, max_eq_right hm0.le, hpM0, ← hz]
      have hu00 : u0 ≠ 0 := hu0.ne'
      field_simp
      ring
    have hcost : k * u0 ^ 2 ≤ max (k * u0 ^ 2) (k * (t0 * u0) ^ 2) := le_max_left _ _
    have huc : c < u0 := by
      have : c / u0 < 1 := by linarith
      rwa [div_lt_one hu0] at this
    set t' := (u0 - c) / (u0 + c) with ht'
    have ht'0 : 0 < t' := div_pos (by linarith) (by linarith)
    have ht'1 : t' < 1 := by rw [ht', div_lt_one (by linarith)]; linarith
    have hfe : (8 - 3 * t') * c / (8 - 5 * t') < u0 := by
      rw [div_lt_iff₀ (by linarith)]
      have : t' * (u0 + c) = u0 - c := by rw [ht']; field_simp
      nlinarith
    have hlb := lbHi t' u0 ht'0 ht'1.le hfe
    have hgap : u0 * ((1 - c / u0) / 2) ^ 2 < (u0 + (8 - t') * c ^ 2 / ((8 - 5 * t') * u0) - 2 * c) / 4 := by
      have h85 : 0 < 8 - 5 * t' := by linarith
      have e : (u0 + (8 - t') * c ^ 2 / ((8 - 5 * t') * u0) - 2 * c) / 4 -
          u0 * ((1 - c / u0) / 2) ^ 2 = c ^ 2 * t' / ((8 - 5 * t') * u0) := by
        have h85' : 8 - 5 * t' ≠ 0 := h85.ne'
        have hu00 : u0 ≠ 0 := hu0.ne'
        clear_value t'
        generalize hD : 8 - 5 * t' = D at *
        field_simp
        have ht : t' = (8 - D) / 5 := by linarith
        subst ht
        ring
      have : 0 < c ^ 2 * t' / ((8 - 5 * t') * u0) := by positivity
      linarith
    unfold PiHi at hlb
    linarith
  · rcases le_or_gt t0 1 with ht1 | ht1
    · -- high branch
      have hA : 0 < t0 * u0 - (t0 * u0) * t0 / 2 := by nlinarith [mul_pos ht0 hu0]
      have hγ : 0 < t0 * u0 := mul_pos ht0 hu0
      have hd := direct_eq hσ w0 u0 t0 q0 t0 hu0 ht0 hq0nn (fun qM => hi_pM u0 t0 ht1 qM q0)
      rw [hd] at henc
      have hm0 : 0 < (1 - t0 * q0 - c / u0) / 2 := by
        by_contra h; push Not at h; rw [max_eq_left h] at henc; exact lt_irrefl _ henc
      have hw := path_foc hσ w0 u0 t0 q0 t0 (t0 * u0) hu0 ht0 hqpos ht0.le
        (hi_pR u0 t0 ht1) (hi_pM u0 t0 ht1) hA hm0 rfl
      have hPq : P = (t0 * u0 - (t0 * u0) * (1 - c / u0) / 2 - 2 * (t0 * u0 - (t0 * u0) * t0 / 2) * q0) * q0 +
          u0 * ((1 - t0 * q0 - c / u0) / 2) ^ 2 - max (k * u0 ^ 2) (k * (t0 * u0) ^ 2) := by
        rw [← payoff_dev hσ u0 t0 q0 t0 (t0 * u0) hu0 ht0 hq0nn (hi_pM u0 t0 ht1)
          (hi_pR u0 t0 ht1) hA hγ hm0, ← hw]
        rfl
      -- the path order maximizes the induced revenue
      let S : Set ℝ := {x | 0 < x ∧ 0 < (1 - t0 * x - c / u0) / 2}
      have hSopen : IsOpen S := by
        apply IsOpen.inter (isOpen_lt continuous_const continuous_id)
        exact isOpen_lt continuous_const
          (show Continuous (fun x : ℝ => (1 - t0 * x - c / u0) / 2) by fun_prop)
      have hmax : ∀ x ∈ S,
          (t0 * u0 - (t0 * u0) * (1 - c / u0) / 2 - 2 * (t0 * u0 - (t0 * u0) * t0 / 2) * x) * x +
            u0 * ((1 - t0 * x - c / u0) / 2) ^ 2 ≤
          (t0 * u0 - (t0 * u0) * (1 - c / u0) / 2 - 2 * (t0 * u0 - (t0 * u0) * t0 / 2) * q0) * q0 +
            u0 * ((1 - t0 * q0 - c / u0) / 2) ^ 2 := by
        intro x hx
        have := payoff_dev hσ u0 t0 x t0 (t0 * u0) hu0 ht0 hx.1.le (hi_pM u0 t0 ht1)
          (hi_pR u0 t0 ht1) hA hγ hx.2
        have h2 := hfo (t0 * u0 - (t0 * u0) * (1 - c / u0) / 2 - 2 * (t0 * u0 - (t0 * u0) * t0 / 2) * x)
          u0 t0 hu0 ht0
        rw [this, hPq] at h2
        linarith
      have hα : 0 < t0 * u0 * (8 - 5 * t0) / 4 := by
        have : 0 < 8 - 5 * t0 := by linarith
        positivity
      have hvert := quad_locmax _ _ _ _ q0 hα (fun x => hi_psi c u0 t0 x hu0 ht1) S
        (hSopen.mem_nhds ⟨hqpos, hm0⟩) hmax
      -- feasibility and the reduced profit
      have h85 : 0 < 8 - 5 * t0 := by linarith
      have hfe : (8 - 3 * t0) * c / (8 - 5 * t0) < u0 := by
        have := hm0
        rw [hvert, hi_m c u0 t0 hu0 ht1] at this
        have hnum : 0 < (8 - 5 * t0) * u0 - (8 - 3 * t0) * c := by
          by_contra h; push Not at h
          have : ((8 - 5 * t0) * u0 - (8 - 3 * t0) * c) / (2 * (8 - 5 * t0) * u0) ≤ 0 :=
            div_nonpos_of_nonpos_of_nonneg h (by positivity)
          linarith
        rw [div_lt_iff₀ h85]; linarith
      have hPPi : P = PiHi k c t0 u0 := by
        rw [hPq, hi_psi c u0 t0 q0 hu0 ht1, hi_cost k u0 t0 hk ht0 ht1, hvert, sub_self, zero_pow two_ne_zero,
          mul_zero, sub_zero]
        unfold PiHi; ring
      exact claim_3 k c t0 u0 hk hc ht0 ht1 hfe (fun t' u' h1 h2 h3 => hPPi ▸ lbHi t' u' h1 h2 h3)
    · -- low branch
      have ht1' : 1 ≤ t0 := ht1.le
      have hA : 0 < t0 * u0 - u0 * 1 / 2 := by nlinarith
      have hd := direct_eq hσ w0 u0 t0 q0 1 hu0 ht0 hq0nn (fun qM => lo_pM u0 t0 ht1' qM q0)
      rw [hd] at henc
      have hm0 : 0 < (1 - 1 * q0 - c / u0) / 2 := by
        by_contra h; push Not at h; rw [max_eq_left h] at henc; exact lt_irrefl _ henc
      have hw := path_foc hσ w0 u0 t0 q0 1 u0 hu0 ht0 hqpos zero_le_one
        (lo_pR u0 t0 ht1') (lo_pM u0 t0 ht1') hA hm0 rfl
      have hPq : P = (t0 * u0 - u0 * (1 - c / u0) / 2 - 2 * (t0 * u0 - u0 * 1 / 2) * q0) * q0 +
          u0 * ((1 - 1 * q0 - c / u0) / 2) ^ 2 - max (k * u0 ^ 2) (k * (t0 * u0) ^ 2) := by
        rw [← payoff_dev hσ u0 t0 q0 1 u0 hu0 ht0 hq0nn (lo_pM u0 t0 ht1')
          (lo_pR u0 t0 ht1') hA hu0 hm0, ← hw]
        rfl
      let S : Set ℝ := {x | 0 < x ∧ 0 < (1 - 1 * x - c / u0) / 2}
      have hSopen : IsOpen S := by
        apply IsOpen.inter (isOpen_lt continuous_const continuous_id)
        exact isOpen_lt continuous_const
          (show Continuous (fun x : ℝ => (1 - 1 * x - c / u0) / 2) by fun_prop)
      have hmax : ∀ x ∈ S,
          (t0 * u0 - u0 * (1 - c / u0) / 2 - 2 * (t0 * u0 - u0 * 1 / 2) * x) * x +
            u0 * ((1 - 1 * x - c / u0) / 2) ^ 2 ≤
          (t0 * u0 - u0 * (1 - c / u0) / 2 - 2 * (t0 * u0 - u0 * 1 / 2) * q0) * q0 +
            u0 * ((1 - 1 * q0 - c / u0) / 2) ^ 2 := by
        intro x hx
        have := payoff_dev hσ u0 t0 x 1 u0 hu0 ht0 hx.1.le (lo_pM u0 t0 ht1')
          (lo_pR u0 t0 ht1') hA hu0 hx.2
        have h2 := hfo (t0 * u0 - u0 * (1 - c / u0) / 2 - 2 * (t0 * u0 - u0 * 1 / 2) * x)
          u0 t0 hu0 ht0
        rw [this, hPq] at h2
        linarith
      have h85 : 0 < 8 * t0 - 5 := by linarith
      have hα : 0 < u0 * (8 * t0 - 5) / 4 := by positivity
      have hvert := quad_locmax _ _ _ _ q0 hα (fun x => lo_psi c u0 t0 x hu0 ht1') S
        (hSopen.mem_nhds ⟨hqpos, hm0⟩) hmax
      have hfe : (8 * t0 - 3) * c < (6 * t0 - 3) * u0 := by
        have := hm0
        rw [hvert, lo_m c u0 t0 hu0 ht1'] at this
        by_contra h; push Not at h
        have : ((6 * t0 - 3) * u0 - (8 * t0 - 3) * c) / (2 * (8 * t0 - 5) * u0) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
        linarith
      have hPPi : P = PiLo k c t0 u0 := by
        rw [hPq, lo_psi c u0 t0 q0 hu0 ht1', lo_cost k u0 t0 hk ht1', hvert, sub_self, zero_pow two_ne_zero,
          mul_zero, sub_zero]
        unfold PiLo; ring
      exact lemma_2 k c t0 u0 hk hc.le ht1' hfe (fun t' u' h1 h2 => hPPi ▸ lbLo t' u' h1 h2)
