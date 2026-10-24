-- Prove2me | solution 1 for RelationalReciprocity.Dynamics.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T21:57:07.495371+00:00
-- url     : https://prove2.me/submissions/2e449128-9d46-41b2-9d66-6ac8626eeb33

import Mathlib
import Definitions.Def_RelationalReciprocity_Dynamics_Model

set_option autoImplicit false

namespace RRP1

noncomputable def Fp (a θ μ p : ℝ) : ℝ := θ * p - μ * p ^ 3 / 3 + a * (θ - μ * p ^ 2) ^ 2 / 4

noncomputable def Lf (a θ μ e s : ℝ) : ℝ :=
  θ * e - μ * (e ^ 3 / 3 - s ^ 2 * e + 2 / 3 * s ^ 3) - s ^ 2 / a

lemma Lf_eq (a θ μ e s : ℝ) (ha : a ≠ 0) :
    Lf a θ μ e s = Fp a θ μ (e - s) - (2 * s - a * (θ - μ * (e - s) ^ 2)) ^ 2 / (4 * a) := by
  unfold Lf Fp; field_simp; ring

lemma GLm (a θ μ u : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hμ : 0 < μ) (hu : 0 ≤ u)
    (hprof : ∀ p, 0 ≤ p → μ * p ^ 2 ≤ θ →
      Fp a θ μ p ≤ Fp a θ μ u ∧ (Fp a θ μ p = Fp a θ μ u → p = u))
    (e s : ℝ) (he : 0 ≤ e) (hs : 0 ≤ s) :
    Lf a θ μ e s ≤ Fp a θ μ u ∧
      (Lf a θ μ e s = Fp a θ μ u → e = u + a * (θ - μ * u ^ 2) / 2 ∧ s = a * (θ - μ * u ^ 2) / 2) := by
  have key1 : ∀ e s : ℝ, 0 ≤ s → s ≤ e → μ * (e - s) ^ 2 ≤ θ →
      Lf a θ μ e s ≤ Fp a θ μ u ∧
      (Lf a θ μ e s = Fp a θ μ u → e = u + a * (θ - μ * u ^ 2) / 2 ∧ s = a * (θ - μ * u ^ 2) / 2) := by
    intro e s hs hse hD
    rw [Lf_eq a θ μ e s ha.ne']
    obtain ⟨h1, h2⟩ := hprof (e - s) (by linarith) hD
    have hnn : 0 ≤ (2 * s - a * (θ - μ * (e - s) ^ 2)) ^ 2 / (4 * a) :=
      div_nonneg (sq_nonneg _) (by positivity)
    refine ⟨by linarith, fun heq => ?_⟩
    have hz : (2 * s - a * (θ - μ * (e - s) ^ 2)) ^ 2 / (4 * a) = 0 := by linarith
    have hpu : e - s = u := h2 (by linarith)
    rw [div_eq_zero_iff] at hz
    rcases hz with hz | hz
    · have h3 : 2 * s - a * (θ - μ * (e - s) ^ 2) = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz
      rw [hpu] at h3
      constructor <;> linarith
    · exfalso; linarith
  have key2 : ∀ e s : ℝ, 0 ≤ s → s ≤ e → θ < μ * (e - s) ^ 2 → Lf a θ μ e s < Fp a θ μ u := by
    intro e s hs hse hD
    set p := e - s with hpdef
    have hp : 0 ≤ p := by linarith
    set r := Real.sqrt (θ / μ) with hr
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hr2 : r ^ 2 = θ / μ := Real.sq_sqrt (by positivity)
    have hμr : μ * r ^ 2 = θ := by rw [hr2]; field_simp
    obtain ⟨h1, -⟩ := hprof r hr0 (le_of_eq hμr)
    have hFr : Fp a θ μ r = θ * r - μ * r ^ 3 / 3 := by
      unfold Fp; rw [hμr]; ring
    have hpr : r < p := by
      by_contra hcon
      push_neg at hcon
      have : p ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hp hcon 2
      nlinarith
    have hG : θ * p - μ * p ^ 3 / 3 < θ * r - μ * r ^ 3 / 3 := by
      have : (θ * r - μ * r ^ 3 / 3) - (θ * p - μ * p ^ 3 / 3) = μ * (p - r) ^ 2 * (2 * r + p) / 3 := by
        rw [← hμr]; ring
      have : 0 < μ * (p - r) ^ 2 * (2 * r + p) / 3 := by
        have hne : p - r ≠ 0 := by linarith
        have : 0 < (p - r) ^ 2 := by positivity
        have : 0 < 2 * r + p := by linarith
        positivity
      linarith
    have hL : Lf a θ μ e s ≤ θ * p - μ * p ^ 3 / 3 := by
      rw [Lf_eq a θ μ e s ha.ne']
      have hDn : θ - μ * p ^ 2 < 0 := by linarith
      have hsq : (a * (θ - μ * p ^ 2)) ^ 2 ≤ (2 * s - a * (θ - μ * p ^ 2)) ^ 2 := by
        have h0 : 0 ≤ -(a * (θ - μ * p ^ 2)) := by nlinarith
        nlinarith
      have : (a * (θ - μ * p ^ 2)) ^ 2 / (4 * a) ≤ (2 * s - a * (θ - μ * p ^ 2)) ^ 2 / (4 * a) :=
        div_le_div_of_nonneg_right hsq (by positivity)
      have hF : Fp a θ μ p = θ * p - μ * p ^ 3 / 3 + (a * (θ - μ * p ^ 2)) ^ 2 / (4 * a) := by
        unfold Fp; field_simp
      linarith
    linarith
  by_cases hse : s ≤ e
  · by_cases hD : μ * (e - s) ^ 2 ≤ θ
    · exact key1 e s hs hse hD
    · push_neg at hD
      have := key2 e s hs hse hD
      exact ⟨this.le, fun h => absurd h this.ne⟩
  · push_neg at hse
    have hee := (key1 e e he le_rfl (by simp; exact hθ.le)).1
    have hlt : Lf a θ μ e s < Lf a θ μ e e := by
      have hid : Lf a θ μ e e - Lf a θ μ e s = μ * ((e - s) ^ 2 * (e + 2 * s)) / 3 + (s ^ 2 - e ^ 2) / a := by
        unfold Lf; ring
      have h1 : 0 ≤ μ * ((e - s) ^ 2 * (e + 2 * s)) / 3 := by
        have : 0 ≤ e + 2 * s := by linarith
        positivity
      have h2 : 0 < (s ^ 2 - e ^ 2) / a := div_pos (by nlinarith) ha
      linarith
    exact ⟨by linarith, fun h => by linarith⟩

lemma Ppos (a θ u : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hu : 0 < u) (hua : u ≤ a * θ) :
    ∀ p, 0 ≤ p → (1 / (a * u)) * p ^ 2 ≤ θ →
      Fp a θ (1 / (a * u)) p ≤ Fp a θ (1 / (a * u)) u ∧
        (Fp a θ (1 / (a * u)) p = Fp a θ (1 / (a * u)) u → p = u) := by
  intro p hp hD
  have hid : Fp a θ (1 / (a * u)) u - Fp a θ (1 / (a * u)) p =
      a * (1 / (a * u)) ^ 2 * (p - u) ^ 2 *
        ((u - p) ^ 2 / 12 + (θ * a * u - u ^ 2) / 6 + (θ * a * u - p ^ 2) / 3) := by
    unfold Fp; field_simp; ring
  have hc1 : 0 ≤ θ * a * u - u ^ 2 := by nlinarith
  have hc2 : 0 ≤ θ * a * u - p ^ 2 := by
    have hau : 0 < a * u := by positivity
    have : p ^ 2 / (a * u) ≤ θ := by rw [div_eq_mul_one_div, mul_comm]; linarith
    rw [div_le_iff₀ hau] at this; nlinarith
  have hk : 0 < a * (1 / (a * u)) ^ 2 := by positivity
  constructor
  · have : 0 ≤ a * (1 / (a * u)) ^ 2 * (p - u) ^ 2 *
        ((u - p) ^ 2 / 12 + (θ * a * u - u ^ 2) / 6 + (θ * a * u - p ^ 2) / 3) := by positivity
    linarith
  · intro heq
    by_contra hne
    have hne' : p - u ≠ 0 := sub_ne_zero.mpr hne
    have h1 : 0 < (p - u) ^ 2 := by positivity
    have h2 : 0 < (u - p) ^ 2 / 12 + (θ * a * u - u ^ 2) / 6 + (θ * a * u - p ^ 2) / 3 := by
      have : 0 < (u - p) ^ 2 := by nlinarith
      positivity
    have : 0 < a * (1 / (a * u)) ^ 2 * (p - u) ^ 2 *
        ((u - p) ^ 2 / 12 + (θ * a * u - u ^ 2) / 6 + (θ * a * u - p ^ 2) / 3) := by positivity
    linarith

lemma Pzero (a θ u : ℝ) (ha : 0 < a) (hθ : 0 < θ) (hu : 0 < u) (hau : a * θ ≤ u) :
    ∀ p, 0 ≤ p → (θ / u ^ 2) * p ^ 2 ≤ θ →
      Fp a θ (θ / u ^ 2) p ≤ Fp a θ (θ / u ^ 2) u ∧
        (Fp a θ (θ / u ^ 2) p = Fp a θ (θ / u ^ 2) u → p = u) := by
  intro p hp hD
  have hid : Fp a θ (θ / u ^ 2) u - Fp a θ (θ / u ^ 2) p =
      (u - p) ^ 2 * θ * (4 * u ^ 2 * (2 * u + p) - 3 * (a * θ) * (u + p) ^ 2) / (12 * u ^ 4) := by
    unfold Fp; field_simp; ring
  have hpu : p ≤ u := by
    have : p ^ 2 ≤ u ^ 2 := by
      have h := hD; rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at h; nlinarith
    nlinarith
  have hX : u * (u - p) * (5 * u + 3 * p) ≤ 4 * u ^ 2 * (2 * u + p) - 3 * (a * θ) * (u + p) ^ 2 := by
    have : 3 * (a * θ) * (u + p) ^ 2 ≤ 3 * u * (u + p) ^ 2 := by
      have : 0 ≤ (u + p) ^ 2 := sq_nonneg _
      nlinarith
    nlinarith
  have hX0 : 0 ≤ u * (u - p) * (5 * u + 3 * p) := by
    have : 0 ≤ u - p := by linarith
    positivity
  constructor
  · have : 0 ≤ (u - p) ^ 2 * θ * (4 * u ^ 2 * (2 * u + p) - 3 * (a * θ) * (u + p) ^ 2) / (12 * u ^ 4) := by
      have : 0 ≤ 4 * u ^ 2 * (2 * u + p) - 3 * (a * θ) * (u + p) ^ 2 := by linarith
      positivity
    linarith
  · intro heq
    by_contra hne
    have hlt : p < u := lt_of_le_of_ne hpu hne
    have h3 : 0 < u * (u - p) * (5 * u + 3 * p) := by
      have : 0 < u - p := by linarith
      have : 0 < 5 * u + 3 * p := by linarith
      positivity
    have : 0 < (u - p) ^ 2 * θ * (4 * u ^ 2 * (2 * u + p) - 3 * (a * θ) * (u + p) ^ 2) / (12 * u ^ 4) := by
      have : 0 < 4 * u ^ 2 * (2 * u + p) - 3 * (a * θ) * (u + p) ^ 2 := by linarith
      have hne' : u - p ≠ 0 := by linarith
      have : 0 < (u - p) ^ 2 := by positivity
      positivity
    linarith


open RelationalReciprocity.Dynamics

noncomputable def cc (P : Params) : ℝ := P.η * P.θ * P.θ
noncomputable def V (P : Params) (u : ℝ) : ℝ := max u (cc P)
noncomputable def E (P : Params) (u : ℝ) : ℝ := (u + V P u) / 2
noncomputable def S (P : Params) (u : ℝ) : ℝ := (V P u - u) / 2
noncomputable def W (P : Params) (u : ℝ) : ℝ := S P u ^ 2 / (P.η * P.θ)
noncomputable def B (P : Params) (u : ℝ) : ℝ := u ^ 2 * (3 * V P u - u) / 6
noncomputable def uF (P : Params) : ℝ :=
  if (P.η * P.θ) ^ 2 * P.θ ≤ 1 then Real.sqrt P.θ else 1 / (P.η * P.θ)

lemma cc_nonneg {P : Params} (hP : P.Standing) : 0 ≤ cc P := by
  obtain ⟨hθ, hη, -⟩ := hP; unfold cc; positivity

lemma S_nonneg (P : Params) (u : ℝ) : 0 ≤ S P u := by
  unfold S V; have := le_max_left u (cc P); linarith

lemma sqrt_W {P : Params} (hP : P.Standing) {u : ℝ} (hu : 0 ≤ u) :
    Real.sqrt (P.η * W P u * P.θ) = S P u := by
  obtain ⟨hθ, hη, -⟩ := hP
  by_cases hη0 : P.η = 0
  · have hS : S P u = 0 := by
      unfold S V cc; rw [hη0]; simp [max_eq_left hu]
    rw [hη0, hS]; simp
  · have ha : 0 < P.η * P.θ := mul_pos (lt_of_le_of_ne hη (Ne.symm hη0)) hθ
    have : P.η * W P u * P.θ = S P u ^ 2 := by unfold W; field_simp
    rw [this, Real.sqrt_sq (S_nonneg P u)]

lemma W_nonneg {P : Params} (hP : P.Standing) (u : ℝ) : 0 ≤ W P u := by
  obtain ⟨hθ, hη, -⟩ := hP
  unfold W; exact div_nonneg (sq_nonneg _) (by positivity)

lemma bonus_at {P : Params} (hP : P.Standing) {u : ℝ} (hu : 0 ≤ u) :
    bonus P (E P u) (W P u) = B P u := by
  have h1 := sqrt_W hP hu
  have hnn : 0 ≤ P.η * W P u * P.θ := by
    have := W_nonneg hP u; obtain ⟨hθ, hη, -⟩ := hP; positivity
  have h2 : P.η * W P u * P.θ = S P u ^ 2 := by rw [← h1, Real.sq_sqrt hnn]
  unfold bonus; rw [h1, h2]; unfold E S B; ring

lemma uF_pos {P : Params} (hP : P.Standing) : 0 < uF P := by
  obtain ⟨hθ, hη, -⟩ := hP
  unfold uF; split_ifs with h
  · exact Real.sqrt_pos.mpr hθ
  · have ha : P.η * P.θ ≠ 0 := by intro h0; rw [h0] at h; norm_num at h
    have : 0 < P.η * P.θ := lt_of_le_of_ne (by positivity) (Ne.symm ha)
    positivity

lemma uF_pos_branch {P : Params} (hP : P.Standing) {u : ℝ} (hu0 : 0 ≤ u) (huF : u ≤ uF P)
    (hc : u ≤ cc P) : P.η * P.θ * u ≤ 1 := by
  obtain ⟨hθ, hη, -⟩ := hP
  have ha : 0 ≤ P.η * P.θ := by positivity
  unfold uF at huF; unfold cc at hc
  split_ifs at huF with h
  · nlinarith
  · have ha' : P.η * P.θ ≠ 0 := by intro h0; rw [h0] at h; norm_num at h
    have ha2 : 0 < P.η * P.θ := lt_of_le_of_ne ha (Ne.symm ha')
    rw [le_div_iff₀ ha2] at huF; linarith

lemma uF_zero_branch {P : Params} (hP : P.Standing) {u : ℝ} (huF : u ≤ uF P)
    (hc : cc P ≤ u) : u ^ 2 ≤ P.θ := by
  have hc0 := cc_nonneg hP
  obtain ⟨hθ, hη, -⟩ := hP
  have ha : 0 ≤ P.η * P.θ := by positivity
  unfold uF at huF; unfold cc at hc hc0
  split_ifs at huF with h
  · have : u ^ 2 ≤ Real.sqrt P.θ ^ 2 := pow_le_pow_left₀ (by linarith) huF 2
    rwa [Real.sq_sqrt hθ.le] at this
  · exfalso
    have ha' : P.η * P.θ ≠ 0 := by intro h0; rw [h0] at h; norm_num at h
    have ha2 : 0 < P.η * P.θ := lt_of_le_of_ne ha (Ne.symm ha')
    rw [le_div_iff₀ ha2] at huF
    apply h; nlinarith

lemma uF_at_pos {P : Params} (hP : P.Standing) (hc : uF P ≤ cc P) : P.η * P.θ * uF P = 1 := by
  obtain ⟨hθ, hη, -⟩ := hP
  have ha : 0 ≤ P.η * P.θ := by positivity
  unfold uF at hc ⊢; unfold cc at hc
  split_ifs at hc ⊢ with h
  · set r := Real.sqrt P.θ with hr
    have hr0 : 0 < r := Real.sqrt_pos.mpr hθ
    have hr2 : r ^ 2 = P.θ := Real.sq_sqrt hθ.le
    rw [← hr2] at hc h ⊢
    have h1 : 1 ≤ P.η * r ^ 2 * r := by nlinarith
    have h3 : (P.η * r ^ 2 * r) ^ 2 ≤ 1 := by nlinarith
    nlinarith
  · have ha' : P.η * P.θ ≠ 0 := by intro h0; rw [h0] at h; norm_num at h
    have hη' : P.η ≠ 0 := left_ne_zero_of_mul ha'
    field_simp

lemma uF_at_zero {P : Params} (hP : P.Standing) (hc : cc P ≤ uF P) : uF P ^ 2 = P.θ := by
  obtain ⟨hθ, hη, -⟩ := hP
  have ha : 0 ≤ P.η * P.θ := by positivity
  unfold uF at hc ⊢; unfold cc at hc
  split_ifs at hc ⊢ with h
  · exact Real.sq_sqrt hθ.le
  · exfalso
    have ha' : P.η * P.θ ≠ 0 := by intro h0; rw [h0] at h; norm_num at h
    have ha2 : 0 < P.η * P.θ := lt_of_le_of_ne ha (Ne.symm ha')
    rw [le_div_iff₀ ha2] at hc
    apply h; nlinarith

lemma B_lt {P : Params} (hP : P.Standing) {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) : B P x < B P y := by
  have hc := cc_nonneg hP
  unfold B V
  set c := cc P
  rcases le_total x c with h1 | h1 <;> rcases le_total y c with h2 | h2
  · rw [max_eq_right h1, max_eq_right h2]
    have hb : 0 < 3 * c * (x + y) - (x ^ 2 + x * y + y ^ 2) := by nlinarith
    have : 0 < (y - x) * (3 * c * (x + y) - (x ^ 2 + x * y + y ^ 2)) := mul_pos (by linarith) hb
    nlinarith
  · rw [max_eq_right h1, max_eq_left h2]
    have hA : x ^ 2 * (3 * c - x) / 6 ≤ c ^ 3 / 3 := by
      have : 0 ≤ (c - x) ^ 2 * (2 * c + x) := by
        have : 0 ≤ 2 * c + x := by linarith
        positivity
      nlinarith
    rcases lt_or_eq_of_le h1 with h1' | h1'
    · have : x ^ 2 * (3 * c - x) / 6 < c ^ 3 / 3 := by
        have : 0 < (c - x) ^ 2 * (2 * c + x) := by
          have : 0 < 2 * c + x := by linarith
          have hne : c - x ≠ 0 := by linarith
          positivity
        nlinarith
      have : c ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ (by linarith) h2 3
      nlinarith
    · rw [h1']
      have : c ^ 3 < y ^ 3 := pow_lt_pow_left₀ (by linarith) (by linarith) (by norm_num)
      nlinarith
  · exfalso; linarith
  · rw [max_eq_left h1, max_eq_left h2]
    have : x ^ 3 < y ^ 3 := pow_lt_pow_left₀ hxy hx (by norm_num)
    nlinarith

lemma B_cont (P : Params) : Continuous (B P) := by
  unfold B V; fun_prop

lemma B_zero (P : Params) : B P 0 = 0 := by unfold B; simp

lemma B_nonneg {P : Params} (hP : P.Standing) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ B P u := by
  rcases lt_or_eq_of_le hu with h | h
  · have := B_lt hP le_rfl h; rw [B_zero] at this; exact this.le
  · rw [← h, B_zero]

lemma B_le_iff {P : Params} (hP : P.Standing) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    B P x ≤ B P y ↔ x ≤ y := by
  constructor
  · intro h; by_contra h'; push_neg at h'; have := B_lt hP hy h'; linarith
  · intro h; rcases lt_or_eq_of_le h with h | h
    · exact (B_lt hP hx h).le
    · rw [h]

lemma B_lt_iff {P : Params} (hP : P.Standing) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    B P x < B P y ↔ x < y := by
  rw [lt_iff_not_ge, lt_iff_not_ge, B_le_iff hP hy hx]

lemma E_lt (P : Params) {x y : ℝ} (hxy : x < y) : E P x < E P y := by
  unfold E V; have := max_le_max_right (cc P) hxy.le; linarith

lemma E_le (P : Params) {x y : ℝ} (hxy : x ≤ y) : E P x ≤ E P y := by
  unfold E V; have := max_le_max_right (cc P) hxy; linarith

lemma S_le (P : Params) {x y : ℝ} (hxy : x ≤ y) : S P y ≤ S P x := by
  unfold S V
  rcases le_total y (cc P) with h | h
  · rw [max_eq_right h, max_eq_right (le_trans hxy h)]; linarith
  · rw [max_eq_left h]
    have := le_max_left x (cc P); linarith

lemma W_le {P : Params} (hP : P.Standing) {x y : ℝ} (hxy : x ≤ y) : W P y ≤ W P x := by
  obtain ⟨hθ, hη, -⟩ := hP
  unfold W
  have h1 := S_le P hxy
  have h0 := S_nonneg P y
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact pow_le_pow_left₀ h0 h1 2

lemma W_lt {P : Params} (hP : P.Standing) {x y : ℝ} (hxy : x < y) (hW : 0 < W P y) :
    W P y < W P x := by
  obtain ⟨hθ, hη, -⟩ := hP
  have ha : 0 < P.η * P.θ := by
    rcases lt_or_eq_of_le (show 0 ≤ P.η * P.θ by positivity) with h | h
    · exact h
    · exfalso; unfold W at hW; rw [← h] at hW; simp at hW
  have hS : 0 < S P y := by
    rcases lt_or_eq_of_le (S_nonneg P y) with h | h
    · exact h
    · exfalso; unfold W at hW; rw [← h] at hW; simp at hW
  have hyc : y < cc P := by
    unfold S V at hS
    by_contra hcon; push_neg at hcon; rw [max_eq_left hcon] at hS; linarith
  have hSx : S P y < S P x := by
    unfold S V; rw [max_eq_right hyc.le, max_eq_right (by linarith)]; linarith
  unfold W
  apply div_lt_div_of_pos_right _ ha
  exact pow_lt_pow_left₀ hSx hS.le (by norm_num)

lemma Lf_profit {P : Params} (hP : P.Standing) (hη : 0 < P.η) (μ e w : ℝ) (hw : 0 ≤ w) :
    Lf (P.η * P.θ) P.θ μ e (Real.sqrt (P.η * w * P.θ)) = profit P e w - (μ - 1) * bonus P e w := by
  have hθ := hP.1
  have hs2 : Real.sqrt (P.η * w * P.θ) ^ 2 = P.η * w * P.θ := Real.sq_sqrt (by positivity)
  unfold Lf profit bonus; rw [hs2]; field_simp; ring

lemma TR {P : Params} (hP : P.Standing) (hη : 0 < P.η) {μ u K e w ec wc : ℝ} (hμ : 1 ≤ μ)
    (hu : 0 ≤ u)
    (hprof : ∀ p, 0 ≤ p → μ * p ^ 2 ≤ P.θ →
      Fp (P.η * P.θ) P.θ μ p ≤ Fp (P.η * P.θ) P.θ μ u ∧
        (Fp (P.η * P.θ) P.θ μ p = Fp (P.η * P.θ) P.θ μ u → p = u))
    (hopt : IsOptimal P K e w) (hfeas : (ec, wc) ∈ Feasible P K)
    (hslack : (μ - 1) * (K - bonus P ec wc) = 0)
    (hc1 : ec - Real.sqrt (P.η * wc * P.θ) = u)
    (hc2 : 2 * Real.sqrt (P.η * wc * P.θ) = P.η * P.θ * (P.θ - μ * u ^ 2)) :
    e = u + P.η * P.θ * (P.θ - μ * u ^ 2) / 2 ∧
      Real.sqrt (P.η * w * P.θ) = P.η * P.θ * (P.θ - μ * u ^ 2) / 2 := by
  have hθ := hP.1
  have ha : 0 < P.η * P.θ := mul_pos hη hθ
  obtain ⟨⟨he, hw, hb⟩, hmax⟩ := hopt
  have hge : profit P ec wc ≤ profit P e w := hmax (ec, wc) hfeas
  obtain ⟨hec, hwc, hbc⟩ := hfeas
  have hLe := Lf_profit hP hη μ e w hw
  have hLc := Lf_profit hP hη μ ec wc hwc
  have hcand : Lf (P.η * P.θ) P.θ μ ec (Real.sqrt (P.η * wc * P.θ)) = Fp (P.η * P.θ) P.θ μ u := by
    rw [Lf_eq _ _ _ _ _ ha.ne', hc1]
    rw [show 2 * Real.sqrt (P.η * wc * P.θ) - P.η * P.θ * (P.θ - μ * u ^ 2) = 0 by linarith]
    simp
  have hmb : (μ - 1) * bonus P e w ≤ (μ - 1) * K := mul_le_mul_of_nonneg_left hb (by linarith)
  have hineq : Fp (P.η * P.θ) P.θ μ u ≤ Lf (P.η * P.θ) P.θ μ e (Real.sqrt (P.η * w * P.θ)) := by
    rw [hLe, ← hcand, hLc]; nlinarith
  obtain ⟨h1, h2⟩ := GLm (P.η * P.θ) P.θ μ u ha hθ (by linarith) hu hprof e
    (Real.sqrt (P.η * w * P.θ)) he (Real.sqrt_nonneg _)
  exact h2 (le_antisymm h1 hineq)

lemma E_nonneg {P : Params} (hP : P.Standing) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ E P u := by
  unfold E V; have := le_max_left u (cc P); linarith

lemma KL {P : Params} (hP : P.Standing) {K e w : ℝ} (hK : 0 ≤ K) (hopt : IsOptimal P K e w) :
    ∃ u, 0 ≤ u ∧ u ≤ uF P ∧ B P u = min K (B P (uF P)) ∧ e = E P u ∧ w = W P u := by
  have huF := uF_pos hP
  obtain ⟨u, hu0, hu1, hmin, hBK, hsl⟩ : ∃ u, 0 ≤ u ∧ u ≤ uF P ∧ B P u = min K (B P (uF P)) ∧
      B P u ≤ K ∧ (u = uF P ∨ B P u = K) := by
    by_cases hKF : K ≤ B P (uF P)
    · have hsub := intermediate_value_Icc huF.le (B_cont P).continuousOn
      have hKmem : K ∈ Set.Icc (B P 0) (B P (uF P)) := ⟨by rw [B_zero]; exact hK, hKF⟩
      obtain ⟨u, ⟨h0, h1⟩, hBu⟩ := hsub hKmem
      exact ⟨u, h0, h1, by rw [hBu, min_eq_left hKF], hBu.le, Or.inr hBu⟩
    · push_neg at hKF
      exact ⟨uF P, huF.le, le_rfl, (min_eq_right hKF.le).symm, hKF.le, Or.inl rfl⟩
  refine ⟨u, hu0, hu1, hmin, ?_⟩
  have hθ := hP.1
  have hη := hP.2.1
  have hfeasC : (E P u, W P u) ∈ Feasible P K :=
    ⟨E_nonneg hP hu0, W_nonneg hP u, by rw [bonus_at hP hu0]; exact hBK⟩
  have hopt' := hopt
  obtain ⟨⟨he, hw, hb⟩, hmax⟩ := hopt
  have hge : profit P (E P u) (W P u) ≤ profit P e w := hmax _ hfeasC
  rcases lt_or_eq_of_le hu0 with hupos | hu00
  · rcases lt_or_eq_of_le hη with hηpos | hη00
    · have ha : 0 < P.η * P.θ := mul_pos hηpos hθ
      have hsw : w = Real.sqrt (P.η * w * P.θ) ^ 2 / (P.η * P.θ) := by
        rw [Real.sq_sqrt (by positivity)]; field_simp
      have hsqc := sqrt_W hP hu0
      rcases le_total u (cc P) with hc | hc
      · have hau := uF_pos_branch hP hu0 hu1 hc
        have hμ1 : 1 ≤ 1 / (P.η * P.θ * u) := by
          rw [le_div_iff₀ (by positivity)]; linarith
        have hslack : (1 / (P.η * P.θ * u) - 1) * (K - bonus P (E P u) (W P u)) = 0 := by
          rw [bonus_at hP hu0]
          rcases hsl with h | h
          · have : P.η * P.θ * u = 1 := by rw [h]; exact uF_at_pos hP (h ▸ hc)
            rw [this]; ring
          · rw [h]; ring
        have hcV : V P u = cc P := max_eq_right hc
        have hc' : u ≤ P.η * P.θ * P.θ := hc
        obtain ⟨h1, h2⟩ := TR hP hηpos hμ1 hu0 (Ppos (P.η * P.θ) P.θ u ha hθ hupos hc') hopt'
          hfeasC hslack (by rw [hsqc]; unfold E S; ring)
          (by rw [hsqc]; unfold S; rw [hcV]; unfold cc; field_simp)
        constructor
        · rw [h1]; unfold E; rw [hcV]; unfold cc; field_simp; ring
        · rw [hsw, h2]; unfold W S; rw [hcV]; unfold cc; field_simp
      · have hu2 := uF_zero_branch hP hu1 hc
        have hμ1 : 1 ≤ P.θ / u ^ 2 := by
          rw [le_div_iff₀ (by positivity)]; linarith
        have hslack : (P.θ / u ^ 2 - 1) * (K - bonus P (E P u) (W P u)) = 0 := by
          rw [bonus_at hP hu0]
          rcases hsl with h | h
          · have : u ^ 2 = P.θ := by rw [h]; exact uF_at_zero hP (h ▸ hc)
            rw [this, div_self hθ.ne']; ring
          · rw [h]; ring
        have hcV : V P u = u := max_eq_left hc
        have hc' : P.η * P.θ * P.θ ≤ u := hc
        obtain ⟨h1, h2⟩ := TR hP hηpos hμ1 hu0 (Pzero (P.η * P.θ) P.θ u ha hθ hupos hc') hopt'
          hfeasC hslack (by rw [hsqc]; unfold E S; ring)
          (by rw [hsqc]; unfold S; rw [hcV]; field_simp; ring)
        constructor
        · rw [h1]; unfold E; rw [hcV]; field_simp; ring
        · rw [hsw, h2]; unfold W S; rw [hcV]; field_simp; ring
    · -- η = 0
      have hc0 : cc P = 0 := by unfold cc; rw [← hη00]; ring
      have hbon : ∀ x y : ℝ, bonus P x y = x ^ 3 / 3 := by
        intro x y; unfold bonus; rw [← hη00]; simp
      have hWu : W P u = 0 := by unfold W; rw [← hη00]; simp
      have hEu : E P u = u := by unfold E V; rw [hc0, max_eq_left hu0]; ring
      have hw0 : w = 0 := by
        have h0 : ((e, (0:ℝ)) : ℝ × ℝ) ∈ Feasible P K := by
          refine ⟨he, le_rfl, ?_⟩; show bonus P e 0 ≤ K; rw [hbon]; rw [hbon] at hb; exact hb
        have := hmax _ h0
        simp only [profit, hbon] at this
        linarith
      have hu2 : u ^ 2 ≤ P.θ := uF_zero_branch hP hu1 (by rw [hc0]; exact hu0)
      have hBu : B P u = u ^ 3 / 3 := by unfold B V; rw [hc0, max_eq_left hu0]; ring
      set μ := P.θ / u ^ 2 with hμdef
      have hμ1 : 1 ≤ μ := by rw [hμdef, le_div_iff₀ (by positivity)]; linarith
      have hθμ : P.θ = μ * u ^ 2 := by rw [hμdef]; field_simp
      have hslack : (μ - 1) * (K - u ^ 3 / 3) = 0 := by
        rcases hsl with h | h
        · have : u ^ 2 = P.θ := by rw [h]; exact uF_at_zero hP (by rw [hc0, ← h]; exact hu0)
          have : μ = 1 := by rw [hμdef, this, div_self hθ.ne']
          rw [this]; ring
        · rw [← hBu, h]; ring
      have hb' : e ^ 3 / 3 ≤ K := by rw [hbon] at hb; exact hb
      have hmb : (μ - 1) * (e ^ 3 / 3) ≤ (μ - 1) * K := mul_le_mul_of_nonneg_left hb' (by linarith)
      simp only [profit, hbon, hEu, hWu] at hge
      have hkey : 0 ≤ (P.θ * e - μ * e ^ 3 / 3) - (P.θ * u - μ * u ^ 3 / 3) := by nlinarith
      have hid : (P.θ * e - μ * e ^ 3 / 3) - (P.θ * u - μ * u ^ 3 / 3) =
          -(μ * (u - e) ^ 2 * (2 * u + e) / 3) := by rw [hθμ]; ring
      have heu : e = u := by
        by_contra hne
        have : 0 < μ * (u - e) ^ 2 * (2 * u + e) / 3 := by
          have hne' : u - e ≠ 0 := fun h => hne (by linarith)
          have : 0 < 2 * u + e := by linarith
          have : 0 < μ := by linarith
          positivity
        linarith
      exact ⟨by rw [hEu, heu], by rw [hWu, hw0]⟩
  · -- u = 0, hence K = 0
    have hK0 : K = 0 := by
      rcases hsl with h | h
      · exfalso; rw [← h] at huF; linarith
      · rw [← h, ← hu00, B_zero]
    subst hu00
    rcases lt_or_eq_of_le hη with hηpos | hη00
    · have ha : 0 < P.η * P.θ := mul_pos hηpos hθ
      set s := Real.sqrt (P.η * w * P.θ) with hs
      have hs0 : 0 ≤ s := Real.sqrt_nonneg _
      have hs2 : s ^ 2 = P.η * w * P.θ := Real.sq_sqrt (by positivity)
      have hbon : bonus P e w = (e - s) ^ 2 * (e + 2 * s) / 3 := by
        unfold bonus; rw [← hs, ← hs2]; ring
      have hes : e = s := by
        have h1 : (e - s) ^ 2 * (e + 2 * s) = 0 := by
          apply le_antisymm _ (by have : 0 ≤ e + 2 * s := by linarith
                                  positivity)
          rw [hbon, hK0] at hb; linarith
        rcases mul_eq_zero.mp h1 with h | h
        · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h; linarith
        · linarith
      have hww : w = s ^ 2 / (P.η * P.θ) := by rw [hs2]; field_simp
      have hcV : V P 0 = P.η * P.θ * P.θ := by unfold V cc; exact max_eq_right (by positivity)
      have hE0 : E P 0 = P.η * P.θ * P.θ / 2 := by unfold E; rw [hcV]; ring
      have hS0 : S P 0 = P.η * P.θ * P.θ / 2 := by unfold S; rw [hcV]; ring
      have hpc : profit P (E P 0) (W P 0) = P.η * P.θ * P.θ ^ 2 / 4 := by
        unfold profit; rw [bonus_at hP le_rfl, B_zero, hE0]; unfold W; rw [hS0]; field_simp; ring
      have hpe : profit P e w = P.θ * e - e ^ 2 / (P.η * P.θ) := by
        unfold profit; rw [hbon, hww, hes]; ring
      rw [hpc, hpe] at hge
      have hsq : (e - P.η * P.θ * P.θ / 2) ^ 2 / (P.η * P.θ) ≤ 0 := by
        have : (e - P.η * P.θ * P.θ / 2) ^ 2 / (P.η * P.θ) =
            P.η * P.θ * P.θ ^ 2 / 4 - (P.θ * e - e ^ 2 / (P.η * P.θ)) := by field_simp; ring
        rw [this]; linarith
      have hsq0 : (e - P.η * P.θ * P.θ / 2) ^ 2 = 0 := by
        have := div_nonpos_iff.mp hsq
        rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · linarith
        · exact le_antisymm h1 (sq_nonneg _)
      have he' : e = P.η * P.θ * P.θ / 2 := by
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq0; linarith
      refine ⟨by rw [hE0, he'], ?_⟩
      rw [hww, ← hes, he']; unfold W; rw [hS0]
    · have hbon : ∀ x y : ℝ, bonus P x y = x ^ 3 / 3 := by
        intro x y; unfold bonus; rw [← hη00]; simp
      have hc0 : cc P = 0 := by unfold cc; rw [← hη00]; ring
      have hE0 : E P 0 = 0 := by unfold E V; rw [hc0]; simp
      have hW0 : W P 0 = 0 := by unfold W; rw [← hη00]; simp
      have he0 : e = 0 := by
        rw [hbon, hK0] at hb
        by_contra hne
        have : 0 < e := lt_of_le_of_ne he (Ne.symm hne)
        have : 0 < e ^ 3 := by positivity
        linarith
      simp only [profit, hbon, hE0, hW0, he0] at hge
      exact ⟨by rw [hE0, he0], by rw [hW0]; linarith⟩

lemma bonus00 (P : Params) : bonus P 0 0 = 0 := by unfold bonus; simp

lemma profit00 (P : Params) : profit P 0 0 = 0 := by unfold profit; rw [bonus00]; ring

lemma PiMono {P : Params} (hP : P.Standing) {e w Pi : ℕ → ℝ} (hpath : IsOptimalPath P e w Pi) :
    ∀ t, 1 ≤ t → t ≤ P.T → 0 ≤ Pi (t + 1) ∧ Pi (t + 1) ≤ Pi t := by
  have hδ := hP.2.2.1
  obtain ⟨hT1, hstep⟩ := hpath
  have key : ∀ j t, t + j = P.T → 1 ≤ t → 0 ≤ Pi (t + 1) ∧ Pi (t + 1) ≤ Pi t := by
    intro j
    induction j with
    | zero =>
      intro t ht h1
      simp only [Nat.add_zero] at ht
      subst ht
      obtain ⟨⟨_, hmax⟩, hPi⟩ := hstep P.T h1 le_rfl
      have h0 : ((0:ℝ), (0:ℝ)) ∈ Feasible P (P.δ * Pi (P.T + 1)) :=
        ⟨le_rfl, le_rfl, by show bonus P 0 0 ≤ _; rw [bonus00, hT1]; simp⟩
      have h00 : profit P 0 0 ≤ profit P (e P.T) (w P.T) := hmax _ h0
      rw [profit00] at h00
      rw [hT1] at hPi ⊢
      exact ⟨le_rfl, by linarith⟩
    | succ j ih =>
      intro t ht h1
      obtain ⟨h2a, h2b⟩ := ih (t + 1) (by omega) (by omega)
      obtain ⟨⟨_, hmax⟩, hPi⟩ := hstep t h1 (by omega)
      obtain ⟨⟨⟨he1, hw1, hb1⟩, _⟩, hPi1⟩ := hstep (t + 1) (by omega) (by omega)
      have hm := mul_le_mul_of_nonneg_left h2b hδ.le
      have hf : (e (t + 1), w (t + 1)) ∈ Feasible P (P.δ * Pi (t + 1)) :=
        ⟨he1, hw1, le_trans hb1 hm⟩
      have : profit P (e (t + 1)) (w (t + 1)) ≤ profit P (e t) (w t) := hmax _ hf
      refine ⟨by linarith, ?_⟩
      linarith
  intro t h1 hT
  exact key (P.T - t) t (by omega) h1

theorem main (P : Params) (hP : P.Standing) (e w Pi : ℕ → ℝ)
    (hpath : IsOptimalPath P e w Pi) :
    (∀ t : ℕ, 2 ≤ t → t ≤ P.T → e t ≤ e (t - 1)) ∧
    (∀ t : ℕ, 2 ≤ t → t + 1 ≤ P.T →
        (e t < e (t - 1) → e (t + 1) < e t) ∧ (e (t + 1) = e t → e t = e (t - 1))) ∧
    (∀ t : ℕ, 2 ≤ t → t ≤ P.T →
        w (t - 1) ≤ w t ∧ bonus P (e t) (w t) ≤ bonus P (e (t - 1)) (w (t - 1))) ∧
    (∀ t : ℕ, 2 ≤ t → t + 1 ≤ P.T →
        (w (t - 1) < w t ∧ bonus P (e t) (w t) < bonus P (e (t - 1)) (w (t - 1)) →
            w t < w (t + 1) ∧ bonus P (e (t + 1)) (w (t + 1)) < bonus P (e t) (w t)) ∧
        (w (t + 1) = w t ∧ bonus P (e (t + 1)) (w (t + 1)) = bonus P (e t) (w t) →
            w t = w (t - 1) ∧ bonus P (e t) (w t) = bonus P (e (t - 1)) (w (t - 1)))) := by
  have hδ := hP.2.2.1
  have hPM := PiMono hP hpath
  have hK0 : ∀ t, 1 ≤ t → t ≤ P.T → 0 ≤ P.δ * Pi (t + 1) :=
    fun t h1 h2 => mul_nonneg hδ.le (hPM t h1 h2).1
  have hu : ∀ t, ∃ u : ℝ, (1 ≤ t ∧ t ≤ P.T) → (0 ≤ u ∧ u ≤ uF P ∧
      B P u = min (P.δ * Pi (t + 1)) (B P (uF P)) ∧ e t = E P u ∧ w t = W P u) := by
    intro t
    by_cases h : 1 ≤ t ∧ t ≤ P.T
    · obtain ⟨u, hu⟩ := KL hP (hK0 t h.1 h.2) (hpath.2 t h.1 h.2).1
      exact ⟨u, fun _ => hu⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose U hU using hu
  set KS := B P (uF P) with hKS
  have hbon : ∀ t, 1 ≤ t → t ≤ P.T → bonus P (e t) (w t) = B P (U t) := by
    intro t h1 h2
    obtain ⟨h0, -, -, he, hw⟩ := hU t ⟨h1, h2⟩
    rw [he, hw, bonus_at hP h0]
  have M1 : ∀ n, 1 ≤ n → n + 1 ≤ P.T → U (n + 1) ≤ U n := by
    intro n h1 h2
    obtain ⟨a0, -, aB, -, -⟩ := hU (n + 1) ⟨by omega, h2⟩
    obtain ⟨b0, -, bB, -, -⟩ := hU n ⟨h1, by omega⟩
    rw [← B_le_iff hP a0 b0, aB, bB]
    have := (hPM (n + 1) (by omega) h2).2
    exact min_le_min_right _ (mul_le_mul_of_nonneg_left this hδ.le)
  have M2 : ∀ n, 1 ≤ n → n + 1 + 1 ≤ P.T → U (n + 1) < U n → U (n + 1 + 1) < U (n + 1) := by
    intro n h1 h2 hlt
    obtain ⟨a0, -, aB, ae, aw⟩ := hU (n + 1) ⟨by omega, by omega⟩
    obtain ⟨b0, -, bB, -, -⟩ := hU n ⟨h1, by omega⟩
    obtain ⟨c0, -, cB, ce, cw⟩ := hU (n + 1 + 1) ⟨by omega, h2⟩
    have hBlt : B P (U (n + 1)) < B P (U n) := (B_lt_iff hP a0 b0).mpr hlt
    rw [aB, bB] at hBlt
    have hK1S : P.δ * Pi (n + 1 + 1) < KS := by
      by_contra hc
      push_neg at hc
      rw [min_eq_right hc] at hBlt
      exact absurd hBlt (not_lt.mpr (min_le_right _ _))
    have hK10 : P.δ * Pi (n + 1 + 1) < P.δ * Pi (n + 1) := by
      rw [min_eq_left hK1S.le] at hBlt; exact lt_of_lt_of_le hBlt (min_le_left _ _)
    have hP10 : Pi (n + 1 + 1) < Pi (n + 1) := lt_of_mul_lt_mul_left hK10 hδ.le
    have hP21 : Pi (n + 1 + 1 + 1) < Pi (n + 1 + 1) := by
      by_contra hc
      push_neg at hc
      have heq : Pi (n + 1 + 1 + 1) = Pi (n + 1 + 1) := le_antisymm (hPM (n + 1 + 1) (by omega) h2).2 hc
      have hUeq : U (n + 1 + 1) = U (n + 1) := by
        apply le_antisymm (M1 (n + 1) (by omega) h2)
        rw [← B_le_iff hP a0 c0, aB, cB, heq]
      obtain ⟨-, hPi1⟩ := hpath.2 (n + 1) (by omega) (by omega)
      obtain ⟨-, hPi2⟩ := hpath.2 (n + 1 + 1) (by omega) h2
      have hpr : profit P (e (n + 1 + 1)) (w (n + 1 + 1)) = profit P (e (n + 1)) (w (n + 1)) := by
        rw [ce, cw, ae, aw, hUeq]
      rw [heq, hpr] at hPi2
      linarith
    have hK21 : P.δ * Pi (n + 1 + 1 + 1) < P.δ * Pi (n + 1 + 1) := mul_lt_mul_of_pos_left hP21 hδ
    have : B P (U (n + 1 + 1)) < B P (U (n + 1)) := by
      rw [cB, aB, min_eq_left (by linarith : P.δ * Pi (n + 1 + 1 + 1) ≤ KS), min_eq_left hK1S.le]
      exact hK21
    exact (B_lt_iff hP c0 a0).mp this
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t h2 hT
    obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [(hU (n + 1) ⟨by omega, hT⟩).2.2.2.1, (hU n ⟨by omega, by omega⟩).2.2.2.1]
    exact E_le P (M1 n (by omega) hT)
  · intro t h2 hT
    obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have ha := hU (n + 1) ⟨by omega, by omega⟩
    have hb := hU n ⟨by omega, by omega⟩
    have hc := hU (n + 1 + 1) ⟨by omega, hT⟩
    rw [ha.2.2.2.1, hb.2.2.2.1, hc.2.2.2.1]
    have m1 := M1 n (by omega) (by omega)
    have m2 := M2 n (by omega) hT
    constructor
    · intro hlt
      have hu : U (n + 1) < U n := by
        by_contra hc'
        push_neg at hc'
        exact absurd hlt (not_lt.mpr (E_le P hc'))
      exact E_lt P (m2 hu)
    · intro heq
      have hnot : ¬ U (n + 1) < U n := by
        intro hu
        have := E_lt P (m2 hu)
        rw [heq] at this
        exact lt_irrefl _ this
      rw [le_antisymm m1 (not_lt.mp hnot)]
  · intro t h2 hT
    obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have ha := hU (n + 1) ⟨by omega, hT⟩
    have hb := hU n ⟨by omega, by omega⟩
    rw [hbon (n + 1) (by omega) hT, hbon n (by omega) (by omega), ha.2.2.2.2, hb.2.2.2.2]
    have m1 := M1 n (by omega) hT
    exact ⟨W_le hP m1, (B_le_iff hP ha.1 hb.1).mpr m1⟩
  · intro t h2 hT
    obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have ha := hU (n + 1) ⟨by omega, by omega⟩
    have hb := hU n ⟨by omega, by omega⟩
    have hc := hU (n + 1 + 1) ⟨by omega, hT⟩
    rw [hbon (n + 1 + 1) (by omega) hT, hbon (n + 1) (by omega) (by omega),
      hbon n (by omega) (by omega), ha.2.2.2.2, hb.2.2.2.2, hc.2.2.2.2]
    have m1 := M1 n (by omega) (by omega)
    have m2 := M2 n (by omega) hT
    constructor
    · rintro ⟨hw, hbb⟩
      have hu : U (n + 1) < U n := (B_lt_iff hP ha.1 hb.1).mp hbb
      have hu2 := m2 hu
      exact ⟨W_lt hP hu2 (lt_of_le_of_lt (W_nonneg hP _) hw), (B_lt_iff hP hc.1 ha.1).mpr hu2⟩
    · rintro ⟨-, hbb⟩
      have hu : U (n + 1 + 1) = U (n + 1) :=
        le_antisymm ((B_le_iff hP hc.1 ha.1).mp hbb.le) ((B_le_iff hP ha.1 hc.1).mp hbb.ge)
      have hnot : ¬ U (n + 1) < U n := fun h => by
        have := m2 h; rw [hu] at this; exact lt_irrefl _ this
      rw [le_antisymm m1 (not_lt.mp hnot)]
      exact ⟨rfl, rfl⟩

end RRP1

open RelationalReciprocity.Dynamics in
theorem solution (P : Params) (hP : P.Standing) (e w Pi : ℕ → ℝ)
    (hpath : IsOptimalPath P e w Pi) :
    (∀ t : ℕ, 2 ≤ t → t ≤ P.T → e t ≤ e (t - 1)) ∧
    (∀ t : ℕ, 2 ≤ t → t + 1 ≤ P.T →
        (e t < e (t - 1) → e (t + 1) < e t) ∧ (e (t + 1) = e t → e t = e (t - 1))) ∧
    (∀ t : ℕ, 2 ≤ t → t ≤ P.T →
        w (t - 1) ≤ w t ∧ bonus P (e t) (w t) ≤ bonus P (e (t - 1)) (w (t - 1))) ∧
    (∀ t : ℕ, 2 ≤ t → t + 1 ≤ P.T →
        (w (t - 1) < w t ∧ bonus P (e t) (w t) < bonus P (e (t - 1)) (w (t - 1)) →
            w t < w (t + 1) ∧ bonus P (e (t + 1)) (w (t + 1)) < bonus P (e t) (w t)) ∧
        (w (t + 1) = w t ∧ bonus P (e (t + 1)) (w (t + 1)) = bonus P (e t) (w t) →
            w t = w (t - 1) ∧ bonus P (e t) (w t) = bonus P (e (t - 1)) (w (t - 1)))) := by
  exact RRP1.main P hP e w Pi hpath
