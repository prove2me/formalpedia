-- Prove2me | solution 1 for STVFriedmann.theorem7_decay_to_minkowski
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T11:07:20.999106+00:00
-- url     : https://prove2.me/submissions/9a68fba7-e557-495b-94f0-61b2e997e575

import Mathlib
import Definitions.Def_STVFriedmann_basic

open Set Real

namespace STV7

/-- barrier argument for |y| -/
lemma barrier_abs {y y' B B' : ℝ → ℝ} {T : ℝ}
    (hy : ∀ τ, HasDerivAt y (y' τ) τ) (hB : ∀ τ, HasDerivAt B (B' τ) τ)
    (hpos : ∀ τ, T ≤ τ → 0 < B τ) (h0 : |y T| ≤ B T)
    (hcross : ∀ τ, T ≤ τ → |y τ| = B τ → y τ * y' τ < B τ * B' τ) :
    ∀ τ, T ≤ τ → |y τ| ≤ B τ := by
  intro τ hτ
  have hyc : Continuous y := continuous_iff_continuousAt.2 fun t => (hy t).continuousAt
  have hBc : Continuous B := continuous_iff_continuousAt.2 fun t => (hB t).continuousAt
  have h1 : y τ ≤ B τ := by
    refine image_le_of_deriv_right_lt_deriv_boundary' (f := y) (f' := y') (B' := B')
      hyc.continuousOn (fun x _ => (hy x).hasDerivWithinAt) (le_of_abs_le h0)
      hBc.continuousOn (fun x _ => (hB x).hasDerivWithinAt) ?_ ⟨hτ, le_rfl⟩
    intro x hx hxe
    have hp := hpos x hx.1
    have := hcross x hx.1 (by rw [hxe, abs_of_pos hp])
    rw [hxe] at this
    exact lt_of_mul_lt_mul_left this hp.le
  have h2 : -y τ ≤ B τ := by
    refine image_le_of_deriv_right_lt_deriv_boundary' (f := fun t => -y t) (f' := fun t => -y' t)
      (B' := B') hyc.neg.continuousOn (fun x _ => (hy x).neg.hasDerivWithinAt)
      (by have := neg_abs_le (y T); linarith)
      hBc.continuousOn (fun x _ => (hB x).hasDerivWithinAt) ?_ ⟨hτ, le_rfl⟩
    intro x hx hxe
    have hp := hpos x hx.1
    have hyx : y x = -B x := by linarith
    have := hcross x hx.1 (by rw [hyx, abs_neg, abs_of_pos hp])
    rw [hyx] at this
    have : B x * (-y' x) < B x * B' x := by linarith
    exact lt_of_mul_lt_mul_left this hp.le
  exact abs_le.2 ⟨by linarith, h1⟩

/-- rough decay at rate 3/4 -/
lemma rough {y y' p g : ℝ → ℝ} {T K : ℝ} (hy : ∀ τ, HasDerivAt y (y' τ) τ)
    (heq : ∀ τ, T ≤ τ → y' τ = -(1 + p τ) * y τ + g τ)
    (hp : ∀ τ, T ≤ τ → |p τ| ≤ 1 / 8) (hg : ∀ τ, T ≤ τ → |g τ| ≤ K * exp (-(3 / 4) * τ)) :
    ∃ C, ∀ τ, T ≤ τ → |y τ| ≤ C * exp (-(3 / 4) * τ) := by
  have hK : 0 ≤ K := by
    have h := hg T le_rfl
    have := abs_nonneg (g T)
    by_contra hK; push Not at hK
    have : K * exp (-(3 / 4) * T) < 0 := mul_neg_of_neg_of_pos hK (exp_pos _)
    linarith
  set C := |y T| * exp ((3 / 4) * T) + 8 * K + 1 with hC
  have hC0 : 0 < C := by positivity
  refine ⟨C, barrier_abs (y := y) (y' := y') (B := fun τ => C * exp (-(3 / 4) * τ))
    (B' := fun τ => C * (exp (-(3 / 4) * τ) * (-(3 / 4)))) hy ?_ ?_ ?_ ?_⟩
  · intro τ
    exact ((hasDerivAt_id τ).const_mul (-(3 / 4))).exp.const_mul C |>.congr_deriv (by simp)
  · intro τ _; positivity
  · show |y T| ≤ C * exp (-(3 / 4) * T)
    rw [mul_comm (-(3/4) : ℝ) T]
    have : |y T| * exp (3 / 4 * T) * exp (T * -(3 / 4)) = |y T| := by
      rw [mul_assoc, ← exp_add]; ring_nf; simp
    have hE := exp_pos (T * -(3/4))
    nlinarith
  · intro τ hτ hcr
    show y τ * y' τ < C * exp (-(3 / 4) * τ) * (C * (exp (-(3 / 4) * τ) * (-(3 / 4))))
    set E := exp (-(3 / 4) * τ) with hE
    have hEp : 0 < E := exp_pos _
    rw [heq τ hτ]
    have hpb := abs_le.1 (hp τ hτ)
    have hy2 : y τ * y τ = (C * E) ^ 2 := by rw [← hcr, ← sq, sq_abs]
    have hyg : y τ * g τ ≤ (C * E) * (K * E) := by
      calc y τ * g τ ≤ |y τ * g τ| := le_abs_self _
        _ = |y τ| * |g τ| := abs_mul _ _
        _ ≤ (C * E) * (K * E) := by
          rw [hcr]; exact mul_le_mul_of_nonneg_left (hg τ hτ) (by positivity)
    have : y τ * (-(1 + p τ) * y τ + g τ) = -(1 + p τ) * (y τ * y τ) + y τ * g τ := by ring
    rw [this, hy2]
    have h78 : -(1 + p τ) * (C * E) ^ 2 ≤ -(7 / 8) * (C * E) ^ 2 := by
      have : 0 ≤ (C * E) ^ 2 := sq_nonneg _
      nlinarith
    have hCE : 0 < C * E := by positivity
    have : (C * E) * (K * E) < (C * E) * (C * E / 8) := by
      apply mul_lt_mul_of_pos_left _ hCE
      have : 8 * K < C := by
        rw [hC]; have := mul_nonneg (abs_nonneg (y T)) (exp_pos (3 / 4 * T)).le; linarith
      nlinarith
    nlinarith

/-- integrating factor bound for y' = -y + g -/
lemma lin_gen {y y' g G G' : ℝ → ℝ} {T : ℝ} (hy : ∀ τ, HasDerivAt y (y' τ) τ)
    (heq : ∀ τ, T ≤ τ → y' τ = - y τ + g τ) (hG : ∀ τ, HasDerivAt G (G' τ) τ)
    (hg : ∀ τ, T ≤ τ → exp τ * |g τ| ≤ G' τ) :
    ∀ τ, T ≤ τ → |y τ| ≤ (|y T| * exp T + G τ - G T) * exp (-τ) := by
  intro τ hτ
  have hF : ∀ t, HasDerivAt (fun t => exp t * y t) (exp t * y t + exp t * y' t) t :=
    fun t => (hasDerivAt_exp t).mul (hy t)
  have hFc : Continuous (fun t => exp t * y t) :=
    continuous_iff_continuousAt.2 fun t => (hF t).continuousAt
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := fun t => exp t * y t)
    (a := T) (b := τ) (B := fun t => |y T| * exp T + G t - G T) (B' := G')
    hFc.continuousOn (fun x _ => (hF x).hasDerivWithinAt)
    (by simp [Real.norm_eq_abs, abs_of_pos (exp_pos T)]; linarith)
    (fun t => ((hG t).const_add (|y T| * exp T)).sub_const (G T) |>.congr_deriv (by simp))
    (by
      intro x hx
      rw [Real.norm_eq_abs, heq x hx.1]
      have : exp x * y x + exp x * (-y x + g x) = exp x * g x := by ring
      rw [this, abs_mul, abs_of_pos (exp_pos x)]
      exact hg x hx.1) ⟨hτ, le_rfl⟩
  simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos τ)] at key
  have : |y τ| = (exp τ * |y τ|) * exp (-τ) := by
    rw [mul_comm (exp τ), mul_assoc, ← exp_add]; simp
  rw [this]
  exact mul_le_mul_of_nonneg_right key (exp_pos _).le

lemma lin_fast {y y' g : ℝ → ℝ} {T K : ℝ} (hy : ∀ τ, HasDerivAt y (y' τ) τ)
    (heq : ∀ τ, T ≤ τ → y' τ = - y τ + g τ) (hg : ∀ τ, T ≤ τ → |g τ| ≤ K * exp (-(5 / 4) * τ)) :
    ∃ C, ∀ τ, T ≤ τ → |y τ| ≤ C * exp (-τ) := by
  have hK : 0 ≤ K := by
    have h := hg T le_rfl
    have := abs_nonneg (g T)
    by_contra hK; push Not at hK
    have : K * exp (-(5 / 4) * T) < 0 := mul_neg_of_neg_of_pos hK (exp_pos _)
    linarith
  have key := lin_gen (G := fun t => -4 * K * exp (-(1/4) * t)) (G' := fun t => K * exp (-(1/4) * t))
    hy heq (fun t => (((hasDerivAt_id t).const_mul (-(1/4))).exp.const_mul (-4 * K)).congr_deriv
      (by simp; ring)) (by
      intro t ht
      have h := hg t ht
      have : exp t * (K * exp (-(5 / 4) * t)) = K * exp (-(1/4) * t) := by
        rw [mul_left_comm, ← exp_add]; ring_nf
      rw [← this]
      exact mul_le_mul_of_nonneg_left h (exp_pos t).le)
  refine ⟨|y T| * exp T + 4 * K * exp (-(1/4) * T), fun τ hτ => (key τ hτ).trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
  have : 0 ≤ 4 * K * exp (-(1/4) * τ) := by positivity
  linarith

lemma lin_res {y y' g : ℝ → ℝ} {T K : ℝ} (hT : 1 ≤ T) (hy : ∀ τ, HasDerivAt y (y' τ) τ)
    (heq : ∀ τ, T ≤ τ → y' τ = - y τ + g τ) (hg : ∀ τ, T ≤ τ → |g τ| ≤ K * exp (-τ)) :
    ∃ C, ∀ τ, T ≤ τ → |y τ| ≤ C * τ * exp (-τ) := by
  have hK : 0 ≤ K := by
    have h := hg T le_rfl
    have := abs_nonneg (g T)
    by_contra hK; push Not at hK
    have : K * exp (-T) < 0 := mul_neg_of_neg_of_pos hK (exp_pos _)
    linarith
  have key := lin_gen (G := fun t => K * t) (G' := fun _ => K)
    hy heq (fun t => ((hasDerivAt_id t).const_mul K).congr_deriv (by simp)) (by
      intro t ht
      have h := hg t ht
      have : exp t * (K * exp (-t)) = K := by
        rw [mul_left_comm, ← exp_add]; simp
      rw [← this]
      exact mul_le_mul_of_nonneg_left h (exp_pos t).le)
  refine ⟨|y T| * exp T + K, fun τ hτ => (key τ hτ).trans ?_⟩
  rw [mul_assoc (|y T| * exp T + K)]
  apply mul_le_mul_of_nonneg_right _ (exp_pos _).le |>.trans_eq (mul_assoc _ _ _)
  have h0 : 0 ≤ |y T| * exp T := by positivity
  nlinarith

end STV7

open Filter Topology Real

namespace STV7

lemma E2_le {τ : ℝ} (hτ : 0 ≤ τ) : exp (-(3 / 4) * τ) * exp (-(3 / 4) * τ) ≤ exp (-(5 / 4) * τ) := by
  rw [← exp_add]; apply exp_le_exp.2; nlinarith

lemma E2_le' {τ : ℝ} (hτ : 0 ≤ τ) : exp (-(3 / 4) * τ) * exp (-(3 / 4) * τ) ≤ exp (-τ) := by
  rw [← exp_add]; apply exp_le_exp.2; nlinarith

lemma mul_bd {x y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) : |x * y| ≤ X * Y := by
  rw [abs_mul]; exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)

lemma neg_bd {x X : ℝ} (hx : |x| ≤ X) : |-x| ≤ X := by rwa [abs_neg]

lemma cmul_bd {c x X : ℝ} (hc : 0 ≤ c) (hx : |x| ≤ X) : |c * x| ≤ c * X := by
  rw [abs_mul, abs_of_nonneg hc]; exact mul_le_mul_of_nonneg_left hx hc

lemma add_bd {x y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) : |x + y| ≤ X + Y :=
  (abs_add_le x y).trans (add_le_add hx hy)

lemma one_add_bd {v : ℝ} (hv : |v| ≤ 1 / 40) : |1 + v| ≤ 2 := by
  have := abs_le.1 hv; rw [abs_le]; constructor <;> linarith

lemma exp_bd {x Q R E : ℝ} (hx : |x| ≤ Q * E) (hQ : |Q| ≤ R) (hE : 0 ≤ E) : |x| ≤ R * E :=
  hx.trans (mul_le_mul_of_nonneg_right ((le_abs_self Q).trans hQ) hE)

end STV7

open STV7 in
theorem solution (U : ℝ → Fin 4 → ℝ) (hU : STVFriedmann.IsSTVSolution STVFriedmann.stvField2 U)
    (hM : Tendsto U atTop (𝓝 STVFriedmann.restM2)) :
    ∃ C T : ℝ, ∀ τ : ℝ, T ≤ τ →
      |U τ 0| ≤ C * Real.exp (-τ) ∧ |U τ 1 - 1| ≤ C * τ * Real.exp (-τ) ∧
      |U τ 2| ≤ C * Real.exp (-τ) ∧ |U τ 3| ≤ C * τ * Real.exp (-τ) := by
  have hd : ∀ i τ, HasDerivAt (fun t => U t i) (STVFriedmann.stvField2 (U τ) i) τ :=
    fun i τ => hasDerivAt_pi.1 (hU τ) i
  obtain ⟨z, hz⟩ : ∃ z : ℝ → ℝ, z = fun t => U t 0 := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : ℝ → ℝ, v = fun t => U t 1 - 1 := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℝ → ℝ, a = fun t => U t 2 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ → ℝ, b = fun t => U t 3 := ⟨_, rfl⟩
  have dz : ∀ τ, HasDerivAt z (-(1 + 3 * v τ) * z τ) τ := by
    intro τ; subst hz hv
    exact (hd 0 τ).congr_deriv (by simp [STVFriedmann.stvField2]; ring)
  have dv : ∀ τ, HasDerivAt v (-(1 + v τ) * v τ + -(z τ / 6)) τ := by
    intro τ; subst hz hv
    exact ((hd 1 τ).sub_const 1).congr_deriv (by simp [STVFriedmann.stvField2]; ring)
  have da : ∀ τ, HasDerivAt a (-(1 + 5 * v τ) * a τ +
      ((5 / 12) * z τ ^ 2 * (1 + v τ) - 5 * z τ * b τ)) τ := by
    intro τ; subst hz hv ha hb
    exact (hd 2 τ).congr_deriv (by simp [STVFriedmann.stvField2]; ring)
  have db : ∀ τ, HasDerivAt b (-(1 + 4 * v τ) * b τ +
      (-(a τ / 10) + z τ * (1 + v τ) ^ 2 / 4 - z τ ^ 2 / 24)) τ := by
    intro τ; subst hz hv ha hb
    exact (hd 3 τ).congr_deriv (by simp [STVFriedmann.stvField2]; ring)
  -- smallness
  have hev : ∀ᶠ t in atTop, |z t| ≤ 1/40 ∧ |v t| ≤ 1/40 ∧ |a t| ≤ 1/40 ∧ |b t| ≤ 1/40 ∧ 1 ≤ t := by
    have h := tendsto_pi_nhds.1 hM
    have e : ∀ i, ∀ᶠ t in atTop, |U t i - STVFriedmann.restM2 i| ≤ 1/40 := fun i =>
      ((h i).eventually (Metric.closedBall_mem_nhds _ (by norm_num : (0:ℝ) < 1/40))).mono
        fun t ht => by simpa [Metric.mem_closedBall, Real.dist_eq] using ht
    filter_upwards [e 0, e 1, e 2, e 3, eventually_ge_atTop 1] with t h0 h1 h2 h3 h4
    subst hz hv ha hb
    simp only [STVFriedmann.restM2] at h0 h1 h2 h3
    refine ⟨by simpa using h0, by simpa using h1, by simpa using h2, by simpa using h3, h4⟩
  obtain ⟨T, hT⟩ := eventually_atTop.1 hev
  have hT1 : 1 ≤ T := (hT T le_rfl).2.2.2.2
  have hp : ∀ (c : ℝ), 0 ≤ c → c ≤ 5 → ∀ τ, T ≤ τ → |c * v τ| ≤ 1 / 8 := by
    intro c hc0 hc τ hτ
    rw [abs_mul, abs_of_nonneg hc0]
    have := (hT τ hτ).2.1
    have := abs_nonneg (v τ)
    nlinarith
  -- rough phase
  obtain ⟨Rz, hRz⟩ := rough (K := 0) (T := T) (p := fun τ => 3 * v τ) (g := fun _ => 0) dz
    (fun τ _ => by ring) (hp 3 (by norm_num) (by norm_num)) (fun τ _ => by simp)
  have hE34 : ∀ τ, 0 ≤ exp (-(3 / 4) * τ) := fun τ => (exp_pos _).le
  have bz0 : ∀ τ, T ≤ τ → |z τ| ≤ |Rz| * exp (-(3 / 4) * τ) := fun τ hτ =>
    exp_bd (hRz τ hτ) le_rfl (hE34 τ)
  obtain ⟨Rv, hRv⟩ := rough (K := 1 / 6 * |Rz|) (T := T) (p := v) (g := fun τ => 1 / 6 * -z τ) dv
    (fun τ _ => by ring) (by simpa using hp 1 (by norm_num) (by norm_num)) (fun τ hτ => by
      rw [mul_assoc]; exact cmul_bd (by norm_num) (neg_bd (bz0 τ hτ)))
  obtain ⟨Ra, hRa⟩ := rough (K := |Rz|) (T := T) (p := fun τ => 5 * v τ)
    (g := fun τ => (5 / 12) * (z τ * (z τ * (1 + v τ))) + 5 * (z τ * -b τ)) da
    (fun τ _ => by ring) (hp 5 (by norm_num) (by norm_num)) (fun τ hτ => by
      obtain ⟨h0, h1, -, h3, -⟩ := hT τ hτ
      have e1 := cmul_bd (c := 5 / 12) (by norm_num) (mul_bd (bz0 τ hτ) (mul_bd h0 (one_add_bd h1)))
      have e2 := cmul_bd (c := 5) (by norm_num) (mul_bd (bz0 τ hτ) (neg_bd h3))
      have := add_bd e1 e2
      have : 0 ≤ |Rz| * exp (-(3 / 4) * τ) := mul_nonneg (abs_nonneg _) (hE34 τ)
      linarith)
  have ba0 : ∀ τ, T ≤ τ → |a τ| ≤ |Ra| * exp (-(3 / 4) * τ) := fun τ hτ =>
    exp_bd (hRa τ hτ) le_rfl (hE34 τ)
  obtain ⟨Rb, hRb⟩ := rough (K := |Ra| + 2 * |Rz|) (T := T) (p := fun τ => 4 * v τ)
    (g := fun τ => 1 / 10 * -a τ + 1 / 4 * (z τ * ((1 + v τ) * (1 + v τ))) + 1 / 24 * (z τ * -z τ)) db
    (fun τ _ => by ring) (hp 4 (by norm_num) (by norm_num)) (fun τ hτ => by
      obtain ⟨h0, h1, -, h3, -⟩ := hT τ hτ
      have e1 := cmul_bd (c := 1 / 10) (by norm_num) (neg_bd (ba0 τ hτ))
      have e2 := cmul_bd (c := 1 / 4) (by norm_num)
        (mul_bd (bz0 τ hτ) (mul_bd (one_add_bd h1) (one_add_bd h1)))
      have e3 := cmul_bd (c := 1 / 24) (by norm_num) (mul_bd (bz0 τ hτ) (neg_bd h0))
      have := add_bd (add_bd e1 e2) e3
      have : 0 ≤ |Rz| * exp (-(3 / 4) * τ) := mul_nonneg (abs_nonneg _) (hE34 τ)
      have : 0 ≤ |Ra| * exp (-(3 / 4) * τ) := mul_nonneg (abs_nonneg _) (hE34 τ)
      have : (|Ra| + 2 * |Rz|) * exp (-(3 / 4) * τ) =
        |Ra| * exp (-(3 / 4) * τ) + 2 * (|Rz| * exp (-(3 / 4) * τ)) := by ring
      linarith)
  -- common rough bound
  set R := max (max |Rz| |Rv|) (max |Ra| |Rb|) with hR
  have bz : ∀ τ, T ≤ τ → |z τ| ≤ R * exp (-(3 / 4) * τ) := fun τ hτ =>
    exp_bd (hRz τ hτ) (by simp [hR]) (hE34 τ)
  have bv : ∀ τ, T ≤ τ → |v τ| ≤ R * exp (-(3 / 4) * τ) := fun τ hτ =>
    exp_bd (hRv τ hτ) (by simp [hR]) (hE34 τ)
  have ba : ∀ τ, T ≤ τ → |a τ| ≤ R * exp (-(3 / 4) * τ) := fun τ hτ =>
    exp_bd (hRa τ hτ) (by simp [hR]) (hE34 τ)
  have bb : ∀ τ, T ≤ τ → |b τ| ≤ R * exp (-(3 / 4) * τ) := fun τ hτ =>
    exp_bd (hRb τ hτ) (by simp [hR]) (hE34 τ)
  have RR : ∀ τ, T ≤ τ → (R * exp (-(3 / 4) * τ)) * (R * exp (-(3 / 4) * τ)) ≤ R ^ 2 * exp (-(5 / 4) * τ) ∧
      (R * exp (-(3 / 4) * τ)) * (R * exp (-(3 / 4) * τ)) ≤ R ^ 2 * exp (-τ) := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := by linarith
    have e : (R * exp (-(3 / 4) * τ)) * (R * exp (-(3 / 4) * τ)) =
        R ^ 2 * (exp (-(3 / 4) * τ) * exp (-(3 / 4) * τ)) := by ring
    rw [e]
    exact ⟨mul_le_mul_of_nonneg_left (E2_le hτ0) (sq_nonneg R),
      mul_le_mul_of_nonneg_left (E2_le' hτ0) (sq_nonneg R)⟩
  -- precise phase
  obtain ⟨Cz, hCz⟩ := lin_fast (K := 3 * R ^ 2) (T := T) (g := fun τ => 3 * (v τ * -z τ)) dz
    (fun τ _ => by ring) (fun τ hτ => by
      have e1 := cmul_bd (c := 3) (by norm_num) (mul_bd (bv τ hτ) (neg_bd (bz τ hτ)))
      have := (RR τ hτ).1
      linarith)
  have hE : ∀ τ, 0 ≤ exp (-τ) := fun τ => (exp_pos _).le
  have cz : ∀ τ, T ≤ τ → |z τ| ≤ |Cz| * exp (-τ) := fun τ hτ => exp_bd (hCz τ hτ) le_rfl (hE τ)
  obtain ⟨Cv, hCv⟩ := lin_res (K := R ^ 2 + 1 / 6 * |Cz|) (T := T) hT1
    (g := fun τ => v τ * -v τ + 1 / 6 * -z τ) dv
    (fun τ _ => by ring) (fun τ hτ => by
      have e1 := mul_bd (bv τ hτ) (neg_bd (bv τ hτ))
      have e2 := cmul_bd (c := 1 / 6) (by norm_num) (neg_bd (cz τ hτ))
      have := add_bd e1 e2
      have := (RR τ hτ).2
      linarith)
  obtain ⟨Ca, hCa⟩ := lin_fast (K := 11 * R ^ 2) (T := T)
    (g := fun τ => 5 * (v τ * -a τ) + (5 / 12) * ((z τ * z τ) * (1 + v τ)) + 5 * (z τ * -b τ)) da
    (fun τ _ => by ring) (fun τ hτ => by
      have e1 := cmul_bd (c := 5) (by norm_num) (mul_bd (bv τ hτ) (neg_bd (ba τ hτ)))
      have e2 := cmul_bd (c := 5 / 12) (by norm_num)
        (mul_bd (mul_bd (bz τ hτ) (bz τ hτ)) (one_add_bd (hT τ hτ).2.1))
      have e3 := cmul_bd (c := 5) (by norm_num) (mul_bd (bz τ hτ) (neg_bd (bb τ hτ)))
      have := add_bd (add_bd e1 e2) e3
      have := (RR τ hτ).1
      have : 11 * R ^ 2 * exp (-(5 / 4) * τ) = 11 * (R ^ 2 * exp (-(5 / 4) * τ)) := by ring
      have : 0 ≤ R ^ 2 * exp (-(5 / 4) * τ) := mul_nonneg (sq_nonneg _) (exp_pos _).le
      linarith)
  have ca : ∀ τ, T ≤ τ → |a τ| ≤ |Ca| * exp (-τ) := fun τ hτ => exp_bd (hCa τ hτ) le_rfl (hE τ)
  obtain ⟨Cb, hCb⟩ := lin_res (K := 5 * R ^ 2 + |Ca| + |Cz|) (T := T) hT1
    (g := fun τ => 4 * (v τ * -b τ) + 1 / 10 * -a τ + 1 / 4 * (z τ * ((1 + v τ) * (1 + v τ)))
      + 1 / 24 * (z τ * -z τ)) db
    (fun τ _ => by ring) (fun τ hτ => by
      have h1 := (hT τ hτ).2.1
      have e1 := cmul_bd (c := 4) (by norm_num) (mul_bd (bv τ hτ) (neg_bd (bb τ hτ)))
      have e2 := cmul_bd (c := 1 / 10) (by norm_num) (neg_bd (ca τ hτ))
      have e3 := cmul_bd (c := 1 / 4) (by norm_num)
        (mul_bd (cz τ hτ) (mul_bd (one_add_bd h1) (one_add_bd h1)))
      have e4 := cmul_bd (c := 1 / 24) (by norm_num) (mul_bd (bz τ hτ) (neg_bd (bz τ hτ)))
      have := add_bd (add_bd (add_bd e1 e2) e3) e4
      have := (RR τ hτ).2
      have : 0 ≤ |Ca| * exp (-τ) := mul_nonneg (abs_nonneg _) (hE τ)
      have : 0 ≤ R * exp (-(3 / 4) * τ) * (R * exp (-(3 / 4) * τ)) := mul_self_nonneg _
      have : 0 ≤ R ^ 2 * exp (-τ) := mul_nonneg (sq_nonneg _) (hE τ)
      have : (5 * R ^ 2 + |Ca| + |Cz|) * exp (-τ) =
        5 * (R ^ 2 * exp (-τ)) + |Ca| * exp (-τ) + |Cz| * exp (-τ) := by ring
      linarith)
  -- assemble
  refine ⟨max (max |Cz| |Cv|) (max |Ca| |Cb|), T, fun τ hτ => ?_⟩
  have hτ0 : 0 ≤ τ := by linarith
  have hτE : 0 ≤ τ * exp (-τ) := mul_nonneg hτ0 (hE τ)
  have hzτ := hCz τ hτ; have hvτ := hCv τ hτ; have haτ := hCa τ hτ; have hbτ := hCb τ hτ
  subst hz hv ha hb
  refine ⟨hzτ.trans ?_, hvτ.trans ?_, haτ.trans ?_, hbτ.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (by simp)) (hE τ)
  · rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (by simp)) hτE
  · exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (by simp)) (hE τ)
  · rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (by simp)) hτE
