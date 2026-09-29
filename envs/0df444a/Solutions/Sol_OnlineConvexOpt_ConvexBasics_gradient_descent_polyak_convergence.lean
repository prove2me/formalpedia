-- Prove2me | solution 1 for OnlineConvexOpt.ConvexBasics.gradient_descent_polyak_convergence
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T20:17:45.068023+00:00
-- url     : https://prove2.me/submissions/b53671fc-c2a4-40e7-adb6-3131a9b8733b

import Mathlib
import Definitions.Def_OnlineConvexOpt_ConvexBasics_GradientDescentPolyak
import Definitions.Def_OnlineConvexOpt_ConvexBasics_StronglyConvexOn
import Definitions.Def_OnlineConvexOpt_ConvexBasics_SmoothOn

/-! 38827468 OnlineConvexOpt.ConvexBasics.gradient_descent_polyak_convergence (Hazan, OCO, Thm 2.3).
Write `h_t = f(x_t) - f(x⋆)`, `a_t = ‖x_t - x⋆‖²`, `η_t = h_t/‖∇_t‖²`, `m = h(x̄) = min_{t ≤ T} h_t`.
Smoothness gives `‖∇f(z)‖² ≤ 2β h(z)` (one `1/β` step), hence `∇f(x⋆) = 0`, and then
`α a/2 ≤ h ≤ β a/2`. Strong convexity gives `⟪∇_t, x_t - x⋆⟫ ≥ h_t + α a_t/2`, and expanding the
Polyak step (`η_t ‖∇_t‖² = h_t`) gives `a_{t+1} ≤ a_t - η_t (h_t + α a_t)`.  Consequences:
* `G² a_{t+1} ≤ G² a_t - h_t (h_t + α a_t)` (as `η_t ≥ h_t/G²`): summing gives `T m² ≤ G² a_0`.
* `2β a_{t+1} ≤ 2β a_t - h_t` (as `η_t ≥ 1/(2β)` when `h_t > 0`): summing gives `T m ≤ 2β a_0`.
* with `b_t = 3α² a_t/(4G²)`: `b_{t+1} ≤ b_t - b_t²`, `b_0 ≤ 3/4`, so `b_t ≤ 1/(t+1)`; summing the
  first bullet over `[⌊T/2⌋, T)` gives `3 α² T² m² ≤ 16 G⁴`, so `m ≤ 3G²/(αT)`.
* `a_{t+1} ≤ (1 - α/(4β)) a_t`, so `m ≤ h_T ≤ β a_T/2 ≤ β a_0 (1 - α/β/4)^T`.
No `Theorems.*` module is imported. -/

set_option autoImplicit false

open scoped InnerProductSpace

/-- One gradient step of length `1/β` from `x` decreases a `β`-smooth `f` by `‖g x‖²/(2β)`. -/
theorem ocp_smooth_step_descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (g : E → E) (β : ℝ) (hβ : 0 < β)
    (hsm : ∀ x y, f y ≤ f x + ⟪g x, y - x⟫_ℝ + (β / 2) * ‖y - x‖ ^ 2) (x : E) :
    f (x - (1 / β) • g x) ≤ f x - (1 / (2 * β)) * ‖g x‖ ^ 2 := by
  have h := hsm x (x - (1 / β) • g x)
  have e1 : x - (1 / β) • g x - x = -((1 / β) • g x) := by abel
  rw [e1, inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq, norm_neg,
    norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 1 / β)] at h
  have e2 : f x + -(1 / β * ‖g x‖ ^ 2) + β / 2 * (1 / β * ‖g x‖) ^ 2
      = f x - (1 / (2 * β)) * ‖g x‖ ^ 2 := by
    field_simp
    ring
  linarith

/-- Telescoping a uniform decrease `u (t+1) ≤ u t - c` over `[k, k + n)`. -/
theorem ocp_telescope (u : ℕ → ℝ) (c : ℝ) (k T : ℕ)
    (h : ∀ t, k ≤ t → t < T → u (t + 1) ≤ u t - c) :
    ∀ n : ℕ, k + n ≤ T → u (k + n) ≤ u k - n * c := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have h2 := h (k + n) (by omega) (by omega)
    rw [show k + (n + 1) = k + n + 1 by omega]
    push_cast
    linarith

/-- `b - b² ≤ 1/(s+1)` whenever `0 ≤ b ≤ 1/s` and `s ≥ 1`. -/
theorem ocp_hyper_step (b s : ℝ) (hs : 1 ≤ s) (hb0 : 0 ≤ b) (hb : b ≤ 1 / s) :
    b - b ^ 2 ≤ 1 / (s + 1) := by
  have hs0 : 0 < s := by linarith
  have hbs : b * s ≤ 1 := by rwa [le_div_iff₀ hs0] at hb
  have hb1 : b ≤ 1 := le_trans hb (by rw [div_le_one hs0]; exact hs)
  rw [le_div_iff₀ (by linarith)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hbs) (sub_nonneg.mpr hb1), sq_nonneg b]

/-- The recursion `0 ≤ b_{t+1} ≤ b_t - b_t²`, `b_0 ≤ 1` forces `b_t ≤ 1/(t+1)`. -/
theorem ocp_hyper (b : ℕ → ℝ) (T : ℕ) (hb0 : ∀ t, 0 ≤ b t) (hinit : b 0 ≤ 1)
    (hstep : ∀ t, t < T → b (t + 1) ≤ b t - b t ^ 2) :
    ∀ t, t ≤ T → b t ≤ 1 / ((t : ℝ) + 1) := by
  intro t
  induction t with
  | zero => intro _; simpa using hinit
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have h2 := hstep n (by omega)
    have h3 := ocp_hyper_step (b n) ((n : ℝ) + 1)
      (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]) (hb0 n) h1
    push_cast
    linarith

/-- Bound 1: `T m² ≤ G² a₀`. -/
theorem ocp_b1 (a h : ℕ → ℝ) (G m d0 : ℝ) (T : ℕ) (hT : 0 < T) (hG : 0 < G)
    (hd0 : 0 ≤ d0) (ha0 : a 0 = d0 ^ 2) (ha : ∀ t, 0 ≤ a t) (hm0 : 0 ≤ m)
    (hm : ∀ s ≤ T, m ≤ h s)
    (hstep : ∀ t, t < T → G ^ 2 * a (t + 1) ≤ G ^ 2 * a t - h t ^ 2) :
    m ≤ G * d0 / Real.sqrt T := by
  have hTpos : (0:ℝ) < T := by exact_mod_cast hT
  have h1 := ocp_telescope (fun t => G ^ 2 * a t) (m ^ 2) 0 T (fun t _ ht => by
      have h1 := hstep t ht
      have h2 := hm t ht.le
      have h4 := mul_le_mul h2 h2 hm0 (le_trans hm0 h2)
      show G ^ 2 * a (t + 1) ≤ G ^ 2 * a t - m ^ 2
      nlinarith) T (by omega)
  rw [zero_add] at h1
  have h1' : G ^ 2 * a T ≤ G ^ 2 * a 0 - (T:ℝ) * m ^ 2 := h1
  have h2 : 0 ≤ G ^ 2 * a T := mul_nonneg (sq_nonneg G) (ha T)
  rw [le_div_iff₀ (Real.sqrt_pos.mpr hTpos)]
  have hmT : 0 ≤ m * Real.sqrt T := mul_nonneg hm0 (Real.sqrt_nonneg _)
  have hGd : 0 ≤ G * d0 := mul_nonneg hG.le hd0
  rw [← sq_le_sq₀ hmT hGd, mul_pow, Real.sq_sqrt hTpos.le, mul_pow, ← ha0]
  linarith

/-- Bound 2: `T m ≤ 2β a₀`. -/
theorem ocp_b2 (a h : ℕ → ℝ) (β m d0 : ℝ) (T : ℕ) (hT : 0 < T) (hβ : 0 < β)
    (ha0 : a 0 = d0 ^ 2) (ha : ∀ t, 0 ≤ a t) (hm : ∀ s ≤ T, m ≤ h s)
    (hstep : ∀ t, 2 * β * a (t + 1) ≤ 2 * β * a t - h t) :
    m ≤ 2 * β * d0 ^ 2 / T := by
  have hTpos : (0:ℝ) < T := by exact_mod_cast hT
  have h1 := ocp_telescope (fun t => 2 * β * a t) m 0 T (fun t _ ht => by
      have h1 := hstep t
      have h2 := hm t ht.le
      show 2 * β * a (t + 1) ≤ 2 * β * a t - m
      linarith) T (by omega)
  rw [zero_add] at h1
  have h1' : 2 * β * a T ≤ 2 * β * a 0 - (T:ℝ) * m := h1
  have h2 : 0 ≤ 2 * β * a T := mul_nonneg (by positivity) (ha T)
  rw [le_div_iff₀ hTpos, ← ha0]
  linarith

/-- The final arithmetic of bound 3. -/
theorem ocp_b3_arith (α G m Ak Tr kr : ℝ) (hα : 0 < α) (hG : 0 < G) (hm0 : 0 ≤ m)
    (hT : 0 < Tr) (a1 : 2 * kr ≤ Tr) (a2 : Tr ≤ 2 * kr + 1)
    (e1 : (Tr - kr) * m ^ 2 ≤ G ^ 2 * Ak) (e2 : 3 * α ^ 2 * (kr + 1) * Ak ≤ 4 * G ^ 2) :
    m ≤ 3 * G ^ 2 / (α * Tr) := by
  have e3 : Tr ^ 2 ≤ 4 * (kr + 1) * (Tr - kr) := by
    have p1 : 0 ≤ 2 * (kr + 1) - Tr := by linarith
    have p2 : 0 ≤ 2 * (Tr - kr) - Tr := by linarith
    nlinarith [mul_nonneg p1 p2, mul_nonneg hT.le p1, mul_nonneg hT.le p2]
  have hTk : 0 ≤ Tr - kr := by linarith
  have hk1 : 0 ≤ kr + 1 := by linarith
  have f1 : 3 * α ^ 2 * Tr ^ 2 * m ^ 2 ≤ 3 * α ^ 2 * (4 * (kr + 1) * (Tr - kr)) * m ^ 2 := by
    gcongr
  have f2 : 3 * α ^ 2 * (kr + 1) * ((Tr - kr) * m ^ 2) ≤ 3 * α ^ 2 * (kr + 1) * (G ^ 2 * Ak) :=
    mul_le_mul_of_nonneg_left e1 (mul_nonneg (by positivity) hk1)
  have f3 : G ^ 2 * (3 * α ^ 2 * (kr + 1) * Ak) ≤ G ^ 2 * (4 * G ^ 2) :=
    mul_le_mul_of_nonneg_left e2 (sq_nonneg G)
  have f4 : 3 * (α * Tr * m) ^ 2 ≤ 16 * G ^ 4 := by linarith [f1, f2, f3]
  have f5 : α * Tr * m ≤ 3 * G ^ 2 := by
    have hG4 : 0 ≤ G ^ 4 := by positivity
    have h : (α * Tr * m) ^ 2 ≤ (3 * G ^ 2) ^ 2 := by linarith
    exact (sq_le_sq₀ (mul_nonneg (mul_nonneg hα.le hT.le) hm0) (by positivity)).mp h
  rw [le_div_iff₀ (by positivity)]
  linarith [f5]

/-- Bound 3: `m ≤ 3G²/(αT)`, via `b_t = 3α² a_t/(4G²) ≤ 1/(t+1)` and the tail over `[⌊T/2⌋, T)`. -/
theorem ocp_b3 (a h : ℕ → ℝ) (α G m : ℝ) (T : ℕ) (hT : 0 < T) (hα : 0 < α) (hG : 0 < G)
    (ha : ∀ t, 0 ≤ a t) (hm0 : 0 ≤ m) (hm : ∀ s ≤ T, m ≤ h s)
    (hlow : ∀ t, α / 2 * a t ≤ h t)
    (hstep : ∀ t, t < T → G ^ 2 * a (t + 1) ≤ G ^ 2 * a t - h t * (h t + α * a t))
    (hd0 : α ^ 2 * a 0 ≤ G ^ 2) :
    m ≤ 3 * G ^ 2 / (α * T) := by
  have hG2 : 0 < G ^ 2 := by positivity
  obtain ⟨c, hc0, hcG⟩ : ∃ c : ℝ, 0 < c ∧ c * G ^ 2 = 3 * α ^ 2 / 4 :=
    ⟨3 * α ^ 2 / (4 * G ^ 2), by positivity, by
      rw [div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by positivity)]
      ring⟩
  have hbstep : ∀ t, t < T → c * a (t + 1) ≤ c * a t - (c * a t) ^ 2 := by
    intro t ht
    have h1 := hstep t ht
    have h2 := hlow t
    have hat := ha t
    have hh : 0 ≤ h t := le_trans (by positivity) h2
    have h3 : 3 * α ^ 2 / 4 * a t ^ 2 ≤ h t * (h t + α * a t) := by
      have hq : 3 * α / 2 * a t ≤ h t + α * a t := by linarith
      have := mul_le_mul h2 hq (by positivity) hh
      linarith [this]
    have h4 : G ^ 2 * a (t + 1) ≤ G ^ 2 * (a t - c * a t ^ 2) := by
      have e : G ^ 2 * (c * a t ^ 2) = 3 * α ^ 2 / 4 * a t ^ 2 := by rw [← hcG]; ring
      linarith [e]
    have h5 : a (t + 1) ≤ a t - c * a t ^ 2 := le_of_mul_le_mul_left h4 hG2
    nlinarith [mul_le_mul_of_nonneg_left h5 hc0.le]
  have hinit : c * a 0 ≤ 1 := by
    have e : G ^ 2 * (c * a 0) = (c * G ^ 2) * a 0 := by ring
    rw [hcG] at e
    have : G ^ 2 * (c * a 0) ≤ G ^ 2 * 1 := by linarith
    exact le_of_mul_le_mul_left this hG2
  have hyp := ocp_hyper (fun t => c * a t) T (fun t => mul_nonneg hc0.le (ha t)) hinit hbstep
  obtain ⟨k, hk1, hk2⟩ : ∃ k : ℕ, 2 * k ≤ T ∧ T ≤ 2 * k + 1 := ⟨T / 2, by omega, by omega⟩
  have hkT : k ≤ T := by omega
  have htel := ocp_telescope (fun t => G ^ 2 * a t) (m ^ 2) k T (fun t _ ht => by
      have h1 := hstep t ht
      have h2 := hm t ht.le
      have hat := ha t
      have hh : 0 ≤ h t := le_trans hm0 h2
      have h4 := mul_le_mul h2 h2 hm0 hh
      have h5 : 0 ≤ h t * (α * a t) := mul_nonneg hh (by positivity)
      show G ^ 2 * a (t + 1) ≤ G ^ 2 * a t - m ^ 2
      nlinarith) (T - k) (by omega)
  have ek : k + (T - k) = T := by omega
  rw [ek, Nat.cast_sub hkT] at htel
  have htail : G ^ 2 * a T ≤ G ^ 2 * a k - ((T:ℝ) - k) * m ^ 2 := htel
  have hlast : 0 ≤ G ^ 2 * a T := mul_nonneg (sq_nonneg G) (ha T)
  have e1 : ((T:ℝ) - k) * m ^ 2 ≤ G ^ 2 * a k := by linarith
  have e2 : 3 * α ^ 2 * ((k:ℝ) + 1) * a k ≤ 4 * G ^ 2 := by
    have hck' : c * a k * ((k:ℝ) + 1) ≤ 1 := by
      have := hyp k hkT
      rwa [le_div_iff₀ (by positivity)] at this
    have e : 3 * α ^ 2 * ((k:ℝ) + 1) * a k = 4 * G ^ 2 * (c * a k * ((k:ℝ) + 1)) := by
      have : 3 * α ^ 2 = 4 * (c * G ^ 2) := by rw [hcG]; ring
      rw [this]; ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hck' (by positivity : (0:ℝ) ≤ 4 * G ^ 2)
    linarith
  exact ocp_b3_arith α G m (a k) T k hα hG hm0 (by exact_mod_cast hT)
    (by exact_mod_cast hk1) (by exact_mod_cast hk2) e1 e2

/-- Bound 4: linear convergence `a_{t+1} ≤ (1 - α/(4β)) a_t`, then `m ≤ h_T ≤ β a_T / 2`. -/
theorem ocp_b4 (a h : ℕ → ℝ) (α β m d0 : ℝ) (T : ℕ) (hα : 0 < α) (hβ : 0 < β)
    (ha0 : a 0 = d0 ^ 2) (ha : ∀ t, 0 ≤ a t) (hm : ∀ s ≤ T, m ≤ h s)
    (hlow : ∀ t, α / 2 * a t ≤ h t) (hup : ∀ t, h t ≤ β / 2 * a t)
    (hstep : ∀ t, 2 * β * a (t + 1) ≤ 2 * β * a t - h t) :
    m ≤ β * d0 ^ 2 * (1 - α / β / 4) ^ T := by
  rw [← ha0]
  rcases eq_or_lt_of_le (ha 0) with h0 | h0
  · have h1 := hup 0
    have h2 := hm 0 (Nat.zero_le _)
    rw [← h0] at h1 ⊢
    linarith
  · have hab : α ≤ β := by
      have h1 := hlow 0
      have h2 := hup 0
      nlinarith
    obtain ⟨r, hr⟩ : ∃ r : ℝ, r = 1 - α / β / 4 := ⟨_, rfl⟩
    rw [← hr]
    have hr0 : 0 ≤ r := by
      have : α / β ≤ 1 := (div_le_one hβ).mpr hab
      rw [hr]; linarith
    have hβα : β * (α / β) = α := mul_div_cancel₀ α hβ.ne'
    have hstep4 : ∀ t, a (t + 1) ≤ r * a t := by
      intro t
      have h1 := hstep t
      have h2 := hlow t
      have e : 2 * β * (r * a t) = 2 * β * a t - α / 2 * a t := by
        rw [hr]; linear_combination (-(a t) / 2) * hβα
      have h3 : 2 * β * a (t + 1) ≤ 2 * β * (r * a t) := by rw [e]; linarith
      exact le_of_mul_le_mul_left h3 (by positivity)
    have hpow : ∀ n : ℕ, a n ≤ r ^ n * a 0 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        calc a (n + 1) ≤ r * a n := hstep4 n
          _ ≤ r * (r ^ n * a 0) := mul_le_mul_of_nonneg_left ih hr0
          _ = r ^ (n + 1) * a 0 := by ring
    have h1 := hm T le_rfl
    have h2 := hup T
    have h3 := hpow T
    have h4 : 0 ≤ r ^ T * a 0 := mul_nonneg (pow_nonneg hr0 T) (ha 0)
    nlinarith [mul_le_mul_of_nonneg_left h3 (by positivity : (0:ℝ) ≤ β / 2),
      mul_nonneg hβ.le h4]

open OnlineConvexOpt.ConvexBasics in
theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ) (g : E → E) (α β G : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hG : 0 < G)
    (hfconv : ConvexOn ℝ Set.univ f)
    (hsc : StronglyConvexOn Set.univ f g α) (hsm : SmoothOn Set.univ f g β)
    (xstar : E) (hxstar : IsMinOn f Set.univ xstar)
    (x : ℕ → E) (hGD : IsGradientDescentPolyak f xstar g x)
    (T : ℕ) (hT : 0 < T)
    (hGbound : ∀ t ≤ T, ‖g (x t)‖ ≤ G)
    (xbar : E) (hxbar : ∃ t ≤ T, xbar = x t ∧ ∀ s ≤ T, f (x t) ≤ f (x s)) :
    f xbar - f xstar ≤
      min (G * ‖x 0 - xstar‖ / Real.sqrt T)
        (min (2 * β * ‖x 0 - xstar‖ ^ 2 / T)
          (min (3 * G ^ 2 / (α * T))
            (β * ‖x 0 - xstar‖ ^ 2 * (1 - α / β / 4) ^ T))) := by
  have hβne : β ≠ 0 := hβ.ne'
  have hGne : G ≠ 0 := hG.ne'
  have hsm' : ∀ x y, f y ≤ f x + ⟪g x, y - x⟫_ℝ + (β / 2) * ‖y - x‖ ^ 2 :=
    fun x y => hsm x (Set.mem_univ _) y (Set.mem_univ _)
  have hsc' : ∀ x y, f y ≥ f x + ⟪g x, y - x⟫_ℝ + (α / 2) * ‖y - x‖ ^ 2 :=
    fun x y => hsc x (Set.mem_univ _) y (Set.mem_univ _)
  have hmin : ∀ z, f xstar ≤ f z := fun z => hxstar (Set.mem_univ z)
  obtain ⟨_, hxs⟩ := hGD
  -- `‖∇f(z)‖² ≤ 2β (f z - f x⋆)`
  have hgradsq : ∀ z, ‖g z‖ ^ 2 ≤ 2 * β * (f z - f xstar) := by
    intro z
    have h1 := ocp_smooth_step_descent f g β hβ hsm' z
    have h2 := hmin (z - (1 / β) • g z)
    have h3 : (1 / (2 * β)) * ‖g z‖ ^ 2 ≤ f z - f xstar := by linarith
    have h4 : 2 * β * ((1 / (2 * β)) * ‖g z‖ ^ 2) = ‖g z‖ ^ 2 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h3 (by positivity : (0:ℝ) ≤ 2 * β)]
  have hg0 : g xstar = 0 := by
    have h := hgradsq xstar
    simp only [sub_self, mul_zero] at h
    have h' : ‖g xstar‖ ^ 2 = 0 := le_antisymm h (sq_nonneg _)
    exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h')
  have hqlow : ∀ z, α / 2 * ‖z - xstar‖ ^ 2 ≤ f z - f xstar := by
    intro z
    have h := hsc' xstar z
    rw [hg0, inner_zero_left] at h
    linarith
  have hqup : ∀ z, f z - f xstar ≤ β / 2 * ‖z - xstar‖ ^ 2 := by
    intro z
    have h := hsm' xstar z
    rw [hg0, inner_zero_left] at h
    linarith
  have hinner : ∀ z, f z - f xstar + α / 2 * ‖z - xstar‖ ^ 2 ≤ ⟪g z, z - xstar⟫_ℝ := by
    intro z
    have h := hsc' z xstar
    have e1 : xstar - z = -(z - xstar) := by abel
    rw [e1, inner_neg_right, norm_neg] at h
    linarith
  have hhz : ∀ t, 0 ≤ f (x t) - f xstar := fun t => sub_nonneg.mpr (hmin _)
  -- `η_t ‖∇_t‖² = h_t` (both sides vanish when `∇_t = 0`)
  have hηn : ∀ t, (f (x t) - f xstar) / ‖g (x t)‖ ^ 2 * ‖g (x t)‖ ^ 2 = f (x t) - f xstar := by
    intro t
    rcases eq_or_ne (g (x t)) 0 with h0 | h0
    · have hi := hinner (x t)
      rw [h0, inner_zero_left] at hi
      have hpos : 0 ≤ α / 2 * ‖x t - xstar‖ ^ 2 := by positivity
      have hz : f (x t) - f xstar = 0 := le_antisymm (by linarith) (hhz t)
      rw [h0, hz]
      simp
    · have hn : 0 < ‖g (x t)‖ ^ 2 := pow_pos (norm_pos_iff.mpr h0) 2
      exact div_mul_cancel₀ _ hn.ne'
  -- the basic one-step inequality
  have hstepgen : ∀ t, ‖x (t + 1) - xstar‖ ^ 2 ≤ ‖x t - xstar‖ ^ 2
      - ((f (x t) - f xstar) / ‖g (x t)‖ ^ 2) *
        ((f (x t) - f xstar) + α * ‖x t - xstar‖ ^ 2) := by
    intro t
    have e : x (t + 1) - xstar
        = (x t - xstar) - ((f (x t) - f xstar) / ‖g (x t)‖ ^ 2) • g (x t) := by
      rw [hxs t]; abel
    have hi := hinner (x t)
    have hn := hηn t
    have hη0 : 0 ≤ (f (x t) - f xstar) / ‖g (x t)‖ ^ 2 := div_nonneg (hhz t) (sq_nonneg _)
    rw [real_inner_comm (x t - xstar) (g (x t))] at hi
    set η := (f (x t) - f xstar) / ‖g (x t)‖ ^ 2 with hη
    rw [e, norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have e2 : η ^ 2 * ‖g (x t)‖ ^ 2 = η * (f (x t) - f xstar) := by
      linear_combination η * hn
    nlinarith [mul_le_mul_of_nonneg_left hi hη0]
  -- bounded-gradient form
  have hS1 : ∀ t, ‖g (x t)‖ ≤ G → G ^ 2 * ‖x (t + 1) - xstar‖ ^ 2 ≤ G ^ 2 * ‖x t - xstar‖ ^ 2
      - (f (x t) - f xstar) * ((f (x t) - f xstar) + α * ‖x t - xstar‖ ^ 2) := by
    intro t hGt
    have hs := hstepgen t
    have hn := hηn t
    have hη0 : 0 ≤ (f (x t) - f xstar) / ‖g (x t)‖ ^ 2 := div_nonneg (hhz t) (sq_nonneg _)
    have hq : 0 ≤ (f (x t) - f xstar) + α * ‖x t - xstar‖ ^ 2 := by
      have := hhz t
      positivity
    have hGG : ‖g (x t)‖ ^ 2 ≤ G ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hGt 2
    set η := (f (x t) - f xstar) / ‖g (x t)‖ ^ 2 with hη
    have k1 : f (x t) - f xstar ≤ η * G ^ 2 := by
      calc f (x t) - f xstar = η * ‖g (x t)‖ ^ 2 := hn.symm
        _ ≤ η * G ^ 2 := mul_le_mul_of_nonneg_left hGG hη0
    have k2 := mul_le_mul_of_nonneg_right k1 hq
    nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg G)]
  -- smooth form
  have hS2 : ∀ t, 2 * β * ‖x (t + 1) - xstar‖ ^ 2
      ≤ 2 * β * ‖x t - xstar‖ ^ 2 - (f (x t) - f xstar) := by
    intro t
    have hs := hstepgen t
    have hn := hηn t
    have hη0 : 0 ≤ (f (x t) - f xstar) / ‖g (x t)‖ ^ 2 := div_nonneg (hhz t) (sq_nonneg _)
    have hgs := hgradsq (x t)
    set η := (f (x t) - f xstar) / ‖g (x t)‖ ^ 2 with hη
    have k1 : f (x t) - f xstar ≤ η * (2 * β * (f (x t) - f xstar)) := by
      calc f (x t) - f xstar = η * ‖g (x t)‖ ^ 2 := hn.symm
        _ ≤ η * (2 * β * (f (x t) - f xstar)) := mul_le_mul_of_nonneg_left hgs hη0
    have k3 : 0 ≤ η * (α * ‖x t - xstar‖ ^ 2) := mul_nonneg hη0 (by positivity)
    have k4 := mul_nonneg (by positivity : (0:ℝ) ≤ 2 * β) k3
    nlinarith [mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ) ≤ 2 * β)]
  -- the minimising iterate
  obtain ⟨t0, ht0, rfl, hmin0⟩ := hxbar
  have hmle : ∀ s ≤ T, f (x t0) - f xstar ≤ f (x s) - f xstar := fun s hs => by
    linarith [hmin0 s hs]
  have ha : ∀ t, 0 ≤ ‖x t - xstar‖ ^ 2 := fun t => sq_nonneg _
  -- `α² a₀ ≤ G²`
  have hd0 : α ^ 2 * ‖x 0 - xstar‖ ^ 2 ≤ G ^ 2 := by
    have h1 := hinner (x 0)
    have h2 := hqlow (x 0)
    have h3 : ⟪g (x 0), x 0 - xstar⟫_ℝ ≤ ‖g (x 0)‖ * ‖x 0 - xstar‖ := real_inner_le_norm _ _
    have h4 : ‖g (x 0)‖ * ‖x 0 - xstar‖ ≤ G * ‖x 0 - xstar‖ :=
      mul_le_mul_of_nonneg_right (hGbound 0 (Nat.zero_le _)) (norm_nonneg _)
    have h5 : α * ‖x 0 - xstar‖ ^ 2 ≤ G * ‖x 0 - xstar‖ := by linarith
    rcases eq_or_lt_of_le (norm_nonneg (x 0 - xstar)) with h6 | h6
    · rw [← h6]
      nlinarith [sq_nonneg G]
    · have h7 : α * ‖x 0 - xstar‖ ≤ G := by
        by_contra hcon
        have hcon' := not_le.1 hcon
        nlinarith
      nlinarith [mul_le_mul h7 h7 (by positivity) hG.le]
  refine le_min ?_ (le_min ?_ (le_min ?_ ?_))
  · exact ocp_b1 (fun t => ‖x t - xstar‖ ^ 2) (fun t => f (x t) - f xstar) G
      (f (x t0) - f xstar) ‖x 0 - xstar‖ T hT hG (norm_nonneg _) rfl ha (hhz t0) hmle
      (fun t ht => by
        have h1 := hS1 t (hGbound t ht.le)
        have h3 : 0 ≤ (f (x t) - f xstar) * (α * ‖x t - xstar‖ ^ 2) :=
          mul_nonneg (hhz t) (by positivity)
        show G ^ 2 * ‖x (t + 1) - xstar‖ ^ 2
          ≤ G ^ 2 * ‖x t - xstar‖ ^ 2 - (f (x t) - f xstar) ^ 2
        nlinarith)
  · exact ocp_b2 (fun t => ‖x t - xstar‖ ^ 2) (fun t => f (x t) - f xstar) β
      (f (x t0) - f xstar) ‖x 0 - xstar‖ T hT hβ rfl ha hmle hS2
  · exact ocp_b3 (fun t => ‖x t - xstar‖ ^ 2) (fun t => f (x t) - f xstar) α G
      (f (x t0) - f xstar) T hT hα hG ha (hhz t0) hmle (fun t => hqlow (x t))
      (fun t ht => hS1 t (hGbound t ht.le)) hd0
  · exact ocp_b4 (fun t => ‖x t - xstar‖ ^ 2) (fun t => f (x t) - f xstar) α β
      (f (x t0) - f xstar) ‖x 0 - xstar‖ T hα hβ rfl ha hmle (fun t => hqlow (x t))
      (fun t => hqup (x t)) hS2
