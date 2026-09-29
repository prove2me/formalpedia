-- Prove2me | solution 1 for Rudin.ch07_uniform_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T21:32:48.474631+00:00
-- url     : https://prove2.me/submissions/6933bee4-2123-45b1-a734-0c221a0ea390

import Mathlib

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace RudinLoc717

open Filter Topology

/-! ### Extending a family beyond `[a, b]` by its tangent lines at the endpoints -/

section
variable (a b : ℝ)

/-- The retraction of `ℝ` onto `[a, b]`. -/
noncomputable def proj (y : ℝ) : ℝ := max a (min b y)

variable {a b}

theorem proj_mem (hab : a ≤ b) (y : ℝ) : proj a b y ∈ Set.Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_left b y)⟩

theorem proj_eq_self {y : ℝ} (hy : y ∈ Set.Icc a b) : proj a b y = y := by
  rw [proj, min_eq_right hy.2, max_eq_right hy.1]

theorem proj_eq_left (hab : a ≤ b) {y : ℝ} (hy : y ≤ a) : proj a b y = a := by
  rw [proj, min_eq_right (hy.trans hab), max_eq_left hy]

theorem proj_eq_right (hab : a ≤ b) {y : ℝ} (hy : b ≤ y) : proj a b y = b := by
  rw [proj, min_eq_left hy, max_eq_right hab]

end

/-! ### Rudin, Theorem 7.17 -/

theorem rudin_7_17 (a b : ℝ) (hab : a < b) (f : ℕ → ℝ → ℝ) (f' : ℕ → ℝ → ℝ)
    (hdiff : ∀ n, ∀ x ∈ Set.Icc a b, HasDerivAt (f n) (f' n x) x)
    (x₀ : ℝ) (hx₀ : x₀ ∈ Set.Icc a b) (hconv : ∃ c : ℝ, Tendsto (fun n => f n x₀) atTop (𝓝 c))
    (h' : ∃ h : ℝ → ℝ, TendstoUniformlyOn f' h atTop (Set.Icc a b)) :
    ∃ g : ℝ → ℝ, ∃ h : ℝ → ℝ,
      TendstoUniformlyOn f g atTop (Set.Icc a b) ∧
      TendstoUniformlyOn f' h atTop (Set.Icc a b) ∧
      ∀ x ∈ Set.Icc a b, HasDerivAt g (h x) x := by
  obtain ⟨h₀, hh₀⟩ := h'
  obtain ⟨c₀, hc₀⟩ := hconv
  set p : ℝ → ℝ := proj a b with hpdef
  have hpmem : ∀ y, p y ∈ Set.Icc a b := proj_mem hab.le
  have hpid : ∀ y ∈ Set.Icc a b, p y = y := fun y hy => proj_eq_self hy
  have hpl : ∀ y ≤ a, p y = a := fun y hy => proj_eq_left hab.le hy
  have hpr : ∀ y, b ≤ y → p y = b := fun y hy => proj_eq_right hab.le hy
  set Fn : ℕ → ℝ → ℝ := fun n y => f n (p y) + f' n (p y) * (y - p y) with hFn
  set Fd : ℕ → ℝ → ℝ := fun n y => f' n (p y) with hFd
  set H : ℝ → ℝ := fun y => h₀ (p y) with hH
  -- `Fn` agrees with `f` on `[a, b]`, and is affine outside
  have hmid : ∀ n, ∀ y ∈ Set.Icc a b, Fn n y = f n y := by
    intro n y hy; rw [hFn]; simp [hpid y hy]
  have haffl : ∀ n, ∀ y ≤ a, Fn n y = f n a + f' n a * (y - a) := by
    intro n y hy; rw [hFn]; simp [hpl y hy]
  have haffr : ∀ n, ∀ y, b ≤ y → Fn n y = f n b + f' n b * (y - b) := by
    intro n y hy; rw [hFn]; simp [hpr y hy]
  have haffderiv : ∀ u v w z : ℝ, HasDerivAt (fun t => u + v * (t - w)) v z := by
    intro u v w z
    simpa using (((hasDerivAt_id z).sub_const w).const_mul v).const_add u
  -- the extended family is differentiable on all of `ℝ`
  have hFnderiv : ∀ n y, HasDerivAt (Fn n) (Fd n y) y := by
    intro n y
    have haend : a ∈ Set.Icc a b := ⟨le_rfl, hab.le⟩
    have hbend : b ∈ Set.Icc a b := ⟨hab.le, le_rfl⟩
    rcases lt_trichotomy y a with hy | hy | hy
    · have hd : Fd n y = f' n a := by rw [hFd]; simp [hpl y hy.le]
      rw [hd]
      refine (haffderiv (f n a) (f' n a) a y).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds hy] with z hz
      exact haffl n z (le_of_lt hz)
    · subst hy
      have hd : Fd n y = f' n y := by rw [hFd]; simp [hpid y haend]
      rw [hd]
      have hleft : HasDerivWithinAt (Fn n) (f' n y) (Set.Iic y) y := by
        refine ((haffderiv (f n y) (f' n y) y y).hasDerivWithinAt).congr
          (fun z hz => haffl n z hz) (haffl n y le_rfl)
      have hright : HasDerivWithinAt (Fn n) (f' n y) (Set.Ici y) y := by
        refine ((hdiff n y haend).hasDerivWithinAt).congr_of_eventuallyEq ?_ (hmid n y haend)
        filter_upwards [self_mem_nhdsWithin,
          mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hab)] with z hz1 hz2
        exact hmid n z ⟨hz1, le_of_lt hz2⟩
      have hu := hleft.union hright
      rwa [Set.Iic_union_Ici, hasDerivWithinAt_univ] at hu
    · rcases lt_trichotomy y b with hy2 | hy2 | hy2
      · have hmem : y ∈ Set.Icc a b := ⟨hy.le, hy2.le⟩
        have hd : Fd n y = f' n y := by rw [hFd]; simp [hpid y hmem]
        rw [hd]
        refine (hdiff n y hmem).congr_of_eventuallyEq ?_
        filter_upwards [Ioo_mem_nhds hy hy2] with z hz
        exact hmid n z ⟨hz.1.le, hz.2.le⟩
      · subst hy2
        have hd : Fd n y = f' n y := by rw [hFd]; simp [hpid y hbend]
        rw [hd]
        have hright : HasDerivWithinAt (Fn n) (f' n y) (Set.Ici y) y := by
          refine ((haffderiv (f n y) (f' n y) y y).hasDerivWithinAt).congr
            (fun z hz => haffr n z hz) (haffr n y le_rfl)
        have hleft : HasDerivWithinAt (Fn n) (f' n y) (Set.Iic y) y := by
          refine ((hdiff n y hbend).hasDerivWithinAt).congr_of_eventuallyEq ?_ (hmid n y hbend)
          filter_upwards [self_mem_nhdsWithin,
            mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hab)] with z hz1 hz2
          exact hmid n z ⟨le_of_lt hz2, hz1⟩
        have hu := hleft.union hright
        rwa [Set.Iic_union_Ici, hasDerivWithinAt_univ] at hu
      · have hd : Fd n y = f' n b := by rw [hFd]; simp [hpr y hy2.le]
        rw [hd]
        refine (haffderiv (f n b) (f' n b) b y).congr_of_eventuallyEq ?_
        filter_upwards [Ioi_mem_nhds hy2] with z hz
        exact haffr n z (le_of_lt hz)
  -- a ball containing `[a, b]`
  set r : ℝ := b - a + 1 with hr
  have hball : Set.Icc a b ⊆ Metric.ball x₀ r := by
    intro y hy
    rw [Metric.mem_ball, Real.dist_eq, abs_lt, hr]
    obtain ⟨hy1, hy2⟩ := hy
    obtain ⟨hz1, hz2⟩ := hx₀
    constructor <;> linarith
  -- the derivatives converge uniformly on the ball
  have hFdunif : TendstoUniformlyOn Fd H atTop (Metric.ball x₀ r) := by
    rw [Metric.tendstoUniformlyOn_iff] at hh₀ ⊢
    intro ε hε
    filter_upwards [hh₀ ε hε] with n hn y _
    exact hn (p y) (hpmem y)
  -- hence the functions themselves are uniformly Cauchy on the ball
  have hUC : UniformCauchySeqOn Fn atTop (Metric.ball x₀ r) := by
    refine uniformCauchySeqOn_ball_of_deriv hFdunif.uniformCauchySeqOn
      (fun n y _ => hFnderiv n y) ?_
    have : (fun n => Fn n x₀) = fun n => f n x₀ := by
      funext n; exact hmid n x₀ hx₀
    rw [this]
    exact hc₀.cauchy_map
  have hex : ∀ y : ℝ, ∃ c : ℝ, y ∈ Metric.ball x₀ r → Tendsto (fun n => Fn n y) atTop (𝓝 c) := by
    intro y
    by_cases hy : y ∈ Metric.ball x₀ r
    · have hcs : CauchySeq (fun n => Fn n y) := by
        rw [Metric.cauchySeq_iff]
        intro ε hε
        obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.1 hUC ε hε
        exact ⟨N, fun m hm n hn => hN m hm n hn y hy⟩
      obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete hcs
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun hc => absurd hc hy⟩
  choose G hG using hex
  have hGunif : TendstoUniformlyOn Fn G atTop (Metric.ball x₀ r) :=
    hUC.tendstoUniformlyOn_of_tendsto fun y hy => hG y hy
  refine ⟨G, H, ?_, ?_, ?_⟩
  · refine (hGunif.mono hball).congr ?_
    filter_upwards with n y hy
    exact hmid n y hy
  · refine TendstoUniformlyOn.congr_right hh₀ ?_
    intro y hy
    rw [hH]
    simp [hpid y hy]
  · intro x hx
    exact hasDerivAt_of_tendstoUniformlyOn Metric.isOpen_ball hFdunif
      (Eventually.of_forall fun n y _ => hFnderiv n y) (fun y hy => hG y hy) (hball hx)

end RudinLoc717

open Filter Topology in
theorem solution (a b : ℝ) (hab : a < b) (f : ℕ → ℝ → ℝ) (f' : ℕ → ℝ → ℝ)
    (hdiff : ∀ n, ∀ x ∈ Set.Icc a b, HasDerivAt (f n) (f' n x) x)
    (x₀ : ℝ) (hx₀ : x₀ ∈ Set.Icc a b) (hconv : ∃ c : ℝ, Tendsto (fun n => f n x₀) atTop (𝓝 c))
    (h' : ∃ h : ℝ → ℝ, TendstoUniformlyOn f' h atTop (Set.Icc a b)) :
    ∃ g : ℝ → ℝ, ∃ h : ℝ → ℝ,
      TendstoUniformlyOn f g atTop (Set.Icc a b) ∧
      TendstoUniformlyOn f' h atTop (Set.Icc a b) ∧
      ∀ x ∈ Set.Icc a b, HasDerivAt g (h x) x :=
  RudinLoc717.rudin_7_17 a b hab f f' hdiff x₀ hx₀ hconv h'
