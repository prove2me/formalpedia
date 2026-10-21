-- Prove2me | solution 1 for OTCChain.Equilibrium.eq_84
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T21:59:49.936115+00:00
-- url     : https://prove2.me/submissions/c62331a9-7d37-47ed-b200-3a28cce3f7c2

import Mathlib
import Definitions.Def_OTCChain_Equilibrium_Model
import Definitions.Def_OTCChain_Equilibrium_ClosedForm

open Set MeasureTheory OTCChain.Equilibrium

namespace OTCAux

section A

variable (M : Params)

lemma f_ii (hM : M.Standing) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ M.Δbar) :
    IntervalIntegrable M.f volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  exact hM.2.2.2.2.2.2.2.2.2.2.1.mono_set (Icc_subset_Icc ha hb)

lemma F_sub (hM : M.Standing) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ M.Δbar) :
    M.F b - M.F a = ∫ x in a..b, M.f x := by
  unfold Params.F
  exact intervalIntegral.integral_interval_sub_left (f_ii M hM le_rfl (ha.trans hab) hb)
    (f_ii M hM le_rfl ha (hab.trans hb))

lemma F_zero : M.F 0 = 0 := by simp [Params.F]

lemma F_bar (hM : M.Standing) : M.F M.Δbar = 1 := hM.2.2.2.2.2.2.2.2.2.2.2

lemma F_mono (hM : M.Standing) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ M.Δbar) :
    M.F a ≤ M.F b := by
  have h := F_sub M hM ha hab hb
  have : 0 ≤ ∫ x in a..b, M.f x :=
    intervalIntegral.integral_nonneg hab (fun u hu =>
      hM.2.2.2.2.2.2.2.2.2.1 u ⟨ha.trans hu.1, hu.2.trans hb⟩)
  linarith

lemma F_nonneg (hM : M.Standing) {a : ℝ} (ha : 0 ≤ a) (hb : a ≤ M.Δbar) : 0 ≤ M.F a := by
  have := F_mono M hM le_rfl ha hb; rwa [F_zero] at this

lemma F_le_one (hM : M.Standing) {a : ℝ} (ha : 0 ≤ a) (hb : a ≤ M.Δbar) : M.F a ≤ 1 := by
  have := F_mono M hM ha hb le_rfl; rwa [F_bar M hM] at this

lemma F_cont (hM : M.Standing) : ContinuousOn M.F (Icc 0 M.Δbar) := by
  have hD : (0:ℝ) ≤ M.Δbar := hM.2.2.2.2.2.2.2.2.1.le
  have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (f := M.f) (a := 0)
    (b := M.Δbar) (by rw [uIcc_of_le hD]; exact hM.2.2.2.2.2.2.2.2.2.2.1)
  rw [uIcc_of_le hD] at this
  exact this

/-! ### The root functions -/

lemma NbOf_root (hM : M.Standing) {y : ℝ} (hy : y ≤ 1) :
    2 * NbOf M y - (M.N - M.N * y - M.X - M.κ / M.lam) =
      Real.sqrt ((M.N - M.N * y - M.X - M.κ / M.lam) ^ 2
        + 4 * (M.κ / M.lam) * (M.N - M.X) * (1 - y)) := by
  unfold NbOf; ring

lemma NbOf_q_nonneg (hM : M.Standing) {y : ℝ} (hy : y ≤ 1) :
    0 ≤ 4 * (M.κ / M.lam) * (M.N - M.X) * (1 - y) := by
  obtain ⟨hX, hXN, hlam, hκ, -⟩ := hM
  have : 0 ≤ 1 - y := by linarith
  have : 0 ≤ M.N - M.X := by linarith
  positivity

lemma NbOf_nonneg (hM : M.Standing) {y : ℝ} (hy : y ≤ 1) : 0 ≤ NbOf M y := by
  have hq := NbOf_q_nonneg M hM hy
  set a := M.N - M.N * y - M.X - M.κ / M.lam
  have h1 : |a| ≤ Real.sqrt (a ^ 2 + 4 * (M.κ / M.lam) * (M.N - M.X) * (1 - y)) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
  have h2 := neg_abs_le a
  unfold NbOf
  linarith

lemma NbOf_eq (hM : M.Standing) {y : ℝ} (hy : y ≤ 1) :
    NbOf M y ^ 2 + (M.κ / M.lam - M.N + M.X + M.N * y) * NbOf M y
      - M.κ / M.lam * (M.N - M.X) * (1 - y) = 0 := by
  have hq := NbOf_q_nonneg M hM hy
  have hr := NbOf_root M hM hy
  set a := M.N - M.N * y - M.X - M.κ / M.lam
  set s := Real.sqrt (a ^ 2 + 4 * (M.κ / M.lam) * (M.N - M.X) * (1 - y))
  have hs : s ^ 2 = a ^ 2 + 4 * (M.κ / M.lam) * (M.N - M.X) * (1 - y) :=
    Real.sq_sqrt (by nlinarith [sq_nonneg a])
  have : NbOf M y = (a + s) / 2 := by linarith
  rw [this]
  have ha : M.κ / M.lam - M.N + M.X + M.N * y = -a := by simp only [a]; ring
  rw [ha]
  nlinarith

lemma NbOf_anti (hM : M.Standing) {y1 y2 : ℝ} (h12 : y1 ≤ y2) (hy2 : y2 ≤ 1) :
    NbOf M y2 ≤ NbOf M y1 := by
  have hy1 : y1 ≤ 1 := h12.trans hy2
  have e1 := NbOf_eq M hM hy1
  have e2 := NbOf_eq M hM hy2
  have r1 := NbOf_root M hM hy1
  have s1 := Real.sqrt_nonneg ((M.N - M.N * y1 - M.X - M.κ / M.lam) ^ 2
        + 4 * (M.κ / M.lam) * (M.N - M.X) * (1 - y1))
  have n1 := NbOf_nonneg M hM hy1
  have n2 := NbOf_nonneg M hM hy2
  obtain ⟨hX, hXN, hlam, hκ, -⟩ := hM
  have hk : 0 < M.κ / M.lam := by positivity
  by_contra hcon
  push Not at hcon
  set t1 := NbOf M y1
  set t2 := NbOf M y2
  -- h(t2,y1) ≤ 0 but > 0
  have hA : t2 ^ 2 + (M.κ / M.lam - M.N + M.X + M.N * y1) * t2
      - M.κ / M.lam * (M.N - M.X) * (1 - y1) ≤ 0 := by
    have : 0 ≤ (y2 - y1) * (M.N * t2 + M.κ / M.lam * (M.N - M.X)) := by
      apply mul_nonneg (by linarith)
      have : 0 ≤ M.N - M.X := by linarith
      have hN : 0 ≤ M.N := by linarith
      nlinarith [mul_nonneg hN n2, mul_nonneg hk.le this]
    nlinarith
  have hB : 0 < (t2 - t1) * (t2 + t1 + (M.κ / M.lam - M.N + M.X + M.N * y1)) := by
    apply mul_pos (by linarith)
    nlinarith
  nlinarith

lemma NsOf_root (hM : M.Standing) (y : ℝ) :
    2 * NsOf M y + (M.κ / M.lam + M.N - M.X - M.N * y) =
      Real.sqrt ((M.κ / M.lam + M.N - M.X - M.N * y) ^ 2 + 4 * (M.κ * M.X / M.lam) * y) := by
  unfold NsOf; ring

lemma NsOf_q_nonneg (hM : M.Standing) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ 4 * (M.κ * M.X / M.lam) * y := by
  obtain ⟨hX, hXN, hlam, hκ, -⟩ := hM
  positivity

lemma NsOf_nonneg (hM : M.Standing) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ NsOf M y := by
  have hq := NsOf_q_nonneg M hM hy
  set a := M.κ / M.lam + M.N - M.X - M.N * y
  have h1 : |a| ≤ Real.sqrt (a ^ 2 + 4 * (M.κ * M.X / M.lam) * y) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
  have h2 := le_abs_self a
  unfold NsOf
  linarith

lemma NsOf_eq (hM : M.Standing) {y : ℝ} (hy : 0 ≤ y) :
    NsOf M y ^ 2 + (M.κ / M.lam + M.N - M.X - M.N * y) * NsOf M y
      - M.κ * M.X / M.lam * y = 0 := by
  have hq := NsOf_q_nonneg M hM hy
  have hr := NsOf_root M hM y
  set a := M.κ / M.lam + M.N - M.X - M.N * y
  set s := Real.sqrt (a ^ 2 + 4 * (M.κ * M.X / M.lam) * y)
  have hs : s ^ 2 = a ^ 2 + 4 * (M.κ * M.X / M.lam) * y := Real.sq_sqrt (by nlinarith [sq_nonneg a])
  have : NsOf M y = (s - a) / 2 := by linarith
  rw [this]
  nlinarith

lemma NsOf_mono (hM : M.Standing) {y1 y2 : ℝ} (hy1 : 0 ≤ y1) (h12 : y1 ≤ y2) :
    NsOf M y1 ≤ NsOf M y2 := by
  have hy2 : 0 ≤ y2 := hy1.trans h12
  have e1 := NsOf_eq M hM hy1
  have e2 := NsOf_eq M hM hy2
  have r2 := NsOf_root M hM y2
  have s2 := Real.sqrt_nonneg ((M.κ / M.lam + M.N - M.X - M.N * y2) ^ 2
    + 4 * (M.κ * M.X / M.lam) * y2)
  have n1 := NsOf_nonneg M hM hy1
  have n2 := NsOf_nonneg M hM hy2
  obtain ⟨hX, hXN, hlam, hκ, -⟩ := hM
  have hk : 0 < M.κ * M.X / M.lam := by positivity
  by_contra hcon
  push Not at hcon
  set s1 := NsOf M y1
  set t2 := NsOf M y2
  have hA : s1 ^ 2 + (M.κ / M.lam + M.N - M.X - M.N * y2) * s1
      - M.κ * M.X / M.lam * y2 ≤ 0 := by
    have : 0 ≤ (y2 - y1) * (M.N * s1 + M.κ * M.X / M.lam) := by
      apply mul_nonneg (by linarith)
      have : 0 ≤ M.N := by linarith
      positivity
    nlinarith
  have hB : 0 < (s1 - t2) * (s1 + t2 + (M.κ / M.lam + M.N - M.X - M.N * y2)) := by
    apply mul_pos (by linarith)
    nlinarith
  nlinarith

lemma NbOf_cont : Continuous (NbOf M) := by
  unfold NbOf; fun_prop

lemma NsOf_cont : Continuous (NsOf M) := by
  unfold NsOf; fun_prop

/-! ### The integrals `I(δ) = ∫₀^δ F` and `J(δ) = ∫_δ^∆̄ (1 - F)` -/

noncomputable def I (δ : ℝ) : ℝ := ∫ x in (0:ℝ)..δ, M.F x
noncomputable def J (δ : ℝ) : ℝ := ∫ x in δ..M.Δbar, (1 - M.F x)

lemma F_intOn (hM : M.Standing) : IntegrableOn M.F (Icc 0 M.Δbar) :=
  (F_cont M hM).integrableOn_Icc

lemma F_ii (hM : M.Standing) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ M.Δbar) :
    IntervalIntegrable M.F volume a b :=
  ((F_cont M hM).mono (Icc_subset_Icc ha hb)).intervalIntegrable_of_Icc hab

lemma I_cont (hM : M.Standing) : ContinuousOn (I M) (Icc 0 M.Δbar) := by
  have hD : (0:ℝ) ≤ M.Δbar := hM.2.2.2.2.2.2.2.2.1.le
  have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (f := M.F) (a := 0)
    (b := M.Δbar) (by rw [uIcc_of_le hD]; exact F_intOn M hM)
  rw [uIcc_of_le hD] at this
  exact this

lemma J_cont (hM : M.Standing) : ContinuousOn (J M) (Icc 0 M.Δbar) := by
  have hD : (0:ℝ) ≤ M.Δbar := hM.2.2.2.2.2.2.2.2.1.le
  have := intervalIntegral.continuousOn_primitive_interval_left (μ := volume)
    (f := fun x => 1 - M.F x) (a := 0) (b := M.Δbar)
    (by rw [uIcc_of_le hD]; exact (continuousOn_const.sub (F_cont M hM)).integrableOn_Icc)
  rw [uIcc_of_le hD] at this
  exact this

lemma I_sub (hM : M.Standing) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ M.Δbar) :
    I M b - I M a = ∫ x in a..b, M.F x := by
  unfold I
  exact intervalIntegral.integral_interval_sub_left (F_ii M hM le_rfl (ha.trans hab) hb)
    (F_ii M hM le_rfl ha (hab.trans hb))

lemma I_nonneg (hM : M.Standing) {a : ℝ} (ha : 0 ≤ a) (hb : a ≤ M.Δbar) : 0 ≤ I M a :=
  intervalIntegral.integral_nonneg ha (fun u hu => F_nonneg M hM hu.1 (hu.2.trans hb))

lemma I_zero : I M 0 = 0 := by simp [I]

/-- `I` is nondecreasing, and strictly so once positive. -/
lemma I_mono (hM : M.Standing) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ M.Δbar) :
    I M a ≤ I M b := by
  have := I_sub M hM ha hab hb
  have : 0 ≤ ∫ x in a..b, M.F x :=
    intervalIntegral.integral_nonneg hab (fun u hu => F_nonneg M hM (ha.trans hu.1) (hu.2.trans hb))
  linarith

lemma F_pos_of_I_pos (hM : M.Standing) {a : ℝ} (ha : 0 ≤ a) (hb : a ≤ M.Δbar) (h : 0 < I M a) :
    0 < M.F a := by
  by_contra hF
  push Not at hF
  have : I M a = 0 := by
    unfold I
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) (fun u hu => by
      rw [uIcc_of_le ha] at hu
      have h1 := F_mono M hM hu.1 hu.2 hb
      have h2 := F_nonneg M hM hu.1 (hu.2.trans hb)
      simp only; linarith)]
    simp
  linarith

lemma I_strict (hM : M.Standing) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ M.Δbar)
    (hpos : 0 < I M a) : I M a < I M b := by
  have hF := F_pos_of_I_pos M hM ha (hab.le.trans hb) hpos
  have := I_sub M hM ha hab.le hb
  have : (b - a) * M.F a ≤ ∫ x in a..b, M.F x := by
    have := intervalIntegral.integral_mono_on hab.le (intervalIntegrable_const)
      (F_ii M hM ha hab.le hb) (fun u hu => F_mono M hM ha hu.1 (hu.2.trans hb))
    simpa using this
  nlinarith

lemma J_sub (hM : M.Standing) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ M.Δbar) :
    J M a - J M b = ∫ x in a..b, (1 - M.F x) := by
  unfold J
  have hi : ∀ c d, 0 ≤ c → c ≤ d → d ≤ M.Δbar →
      IntervalIntegrable (fun x => 1 - M.F x) volume c d :=
    fun c d hc hcd hd => intervalIntegrable_const.sub (F_ii M hM hc hcd hd)
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi a b ha hab hb)
    (hi b M.Δbar (ha.trans hab) hb le_rfl)]
  ring

lemma one_sub_F_nonneg (hM : M.Standing) {a : ℝ} (ha : 0 ≤ a) (hb : a ≤ M.Δbar) :
    0 ≤ 1 - M.F a := by linarith [F_le_one M hM ha hb]

lemma J_nonneg (hM : M.Standing) {a : ℝ} (ha : 0 ≤ a) (hb : a ≤ M.Δbar) : 0 ≤ J M a :=
  intervalIntegral.integral_nonneg hb (fun u hu => one_sub_F_nonneg M hM (ha.trans hu.1) hu.2)

lemma J_bar : J M M.Δbar = 0 := by simp [J]

lemma J_anti (hM : M.Standing) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ M.Δbar) :
    J M b ≤ J M a := by
  have := J_sub M hM ha hab hb
  have : 0 ≤ ∫ x in a..b, (1 - M.F x) :=
    intervalIntegral.integral_nonneg hab
      (fun u hu => one_sub_F_nonneg M hM (ha.trans hu.1) (hu.2.trans hb))
  linarith

lemma F_lt_one_of_J_pos (hM : M.Standing) {b : ℝ} (ha : 0 ≤ b) (hb : b ≤ M.Δbar)
    (h : 0 < J M b) : M.F b < 1 := by
  by_contra hF
  push Not at hF
  have : J M b = 0 := by
    unfold J
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) (fun u hu => by
      rw [uIcc_of_le hb] at hu
      have h1 := F_mono M hM ha hu.1 hu.2
      have h2 := F_le_one M hM (ha.trans hu.1) hu.2
      simp only; linarith)]
    simp
  linarith

lemma J_strict (hM : M.Standing) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ M.Δbar)
    (hpos : 0 < J M b) : J M b < J M a := by
  have hF := F_lt_one_of_J_pos M hM (ha.trans hab.le) hb hpos
  have := J_sub M hM ha hab.le hb
  have : (b - a) * (1 - M.F b) ≤ ∫ x in a..b, (1 - M.F x) := by
    have := intervalIntegral.integral_mono_on hab.le (intervalIntegrable_const)
      (intervalIntegrable_const.sub (F_ii M hM ha hab.le hb))
      (fun u hu => by
        have := F_mono M hM (ha.trans hu.1) hu.2 hb
        show 1 - M.F b ≤ 1 - M.F u
        linarith)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  nlinarith

/-! ### The prefactors -/

noncomputable def P20 (δ : ℝ) : ℝ :=
  M.lam * M.κ * M.η * M.X /
      ((M.κ + M.r + M.lam * NbOf M (M.F δ) * (1 - M.η)) * (M.κ + M.lam * NbOf M (M.F δ)))

noncomputable def P21 (δ : ℝ) : ℝ :=
  M.lam * M.κ * (1 - M.η) * (M.N - M.X) /
      ((M.κ + M.r + M.lam * M.η * NsOf M (M.F δ)) * (M.κ + M.lam * NsOf M (M.F δ)))

lemma rhs20_eq (δ : ℝ) : rhs20 M δ = P20 M δ * I M δ := rfl
lemma rhs21_eq (δ : ℝ) : rhs21 M δ = P21 M δ * J M δ := rfl

lemma P20_pos (hM : M.Standing) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ M.Δbar) : 0 < P20 M δ := by
  have hn := NbOf_nonneg M hM (F_le_one M hM h0 h1)
  obtain ⟨hX, hXN, hlam, hκ, hr, hη, hη1, -⟩ := hM
  have : 0 < 1 - M.η := by linarith
  unfold P20; positivity

lemma P21_pos (hM : M.Standing) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ M.Δbar) : 0 < P21 M δ := by
  have hn := NsOf_nonneg M hM (F_nonneg M hM h0 h1)
  obtain ⟨hX, hXN, hlam, hκ, hr, hη, hη1, -⟩ := hM
  have : 0 < 1 - M.η := by linarith
  have : 0 < M.N - M.X := by linarith
  unfold P21; positivity

lemma P20_mono (hM : M.Standing) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ M.Δbar) :
    P20 M a ≤ P20 M b := by
  have hFa := F_le_one M hM ha (hab.trans hb)
  have hFb := F_le_one M hM (ha.trans hab) hb
  have hn := NbOf_anti M hM (F_mono M hM ha hab hb) hFb
  have na := NbOf_nonneg M hM hFa
  have nb := NbOf_nonneg M hM hFb
  obtain ⟨hX, hXN, hlam, hκ, hr, hη, hη1, -⟩ := hM
  have h1η : 0 < 1 - M.η := by linarith
  have k1 := mul_le_mul_of_nonneg_left hn (le_of_lt (mul_pos hlam h1η))
  have k2 := mul_le_mul_of_nonneg_left hn hlam.le
  unfold P20
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  apply mul_le_mul
  · nlinarith
  · nlinarith
  · positivity
  · positivity

lemma P21_anti (hM : M.Standing) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ M.Δbar) :
    P21 M b ≤ P21 M a := by
  have hFa := F_nonneg M hM ha (hab.trans hb)
  have hn := NsOf_mono M hM hFa (F_mono M hM ha hab hb)
  have na := NsOf_nonneg M hM hFa
  have nb := NsOf_nonneg M hM (F_nonneg M hM (ha.trans hab) hb)
  obtain ⟨hX, hXN, hlam, hκ, hr, hη, hη1, -⟩ := hM
  have h1η : 0 < 1 - M.η := by linarith
  have : 0 < M.N - M.X := by linarith
  have k1 := mul_le_mul_of_nonneg_left hn (le_of_lt (mul_pos hlam hη))
  have k2 := mul_le_mul_of_nonneg_left hn hlam.le
  have hK : 0 ≤ M.lam * M.κ * (1 - M.η) * (M.N - M.X) := by positivity
  have hd : 0 < (M.κ + M.r + M.lam * M.η * NsOf M (M.F a)) * (M.κ + M.lam * NsOf M (M.F a)) := by
    positivity
  unfold P21
  apply div_le_div_of_nonneg_left hK hd
  apply mul_le_mul
  · nlinarith
  · nlinarith
  · positivity
  · positivity

lemma P20_cont (hM : M.Standing) : ContinuousOn (P20 M) (Icc 0 M.Δbar) := by
  have hc : ContinuousOn (fun δ => NbOf M (M.F δ)) (Icc 0 M.Δbar) :=
    (NbOf_cont M).comp_continuousOn (F_cont M hM)
  unfold P20
  apply ContinuousOn.div continuousOn_const
  · exact ((continuousOn_const.add (continuousOn_const.mul hc |>.mul continuousOn_const)).mul
      (continuousOn_const.add (continuousOn_const.mul hc)))
  · intro δ hδ
    have hn := NbOf_nonneg M hM (F_le_one M hM hδ.1 hδ.2)
    obtain ⟨hX, hXN, hlam, hκ, hr, hη, hη1, -⟩ := hM
    have : 0 < 1 - M.η := by linarith
    positivity

lemma P21_cont (hM : M.Standing) : ContinuousOn (P21 M) (Icc 0 M.Δbar) := by
  have hc : ContinuousOn (fun δ => NsOf M (M.F δ)) (Icc 0 M.Δbar) :=
    (NsOf_cont M).comp_continuousOn (F_cont M hM)
  unfold P21
  apply ContinuousOn.div continuousOn_const
  · exact ((continuousOn_const.add (continuousOn_const.mul hc)).mul
      (continuousOn_const.add (continuousOn_const.mul hc)))
  · intro δ hδ
    have hn := NsOf_nonneg M hM (F_nonneg M hM hδ.1 hδ.2)
    obtain ⟨hX, hXN, hlam, hκ, hr, hη, hη1, -⟩ := hM
    positivity

lemma rhs20_cont (hM : M.Standing) : ContinuousOn (rhs20 M) (Icc 0 M.Δbar) :=
  (P20_cont M hM).mul (I_cont M hM)

lemma rhs21_cont (hM : M.Standing) : ContinuousOn (rhs21 M) (Icc 0 M.Δbar) :=
  (P21_cont M hM).mul (J_cont M hM)

lemma rhs20_nonneg (hM : M.Standing) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ M.Δbar) : 0 ≤ rhs20 M δ :=
  mul_nonneg (P20_pos M hM h0 h1).le (I_nonneg M hM h0 h1)

lemma rhs21_nonneg (hM : M.Standing) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ M.Δbar) : 0 ≤ rhs21 M δ :=
  mul_nonneg (P21_pos M hM h0 h1).le (J_nonneg M hM h0 h1)

lemma rhs20_zero : rhs20 M 0 = 0 := by rw [rhs20_eq, I_zero, mul_zero]
lemma rhs21_bar : rhs21 M M.Δbar = 0 := by rw [rhs21_eq, J_bar, mul_zero]

lemma rhs20_mono (hM : M.Standing) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ M.Δbar) :
    rhs20 M a ≤ rhs20 M b := by
  rw [rhs20_eq, rhs20_eq]
  exact mul_le_mul (P20_mono M hM ha hab hb) (I_mono M hM ha hab hb) (I_nonneg M hM ha (hab.trans hb))
    (P20_pos M hM (ha.trans hab) hb).le

lemma rhs21_anti (hM : M.Standing) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ M.Δbar) :
    rhs21 M b ≤ rhs21 M a := by
  rw [rhs21_eq, rhs21_eq]
  exact mul_le_mul (P21_anti M hM ha hab hb) (J_anti M hM ha hab hb)
    (J_nonneg M hM (ha.trans hab) hb) (P21_pos M hM ha (hab.trans hb)).le

lemma rhs20_strict (hM : M.Standing) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ M.Δbar)
    (hpos : 0 < rhs20 M a) : rhs20 M a < rhs20 M b := by
  have hPa := P20_pos M hM ha (hab.le.trans hb)
  have hIa : 0 < I M a := by
    rw [rhs20_eq] at hpos
    by_contra h; push Not at h; nlinarith [I_nonneg M hM ha (hab.le.trans hb)]
  have := I_strict M hM ha hab hb hIa
  have := P20_mono M hM ha hab.le hb
  rw [rhs20_eq, rhs20_eq]
  nlinarith

lemma rhs21_strict (hM : M.Standing) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ M.Δbar)
    (hpos : 0 < rhs21 M b) : rhs21 M b < rhs21 M a := by
  have hPb := P21_pos M hM (ha.trans hab.le) hb
  have hJb : 0 < J M b := by
    rw [rhs21_eq] at hpos
    by_contra h; push Not at h; nlinarith [J_nonneg M hM (ha.trans hab.le) hb]
  have := J_strict M hM ha hab hb hJb
  have := P21_anti M hM ha hab.le hb
  rw [rhs21_eq, rhs21_eq]
  nlinarith

/-- Unique solvability of `rhs20 δ = c` for `0 < c ≤ rhs20 ∆̄`. -/
lemma rhs20_unique (hM : M.Standing) (c : ℝ) (hc : 0 < c) (hcb : c ≤ rhs20 M M.Δbar) :
    ∃! δ, δ ∈ Icc 0 M.Δbar ∧ rhs20 M δ = c := by
  have hD : (0:ℝ) ≤ M.Δbar := hM.2.2.2.2.2.2.2.2.1.le
  obtain ⟨δ, hδ, hδc⟩ := intermediate_value_Icc hD (rhs20_cont M hM)
    ⟨by rw [rhs20_zero]; exact hc.le, hcb⟩
  refine ⟨δ, ⟨hδ, hδc⟩, fun δ' ⟨hδ', hδ'c⟩ => ?_⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := rhs20_strict M hM hδ'.1 h hδ.2 (by rw [hδ'c]; exact hc); linarith
  · have := rhs20_strict M hM hδ.1 h hδ'.2 (by rw [hδc]; exact hc); linarith

lemma rhs21_unique (hM : M.Standing) (c : ℝ) (hc : 0 < c) (hcb : c ≤ rhs21 M 0) :
    ∃! δ, δ ∈ Icc 0 M.Δbar ∧ rhs21 M δ = c := by
  have hD : (0:ℝ) ≤ M.Δbar := hM.2.2.2.2.2.2.2.2.1.le
  obtain ⟨δ, hδ, hδc⟩ := intermediate_value_Icc' hD (rhs21_cont M hM)
    ⟨by rw [rhs21_bar]; exact hc.le, hcb⟩
  refine ⟨δ, ⟨hδ, hδc⟩, fun δ' ⟨hδ', hδ'c⟩ => ?_⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := rhs21_strict M hM hδ'.1 h hδ.2 (by rw [hδc]; exact hc); linarith
  · have := rhs21_strict M hM hδ.1 h hδ'.2 (by rw [hδ'c]; exact hc); linarith

end A

end OTCAux

namespace OTCAux

variable (M : Params)

lemma I_pos (hM : M.Standing) {δ : ℝ} (h0 : 0 < δ) (h1 : δ ≤ M.Δbar) (hF : 0 < M.F δ) :
    0 < I M δ :=
  intervalIntegral.integral_pos h0 ((F_cont M hM).mono (Icc_subset_Icc le_rfl h1))
    (fun x hx => F_nonneg M hM hx.1.le (hx.2.trans h1)) ⟨δ, ⟨h0.le, le_rfl⟩, hF⟩

lemma J_pos (hM : M.Standing) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < M.Δbar) (hF : M.F δ < 1) :
    0 < J M δ :=
  intervalIntegral.integral_pos h1
    ((continuousOn_const.sub (F_cont M hM)).mono (Icc_subset_Icc h0 le_rfl))
    (fun x hx => one_sub_F_nonneg M hM (h0.trans hx.1.le) hx.2) ⟨δ, ⟨le_rfl, h1.le⟩, by linarith⟩

lemma not_both_zero (hM : M.Standing) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ M.Δbar) :
    0 < I M δ ∨ 0 < J M δ := by
  have hD : 0 < M.Δbar := hM.2.2.2.2.2.2.2.2.1
  rcases h0.lt_or_eq with h0' | h0'
  · rcases h1.lt_or_eq with h1' | h1'
    · rcases (F_nonneg M hM h0 h1).lt_or_eq with hF | hF
      · exact Or.inl (I_pos M hM h0' h1 hF)
      · exact Or.inr (J_pos M hM h0 h1' (by rw [← hF]; norm_num))
    · subst h1'; exact Or.inl (I_pos M hM h0' le_rfl (by rw [F_bar M hM]; norm_num))
  · subst h0'; exact Or.inr (J_pos M hM le_rfl hD (by rw [F_zero]; norm_num))

lemma rhs_not_both_zero (hM : M.Standing) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ M.Δbar) :
    0 < rhs20 M δ ∨ 0 < rhs21 M δ := by
  rcases not_both_zero M hM h0 h1 with h | h
  · exact Or.inl (by rw [rhs20_eq]; exact mul_pos (P20_pos M hM h0 h1) h)
  · exact Or.inr (by rw [rhs21_eq]; exact mul_pos (P21_pos M hM h0 h1) h)

def Sset : Set ℝ := {δ : ℝ | δ ∈ Icc 0 M.Δbar ∧ rhs21 M δ ≤ rhs20 M δ}

lemma Sset_closed (hM : M.Standing) : IsClosed (Sset M) := by
  have h := ContinuousOn.preimage_isClosed_of_isClosed ((rhs20_cont M hM).sub (rhs21_cont M hM))
    isClosed_Icc (isClosed_Ici (a := (0:ℝ)))
  convert h using 1
  ext δ
  simp only [Sset, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_Ici, Pi.sub_apply, sub_nonneg]

lemma Sset_bar (hM : M.Standing) : M.Δbar ∈ Sset M :=
  ⟨⟨hM.2.2.2.2.2.2.2.2.1.le, le_rfl⟩, by
    rw [rhs21_bar]; exact rhs20_nonneg M hM hM.2.2.2.2.2.2.2.2.1.le le_rfl⟩

lemma δStar_mem (hM : M.Standing) : δStar M ∈ Sset M :=
  (Sset_closed M hM).csInf_mem ⟨_, Sset_bar M hM⟩ ⟨0, fun _ h => h.1.1⟩

lemma δStar_le (hM : M.Standing) {δ : ℝ} (h : δ ∈ Sset M) : δStar M ≤ δ :=
  csInf_le ⟨0, fun _ h => h.1.1⟩ h

/-- The crossing package (84). -/
lemma crossing (hM : M.Standing) :
    δStar M ∈ Ioo 0 M.Δbar ∧ rhs20 M (δStar M) = rhs21 M (δStar M) ∧
    (∀ δ ∈ Icc 0 M.Δbar, rhs20 M δ = rhs21 M δ → δ = δStar M) ∧
    0 < cStar M ∧ cStar M ≤ rhs20 M M.Δbar ∧ cStar M ≤ rhs21 M 0 ∧
    ∀ c δb δs : ℝ, 0 < c → δb ∈ Icc 0 M.Δbar → rhs20 M δb = c →
      δs ∈ Icc 0 M.Δbar → rhs21 M δs = c → (δb < δs ↔ c < cStar M) := by
  have hD : 0 < M.Δbar := hM.2.2.2.2.2.2.2.2.1
  obtain ⟨⟨hd0, hd1⟩, hdS⟩ := δStar_mem M hM
  set d := δStar M with hd
  have below : ∀ δ, 0 ≤ δ → δ < d → rhs20 M δ < rhs21 M δ := by
    intro δ h0 hδ
    by_contra h; push Not at h
    have := δStar_le M hM ⟨⟨h0, by linarith⟩, h⟩
    linarith
  have hdpos : 0 < d := by
    rcases hd0.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at hdS
      rw [rhs20_zero] at hdS
      rcases rhs_not_both_zero M hM le_rfl hD.le with h' | h'
      · rw [rhs20_zero] at h'; linarith
      · linarith
  have heq : rhs20 M d = rhs21 M d := by
    refine le_antisymm ?_ hdS
    -- closure argument
    have hT : IsClosed (Icc 0 d ∩ (fun δ => rhs21 M δ - rhs20 M δ) ⁻¹' Ici 0) :=
      ContinuousOn.preimage_isClosed_of_isClosed
        (((rhs21_cont M hM).sub (rhs20_cont M hM)).mono (Icc_subset_Icc le_rfl hd1))
        isClosed_Icc isClosed_Ici
    have hsub : Ico 0 d ⊆ Icc 0 d ∩ (fun δ => rhs21 M δ - rhs20 M δ) ⁻¹' Ici 0 := by
      intro δ hδ
      exact ⟨Ico_subset_Icc_self hδ, by
        simp only [mem_preimage, mem_Ici, sub_nonneg]; exact (below δ hδ.1 hδ.2).le⟩
    have hmem : d ∈ closure (Ico 0 d) := by
      rw [closure_Ico hdpos.ne]; exact ⟨hdpos.le, le_rfl⟩
    have := (hT.closure_subset_iff.2 hsub) hmem
    simp only [mem_inter_iff, mem_preimage, mem_Ici, sub_nonneg] at this
    exact this.2
  have hcpos : 0 < cStar M := by
    show 0 < rhs20 M d
    rcases rhs_not_both_zero M hM hd0 hd1 with h | h
    · exact h
    · rw [heq]; exact h
  have hdlt : d < M.Δbar := by
    rcases hd1.lt_or_eq with h | h
    · exact h
    · exfalso
      have : rhs21 M d = 0 := by rw [h, rhs21_bar]
      have : cStar M = 0 := by show rhs20 M d = 0; rw [heq]; exact this
      linarith
  have hc20 : cStar M = rhs20 M d := rfl
  have hc21 : cStar M = rhs21 M d := by rw [hc20, heq]
  refine ⟨⟨hdpos, hdlt⟩, heq, ?_, hcpos, ?_, ?_, ?_⟩
  · intro δ hδ he
    have hle := δStar_le M hM ⟨hδ, he.symm.le⟩
    by_contra hne
    have hlt : d < δ := lt_of_le_of_ne hle (Ne.symm hne)
    have a1 := rhs20_mono M hM hd0 hlt.le hδ.2
    have a2 := rhs21_anti M hM hd0 hlt.le hδ.2
    have hv : rhs20 M d = rhs20 M δ := by linarith
    have := rhs20_strict M hM hd0 hlt hδ.2 (by rw [← hc20]; exact hcpos)
    linarith
  · rw [hc20]; exact rhs20_mono M hM hd0 hd1 le_rfl
  · rw [hc21]; exact rhs21_anti M hM le_rfl hd0 hd1
  · intro c δb δs hc hb hbc hs hsc
    constructor
    · intro hlt
      by_contra hge; push Not at hge
      have h1 : d ≤ δb := by
        by_contra h; push Not at h
        have := rhs20_strict M hM hb.1 h hd1 (by rw [hbc]; exact hc)
        rw [hbc, ← hc20] at this; linarith
      have h2 : δs ≤ d := by
        by_contra h; push Not at h
        have := rhs21_strict M hM hd0 h hs.2 (by rw [hsc]; exact hc)
        rw [hsc, ← hc21] at this; linarith
      linarith
    · intro hlt
      have h1 : δb < d := by
        by_contra h; push Not at h
        have := rhs20_mono M hM hd0 h hb.2
        rw [hbc, ← hc20] at this; linarith
      have h2 : d < δs := by
        by_contra h; push Not at h
        have := rhs21_anti M hM hs.1 h hd1
        rw [hsc, ← hc21] at this; linarith
      linarith

end OTCAux


open Set OTCChain.Equilibrium

theorem solution (M : Params) (hM : M.Standing) :
    δStar M ∈ Ioo 0 M.Δbar ∧ rhs20 M (δStar M) = rhs21 M (δStar M) ∧
    (∀ δ ∈ Icc 0 M.Δbar, rhs20 M δ = rhs21 M δ → δ = δStar M) ∧
    0 < cStar M ∧ cStar M ≤ rhs20 M M.Δbar ∧ cStar M ≤ rhs21 M 0 ∧
    ∀ c δb δs : ℝ, 0 < c → δb ∈ Icc 0 M.Δbar → rhs20 M δb = c →
      δs ∈ Icc 0 M.Δbar → rhs21 M δs = c → (δb < δs ↔ c < cStar M) :=
  OTCAux.crossing M hM
