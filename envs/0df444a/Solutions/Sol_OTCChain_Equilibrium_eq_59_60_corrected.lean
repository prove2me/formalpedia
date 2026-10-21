-- Prove2me | solution 1 for OTCChain.Equilibrium.eq_59_60_corrected
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T22:36:57.952052+00:00
-- url     : https://prove2.me/submissions/066e8e47-1d3b-4aa2-a52b-ef6caebe4b23

import Mathlib
import Definitions.Def_OTCChain_Equilibrium_Model
import Definitions.Def_OTCChain_Equilibrium_ClosedForm
import Theorems.Thm_OTCChain_Equilibrium_eq_55_57
import Theorems.Thm_OTCChain_Equilibrium_eq_61_63
import Theorems.Thm_OTCChain_Equilibrium_eq_64_Ns
import Theorems.Thm_OTCChain_Equilibrium_eq_65_66_Nb

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

namespace OTCAux

variable (M : Params)

lemma F_ae_deriv (hM : M.Standing) {b : ℝ} (hb0 : 0 ≤ b) (hb : b ≤ M.Δbar) :
    ∀ᵐ x, x ∈ uIcc 0 b → HasDerivAt M.F (M.f x) x := by
  filter_upwards [(f_ii M hM le_rfl hb0 hb).ae_hasDerivAt_integral] with x hx hxm
  exact hx hxm 0 left_mem_uIcc

lemma F_ac (hM : M.Standing) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ M.Δbar) :
    AbsolutelyContinuousOnInterval M.F a b := by
  have h := (f_ii M hM le_rfl (ha.trans hab) hb).absolutelyContinuousOnInterval_intervalIntegral
    (c := 0) left_mem_uIcc
  exact h.mono (by rw [uIcc_of_le hab, uIcc_of_le (ha.trans hab)]; exact Icc_subset_Icc ha le_rfl)

/-- Integration by parts against `dF = f dx` for an affine weight. -/
lemma int_affine_mul_f (hM : M.Standing) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ M.Δbar)
    (p q : ℝ) :
    ∫ x in a..b, (p + q * x) * M.f x
      = (p + q * b) * M.F b - (p + q * a) * M.F a - q * ∫ x in a..b, M.F x := by
  have hu : AbsolutelyContinuousOnInterval (fun x => p + q * x) a b :=
    ContDiffOn.absolutelyContinuousOnInterval (by fun_prop)
  have key := hu.integral_mul_deriv_eq_deriv_mul (F_ac M hM ha hab hb)
  have hdu : ∀ x, deriv (fun x => p + q * x) x = q := by
    intro x
    have : HasDerivAt (fun x => p + q * x) q x := by
      simpa using ((hasDerivAt_id x).const_mul q).const_add p
    exact this.deriv
  simp only [hdu] at key
  rw [intervalIntegral.integral_const_mul] at key
  rw [← key]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [F_ae_deriv M hM (ha.trans hab) hb] with x hx hxm
  have hx' : x ∈ uIcc 0 b := by
    rw [uIoc_of_le hab] at hxm
    rw [uIcc_of_le (ha.trans hab)]
    exact ⟨ha.trans hxm.1.le, hxm.2⟩
  rw [(hx hx').deriv]

lemma int_lin_low (hM : M.Standing) {a : ℝ} (ha : 0 ≤ a) (hb : a ≤ M.Δbar) :
    ∫ x in (0:ℝ)..a, (a - x) * M.f x = I M a := by
  have := int_affine_mul_f M hM le_rfl ha hb a (-1)
  simp only [F_zero, mul_zero, sub_zero] at this
  unfold I
  rw [show (fun x => (a - x) * M.f x) = fun x => (a + -1 * x) * M.f x by ext; ring, this]
  ring

lemma int_lin_high (hM : M.Standing) {a : ℝ} (ha : 0 ≤ a) (hb : a ≤ M.Δbar) :
    ∫ x in a..M.Δbar, (x - a) * M.f x = J M a := by
  have := int_affine_mul_f M hM ha hb le_rfl (-a) 1
  rw [F_bar M hM] at this
  unfold J
  rw [show (fun x => (x - a) * M.f x) = fun x => (-a + 1 * x) * M.f x by ext; ring, this,
    intervalIntegral.integral_sub intervalIntegrable_const (F_ii M hM ha hb le_rfl)]
  simp
  ring

end OTCAux


open Set MeasureTheory OTCChain.Equilibrium Filter Topology

namespace OTCAux

section E

variable (M : Params)

noncomputable def Ay (y : ℝ) : ℝ := M.N - M.N * y - M.X - M.κ / M.lam
noncomputable def qy (y : ℝ) : ℝ := 4 * (M.κ / M.lam) * (M.N - M.X) * (1 - y)
noncomputable def Ry (y : ℝ) : ℝ := Real.sqrt (Ay M y ^ 2 + qy M y)
noncomputable def kk : ℝ := 2 * M.κ * (M.N - M.X) / (M.lam * M.N)
noncomputable def dNb (y : ℝ) : ℝ := -(M.N / 2 * (1 + (Ay M y + kk M) / Ry M y))

lemma NbOf_eq_AR (y : ℝ) : NbOf M y = Ay M y / 2 + Ry M y / 2 := by
  unfold NbOf Ry qy; unfold Ay; ring

lemma arg_pos (hM : M.Standing) {y : ℝ} (hy : y ≤ 1) : 0 < Ay M y ^ 2 + qy M y := by
  obtain ⟨hX, hXN, hlam, hκ, -⟩ := hM
  rcases hy.lt_or_eq with h | h
  · have : 0 < qy M y := by
      unfold qy
      have : 0 < 1 - y := by linarith
      have : 0 < M.N - M.X := by linarith
      positivity
    nlinarith [sq_nonneg (Ay M y)]
  · subst h
    have : Ay M 1 = -(M.X + M.κ / M.lam) := by unfold Ay; ring
    have hk : 0 < M.κ / M.lam := by positivity
    have : qy M 1 = 0 := by unfold qy; ring
    rw [‹Ay M 1 = _›, this]
    nlinarith

lemma Ry_pos (hM : M.Standing) {y : ℝ} (hy : y ≤ 1) : 0 < Ry M y :=
  Real.sqrt_pos.2 (arg_pos M hM hy)

lemma Ry_sq (hM : M.Standing) {y : ℝ} (hy : y ≤ 1) : Ry M y ^ 2 = Ay M y ^ 2 + qy M y :=
  Real.sq_sqrt (arg_pos M hM hy).le

/-- `|A + k| ≤ R`, so that the middle densities lie in `[0, N f]`. -/
lemma Ak_le_R (hM : M.Standing) {y : ℝ} (hy : y ≤ 1) : |Ay M y + kk M| ≤ Ry M y := by
  have hR := Ry_pos M hM hy
  rw [← abs_of_pos hR, ← sq_le_sq, Ry_sq M hM hy]
  obtain ⟨hX, hXN, hlam, hκ, -⟩ := hM
  have hN : 0 < M.N := by linarith
  unfold Ay qy kk
  have e : (M.N - M.N * y - M.X - M.κ / M.lam + 2 * M.κ * (M.N - M.X) / (M.lam * M.N)) ^ 2
      = (M.N - M.N * y - M.X - M.κ / M.lam) ^ 2 + 4 * (M.κ / M.lam) * (M.N - M.X) * (1 - y)
        - 4 * (M.κ / M.lam) * (M.N - M.X) * (M.X + M.κ * M.X / (M.lam * M.N)) / M.N := by
    field_simp; ring
  rw [e]
  have : 0 ≤ 4 * (M.κ / M.lam) * (M.N - M.X) * (M.X + M.κ * M.X / (M.lam * M.N)) / M.N := by
    have : 0 < M.N - M.X := by linarith
    positivity
  linarith

lemma hasDerivAt_NbOf (hM : M.Standing) {y : ℝ} (hy : y ≤ 1) :
    HasDerivAt (NbOf M) (dNb M y) y := by
  have hN : M.N ≠ 0 := by linarith [hM.1, hM.2.1]
  have hlam : M.lam ≠ 0 := hM.2.2.1.ne'
  have hpos := arg_pos M hM hy
  have hA : HasDerivAt (Ay M) (-M.N) y := by
    unfold Ay
    have := ((((hasDerivAt_id y).const_mul M.N).const_sub M.N).sub_const M.X).sub_const (M.κ / M.lam)
    simpa using this
  have hq : HasDerivAt (qy M) (-(4 * (M.κ / M.lam) * (M.N - M.X))) y := by
    unfold qy
    have := ((hasDerivAt_id y).const_sub 1).const_mul (4 * (M.κ / M.lam) * (M.N - M.X))
    simpa using this
  have hin : HasDerivAt (fun y => Ay M y ^ 2 + qy M y)
      (2 * Ay M y * (-M.N) - 4 * (M.κ / M.lam) * (M.N - M.X)) y := by
    refine ((hA.pow 2).add hq).congr_deriv ?_
    simp only [Nat.cast_ofNat]
    ring
  have hR : HasDerivAt (Ry M) ((2 * Ay M y * (-M.N) - 4 * (M.κ / M.lam) * (M.N - M.X))
      / (2 * Real.sqrt (Ay M y ^ 2 + qy M y))) y := hin.sqrt hpos.ne'
  have hfun : NbOf M = fun y => Ay M y / 2 + Ry M y / 2 := funext (NbOf_eq_AR M)
  rw [hfun]
  refine ((hA.div_const 2).add (hR.div_const 2)).congr_deriv ?_
  have hRp := Ry_pos M hM hy
  unfold dNb kk
  rw [show Real.sqrt (Ay M y ^ 2 + qy M y) = Ry M y from rfl]
  field_simp
  ring

lemma dNb_abs_le (hM : M.Standing) {y : ℝ} (hy : y ≤ 1) : |dNb M y| ≤ M.N := by
  have h := Ak_le_R M hM hy
  have hR := Ry_pos M hM hy
  have hN : 0 < M.N := by linarith [hM.1, hM.2.1]
  have h1 : |(Ay M y + kk M) / Ry M y| ≤ 1 := by
    rw [abs_div, abs_of_pos hR, div_le_one hR]; exact h
  rw [abs_le] at h1
  unfold dNb
  rw [abs_le]
  constructor <;> nlinarith

lemma NbOf_lip (hM : M.Standing) {y y' : ℝ} (hy : y ∈ Icc (0:ℝ) 1) (hy' : y' ∈ Icc (0:ℝ) 1) :
    |NbOf M y - NbOf M y'| ≤ M.N * |y - y'| := by
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := NbOf M) (f' := dNb M) (C := M.N)
    (s := Icc 0 1) (fun x hx => (hasDerivAt_NbOf M hM hx.2).hasDerivWithinAt)
    (fun x hx => by rw [Real.norm_eq_abs]; exact dNb_abs_le M hM hx.2) (convex_Icc 0 1) hy' hy
  simpa [Real.norm_eq_abs] using this

lemma ac_comp_lip {f g : ℝ → ℝ} {a b K : ℝ} (hK : 0 ≤ K) (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : ∀ x ∈ uIcc a b, ∀ y ∈ uIcc a b, |g (f x) - g (f y)| ≤ K * |f x - f y|) :
    AbsolutelyContinuousOnInterval (fun x => g (f x)) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hf (ε / (K + 1)) (by positivity)
  refine ⟨δ, hδ, fun E hE hs => ?_⟩
  have h1 := h E hE hs
  calc ∑ i ∈ Finset.range E.1, dist (g (f (E.2 i).1)) (g (f (E.2 i).2))
      ≤ ∑ i ∈ Finset.range E.1, K * dist (f (E.2 i).1) (f (E.2 i).2) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Real.dist_eq, Real.dist_eq]
        exact hg _ (hE.1 i hi).1 _ (hE.1 i hi).2
    _ = K * ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) := by rw [Finset.mul_sum]
    _ ≤ K * (ε / (K + 1)) := by gcongr
    _ < ε := by
        rw [mul_div_assoc']
        rw [div_lt_iff₀ (by linarith)]
        nlinarith

/-- Change of variables: `∫_a^b (−N_b'(F x)) f(x) dx = N_b(F a) − N_b(F b)`. -/
lemma int_dNb (hM : M.Standing) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ M.Δbar) :
    ∫ x in a..b, dNb M (M.F x) * M.f x = NbOf M (M.F b) - NbOf M (M.F a) := by
  have hFI : ∀ x ∈ uIcc a b, M.F x ∈ Icc (0:ℝ) 1 := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact ⟨F_nonneg M hM (ha.trans hx.1) (hx.2.trans hb), F_le_one M hM (ha.trans hx.1) (hx.2.trans hb)⟩
  have hac : AbsolutelyContinuousOnInterval (fun x => NbOf M (M.F x)) a b :=
    ac_comp_lip (le_of_lt (by linarith [hM.1, hM.2.1])) (F_ac M hM ha hab hb)
      (fun x hx y hy => NbOf_lip M hM (hFI x hx) (hFI y hy))
  rw [← hac.integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [F_ae_deriv M hM (ha.trans hab) hb] with x hx hxm
  have hx' : x ∈ uIcc 0 b := by
    rw [uIoc_of_le hab] at hxm
    rw [uIcc_of_le (ha.trans hab)]
    exact ⟨ha.trans hxm.1.le, hxm.2⟩
  have hxI : x ∈ uIcc a b := uIoc_subset_uIcc hxm
  have := (hasDerivAt_NbOf M hM (hFI x hxI).2).comp x (hx hx')
  exact this.deriv.symm

end E

end OTCAux


open Set MeasureTheory OTCChain.Equilibrium Filter Topology

namespace OTCAux

section F

variable {M : Params} {Δb Δs : ℝ} {μ : Densities}

lemma root_eq_NbOf (hM : M.Standing) {y t : ℝ} (hy : y ≤ 1) (ht : 0 ≤ t)
    (heq : t ^ 2 - Ay M y * t - M.κ / M.lam * (M.N - M.X) * (1 - y) = 0) : t = NbOf M y := by
  obtain ⟨hX, hXN, hlam, hκ, -⟩ := hM
  have hq : 0 ≤ M.κ / M.lam * (M.N - M.X) * (1 - y) := by
    have : 0 ≤ 1 - y := by linarith
    have : 0 ≤ M.N - M.X := by linarith
    positivity
  set a := Ay M y
  set q := M.κ / M.lam * (M.N - M.X) * (1 - y)
  have hsq : (2 * t - a) ^ 2 = a ^ 2 + 4 * q := by linear_combination 4 * heq
  unfold NbOf
  rw [show M.N - M.N * y - M.X - M.κ / M.lam = a from rfl,
    show 4 * (M.κ / M.lam) * (M.N - M.X) * (1 - y) = 4 * q by ring]
  rcases le_or_gt 0 (2 * t - a) with hpa | hna
  · rw [← hsq, Real.sqrt_sq hpa]; ring
  · exfalso
    have hq0 : q ≤ 0 := by nlinarith
    have hq0' : q = 0 := le_antisymm hq0 hq
    have hF : y = 1 := by
      have : M.κ / M.lam * (M.N - M.X) ≠ 0 := by
        have : 0 < M.N - M.X := by linarith
        positivity
      rcases mul_eq_zero.1 hq0' with h | h
      · exact absurd h this
      · linarith
    have : a < 0 := by
      show M.N - M.N * y - M.X - M.κ / M.lam < 0
      rw [hF]; have : 0 < M.κ / M.lam := by positivity
      linarith
    linarith

lemma ss_ii (hM : M.Standing) {g : ℝ → ℝ} (hg : IntegrableOn g (Icc 0 M.Δbar))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ M.Δbar) : IntervalIntegrable g volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  exact hg.mono_set (Icc_subset_Icc ha hb)

lemma tail_eq (hM : M.Standing) (hSS : IsSteadyState M Δb Δs μ) {x : ℝ} (hx : x ∈ Icc 0 M.Δbar) :
    ∫ t in x..M.Δbar, μ.μb t = μ.Nb M - μ.Fb x := by
  have hD : 0 ≤ M.Δbar := hM.2.2.2.2.2.2.2.2.1.le
  unfold Densities.Nb Densities.Fb
  rw [← intervalIntegral.integral_add_adjacent_intervals (ss_ii hM hSS.2.1 le_rfl hx.1 hx.2)
    (ss_ii hM hSS.2.1 hx.1 hx.2 le_rfl)]
  ring

lemma prim_ae_deriv (hM : M.Standing) {g : ℝ → ℝ} (hg : IntegrableOn g (Icc 0 M.Δbar)) :
    ∀ᵐ x, x ∈ uIcc 0 M.Δbar → HasDerivAt (fun x => ∫ t in (0:ℝ)..x, g t) (g x) x := by
  have hD : 0 ≤ M.Δbar := hM.2.2.2.2.2.2.2.2.1.le
  filter_upwards [(ss_ii hM hg le_rfl hD le_rfl).ae_hasDerivAt_integral] with x hx hxm
  exact hx hxm 0 left_mem_uIcc

lemma prim_ac (hM : M.Standing) {g : ℝ → ℝ} (hg : IntegrableOn g (Icc 0 M.Δbar))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ M.Δbar) :
    AbsolutelyContinuousOnInterval (fun x => ∫ t in (0:ℝ)..x, g t) a b := by
  have h := (ss_ii hM hg le_rfl (ha.trans hab) hb).absolutelyContinuousOnInterval_intervalIntegral
    (c := 0) left_mem_uIcc
  exact h.mono (by rw [uIcc_of_le hab, uIcc_of_le (ha.trans hab)]; exact Icc_subset_Icc ha le_rfl)

variable (hM : M.Standing) (h0 : 0 < Δb) (h1 : Δb < Δs) (h2 : Δs < M.Δbar)
  (hSS : IsSteadyState M Δb Δs μ)
include hM h0 h1 h2 hSS

lemma Nb_nn : 0 ≤ μ.Nb M :=
  intervalIntegral.integral_nonneg hM.2.2.2.2.2.2.2.2.1.le (fun u hu => (hSS.1 u hu).1)

lemma Ns_nn : 0 ≤ μ.Ns M :=
  intervalIntegral.integral_nonneg hM.2.2.2.2.2.2.2.2.1.le (fun u hu => (hSS.1 u hu).2.1)

lemma u_at_b : μ.Fs Δb = M.κ * M.X / (M.κ + M.lam * μ.Nb M) * M.F Δb := by
  unfold Densities.Fs
  rw [intervalIntegral.integral_congr_ae (g := fun x => M.κ * M.X / (M.κ + M.lam * μ.Nb M) * M.f x),
    intervalIntegral.integral_const_mul]
  · rfl
  filter_upwards [Measure.ae_ne volume Δb] with x hx1 hx
  rw [uIoc_of_le h0.le] at hx
  exact (eq_55_57 M hM Δb Δs h0 h1 h2 μ hSS x ⟨hx.1.le, lt_of_le_of_ne hx.2 hx1⟩).2.2.2

lemma Fb_at_b : μ.Fb Δb = 0 := by
  unfold Densities.Fb
  rw [intervalIntegral.integral_congr_ae (g := fun _ => (0:ℝ))]
  · simp
  filter_upwards [Measure.ae_ne volume Δb] with x hx1 hx
  rw [uIoc_of_le h0.le] at hx
  exact (eq_55_57 M hM Δb Δs h0 h1 h2 μ hSS x ⟨hx.1.le, lt_of_le_of_ne hx.2 hx1⟩).1

lemma u_at_s : μ.Fs Δs = μ.Ns M := by
  have hD : 0 ≤ M.Δbar := hM.2.2.2.2.2.2.2.2.1.le
  have hz : ∫ x in Δs..M.Δbar, μ.μs x = 0 := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0:ℝ))]
    · simp
    refine Eventually.of_forall (fun x hx => ?_)
    rw [uIoc_of_le h2.le] at hx
    exact (eq_61_63 M hM Δb Δs h0 h1 h2 μ hSS x hx).2.1
  unfold Densities.Fs Densities.Ns
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (ss_ii hM hSS.2.2.1 le_rfl (by linarith) h2.le) (ss_ii hM hSS.2.2.1 (by linarith) h2.le le_rfl),
    hz, add_zero]

lemma bb_at_s : μ.Nb M - μ.Fb Δs =
    M.κ * (M.N - M.X) / (M.κ + M.lam * μ.Ns M) * (1 - M.F Δs) := by
  rw [← tail_eq hM hSS ⟨by linarith, h2.le⟩]
  rw [intervalIntegral.integral_congr_ae (g := fun x => M.κ * (M.N - M.X) / (M.κ + M.lam * μ.Ns M)
    * M.f x), intervalIntegral.integral_const_mul]
  · congr 1
    rw [← F_bar M hM, F_sub M hM (by linarith) h2.le le_rfl]
  refine Eventually.of_forall (fun x hx => ?_)
  rw [uIoc_of_le h2.le] at hx
  exact (eq_61_63 M hM Δb Δs h0 h1 h2 μ hSS x hx).2.2.1

/-- The two conserved quantities of (17)–(18) on `[∆b, ∆s]`. -/
lemma conserved :
    ∀ x ∈ Icc Δb Δs,
      M.κ * μ.Fs x + M.lam * μ.Fs x * (μ.Nb M - μ.Fb x) - M.κ * M.X * M.F x = 0 ∧
      M.κ * (μ.Nb M - μ.Fb x) + M.lam * μ.Fs x * (μ.Nb M - μ.Fb x)
        - M.κ * (M.N - M.X) * (1 - M.F x) = 0 := by
  have hD : 0 ≤ M.Δbar := hM.2.2.2.2.2.2.2.2.1.le
  have hb0 : 0 ≤ Δb := h0.le
  have hsD : Δs ≤ M.Δbar := h2.le
  have acu : AbsolutelyContinuousOnInterval μ.Fs Δb Δs :=
    prim_ac hM hSS.2.2.1 hb0 h1.le hsD
  have acb : AbsolutelyContinuousOnInterval μ.Fb Δb Δs :=
    prim_ac hM hSS.2.1 hb0 h1.le hsD
  have acF : AbsolutelyContinuousOnInterval M.F Δb Δs := F_ac M hM hb0 h1.le hsD
  have acc : ∀ c : ℝ, AbsolutelyContinuousOnInterval (fun _ => c) Δb Δs := fun c =>
    (contDiffOn_const).absolutelyContinuousOnInterval
  have acbb : AbsolutelyContinuousOnInterval (fun x => μ.Nb M - μ.Fb x) Δb Δs :=
    (acc (μ.Nb M)).sub acb
  have acΦ : AbsolutelyContinuousOnInterval (fun x => M.κ * μ.Fs x
      + M.lam * μ.Fs x * (μ.Nb M - μ.Fb x) - M.κ * M.X * M.F x) Δb Δs :=
    ((acu.const_mul M.κ).add ((acu.const_mul M.lam).mul acbb)).sub (acF.const_mul (M.κ * M.X))
  have acΨ : AbsolutelyContinuousOnInterval (fun x => M.κ * (μ.Nb M - μ.Fb x)
      + M.lam * μ.Fs x * (μ.Nb M - μ.Fb x) - M.κ * (M.N - M.X) * (1 - M.F x)) Δb Δs :=
    ((acbb.const_mul M.κ).add ((acu.const_mul M.lam).mul acbb)).sub
      (((acc 1).sub acF).const_mul (M.κ * (M.N - M.X)))
  have hderivs : ∀ᵐ x, x ∈ uIcc Δb Δs → x ≠ Δb → x ≠ Δs →
      HasDerivAt μ.Fs (μ.μs x) x ∧ HasDerivAt μ.Fb (μ.μb x) x ∧ HasDerivAt M.F (M.f x) x := by
    filter_upwards [prim_ae_deriv hM hSS.2.2.1, prim_ae_deriv hM hSS.2.1, F_ae_deriv M hM hD le_rfl]
      with x hx1 hx2 hx3 hxm _ _
    have hx' : x ∈ uIcc 0 M.Δbar := by
      rw [uIcc_of_le h1.le] at hxm; rw [uIcc_of_le hD]; exact ⟨hb0.trans hxm.1, hxm.2.trans hsD⟩
    exact ⟨hx1 hx', hx2 hx', hx3 hx'⟩
  have hmid : ∀ x ∈ uIcc Δb Δs, x ≠ Δb → x ≠ Δs → x ∈ Ioo Δb Δs := by
    intro x hx hx1 hx2
    rw [uIcc_of_le h1.le] at hx
    exact ⟨lt_of_le_of_ne hx.1 (Ne.symm hx1), lt_of_le_of_ne hx.2 hx2⟩
  have h18 : ∀ x ∈ Ioo Δb Δs, M.κ * μ.μs x = M.κ * M.X * M.f x
      - M.lam * μ.μs x * (μ.Nb M - μ.Fb x) + M.lam * μ.μb x * μ.Fs x := by
    intro x hx
    have := (hSS.2.2.2.2.2.2.2.2.1 x hx).2.2
    rw [tail_eq hM hSS ⟨hb0.trans hx.1.le, hx.2.le.trans hsD⟩] at this
    exact this
  have hsum : ∀ x ∈ Ioo Δb Δs, μ.μb x = M.N * M.f x - μ.μs x := by
    intro x hx
    have e12 := hSS.2.2.2.2.2.1 x ⟨hb0.trans hx.1.le, hx.2.le.trans hsD⟩
    obtain ⟨e1, e2, -⟩ := hSS.2.2.2.2.2.2.2.2.1 x hx
    rw [e1, e2] at e12; linarith
  obtain ⟨CΦ, hCΦ⟩ := acΦ.const_of_ae_hasDerivAt_zero (by
    filter_upwards [hderivs, Measure.ae_ne volume Δb, Measure.ae_ne volume Δs]
      with x hd hx1 hx2 hxm
    obtain ⟨du, db, dF⟩ := hd hxm hx1 hx2
    have hx := hmid x hxm hx1 hx2
    refine (((du.const_mul M.κ).add ((du.const_mul M.lam).mul (db.const_sub (μ.Nb M)))).sub
      (dF.const_mul (M.κ * M.X))).congr_deriv ?_
    linear_combination h18 x hx)
  obtain ⟨CΨ, hCΨ⟩ := acΨ.const_of_ae_hasDerivAt_zero (by
    filter_upwards [hderivs, Measure.ae_ne volume Δb, Measure.ae_ne volume Δs]
      with x hd hx1 hx2 hxm
    obtain ⟨du, db, dF⟩ := hd hxm hx1 hx2
    have hx := hmid x hxm hx1 hx2
    refine (((db.const_sub (μ.Nb M)).const_mul M.κ).add ((du.const_mul M.lam).mul
      (db.const_sub (μ.Nb M)))).sub ((dF.const_sub 1).const_mul (M.κ * (M.N - M.X))) |>.congr_deriv ?_
    linear_combination h18 x hx - M.κ * hsum x hx)
  have hb_mem : Δb ∈ uIcc Δb Δs := left_mem_uIcc
  have hs_mem : Δs ∈ uIcc Δb Δs := right_mem_uIcc
  have hNbp : 0 < M.κ + M.lam * μ.Nb M := by
    have := Nb_nn hM h0 h1 h2 hSS; nlinarith [hM.2.2.1, hM.2.2.2.1]
  have hNsp : 0 < M.κ + M.lam * μ.Ns M := by
    have := Ns_nn hM h0 h1 h2 hSS; nlinarith [hM.2.2.1, hM.2.2.2.1]
  have hΦb : CΦ = 0 := by
    have := hCΦ Δb hb_mem
    rw [← this, u_at_b hM h0 h1 h2 hSS, Fb_at_b hM h0 h1 h2 hSS]
    field_simp; ring
  have hΨs : CΨ = 0 := by
    have := hCΨ Δs hs_mem
    rw [← this, u_at_s hM h0 h1 h2 hSS, bb_at_s hM h0 h1 h2 hSS]
    field_simp; ring
  intro x hx
  have hx' : x ∈ uIcc Δb Δs := by rw [uIcc_of_le h1.le]; exact hx
  exact ⟨(hCΦ x hx').trans hΦb, (hCΨ x hx').trans hΨs⟩


lemma bb_eq_NbOf : ∀ x ∈ Icc Δb Δs, μ.Nb M - μ.Fb x = NbOf M (M.F x) ∧
    μ.Fs x = μ.Nb M - μ.Fb x - (M.N - M.N * M.F x - M.X) := by
  intro x hx
  obtain ⟨e1, e2⟩ := conserved hM h0 h1 h2 hSS x hx
  have hxI : x ∈ Icc 0 M.Δbar := ⟨h0.le.trans hx.1, hx.2.trans h2.le⟩
  have hκ := hM.2.2.2.1
  have hlam := hM.2.2.1
  have hu : μ.Fs x = μ.Nb M - μ.Fb x - (M.N - M.N * M.F x - M.X) := by
    have : M.κ * (μ.Fs x - (μ.Nb M - μ.Fb x)) = M.κ * (M.X * M.F x - (M.N - M.X) * (1 - M.F x)) := by
      linear_combination e1 - e2
    have := mul_left_cancel₀ hκ.ne' this
    linarith
  refine ⟨?_, hu⟩
  have hbb : 0 ≤ μ.Nb M - μ.Fb x := by
    rw [← tail_eq hM hSS hxI]
    exact intervalIntegral.integral_nonneg hxI.2 (fun u hu => (hSS.1 u ⟨hxI.1.trans hu.1, hu.2⟩).1)
  apply root_eq_NbOf hM (F_le_one M hM hxI.1 hxI.2) hbb
  rw [hu] at e2
  unfold Ay
  field_simp
  linear_combination e2

lemma mid_unique : ∀ Δ ∈ Ioo Δb Δs,
      μ.μn Δ = 0 ∧ μ.μh Δ = 0 ∧
      (∫ x in Δ..M.Δbar, μ.μb x) = NbOf M (M.F Δ) ∧
      μ.μb Δ = M.N * M.f Δ / 2 *
        (1 + (M.N - M.N * M.F Δ - M.X - M.κ / M.lam + 2 * M.κ * (M.N - M.X) / (M.lam * M.N)) /
          Real.sqrt ((M.N - M.N * M.F Δ - M.X - M.κ / M.lam) ^ 2
            + 4 * (M.κ / M.lam) * (M.N - M.X) * (1 - M.F Δ))) ∧
      μ.μs Δ = M.N * M.f Δ - μ.μb Δ := by
  intro Δ hΔ
  have hΔI : Δ ∈ Icc 0 M.Δbar := ⟨h0.le.trans hΔ.1.le, hΔ.2.le.trans h2.le⟩
  obtain ⟨e1, e2, e18⟩ := hSS.2.2.2.2.2.2.2.2.1 Δ hΔ
  have e12 := hSS.2.2.2.2.2.1 Δ hΔI
  rw [e1, e2] at e12
  have hs : μ.μs Δ = M.N * M.f Δ - μ.μb Δ := by linarith
  obtain ⟨hb, hu⟩ := bb_eq_NbOf hM h0 h1 h2 hSS Δ (Ioo_subset_Icc_self hΔ)
  refine ⟨e1, e2, by rw [tail_eq hM hSS hΔI, hb], ?_, hs⟩
  rw [tail_eq hM hSS hΔI] at e18
  have hFle := F_le_one M hM hΔI.1 hΔI.2
  have hR := Ry_pos M hM hFle
  have hRsq := Ry_sq M hM hFle
  have hNb : NbOf M (M.F Δ) = Ay M (M.F Δ) / 2 + Ry M (M.F Δ) / 2 := NbOf_eq_AR M _
  have hlam := hM.2.2.1
  have hN : 0 < M.N := by linarith [hM.1, hM.2.1]
  rw [hs, show (∫ x in (0:ℝ)..Δ, μ.μs x) = μ.Fs Δ from rfl, hu, hb, hNb] at e18
  obtain ⟨k, hk⟩ : ∃ k, M.κ = M.lam * k := ⟨M.κ / M.lam, by field_simp⟩
  have hkd : M.κ / M.lam = k := by rw [hk]; field_simp
  set R := Ry M (M.F Δ)
  simp only [Ay] at e18
  rw [hkd] at e18
  rw [hkd, show Real.sqrt ((M.N - M.N * M.F Δ - M.X - k) ^ 2
      + 4 * k * (M.N - M.X) * (1 - M.F Δ)) = R by
    simp only [R, Ry, Ay, qy, hkd]]
  rw [hk] at e18 ⊢
  have hlin : μ.μb Δ * (M.lam * R) = M.lam * k * (M.N - M.X) * M.f Δ
      + M.lam * M.N * M.f Δ * ((M.N - M.N * M.F Δ - M.X - k) + R) / 2 := by
    linear_combination -e18
  have hLR : M.lam * R ≠ 0 := (mul_pos hlam hR).ne'
  rw [eq_div_of_mul_eq hLR hlin]
  field_simp
  ring

end F

end OTCAux


open Set MeasureTheory OTCChain.Equilibrium Filter Topology

namespace OTCAux

section G

variable (M : Params)

/-- `N_s(y) = N_b(y) − (N − N y − X)`. -/
lemma NsOf_eq_NbOf (y : ℝ) : NsOf M y = NbOf M y - (M.N - M.N * y - M.X) := by
  unfold NsOf NbOf
  have : (M.κ / M.lam + M.N - M.X - M.N * y) ^ 2 + 4 * (M.κ * M.X / M.lam) * y
      = (M.N - M.N * y - M.X - M.κ / M.lam) ^ 2 + 4 * (M.κ / M.lam) * (M.N - M.X) * (1 - y) := by
    ring
  rw [this]; ring

lemma ID1 (hM : M.Standing) {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1) :
    M.κ * (M.N - M.X) / (M.κ + M.lam * NsOf M y) * (1 - y) = NbOf M y := by
  have hn := NsOf_nonneg M hM hy0
  have hpos : 0 < M.κ + M.lam * NsOf M y := by nlinarith [hM.2.2.1, hM.2.2.2.1]
  have e := NbOf_eq M hM hy
  rw [div_mul_eq_mul_div, div_eq_iff hpos.ne', NsOf_eq_NbOf]
  have hlam := hM.2.2.1
  field_simp at e
  linear_combination -e

lemma ID2 (hM : M.Standing) {y : ℝ} (hy : y ≤ 1) :
    M.κ * M.X / (M.κ + M.lam * NbOf M y) * y = NbOf M y - (M.N - M.N * y - M.X) := by
  have hn := NbOf_nonneg M hM hy
  have hpos : 0 < M.κ + M.lam * NbOf M y := by nlinarith [hM.2.2.1, hM.2.2.2.1]
  have e := NbOf_eq M hM hy
  rw [div_mul_eq_mul_div, div_eq_iff hpos.ne']
  have hlam := hM.2.2.1
  field_simp at e
  linear_combination -e

lemma ID4 (hM : M.Standing) {y : ℝ} (hy0 : 0 ≤ y) :
    NsOf M y + (M.κ * M.X + M.lam * NsOf M y * M.N) / (M.κ + M.lam * NsOf M y) * (1 - y) = M.X := by
  have hn := NsOf_nonneg M hM hy0
  have hpos : 0 < M.κ + M.lam * NsOf M y := by nlinarith [hM.2.2.1, hM.2.2.2.1]
  have e := NsOf_eq M hM hy0
  have hlam := hM.2.2.1
  field_simp at e
  have : (M.κ * M.X + M.lam * NsOf M y * M.N) / (M.κ + M.lam * NsOf M y) * (1 - y)
      = M.X - NsOf M y := by
    rw [div_mul_eq_mul_div, div_eq_iff hpos.ne']
    linear_combination e
  linarith


variable (Δb Δs : ℝ)

noncomputable def Nb0 : ℝ := NbOf M (M.F Δb)
noncomputable def Ns0 : ℝ := NsOf M (M.F Δs)
noncomputable def Ks : ℝ := M.κ * M.X / (M.κ + M.lam * Nb0 M Δb)
noncomputable def Kn : ℝ := (M.κ * (M.N - M.X) + M.lam * Nb0 M Δb * M.N) / (M.κ + M.lam * Nb0 M Δb)
noncomputable def Kb : ℝ := M.κ * (M.N - M.X) / (M.κ + M.lam * Ns0 M Δs)
noncomputable def Kh : ℝ := (M.κ * M.X + M.lam * Ns0 M Δs * M.N) / (M.κ + M.lam * Ns0 M Δs)
noncomputable def mB (x : ℝ) : ℝ := -(dNb M (M.F x) * M.f x)

lemma cand_low {x : ℝ} (hx : x < Δb) (h1 : Δb < Δs) :
    (candDensities M Δb Δs).μb x = 0 ∧ (candDensities M Δb Δs).μs x = Ks M Δb * M.f x ∧
    (candDensities M Δb Δs).μn x = Kn M Δb * M.f x ∧ (candDensities M Δb Δs).μh x = 0 := by
  have hx2 : x < Δs := hx.trans h1
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [candDensities, if_pos hx, if_pos hx2, Ks, Kn, Nb0]

lemma cand_mid {x : ℝ} (hx1 : Δb ≤ x) (hx2 : x < Δs) :
    (candDensities M Δb Δs).μb x = mB M x ∧
    (candDensities M Δb Δs).μs x = M.N * M.f x - mB M x ∧
    (candDensities M Δb Δs).μn x = 0 ∧ (candDensities M Δb Δs).μh x = 0 := by
  have hn : ¬ x < Δb := not_lt.2 hx1
  have hm : M.N * M.f x / 2 * (1 + (M.N - M.N * M.F x - M.X - M.κ / M.lam
      + 2 * M.κ * (M.N - M.X) / (M.lam * M.N)) /
        Real.sqrt ((M.N - M.N * M.F x - M.X - M.κ / M.lam) ^ 2
          + 4 * (M.κ / M.lam) * (M.N - M.X) * (1 - M.F x))) = mB M x := by
    unfold mB dNb Ry qy kk; unfold Ay; ring
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [candDensities, if_neg hn, if_pos hx2]
  · exact hm
  · rw [hm]

lemma cand_high {x : ℝ} (hx : Δs ≤ x) (h1 : Δb < Δs) :
    (candDensities M Δb Δs).μb x = Kb M Δs * M.f x ∧ (candDensities M Δb Δs).μs x = 0 ∧
    (candDensities M Δb Δs).μn x = 0 ∧ (candDensities M Δb Δs).μh x = Kh M Δs * M.f x := by
  have hn : ¬ x < Δb := not_lt.2 (h1.le.trans hx)
  have hn2 : ¬ x < Δs := not_lt.2 hx
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [candDensities, if_neg hn, if_neg hn2, Kb, Kh, Ns0]


lemma integral_congr_Ioo {g h : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (he : ∀ x ∈ Ioo a b, g x = h x) :
    ∫ x in a..b, g x = ∫ x in a..b, h x := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne volume b] with x hx1 hx
  rw [uIoc_of_le hab] at hx
  exact he x ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩

lemma dNbF_contOn (hM : M.Standing) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ M.Δbar) :
    ContinuousOn (fun x => dNb M (M.F x)) (Icc a b) := by
  have hF : ContinuousOn M.F (Icc a b) := (F_cont M hM).mono (Icc_subset_Icc ha hb)
  have hA : ContinuousOn (fun x => Ay M (M.F x)) (Icc a b) := by
    unfold Ay; fun_prop
  have hR : ContinuousOn (fun x => Ry M (M.F x)) (Icc a b) := by
    unfold Ry; unfold qy
    exact (hA.pow 2 |>.add (continuousOn_const.mul (continuousOn_const.sub hF))).sqrt
  unfold dNb
  apply ContinuousOn.neg
  apply continuousOn_const.mul
  apply continuousOn_const.add
  apply (hA.add continuousOn_const).div hR
  intro x hx
  exact (Ry_pos M hM (F_le_one M hM (ha.trans hx.1) (hx.2.trans hb))).ne'

lemma mB_intOn (hM : M.Standing) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ M.Δbar) :
    IntegrableOn (mB M) (Icc a b) := by
  have hfi : IntegrableOn M.f (Icc a b) :=
    hM.2.2.2.2.2.2.2.2.2.2.1.mono_set (Icc_subset_Icc ha hb)
  have := Integrable.bdd_mul (c := M.N) hfi ((dNbF_contOn M hM ha hb).aestronglyMeasurable
    measurableSet_Icc) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      rw [Real.norm_eq_abs]
      exact dNb_abs_le M hM (F_le_one M hM (ha.trans hx.1) (hx.2.trans hb)))
  unfold mB
  exact this.neg

lemma int_mB (hM : M.Standing) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ M.Δbar) :
    ∫ x in a..b, mB M x = NbOf M (M.F a) - NbOf M (M.F b) := by
  unfold mB
  rw [intervalIntegral.integral_neg, int_dNb M hM ha hab hb]; ring

lemma f_intOn (hM : M.Standing) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ M.Δbar) :
    IntegrableOn M.f (Icc a b) := hM.2.2.2.2.2.2.2.2.2.2.1.mono_set (Icc_subset_Icc ha hb)

lemma int_cf (hM : M.Standing) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ M.Δbar) (k : ℝ) :
    ∫ x in a..b, k * M.f x = k * (M.F b - M.F a) := by
  rw [intervalIntegral.integral_const_mul, F_sub M hM ha hab hb]

lemma intOn_piece3 {g g1 g2 g3 : ℝ → ℝ} (h0 : 0 < Δb) (h1 : Δb < Δs) (h2 : Δs < M.Δbar)
    (hg1 : IntegrableOn g1 (Icc 0 Δb)) (hg2 : IntegrableOn g2 (Icc Δb Δs))
    (hg3 : IntegrableOn g3 (Icc Δs M.Δbar))
    (e1 : ∀ x ∈ Ico 0 Δb, g x = g1 x) (e2 : ∀ x ∈ Ico Δb Δs, g x = g2 x)
    (e3 : ∀ x ∈ Icc Δs M.Δbar, g x = g3 x) : IntegrableOn g (Icc 0 M.Δbar) := by
  have hU : Icc 0 M.Δbar = Ico 0 Δb ∪ (Ico Δb Δs ∪ Icc Δs M.Δbar) := by
    rw [Ico_union_Icc_eq_Icc h1.le h2.le, Ico_union_Icc_eq_Icc h0.le (h1.le.trans h2.le)]
  rw [hU]
  refine IntegrableOn.union ?_ (IntegrableOn.union ?_ ?_)
  · exact (hg1.mono_set Ico_subset_Icc_self).congr_fun (fun x hx => (e1 x hx).symm) measurableSet_Ico
  · exact (hg2.mono_set Ico_subset_Icc_self).congr_fun (fun x hx => (e2 x hx).symm) measurableSet_Ico
  · exact hg3.congr_fun (fun x hx => (e3 x hx).symm) measurableSet_Icc


lemma ii_Icc {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (h : IntegrableOn g (Icc a b)) :
    IntervalIntegrable g volume a b := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 h

lemma split3 {g g1 g2 g3 : ℝ → ℝ} (h0 : 0 < Δb) (h1 : Δb < Δs) (h2 : Δs < M.Δbar)
    (hg : IntegrableOn g (Icc 0 M.Δbar))
    (e1 : ∀ x ∈ Ioo 0 Δb, g x = g1 x) (e2 : ∀ x ∈ Ioo Δb Δs, g x = g2 x)
    (e3 : ∀ x ∈ Ioo Δs M.Δbar, g x = g3 x) :
    ∫ x in (0:ℝ)..M.Δbar, g x
      = (∫ x in (0:ℝ)..Δb, g1 x) + (∫ x in Δb..Δs, g2 x) + ∫ x in Δs..M.Δbar, g3 x := by
  have ii : ∀ a b, 0 ≤ a → a ≤ b → b ≤ M.Δbar → IntervalIntegrable g volume a b := by
    intro a b ha hab hb
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact hg.mono_set (Icc_subset_Icc ha hb)
  rw [← intervalIntegral.integral_add_adjacent_intervals (ii 0 Δb le_rfl h0.le (by linarith))
    (ii Δb M.Δbar h0.le (by linarith) le_rfl),
    ← intervalIntegral.integral_add_adjacent_intervals (ii Δb Δs h0.le h1.le h2.le)
    (ii Δs M.Δbar (by linarith) h2.le le_rfl),
    integral_congr_Ioo h0.le e1, integral_congr_Ioo h1.le e2, integral_congr_Ioo h2.le e3]
  ring

section cand

variable (hM : M.Standing) (h0 : 0 < Δb) (h1 : Δb < Δs) (h2 : Δs < M.Δbar)
include hM h0 h1 h2

lemma Fb01 : 0 ≤ M.F Δb ∧ M.F Δb ≤ 1 :=
  ⟨F_nonneg M hM h0.le (by linarith), F_le_one M hM h0.le (by linarith)⟩

lemma Fs01 : 0 ≤ M.F Δs ∧ M.F Δs ≤ 1 :=
  ⟨F_nonneg M hM (by linarith) h2.le, F_le_one M hM (by linarith) h2.le⟩

lemma Nb0_nn : 0 ≤ Nb0 M Δb := NbOf_nonneg M hM (Fb01 M Δb Δs hM h0 h1 h2).2
lemma Ns0_nn : 0 ≤ Ns0 M Δs := NsOf_nonneg M hM (Fs01 M Δb Δs hM h0 h1 h2).1

lemma denb_pos : 0 < M.κ + M.lam * Nb0 M Δb := by
  have := Nb0_nn M Δb Δs hM h0 h1 h2; nlinarith [hM.2.2.1, hM.2.2.2.1]
lemma dens_pos : 0 < M.κ + M.lam * Ns0 M Δs := by
  have := Ns0_nn M Δb Δs hM h0 h1 h2; nlinarith [hM.2.2.1, hM.2.2.2.1]

lemma c_ib : IntegrableOn (candDensities M Δb Δs).μb (Icc 0 M.Δbar) :=
  intOn_piece3 M Δb Δs (g1 := fun _ => 0) (g2 := mB M) (g3 := fun x => Kb M Δs * M.f x) h0 h1 h2
    integrableOn_zero (mB_intOn M hM h0.le h1.le h2.le) ((f_intOn M hM (by linarith) le_rfl).const_mul _)
    (fun x hx => (cand_low M Δb Δs hx.2 h1).1) (fun x hx => (cand_mid M Δb Δs hx.1 hx.2).1)
    (fun x hx => (cand_high M Δb Δs hx.1 h1).1)

lemma c_is : IntegrableOn (candDensities M Δb Δs).μs (Icc 0 M.Δbar) :=
  intOn_piece3 M Δb Δs (g1 := fun x => Ks M Δb * M.f x) (g2 := fun x => M.N * M.f x - mB M x)
    (g3 := fun _ => 0) h0 h1 h2 ((f_intOn M hM le_rfl (by linarith)).const_mul _)
    (((f_intOn M hM h0.le h2.le).const_mul _).sub (mB_intOn M hM h0.le h1.le h2.le)) integrableOn_zero
    (fun x hx => (cand_low M Δb Δs hx.2 h1).2.1) (fun x hx => (cand_mid M Δb Δs hx.1 hx.2).2.1)
    (fun x hx => (cand_high M Δb Δs hx.1 h1).2.1)

lemma c_in : IntegrableOn (candDensities M Δb Δs).μn (Icc 0 M.Δbar) :=
  intOn_piece3 M Δb Δs (g1 := fun x => Kn M Δb * M.f x) (g2 := fun _ => 0)
    (g3 := fun _ => 0) h0 h1 h2 ((f_intOn M hM le_rfl (by linarith)).const_mul _)
    integrableOn_zero integrableOn_zero
    (fun x hx => (cand_low M Δb Δs hx.2 h1).2.2.1) (fun x hx => (cand_mid M Δb Δs hx.1 hx.2).2.2.1)
    (fun x hx => (cand_high M Δb Δs hx.1 h1).2.2.1)

lemma c_ih : IntegrableOn (candDensities M Δb Δs).μh (Icc 0 M.Δbar) :=
  intOn_piece3 M Δb Δs (g1 := fun _ => 0) (g2 := fun _ => 0)
    (g3 := fun x => Kh M Δs * M.f x) h0 h1 h2 integrableOn_zero integrableOn_zero
    ((f_intOn M hM (by linarith) le_rfl).const_mul _)
    (fun x hx => (cand_low M Δb Δs hx.2 h1).2.2.2) (fun x hx => (cand_mid M Δb Δs hx.1 hx.2).2.2.2)
    (fun x hx => (cand_high M Δb Δs hx.1 h1).2.2.2)

lemma c_Nb : (candDensities M Δb Δs).Nb M = Nb0 M Δb := by
  unfold Densities.Nb
  rw [split3 M Δb Δs (g1 := fun _ => 0) (g2 := mB M) (g3 := fun x => Kb M Δs * M.f x) h0 h1 h2
    (c_ib M Δb Δs hM h0 h1 h2) (fun x hx => (cand_low M Δb Δs hx.2 h1).1)
    (fun x hx => (cand_mid M Δb Δs hx.1.le hx.2).1)
    (fun x hx => (cand_high M Δb Δs hx.1.le h1).1),
    int_mB M hM h0.le h1.le h2.le, int_cf M hM (by linarith) h2.le le_rfl, F_bar M hM]
  have := ID1 M hM (Fs01 M Δb Δs hM h0 h1 h2).1 (Fs01 M Δb Δs hM h0 h1 h2).2
  unfold Kb Ns0 Nb0
  simp only [intervalIntegral.integral_zero]
  linarith

lemma c_Ns : (candDensities M Δb Δs).Ns M = Ns0 M Δs := by
  unfold Densities.Ns
  rw [split3 M Δb Δs (g1 := fun x => Ks M Δb * M.f x) (g2 := fun x => M.N * M.f x - mB M x)
    (g3 := fun _ => 0) h0 h1 h2
    (c_is M Δb Δs hM h0 h1 h2) (fun x hx => (cand_low M Δb Δs hx.2 h1).2.1)
    (fun x hx => (cand_mid M Δb Δs hx.1.le hx.2).2.1)
    (fun x hx => (cand_high M Δb Δs hx.1.le h1).2.1),
    int_cf M hM le_rfl h0.le (by linarith),
    intervalIntegral.integral_sub ((ii_Icc h1.le (f_intOn M hM h0.le (by linarith))).const_mul _)
      (ii_Icc h1.le (mB_intOn M hM h0.le h1.le h2.le)),
    int_cf M hM h0.le h1.le h2.le, int_mB M hM h0.le h1.le h2.le, F_zero]
  have e2 := ID2 M hM (Fb01 M Δb Δs hM h0 h1 h2).2
  have e3 := NsOf_eq_NbOf M (M.F Δs)
  unfold Ks Nb0 Ns0
  simp only [intervalIntegral.integral_zero]
  linarith

lemma c_tail {Δ : ℝ} (hΔ : Δ ∈ Ioo Δb Δs) :
    ∫ x in Δ..M.Δbar, (candDensities M Δb Δs).μb x = NbOf M (M.F Δ) := by
  have ii := fun a b (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ M.Δbar) =>
    ii_Icc hab ((c_ib M Δb Δs hM h0 h1 h2).mono_set (Icc_subset_Icc ha hb))
  have hΔ0 : 0 ≤ Δ := by linarith [hΔ.1]
  rw [← intervalIntegral.integral_add_adjacent_intervals (ii Δ Δs hΔ0 hΔ.2.le h2.le)
    (ii Δs M.Δbar (by linarith) h2.le le_rfl),
    integral_congr_Ioo hΔ.2.le (g := (candDensities M Δb Δs).μb) (h := mB M)
      (fun x hx => (cand_mid M Δb Δs (hΔ.1.le.trans hx.1.le) hx.2).1),
    integral_congr_Ioo h2.le (g := (candDensities M Δb Δs).μb) (h := fun x => Kb M Δs * M.f x)
      (fun x hx => (cand_high M Δb Δs hx.1.le h1).1),
    int_mB M hM hΔ0 hΔ.2.le h2.le, int_cf M hM (by linarith) h2.le le_rfl, F_bar M hM]
  have := ID1 M hM (Fs01 M Δb Δs hM h0 h1 h2).1 (Fs01 M Δb Δs hM h0 h1 h2).2
  unfold Kb Ns0
  linarith

lemma c_head {Δ : ℝ} (hΔ : Δ ∈ Ioo Δb Δs) :
    ∫ x in (0:ℝ)..Δ, (candDensities M Δb Δs).μs x = NbOf M (M.F Δ) - (M.N - M.N * M.F Δ - M.X) := by
  have ii := fun a b (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ M.Δbar) =>
    ii_Icc hab ((c_is M Δb Δs hM h0 h1 h2).mono_set (Icc_subset_Icc ha hb))
  have hΔ0 : 0 ≤ Δ := by linarith [hΔ.1]
  have hΔD : Δ ≤ M.Δbar := by linarith [hΔ.2]
  rw [← intervalIntegral.integral_add_adjacent_intervals (ii 0 Δb le_rfl h0.le (by linarith))
    (ii Δb Δ h0.le hΔ.1.le hΔD),
    integral_congr_Ioo h0.le (g := (candDensities M Δb Δs).μs) (h := fun x => Ks M Δb * M.f x)
      (fun x hx => (cand_low M Δb Δs hx.2 h1).2.1),
    integral_congr_Ioo hΔ.1.le (g := (candDensities M Δb Δs).μs) (h := fun x => M.N * M.f x - mB M x)
      (fun x hx => (cand_mid M Δb Δs hx.1.le (hx.2.trans hΔ.2)).2.1),
    int_cf M hM le_rfl h0.le (by linarith),
    intervalIntegral.integral_sub ((ii_Icc hΔ.1.le (f_intOn M hM h0.le hΔD)).const_mul _)
      (ii_Icc hΔ.1.le (mB_intOn M hM h0.le hΔ.1.le hΔD)),
    int_cf M hM h0.le hΔ.1.le hΔD, int_mB M hM h0.le hΔ.1.le hΔD, F_zero]
  have e2 := ID2 M hM (Fb01 M Δb Δs hM h0 h1 h2).2
  unfold Ks Nb0 at *
  linarith

lemma c_clear : ∫ x in (0:ℝ)..M.Δbar,
    ((candDensities M Δb Δs).μs x + (candDensities M Δb Δs).μh x) = M.X := by
  rw [split3 M Δb Δs (g := fun x => (candDensities M Δb Δs).μs x + (candDensities M Δb Δs).μh x)
    (g1 := fun x => Ks M Δb * M.f x) (g2 := fun x => M.N * M.f x - mB M x)
    (g3 := fun x => Kh M Δs * M.f x) h0 h1 h2
    ((c_is M Δb Δs hM h0 h1 h2).add (c_ih M Δb Δs hM h0 h1 h2))
    (fun x hx => by
      rw [(cand_low M Δb Δs hx.2 h1).2.1, (cand_low M Δb Δs hx.2 h1).2.2.2, add_zero])
    (fun x hx => by
      rw [(cand_mid M Δb Δs hx.1.le hx.2).2.1, (cand_mid M Δb Δs hx.1.le hx.2).2.2.2, add_zero])
    (fun x hx => by
      rw [(cand_high M Δb Δs hx.1.le h1).2.1, (cand_high M Δb Δs hx.1.le h1).2.2.2, zero_add]),
    int_cf M hM le_rfl h0.le (by linarith),
    intervalIntegral.integral_sub ((ii_Icc h1.le (f_intOn M hM h0.le (by linarith))).const_mul _)
      (ii_Icc h1.le (mB_intOn M hM h0.le h1.le h2.le)),
    int_cf M hM h0.le h1.le h2.le, int_mB M hM h0.le h1.le h2.le, F_zero,
    int_cf M hM (by linarith) h2.le le_rfl, F_bar M hM]
  have e2 := ID2 M hM (Fb01 M Δb Δs hM h0 h1 h2).2
  have e3 := NsOf_eq_NbOf M (M.F Δs)
  have e4 := ID4 M hM (Fs01 M Δb Δs hM h0 h1 h2).1
  unfold Ks Kh Nb0 Ns0 at *
  linarith

lemma mB_bounds {x : ℝ} (hx : x ∈ Icc 0 M.Δbar) : 0 ≤ mB M x ∧ mB M x ≤ M.N * M.f x := by
  have hf := hM.2.2.2.2.2.2.2.2.2.1 x hx
  have hFle := F_le_one M hM hx.1 hx.2
  have h := Ak_le_R M hM hFle
  have hR := Ry_pos M hM hFle
  have hN : 0 < M.N := by linarith [hM.1, hM.2.1]
  have h1' : |(Ay M (M.F x) + kk M) / Ry M (M.F x)| ≤ 1 := by
    rw [abs_div, abs_of_pos hR, div_le_one hR]; exact h
  rw [abs_le] at h1'
  have hmB : mB M x = M.N * M.f x / 2 * (1 + (Ay M (M.F x) + kk M) / Ry M (M.F x)) := by
    unfold mB dNb; ring
  rw [hmB]
  have hNf : 0 ≤ M.N * M.f x := by positivity
  constructor <;> nlinarith

lemma c_SS : IsSteadyState M Δb Δs (candDensities M Δb Δs) := by
  have hk := hM.2.2.2.1
  have hlam := hM.2.2.1
  have hNb := c_Nb M Δb Δs hM h0 h1 h2
  have hNs := c_Ns M Δb Δs hM h0 h1 h2
  have db := denb_pos M Δb Δs hM h0 h1 h2
  have ds := dens_pos M Δb Δs hM h0 h1 h2
  have nb := Nb0_nn M Δb Δs hM h0 h1 h2
  have ns := Ns0_nn M Δb Δs hM h0 h1 h2
  have hXN : 0 < M.N - M.X := by linarith [hM.2.1]
  have hX := hM.1
  refine ⟨?_, c_ib M Δb Δs hM h0 h1 h2, c_is M Δb Δs hM h0 h1 h2, c_in M Δb Δs hM h0 h1 h2,
    c_ih M Δb Δs hM h0 h1 h2, ?_, ?_, ?_, ?_, c_clear M Δb Δs hM h0 h1 h2⟩
  · intro x hx
    have hf := hM.2.2.2.2.2.2.2.2.2.1 x hx
    rcases lt_or_ge x Δb with hl | hl
    · obtain ⟨e1, e2, e3, e4⟩ := cand_low M Δb Δs hl h1
      rw [e1, e2, e3, e4]
      have hN : 0 ≤ M.N := by linarith
      refine ⟨le_rfl, mul_nonneg (div_nonneg (by positivity) db.le) hf,
        mul_nonneg (div_nonneg (add_nonneg (mul_nonneg hk.le hXN.le)
          (mul_nonneg (mul_nonneg hlam.le nb) hN)) db.le) hf, le_rfl⟩
    · rcases lt_or_ge x Δs with hm | hm
      · obtain ⟨e1, e2, e3, e4⟩ := cand_mid M Δb Δs hl hm
        obtain ⟨b1, b2⟩ := mB_bounds M Δb Δs hM h0 h1 h2 hx
        rw [e1, e2, e3, e4]
        exact ⟨b1, by linarith, le_rfl, le_rfl⟩
      · obtain ⟨e1, e2, e3, e4⟩ := cand_high M Δb Δs hm h1
        rw [e1, e2, e3, e4]
        have hN : 0 ≤ M.N := by linarith
        refine ⟨mul_nonneg (div_nonneg (mul_nonneg hk.le hXN.le) ds.le) hf, le_rfl, le_rfl,
          mul_nonneg (div_nonneg (add_nonneg (mul_nonneg hk.le hX.le)
            (mul_nonneg (mul_nonneg hlam.le ns) hN)) ds.le) hf⟩
  · intro x hx
    rcases lt_or_ge x Δb with hl | hl
    · obtain ⟨e1, e2, e3, e4⟩ := cand_low M Δb Δs hl h1
      rw [e1, e2, e3, e4]; unfold Ks Kn; field_simp; ring
    · rcases lt_or_ge x Δs with hm | hm
      · obtain ⟨e1, e2, e3, e4⟩ := cand_mid M Δb Δs hl hm
        rw [e1, e2, e3, e4]; ring
      · obtain ⟨e1, e2, e3, e4⟩ := cand_high M Δb Δs hm h1
        rw [e1, e2, e3, e4]; unfold Kb Kh; field_simp; ring
  · intro x hx
    obtain ⟨e1, e2, e3, e4⟩ := cand_high M Δb Δs hx.1.le h1
    refine ⟨e3, e2, ?_⟩
    rw [e1, e4, hNs]; unfold Kb Kh; field_simp; ring
  · intro x hx
    obtain ⟨e1, e2, e3, e4⟩ := cand_low M Δb Δs hx.2 h1
    refine ⟨e1, e4, ?_⟩
    rw [e2, e3, hNb]; unfold Ks Kn; field_simp; ring
  · intro x hx
    obtain ⟨e1, e2, e3, e4⟩ := cand_mid M Δb Δs hx.1.le hx.2
    refine ⟨e3, e4, ?_⟩
    rw [c_tail M Δb Δs hM h0 h1 h2 hx, c_head M Δb Δs hM h0 h1 h2 hx, e1, e2]
    have hxI : x ∈ Icc 0 M.Δbar := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hFle := F_le_one M hM hxI.1 hxI.2
    have hR := Ry_pos M hM hFle
    have hN : 0 < M.N := by linarith [hM.1, hM.2.1]
    rw [NbOf_eq_AR]
    unfold mB dNb kk
    set R := Ry M (M.F x)
    unfold Ay
    field_simp
    ring

end cand

end G

end OTCAux


open Set OTCChain.Equilibrium

theorem solution (M : Params) (hM : M.Standing) (Δb Δs : ℝ) (h0 : 0 < Δb)
    (h1 : Δb < Δs) (h2 : Δs < M.Δbar) :
    IsSteadyState M Δb Δs (candDensities M Δb Δs) ∧
    ∀ μ : Densities, IsSteadyState M Δb Δs μ → ∀ Δ ∈ Ioo Δb Δs,
      μ.μn Δ = 0 ∧ μ.μh Δ = 0 ∧
      (∫ x in Δ..M.Δbar, μ.μb x) = NbOf M (M.F Δ) ∧
      μ.μb Δ = M.N * M.f Δ / 2 *
        (1 + (M.N - M.N * M.F Δ - M.X - M.κ / M.lam + 2 * M.κ * (M.N - M.X) / (M.lam * M.N)) /
          Real.sqrt ((M.N - M.N * M.F Δ - M.X - M.κ / M.lam) ^ 2
            + 4 * (M.κ / M.lam) * (M.N - M.X) * (1 - M.F Δ))) ∧
      μ.μs Δ = M.N * M.f Δ - μ.μb Δ :=
  ⟨OTCAux.c_SS M Δb Δs hM h0 h1 h2, fun μ hSS => OTCAux.mid_unique hM h0 h1 h2 hSS⟩
