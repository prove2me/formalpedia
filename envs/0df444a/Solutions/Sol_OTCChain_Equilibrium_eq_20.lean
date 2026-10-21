-- Prove2me | solution 1 for OTCChain.Equilibrium.eq_20
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T22:09:20.907788+00:00
-- url     : https://prove2.me/submissions/eccc0945-8d5a-41f7-8843-5313f89e29bb

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


open Set MeasureTheory OTCChain.Equilibrium

namespace OTCAux

/-- The reservation-value gap `D(∆) = V(1, ∆) − V(0, ∆)`; the surplus is `S(x, y) = D x − D y`. -/
def D (V : Values) (x : ℝ) : ℝ := V.V1 x - V.V0 x

lemma surplus_eq (V : Values) (x y : ℝ) : surplus V x y = D V x - D V y := by
  unfold surplus D; ring

noncomputable def phib (M : Params) (μ : Densities) (V : Values) (d : ℝ) : ℝ :=
  ∫ x in (0:ℝ)..M.Δbar, max (D V x - d) 0 * μ.μb x

noncomputable def phis (M : Params) (μ : Densities) (V : Values) (d : ℝ) : ℝ :=
  ∫ x in (0:ℝ)..M.Δbar, max (d - D V x) 0 * μ.μs x

section B

variable {M : Params} {Δb Δs : ℝ} {μ : Densities} {V : Values}

lemma E_hD (hE : IsIntermEq M Δb Δs μ V) : 0 < M.Δbar := by
  obtain ⟨h0, h1, h2, -⟩ := hE; linarith

lemma bell (hE : IsIntermEq M Δb Δs μ V) {Δ : ℝ} (hΔ : Δ ∈ Icc 0 M.Δbar) :
    (M.κ + M.r) * V.Vh Δ = 1 + Δ + M.κ * M.E V.V1 ∧
    (M.κ + M.r) * V.Vs Δ = 1 + Δ - M.c + M.lam * (1 - M.η) * phib M μ V (D V Δ)
      + M.κ * M.E V.V1 ∧
    (M.κ + M.r) * V.Vn Δ = M.κ * M.E V.V0 ∧
    (M.κ + M.r) * V.Vb Δ = -M.c + M.lam * M.η * phis M μ V (D V Δ) + M.κ * M.E V.V0 := by
  obtain ⟨-, -, -, -, ⟨-, -, -, -, -, hB⟩, -⟩ := hE
  obtain ⟨e8, e9, e10, e11⟩ := hB Δ hΔ
  refine ⟨e8, ?_, e10, ?_⟩
  · rw [e9]; unfold phib; simp only [surplus_eq]
  · rw [e11]; unfold phis; simp only [surplus_eq]

lemma bound (hE : IsIntermEq M Δb Δs μ V) : ∃ B, 0 ≤ B ∧ ∀ x ∈ Icc 0 M.Δbar,
    |V.Vh x| ≤ B ∧ |V.Vs x| ≤ B ∧ |V.Vn x| ≤ B ∧ |V.Vb x| ≤ B := by
  have hD := (E_hD hE).le
  obtain ⟨-, -, -, -, ⟨⟨B, hB⟩, -⟩, -⟩ := hE
  refine ⟨B, ?_, hB⟩
  have := (hB 0 ⟨le_rfl, hD⟩).1
  exact (abs_nonneg _).trans this

lemma D_bound (hE : IsIntermEq M Δb Δs μ V) : ∃ B, ∀ x ∈ Icc 0 M.Δbar, |D V x| ≤ B := by
  obtain ⟨B, -, hB⟩ := bound hE
  refine ⟨2 * B, fun x hx => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hB x hx
  unfold D Values.V1 Values.V0
  rw [abs_le] at *
  constructor
  · have := le_max_left (V.Vh x) (V.Vs x)
    have := max_le_iff.2 (show V.Vn x ≤ B ∧ V.Vb x ≤ B from ⟨h3.2, h4.2⟩)
    linarith
  · have := max_le_iff.2 (show V.Vh x ≤ B ∧ V.Vs x ≤ B from ⟨h1.2, h2.2⟩)
    have := le_max_left (V.Vn x) (V.Vb x)
    linarith

lemma D_meas (hE : IsIntermEq M Δb Δs μ V) :
    AEStronglyMeasurable (D V) (volume.restrict (Icc 0 M.Δbar)) := by
  obtain ⟨-, -, -, -, ⟨-, hh, hs, hn, hb, -⟩, -⟩ := hE
  unfold D Values.V1 Values.V0
  exact (hh.sup hs).sub (hn.sup hb)

lemma intOn_b (hE : IsIntermEq M Δb Δs μ V) (d : ℝ) :
    IntegrableOn (fun x => max (D V x - d) 0 * μ.μb x) (Icc 0 M.Δbar) := by
  obtain ⟨B, hB⟩ := D_bound hE
  have hib : IntegrableOn μ.μb (Icc 0 M.Δbar) := hE.2.2.2.1.2.1
  refine Integrable.bdd_mul (c := B + |d|) hib (((D_meas hE).sub aestronglyMeasurable_const).sup
    aestronglyMeasurable_const) ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  have := hB x hx
  rw [Real.norm_eq_abs, abs_le]
  rw [abs_le] at this
  have := neg_abs_le d
  have := le_abs_self d
  constructor
  · have := le_max_right (D V x - d) 0; linarith [abs_nonneg d]
  · apply max_le <;> linarith [abs_nonneg d]

lemma intOn_s (hE : IsIntermEq M Δb Δs μ V) (d : ℝ) :
    IntegrableOn (fun x => max (d - D V x) 0 * μ.μs x) (Icc 0 M.Δbar) := by
  obtain ⟨B, hB⟩ := D_bound hE
  have his : IntegrableOn μ.μs (Icc 0 M.Δbar) := hE.2.2.2.1.2.2.1
  refine Integrable.bdd_mul (c := B + |d|) his ((aestronglyMeasurable_const.sub (D_meas hE)).sup
    aestronglyMeasurable_const) ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  have := hB x hx
  rw [Real.norm_eq_abs, abs_le]
  rw [abs_le] at this
  have := neg_abs_le d
  have := le_abs_self d
  constructor
  · have := le_max_right (d - D V x) 0; linarith [abs_nonneg d]
  · apply max_le <;> linarith [abs_nonneg d]

lemma ii_of_intOn {g : ℝ → ℝ} (hD : 0 ≤ M.Δbar) (hg : IntegrableOn g (Icc 0 M.Δbar))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ M.Δbar) : IntervalIntegrable g volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  exact hg.mono_set (Icc_subset_Icc ha hb)

lemma phib_anti (hE : IsIntermEq M Δb Δs μ V) {d d' : ℝ} (h : d ≤ d') :
    phib M μ V d' ≤ phib M μ V d := by
  have hD := (E_hD hE).le
  have hnn := hE.2.2.2.1.1
  apply intervalIntegral.integral_mono_on hD (ii_of_intOn hD (intOn_b hE d') le_rfl hD le_rfl)
    (ii_of_intOn hD (intOn_b hE d) le_rfl hD le_rfl)
  intro x hx
  exact mul_le_mul_of_nonneg_right (max_le_max (by linarith) le_rfl) (hnn x hx).1

lemma phis_mono (hE : IsIntermEq M Δb Δs μ V) {d d' : ℝ} (h : d ≤ d') :
    phis M μ V d ≤ phis M μ V d' := by
  have hD := (E_hD hE).le
  have hnn := hE.2.2.2.1.1
  apply intervalIntegral.integral_mono_on hD (ii_of_intOn hD (intOn_s hE d) le_rfl hD le_rfl)
    (ii_of_intOn hD (intOn_s hE d') le_rfl hD le_rfl)
  intro x hx
  exact mul_le_mul_of_nonneg_right (max_le_max (by linarith) le_rfl) (hnn x hx).2.1

lemma max_scale {k a b : ℝ} (hk : 0 < k) : k * max a b = k * a + max 0 (k * b - k * a) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (by nlinarith)]; ring
  · rw [max_eq_left h, max_eq_left (by nlinarith)]; ring

/-- The fixed-point identity for `D`. -/
lemma D_eq (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) {Δ : ℝ} (hΔ : Δ ∈ Icc 0 M.Δbar) :
    (M.κ + M.r) * D V Δ = 1 + Δ + M.κ * M.E V.V1 - M.κ * M.E V.V0
      + max 0 (-M.c + M.lam * (1 - M.η) * phib M μ V (D V Δ))
      - max 0 (-M.c + M.lam * M.η * phis M μ V (D V Δ)) := by
  have hk : 0 < M.κ + M.r := by linarith [hM.2.2.2.1, hM.2.2.2.2.1]
  obtain ⟨e8, e9, e10, e11⟩ := bell hE hΔ
  have h1 : (M.κ + M.r) * V.V1 Δ = 1 + Δ + M.κ * M.E V.V1
      + max 0 (-M.c + M.lam * (1 - M.η) * phib M μ V (D V Δ)) := by
    show (M.κ + M.r) * max (V.Vh Δ) (V.Vs Δ) = _
    rw [max_scale hk, e8, e9]; ring_nf
  have h0 : (M.κ + M.r) * V.V0 Δ = M.κ * M.E V.V0
      + max 0 (-M.c + M.lam * M.η * phis M μ V (D V Δ)) := by
    show (M.κ + M.r) * max (V.Vn Δ) (V.Vb Δ) = _
    rw [max_scale hk, e10, e11]; ring_nf
  have : (M.κ + M.r) * D V Δ = (M.κ + M.r) * V.V1 Δ - (M.κ + M.r) * V.V0 Δ := by
    unfold D; ring
  rw [this, h1, h0]; ring

/-- `D` is strictly increasing on `[0, ∆̄]`, with slopes at most `1/(κ + r)`. -/
lemma D_strict (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) {Δ Δ' : ℝ}
    (hΔ : Δ ∈ Icc 0 M.Δbar) (hΔ' : Δ' ∈ Icc 0 M.Δbar) (hlt : Δ < Δ') :
    D V Δ < D V Δ' ∧ (M.κ + M.r) * (D V Δ' - D V Δ) ≤ Δ' - Δ := by
  have hk : 0 < M.κ + M.r := by linarith [hM.2.2.2.1, hM.2.2.2.2.1]
  have hl1 : 0 ≤ M.lam * (1 - M.η) := mul_nonneg hM.2.2.1.le (by linarith [hM.2.2.2.2.2.2.1])
  have hl2 : 0 ≤ M.lam * M.η := mul_nonneg hM.2.2.1.le hM.2.2.2.2.2.1.le
  have e := D_eq hM hE hΔ
  have e' := D_eq hM hE hΔ'
  have key : ∀ a a' : ℝ, a ≤ a' →
      max 0 (-M.c + M.lam * (1 - M.η) * phib M μ V a') ≤
        max 0 (-M.c + M.lam * (1 - M.η) * phib M μ V a) ∧
      max 0 (-M.c + M.lam * M.η * phis M μ V a) ≤
        max 0 (-M.c + M.lam * M.η * phis M μ V a') := by
    intro a a' h
    exact ⟨max_le_max le_rfl (by nlinarith [phib_anti hE h]),
      max_le_max le_rfl (by nlinarith [phis_mono hE h])⟩
  have hgt : D V Δ < D V Δ' := by
    by_contra hc
    push Not at hc
    obtain ⟨k1, k2⟩ := key _ _ hc
    nlinarith
  refine ⟨hgt, ?_⟩
  obtain ⟨k1, k2⟩ := key _ _ hgt.le
  nlinarith

lemma D_mono_le (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) {Δ Δ' : ℝ}
    (hΔ : Δ ∈ Icc 0 M.Δbar) (hΔ' : Δ' ∈ Icc 0 M.Δbar) (hle : Δ ≤ Δ') : D V Δ ≤ D V Δ' := by
  rcases hle.lt_or_eq with h | h
  · exact (D_strict hM hE hΔ hΔ' h).1.le
  · rw [h]

lemma D_lip (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) {Δ Δ' : ℝ}
    (hΔ : Δ ∈ Icc 0 M.Δbar) (hΔ' : Δ' ∈ Icc 0 M.Δbar) :
    |D V Δ' - D V Δ| ≤ |Δ' - Δ| / (M.κ + M.r) := by
  have hk : 0 < M.κ + M.r := by linarith [hM.2.2.2.1, hM.2.2.2.2.1]
  rw [le_div_iff₀ hk]
  rcases lt_trichotomy Δ Δ' with h | h | h
  · obtain ⟨a, b⟩ := D_strict hM hE hΔ hΔ' h
    rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]; linarith
  · subst h; simp
  · obtain ⟨a, b⟩ := D_strict hM hE hΔ' hΔ h
    rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]; linarith

lemma D_cont (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) :
    ContinuousOn (D V) (Icc 0 M.Δbar) := by
  have hk : 0 < M.κ + M.r := by linarith [hM.2.2.2.1, hM.2.2.2.2.1]
  intro x hx
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨ε * (M.κ + M.r), by positivity, fun y hy hd => ?_⟩
  rw [Real.dist_eq] at *
  have := D_lip hM hE hx hy
  calc |D V y - D V x| ≤ |y - x| / (M.κ + M.r) := this
    _ < ε * (M.κ + M.r) / (M.κ + M.r) := by gcongr
    _ = ε := by field_simp


/-! ### Regions -/

lemma V1_Vs (hE : IsIntermEq M Δb Δs μ V) {Δ : ℝ} (h : Δ ∈ Ico 0 Δs) : V.V1 Δ = V.Vs Δ :=
  max_eq_right (hE.2.2.2.2.2.2.2.1 Δ h)

lemma V1_Vh (hE : IsIntermEq M Δb Δs μ V) {Δ : ℝ} (h : Δ ∈ Ioc Δs M.Δbar) : V.V1 Δ = V.Vh Δ :=
  max_eq_left (hE.2.2.2.2.2.2.2.2 Δ h)

lemma V0_Vn (hE : IsIntermEq M Δb Δs μ V) {Δ : ℝ} (h : Δ ∈ Ico 0 Δb) : V.V0 Δ = V.Vn Δ :=
  max_eq_left (hE.2.2.2.2.2.1 Δ h)

lemma V0_Vb (hE : IsIntermEq M Δb Δs μ V) {Δ : ℝ} (h : Δ ∈ Ioc Δb M.Δbar) : V.V0 Δ = V.Vb Δ :=
  max_eq_right (hE.2.2.2.2.2.2.1 Δ h)

lemma kr_pos (hM : M.Standing) : 0 < M.κ + M.r := by linarith [hM.2.2.2.1, hM.2.2.2.2.1]

lemma Vn_eq (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) {Δ : ℝ} (hΔ : Δ ∈ Icc 0 M.Δbar) :
    V.Vn Δ = M.κ * M.E V.V0 / (M.κ + M.r) := by
  rw [eq_div_iff (kr_pos hM).ne', mul_comm]; exact (bell hE hΔ).2.2.1

lemma Vh_eq (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) {Δ : ℝ} (hΔ : Δ ∈ Icc 0 M.Δbar) :
    V.Vh Δ = (1 + Δ + M.κ * M.E V.V1) / (M.κ + M.r) := by
  rw [eq_div_iff (kr_pos hM).ne', mul_comm]; exact (bell hE hΔ).1

lemma intOn_Dmul (hE : IsIntermEq M Δb Δs μ V) {g : ℝ → ℝ} (hg : IntegrableOn g (Icc 0 M.Δbar)) :
    IntegrableOn (fun x => D V x * g x) (Icc 0 M.Δbar) := by
  obtain ⟨B, hB⟩ := D_bound hE
  refine Integrable.bdd_mul (c := B) hg (D_meas hE) ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [Real.norm_eq_abs]; exact hB x hx

lemma ib (hE : IsIntermEq M Δb Δs μ V) : IntegrableOn μ.μb (Icc 0 M.Δbar) := hE.2.2.2.1.2.1
lemma is_ (hE : IsIntermEq M Δb Δs μ V) : IntegrableOn μ.μs (Icc 0 M.Δbar) := hE.2.2.2.1.2.2.1

/-- (P1): below the buyer cutoff, `φb(D ∆) = ∫ D μb − D(∆) N_b`. -/
lemma phib_low (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) {Δ : ℝ}
    (hΔ : Δ ∈ Icc 0 M.Δbar) (hle : Δ ≤ Δb) :
    phib M μ V (D V Δ) = (∫ x in (0:ℝ)..M.Δbar, D V x * μ.μb x) - D V Δ * μ.Nb M := by
  have hD := (E_hD hE).le
  have h16 := hE.2.2.2.1.2.2.2.2.2.2.2.1
  unfold phib Densities.Nb
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
    (ii_of_intOn hD (intOn_Dmul hE (ib hE)) le_rfl hD le_rfl)
    ((ii_of_intOn hD (ib hE) le_rfl hD le_rfl).const_mul _)]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hD] at hx
  simp only
  rcases lt_trichotomy x Δ with h | h | h
  · rw [(h16 x ⟨hx.1, lt_of_lt_of_le h hle⟩).1]; ring
  · subst h; simp
  · rw [max_eq_left (by linarith [(D_strict hM hE hΔ hx h).1])]; ring

/-- (P2): above the seller cutoff, `φs(D ∆) = D(∆) N_s − ∫ D μs`. -/
lemma phis_high (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) {Δ : ℝ}
    (hΔ : Δ ∈ Icc 0 M.Δbar) (hle : Δs ≤ Δ) :
    phis M μ V (D V Δ) = D V Δ * μ.Ns M - (∫ x in (0:ℝ)..M.Δbar, D V x * μ.μs x) := by
  have hD := (E_hD hE).le
  have h14 := hE.2.2.2.1.2.2.2.2.2.2.1
  unfold phis Densities.Ns
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
    ((ii_of_intOn hD (is_ hE) le_rfl hD le_rfl).const_mul _)
    (ii_of_intOn hD (intOn_Dmul hE (is_ hE)) le_rfl hD le_rfl)]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hD] at hx
  simp only
  rcases lt_trichotomy x Δ with h | h | h
  · rw [max_eq_left (by linarith [(D_strict hM hE hx hΔ h).1])]; ring
  · subst h; simp
  · rw [(h14 x ⟨lt_of_le_of_lt hle h, hx.2⟩).2.1]; ring

/-- (G1): `φs(D ∆) = ∫₀^∆ (D ∆ − D x) μs(x) dx`. -/
lemma phis_eq (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) {Δ : ℝ}
    (hΔ : Δ ∈ Icc 0 M.Δbar) :
    phis M μ V (D V Δ) = ∫ x in (0:ℝ)..Δ, (D V Δ - D V x) * μ.μs x := by
  have hD := (E_hD hE).le
  unfold phis
  have hi := intOn_s hE (D V Δ)
  rw [← intervalIntegral.integral_add_adjacent_intervals (ii_of_intOn hD hi le_rfl hΔ.1 hΔ.2)
    (ii_of_intOn hD hi hΔ.1 hΔ.2 le_rfl)]
  have h2 : ∫ x in Δ..M.Δbar, max (D V Δ - D V x) 0 * μ.μs x = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ))]
    · simp
    intro x hx
    rw [uIcc_of_le hΔ.2] at hx
    simp only
    rw [max_eq_right (by linarith [D_mono_le hM hE hΔ ⟨hΔ.1.trans hx.1, hx.2⟩ hx.1])]; ring
  rw [h2, add_zero]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hΔ.1] at hx
  simp only
  rw [max_eq_left (by linarith [D_mono_le hM hE ⟨hx.1, hx.2.trans hΔ.2⟩ hΔ hx.2])]

/-- (G2): `φb(D ∆) = ∫_∆^∆̄ (D x − D ∆) μb(x) dx`. -/
lemma phib_eq (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) {Δ : ℝ}
    (hΔ : Δ ∈ Icc 0 M.Δbar) :
    phib M μ V (D V Δ) = ∫ x in Δ..M.Δbar, (D V x - D V Δ) * μ.μb x := by
  have hD := (E_hD hE).le
  unfold phib
  have hi := intOn_b hE (D V Δ)
  rw [← intervalIntegral.integral_add_adjacent_intervals (ii_of_intOn hD hi le_rfl hΔ.1 hΔ.2)
    (ii_of_intOn hD hi hΔ.1 hΔ.2 le_rfl)]
  have h1 : ∫ x in (0:ℝ)..Δ, max (D V x - D V Δ) 0 * μ.μb x = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ))]
    · simp
    intro x hx
    rw [uIcc_of_le hΔ.1] at hx
    simp only
    rw [max_eq_right (by linarith [D_mono_le hM hE ⟨hx.1, hx.2.trans hΔ.2⟩ hΔ hx.2])]; ring
  rw [h1, zero_add]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hΔ.2] at hx
  simp only
  rw [max_eq_left (by linarith [D_mono_le hM hE hΔ ⟨hΔ.1.trans hx.1, hx.2⟩ hx.1])]

/-! ### Continuity of the value functions -/

lemma phib_lip (hE : IsIntermEq M Δb Δs μ V) (d d' : ℝ) :
    |phib M μ V d - phib M μ V d'| ≤ μ.Nb M * |d - d'| := by
  have hD := (E_hD hE).le
  have hnn := hE.2.2.2.1.1
  unfold phib Densities.Nb
  rw [← intervalIntegral.integral_sub (ii_of_intOn hD (intOn_b hE d) le_rfl hD le_rfl)
    (ii_of_intOn hD (intOn_b hE d') le_rfl hD le_rfl), ← intervalIntegral.integral_mul_const]
  refine (intervalIntegral.abs_integral_le_integral_abs hD).trans ?_
  apply intervalIntegral.integral_mono_on hD
  · exact ((ii_of_intOn hD (intOn_b hE d) le_rfl hD le_rfl).sub
      (ii_of_intOn hD (intOn_b hE d') le_rfl hD le_rfl)).abs
  · exact (ii_of_intOn hD (ib hE) le_rfl hD le_rfl).mul_const _
  intro x hx
  have hb := (hnn x hx).1
  rw [← sub_mul, abs_mul, abs_of_nonneg hb, mul_comm]
  apply mul_le_mul_of_nonneg_left _ hb
  rw [abs_le]
  constructor
  · rcases le_total (D V x - d) 0 with h1 | h1 <;> rcases le_total (D V x - d') 0 with h2 | h2 <;>
      simp only [max_eq_left, max_eq_right, h1, h2] <;>
      linarith [neg_abs_le (d - d'), le_abs_self (d - d')]
  · rcases le_total (D V x - d) 0 with h1 | h1 <;> rcases le_total (D V x - d') 0 with h2 | h2 <;>
      simp only [max_eq_left, max_eq_right, h1, h2] <;>
      linarith [neg_abs_le (d - d'), le_abs_self (d - d')]

lemma phis_lip (hE : IsIntermEq M Δb Δs μ V) (d d' : ℝ) :
    |phis M μ V d - phis M μ V d'| ≤ μ.Ns M * |d - d'| := by
  have hD := (E_hD hE).le
  have hnn := hE.2.2.2.1.1
  unfold phis Densities.Ns
  rw [← intervalIntegral.integral_sub (ii_of_intOn hD (intOn_s hE d) le_rfl hD le_rfl)
    (ii_of_intOn hD (intOn_s hE d') le_rfl hD le_rfl), ← intervalIntegral.integral_mul_const]
  refine (intervalIntegral.abs_integral_le_integral_abs hD).trans ?_
  apply intervalIntegral.integral_mono_on hD
  · exact ((ii_of_intOn hD (intOn_s hE d) le_rfl hD le_rfl).sub
      (ii_of_intOn hD (intOn_s hE d') le_rfl hD le_rfl)).abs
  · exact (ii_of_intOn hD (is_ hE) le_rfl hD le_rfl).mul_const _
  intro x hx
  have hb := (hnn x hx).2.1
  rw [← sub_mul, abs_mul, abs_of_nonneg hb, mul_comm]
  apply mul_le_mul_of_nonneg_left _ hb
  rw [abs_le]
  constructor
  · rcases le_total (d - D V x) 0 with h1 | h1 <;> rcases le_total (d' - D V x) 0 with h2 | h2 <;>
      simp only [max_eq_left, max_eq_right, h1, h2] <;>
      linarith [neg_abs_le (d - d'), le_abs_self (d - d')]
  · rcases le_total (d - D V x) 0 with h1 | h1 <;> rcases le_total (d' - D V x) 0 with h2 | h2 <;>
      simp only [max_eq_left, max_eq_right, h1, h2] <;>
      linarith [neg_abs_le (d - d'), le_abs_self (d - d')]

lemma cont_of_lip {g : ℝ → ℝ} {L : ℝ} (h : ∀ d d', |g d - g d'| ≤ L * |d - d'|) :
    Continuous g := by
  have hL : ∀ d d', |g d - g d'| ≤ (max L 0) * |d - d'| := fun d d' =>
    (h d d').trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  have : LipschitzWith (Real.toNNReal (max L 0)) g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (le_max_right _ _)]
    exact hL x y
  exact this.continuous

lemma Vs_cont (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) :
    ContinuousOn V.Vs (Icc 0 M.Δbar) := by
  have hk := kr_pos hM
  have hc : ContinuousOn (fun Δ => (1 + Δ - M.c + M.lam * (1 - M.η) * phib M μ V (D V Δ)
      + M.κ * M.E V.V1) / (M.κ + M.r)) (Icc 0 M.Δbar) := by
    apply ContinuousOn.div_const
    exact (((continuousOn_const.add continuousOn_id).sub continuousOn_const).add
      (continuousOn_const.mul ((cont_of_lip (phib_lip hE)).comp_continuousOn (D_cont hM hE)))).add
      continuousOn_const
  refine hc.congr (fun Δ hΔ => ?_)
  simp only
  rw [eq_div_iff hk.ne', mul_comm]; exact (bell hE hΔ).2.1

lemma Vb_cont (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) :
    ContinuousOn V.Vb (Icc 0 M.Δbar) := by
  have hk := kr_pos hM
  have hc : ContinuousOn (fun Δ => (-M.c + M.lam * M.η * phis M μ V (D V Δ)
      + M.κ * M.E V.V0) / (M.κ + M.r)) (Icc 0 M.Δbar) := by
    apply ContinuousOn.div_const
    exact ((continuousOn_const.add
      (continuousOn_const.mul ((cont_of_lip (phis_lip hE)).comp_continuousOn (D_cont hM hE))))).add
      continuousOn_const
  refine hc.congr (fun Δ hΔ => ?_)
  simp only
  rw [eq_div_iff hk.ne', mul_comm]; exact (bell hE hΔ).2.2.2

lemma Vh_cont (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) :
    ContinuousOn V.Vh (Icc 0 M.Δbar) := by
  have hc : ContinuousOn (fun Δ => (1 + Δ + M.κ * M.E V.V1) / (M.κ + M.r)) (Icc 0 M.Δbar) := by
    apply ContinuousOn.div_const; fun_prop
  exact hc.congr (fun Δ hΔ => Vh_eq hM hE hΔ)

lemma Vn_cont (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) :
    ContinuousOn V.Vn (Icc 0 M.Δbar) :=
  continuousOn_const.congr (fun Δ hΔ => Vn_eq hM hE hΔ)

/-- Closure principle: a continuous inequality on `[a, b)` extends to `b`. -/
lemma le_at_right {g h : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hg : ContinuousOn g (Icc a b))
    (hh : ContinuousOn h (Icc a b)) (hle : ∀ x ∈ Ico a b, g x ≤ h x) : g b ≤ h b := by
  have hT : IsClosed (Icc a b ∩ (fun x => h x - g x) ⁻¹' Ici 0) :=
    ContinuousOn.preimage_isClosed_of_isClosed (hh.sub hg) isClosed_Icc isClosed_Ici
  have hsub : Ico a b ⊆ Icc a b ∩ (fun x => h x - g x) ⁻¹' Ici 0 := fun x hx =>
    ⟨Ico_subset_Icc_self hx, by simp only [mem_preimage, mem_Ici, sub_nonneg]; exact hle x hx⟩
  have hmem : b ∈ closure (Ico a b) := by rw [closure_Ico hab.ne]; exact ⟨hab.le, le_rfl⟩
  have := (hT.closure_subset_iff.2 hsub) hmem
  simp only [mem_inter_iff, mem_preimage, mem_Ici, sub_nonneg] at this
  exact this.2

lemma le_at_left {g h : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hg : ContinuousOn g (Icc a b))
    (hh : ContinuousOn h (Icc a b)) (hle : ∀ x ∈ Ioc a b, g x ≤ h x) : g a ≤ h a := by
  have hT : IsClosed (Icc a b ∩ (fun x => h x - g x) ⁻¹' Ici 0) :=
    ContinuousOn.preimage_isClosed_of_isClosed (hh.sub hg) isClosed_Icc isClosed_Ici
  have hsub : Ioc a b ⊆ Icc a b ∩ (fun x => h x - g x) ⁻¹' Ici 0 := fun x hx =>
    ⟨Ioc_subset_Icc_self hx, by simp only [mem_preimage, mem_Ici, sub_nonneg]; exact hle x hx⟩
  have hmem : a ∈ closure (Ioc a b) := by rw [closure_Ioc hab.ne]; exact ⟨le_rfl, hab.le⟩
  have := (hT.closure_subset_iff.2 hsub) hmem
  simp only [mem_inter_iff, mem_preimage, mem_Ici, sub_nonneg] at this
  exact this.2

/-- Indifference at the buyer cutoff: `Vb(∆b) = Vn`. -/
lemma indiff_b (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) : V.Vb Δb = V.Vn Δb := by
  obtain ⟨h0, h1, h2, -, -, hO⟩ := id hE
  have hsub1 : Icc 0 Δb ⊆ Icc 0 M.Δbar := Icc_subset_Icc le_rfl (by linarith)
  have hsub2 : Icc Δb M.Δbar ⊆ Icc 0 M.Δbar := Icc_subset_Icc h0.le le_rfl
  apply le_antisymm
  · exact le_at_right h0 ((Vb_cont hM hE).mono hsub1) ((Vn_cont hM hE).mono hsub1)
      (fun x hx => hO.1 x hx)
  · exact le_at_left (by linarith) ((Vn_cont hM hE).mono hsub2) ((Vb_cont hM hE).mono hsub2)
      (fun x hx => hO.2.1 x hx)

/-- Indifference at the seller cutoff: `Vs(∆s) = Vh(∆s)`. -/
lemma indiff_s (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) : V.Vs Δs = V.Vh Δs := by
  obtain ⟨h0, h1, h2, -, -, hO⟩ := id hE
  have hsub1 : Icc 0 Δs ⊆ Icc 0 M.Δbar := Icc_subset_Icc le_rfl h2.le
  have hsub2 : Icc Δs M.Δbar ⊆ Icc 0 M.Δbar := Icc_subset_Icc (by linarith) le_rfl
  apply le_antisymm
  · exact le_at_left h2 ((Vs_cont hM hE).mono hsub2) ((Vh_cont hM hE).mono hsub2)
      (fun x hx => hO.2.2.2 x hx)
  · exact le_at_right (by linarith) ((Vh_cont hM hE).mono hsub1) ((Vs_cont hM hE).mono hsub1)
      (fun x hx => hO.2.2.1 x hx)

end B

end OTCAux


open Set MeasureTheory OTCChain.Equilibrium

namespace OTCAux

section C

variable {M : Params} {Δb Δs : ℝ} {μ : Densities} {V : Values}

lemma eq_at_right {g h : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hg : ContinuousOn g (Icc a b))
    (hh : ContinuousOn h (Icc a b)) (he : ∀ x ∈ Ico a b, g x = h x) : g b = h b :=
  le_antisymm (le_at_right hab hg hh (fun x hx => (he x hx).le))
    (le_at_right hab hh hg (fun x hx => (he x hx).ge))

lemma eq_at_left {g h : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hg : ContinuousOn g (Icc a b))
    (hh : ContinuousOn h (Icc a b)) (he : ∀ x ∈ Ioc a b, g x = h x) : g a = h a :=
  le_antisymm (le_at_left hab hg hh (fun x hx => (he x hx).le))
    (le_at_left hab hh hg (fun x hx => (he x hx).ge))

lemma Nb_nonneg (hE : IsIntermEq M Δb Δs μ V) : 0 ≤ μ.Nb M :=
  intervalIntegral.integral_nonneg (E_hD hE).le (fun u hu => (hE.2.2.2.1.1 u hu).1)

lemma Ns_nonneg (hE : IsIntermEq M Δb Δs μ V) : 0 ≤ μ.Ns M :=
  intervalIntegral.integral_nonneg (E_hD hE).le (fun u hu => (hE.2.2.2.1.1 u hu).2.1)

/-- Below the buyer cutoff `D` is affine with slope `1/(κ + r + λ(1 − η) N_b)`. -/
lemma D_low (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) :
    ∃ C, ∀ x ∈ Icc 0 Δb, D V x = (x + C) / (M.κ + M.r + M.lam * (1 - M.η) * μ.Nb M) := by
  obtain ⟨h0, h1, h2, -⟩ := id hE
  have hk := kr_pos hM
  have hl : 0 ≤ M.lam * (1 - M.η) := mul_nonneg hM.2.2.1.le (by linarith [hM.2.2.2.2.2.2.1])
  have hden : 0 < M.κ + M.r + M.lam * (1 - M.η) * μ.Nb M := by
    have := Nb_nonneg hE; positivity
  set vn := M.κ * M.E V.V0 / (M.κ + M.r)
  set C := 1 - M.c + M.lam * (1 - M.η) * ((∫ x in (0:ℝ)..M.Δbar, D V x * μ.μb x) + μ.Nb M * vn)
    + M.κ * M.E V.V1 - (M.κ + M.r + M.lam * (1 - M.η) * μ.Nb M) * vn
  refine ⟨C, ?_⟩
  have hopen : ∀ x ∈ Ico 0 Δb, D V x = (x + C) / (M.κ + M.r + M.lam * (1 - M.η) * μ.Nb M) := by
    intro x hx
    have hxI : x ∈ Icc 0 M.Δbar := ⟨hx.1, by linarith [hx.2]⟩
    have e9 := (bell hE hxI).2.1
    rw [phib_low hM hE hxI hx.2.le] at e9
    have hDx : D V x = V.Vs x - vn := by
      unfold D; rw [V1_Vs hE ⟨hx.1, by linarith [hx.2]⟩, V0_Vn hE hx, Vn_eq hM hE hxI]
    rw [hDx] at e9 ⊢
    rw [eq_div_iff hden.ne']
    simp only [C]
    linear_combination e9
  intro x hx
  rcases hx.2.lt_or_eq with h | h
  · exact hopen x ⟨hx.1, h⟩
  · subst h
    exact eq_at_right h0 ((D_cont hM hE).mono (Icc_subset_Icc le_rfl (by linarith)))
      (by apply ContinuousOn.div_const; fun_prop) hopen

/-- Above the seller cutoff `D` is affine with slope `1/(κ + r + λη N_s)`. -/
lemma D_high (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) :
    ∃ C, ∀ x ∈ Icc Δs M.Δbar, D V x = (x + C + 1) / (M.κ + M.r + M.lam * M.η * μ.Ns M) := by
  obtain ⟨h0, h1, h2, -⟩ := id hE
  have hk := kr_pos hM
  have hl : 0 ≤ M.lam * M.η := mul_nonneg hM.2.2.1.le hM.2.2.2.2.2.1.le
  have hden : 0 < M.κ + M.r + M.lam * M.η * μ.Ns M := by
    have := Ns_nonneg hE; positivity
  set C := M.κ * M.E V.V1 + M.c + M.lam * M.η * (∫ x in (0:ℝ)..M.Δbar, D V x * μ.μs x)
    - M.κ * M.E V.V0 + 1
  refine ⟨C - 1, ?_⟩
  have hopen : ∀ x ∈ Ioc Δs M.Δbar, D V x = (x + (C - 1) + 1) / (M.κ + M.r + M.lam * M.η * μ.Ns M) := by
    intro x hx
    have hxI : x ∈ Icc 0 M.Δbar := ⟨by linarith [hx.1], hx.2⟩
    have e11 := (bell hE hxI).2.2.2
    rw [phis_high hM hE hxI hx.1.le] at e11
    have hVh := Vh_eq hM hE hxI
    have hDx : D V x = V.Vh x - V.Vb x := by
      unfold D; rw [V1_Vh hE hx, V0_Vb hE ⟨by linarith [hx.1], hx.2⟩]
    rw [hDx] at e11 ⊢
    rw [eq_div_iff hden.ne']
    rw [eq_div_iff hk.ne'] at hVh
    simp only [C]
    linear_combination hVh - e11
  intro x hx
  rcases hx.1.lt_or_eq with h | h
  · exact hopen x ⟨h, hx.2⟩
  · subst h
    exact eq_at_left h2 ((D_cont hM hE).mono (Icc_subset_Icc (by linarith) le_rfl))
      (by apply ContinuousOn.div_const; fun_prop) hopen


/-- The buyer cutoff solves (20). -/
lemma cutoff_b (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) : rhs20 M Δb = M.c := by
  obtain ⟨h0, h1, h2, hSS, -⟩ := id hE
  have hk := kr_pos hM
  have hbI : Δb ∈ Icc 0 M.Δbar := ⟨h0.le, by linarith⟩
  obtain ⟨-, -, e10, e11⟩ := bell hE hbI
  have hind := indiff_b hM hE
  have hc : M.c = M.lam * M.η * phis M μ V (D V Δb) := by
    rw [hind] at e11; linarith
  rw [phis_eq hM hE hbI] at hc
  obtain ⟨C, hC⟩ := D_low hM hE
  set den := M.κ + M.r + M.lam * (1 - M.η) * μ.Nb M
  have hNb := Nb_nonneg hE
  have hl : 0 ≤ M.lam * (1 - M.η) := mul_nonneg hM.2.2.1.le (by linarith [hM.2.2.2.2.2.2.1])
  have hden : 0 < den := by positivity
  have hkn : 0 < M.κ + M.lam * μ.Nb M := by linarith [mul_nonneg hM.2.2.1.le hNb, hM.2.2.2.1]
  set K := M.κ * M.X / ((M.κ + M.lam * μ.Nb M) * den)
  have hint : ∫ x in (0:ℝ)..Δb, (D V Δb - D V x) * μ.μs x
      = ∫ x in (0:ℝ)..Δb, K * ((Δb - x) * M.f x) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume Δb] with x hx1 hx
    rw [uIoc_of_le h0.le] at hx
    have hxo : x ∈ Ico 0 Δb := ⟨hx.1.le, lt_of_le_of_ne hx.2 hx1⟩
    rw [hC Δb ⟨h0.le, le_rfl⟩, hC x ⟨hxo.1, hxo.2.le⟩,
      (eq_55_57 M hM Δb Δs h0 h1 h2 μ hSS x hxo).2.2.2]
    simp only [K]
    field_simp
    ring
  rw [hint, intervalIntegral.integral_const_mul, int_lin_low M hM h0.le hbI.2] at hc
  rw [rhs20_eq]
  unfold P20
  rw [← (eq_65_66_Nb M hM Δb Δs h0 h1 h2 μ hSS).2, hc]
  simp only [K, den]
  field_simp

/-- The seller cutoff solves (21). -/
lemma cutoff_s (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) : rhs21 M Δs = M.c := by
  obtain ⟨h0, h1, h2, hSS, -⟩ := id hE
  have hk := kr_pos hM
  have hsI : Δs ∈ Icc 0 M.Δbar := ⟨by linarith, h2.le⟩
  obtain ⟨e8, e9, -, -⟩ := bell hE hsI
  have hind := indiff_s hM hE
  have hc : M.c = M.lam * (1 - M.η) * phib M μ V (D V Δs) := by
    rw [hind] at e9; linarith
  rw [phib_eq hM hE hsI] at hc
  obtain ⟨C, hC⟩ := D_high hM hE
  set den := M.κ + M.r + M.lam * M.η * μ.Ns M
  have hNs := Ns_nonneg hE
  have hl : 0 ≤ M.lam * M.η := mul_nonneg hM.2.2.1.le hM.2.2.2.2.2.1.le
  have hden : 0 < den := by positivity
  have hkn : 0 < M.κ + M.lam * μ.Ns M := by linarith [mul_nonneg hM.2.2.1.le hNs, hM.2.2.2.1]
  set K := M.κ * (M.N - M.X) / ((M.κ + M.lam * μ.Ns M) * den)
  have hint : ∫ x in Δs..M.Δbar, (D V x - D V Δs) * μ.μb x
      = ∫ x in Δs..M.Δbar, K * ((x - Δs) * M.f x) := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    rw [uIoc_of_le h2.le] at hx
    rw [hC Δs ⟨le_rfl, h2.le⟩, hC x ⟨hx.1.le, hx.2⟩,
      (eq_61_63 M hM Δb Δs h0 h1 h2 μ hSS x hx).2.2.1]
    simp only [K]
    field_simp
    ring
  rw [hint, intervalIntegral.integral_const_mul, int_lin_high M hM hsI.1 hsI.2] at hc
  rw [rhs21_eq]
  unfold P21
  rw [← (eq_64_Ns M hM Δb Δs h0 h1 h2 μ hSS).2, hc]
  simp only [K, den]
  field_simp

end C

end OTCAux


open Set OTCChain.Equilibrium

theorem solution (M : Params) (hM : M.Standing) :
    rhs20 M 0 = 0 ∧ MonotoneOn (rhs20 M) (Icc 0 M.Δbar) ∧
    (∀ c : ℝ, 0 < c → c ≤ rhs20 M M.Δbar → ∃! δ, δ ∈ Icc 0 M.Δbar ∧ rhs20 M δ = c) ∧
    (0 < M.c → M.c < cStar M → ∀ (Δb Δs : ℝ) (μ : Densities) (V : Values),
      IsIntermEq M Δb Δs μ V → rhs20 M Δb = M.c) :=
  ⟨OTCAux.rhs20_zero M, fun _ ha _ hb hab => OTCAux.rhs20_mono M hM ha.1 hab hb.2,
    fun c hc hcb => OTCAux.rhs20_unique M hM c hc hcb,
    fun _ _ _ _ _ _ hE => OTCAux.cutoff_b hM hE⟩
