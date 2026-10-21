-- Prove2me | solution 1 for OTCChain.Equilibrium.eq_79_82
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T22:46:50.110992+00:00
-- url     : https://prove2.me/submissions/b177176b-762a-4886-9c75-eb30c504275f

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

namespace OTCAux

variable (M : Params)

/-- Integration by parts of a primitive against `dF = f dx`. -/
lemma int_prim_mul_f (hM : M.Standing) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ M.Δbar)
    {k : ℝ → ℝ} (hk : IntervalIntegrable k volume a b) :
    ∫ x in a..b, (∫ t in a..x, k t) * M.f x
      = (∫ t in a..b, k t) * M.F b - ∫ x in a..b, k x * M.F x := by
  have hG := hk.absolutelyContinuousOnInterval_intervalIntegral (c := a) left_mem_uIcc
  have key := hG.integral_mul_deriv_eq_deriv_mul (F_ac M hM ha hab hb)
  simp only [intervalIntegral.integral_same, zero_mul, sub_zero] at key
  have e1 : ∫ x in a..b, (∫ t in a..x, k t) * M.f x
      = ∫ x in a..b, (∫ t in a..x, k t) * deriv M.F x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [F_ae_deriv M hM (ha.trans hab) hb] with x hx hxm
    have hx' : x ∈ uIcc 0 b := by
      rw [uIoc_of_le hab] at hxm
      rw [uIcc_of_le (ha.trans hab)]
      exact ⟨ha.trans hxm.1.le, hxm.2⟩
    rw [(hx hx').deriv]
  have e2 : ∫ x in a..b, deriv (fun x => ∫ t in a..x, k t) x * M.F x
      = ∫ x in a..b, k x * M.F x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hk.ae_hasDerivAt_integral] with x hx hxm
    rw [(hx (uIoc_subset_uIcc hxm) a left_mem_uIcc).deriv]
  rw [e1, key, e2]

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


open Set MeasureTheory OTCChain.Equilibrium Filter Topology

namespace OTCAux

section D

variable {M : Params} {Δb Δs : ℝ} {μ : Densities} {V : Values}

/-- Tail mass of buyers `T(y) = ∫_y^∆̄ μb`. -/
noncomputable def Tb (M : Params) (μ : Densities) (y : ℝ) : ℝ := ∫ x in y..M.Δbar, μ.μb x

lemma Tb_eq (hE : IsIntermEq M Δb Δs μ V) {y : ℝ} (hy : y ∈ Icc 0 M.Δbar) :
    Tb M μ y = μ.Nb M - μ.Fb y := by
  have hD := (E_hD hE).le
  unfold Tb Densities.Nb Densities.Fb
  rw [← intervalIntegral.integral_add_adjacent_intervals (ii_of_intOn hD (ib hE) le_rfl hy.1 hy.2)
    (ii_of_intOn hD (ib hE) hy.1 hy.2 le_rfl)]
  ring

lemma Tb_sub (hE : IsIntermEq M Δb Δs μ V) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ M.Δbar) : Tb M μ a - Tb M μ b = ∫ x in a..b, μ.μb x := by
  have hD := (E_hD hE).le
  unfold Tb
  rw [← intervalIntegral.integral_add_adjacent_intervals (ii_of_intOn hD (ib hE) ha hab hb)
    (ii_of_intOn hD (ib hE) (ha.trans hab) hb le_rfl)]
  ring

lemma Fs_sub (hE : IsIntermEq M Δb Δs μ V) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ M.Δbar) : μ.Fs b - μ.Fs a = ∫ x in a..b, μ.μs x := by
  have hD := (E_hD hE).le
  unfold Densities.Fs
  exact intervalIntegral.integral_interval_sub_left
    (ii_of_intOn hD (is_ hE) le_rfl (ha.trans hab) hb) (ii_of_intOn hD (is_ hE) le_rfl ha (hab.trans hb))

lemma intOn_Dsub (hE : IsIntermEq M Δb Δs μ V) {g : ℝ → ℝ} (hg : IntegrableOn g (Icc 0 M.Δbar))
    (c : ℝ) : IntegrableOn (fun x => (D V x - c) * g x) (Icc 0 M.Δbar) := by
  have := (intOn_Dmul hE hg).sub (hg.const_mul c)
  exact IntegrableOn.congr_fun this (fun x _ => by simp only [Pi.sub_apply]; ring) measurableSet_Icc

lemma intOn_subD (hE : IsIntermEq M Δb Δs μ V) {g : ℝ → ℝ} (hg : IntegrableOn g (Icc 0 M.Δbar))
    (c : ℝ) : IntegrableOn (fun x => (c - D V x) * g x) (Icc 0 M.Δbar) := by
  have := (hg.const_mul c).sub (intOn_Dmul hE hg)
  exact IntegrableOn.congr_fun this (fun x _ => by simp only [Pi.sub_apply]; ring) measurableSet_Icc

/-- Bracket for `φb` between two types `a < b`. -/
lemma phib_bracket (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ M.Δbar) :
    (D V b - D V a) * Tb M μ b ≤ phib M μ V (D V a) - phib M μ V (D V b) ∧
    phib M μ V (D V a) - phib M μ V (D V b) ≤ (D V b - D V a) * Tb M μ a := by
  have hD := (E_hD hE).le
  have hnn := hE.2.2.2.1.1
  have haI : a ∈ Icc 0 M.Δbar := ⟨ha, hab.le.trans hb⟩
  have hbI : b ∈ Icc 0 M.Δbar := ⟨ha.trans hab.le, hb⟩
  have hDab := (D_strict hM hE haI hbI hab).1
  rw [phib_eq hM hE haI, phib_eq hM hE hbI]
  have i1 := intOn_Dsub hE (ib hE) (D V a)
  have i2 := intOn_Dsub hE (ib hE) (D V b)
  rw [← intervalIntegral.integral_add_adjacent_intervals (ii_of_intOn hD i1 ha hab.le hb)
    (ii_of_intOn hD i1 (ha.trans hab.le) hb le_rfl)]
  have hsplit : (∫ x in b..M.Δbar, (D V x - D V a) * μ.μb x)
      - ∫ x in b..M.Δbar, (D V x - D V b) * μ.μb x = (D V b - D V a) * Tb M μ b := by
    rw [← intervalIntegral.integral_sub (ii_of_intOn hD i1 (ha.trans hab.le) hb le_rfl)
      (ii_of_intOn hD i2 (ha.trans hab.le) hb le_rfl), Tb, ← intervalIntegral.integral_const_mul]
    congr 1; ext x; ring
  have hmid0 : 0 ≤ ∫ x in a..b, (D V x - D V a) * μ.μb x :=
    intervalIntegral.integral_nonneg hab.le (fun x hx => mul_nonneg
      (by linarith [D_mono_le hM hE haI ⟨ha.trans hx.1, hx.2.trans hb⟩ hx.1])
      (hnn x ⟨ha.trans hx.1, hx.2.trans hb⟩).1)
  have hmid1 : ∫ x in a..b, (D V x - D V a) * μ.μb x ≤ (D V b - D V a) * (Tb M μ a - Tb M μ b) := by
    rw [Tb_sub hE ha hab.le hb, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hab.le (ii_of_intOn hD i1 ha hab.le hb)
      ((ii_of_intOn hD (ib hE) ha hab.le hb).const_mul _)
    intro x hx
    have hxI : x ∈ Icc 0 M.Δbar := ⟨ha.trans hx.1, hx.2.trans hb⟩
    exact mul_le_mul_of_nonneg_right (by linarith [D_mono_le hM hE hxI hbI hx.2]) (hnn x hxI).1
  constructor <;> nlinarith

/-- Bracket for `φs` between two types `a < b`. -/
lemma phis_bracket (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ M.Δbar) :
    (D V b - D V a) * μ.Fs a ≤ phis M μ V (D V b) - phis M μ V (D V a) ∧
    phis M μ V (D V b) - phis M μ V (D V a) ≤ (D V b - D V a) * μ.Fs b := by
  have hD := (E_hD hE).le
  have hnn := hE.2.2.2.1.1
  have haI : a ∈ Icc 0 M.Δbar := ⟨ha, hab.le.trans hb⟩
  have hbI : b ∈ Icc 0 M.Δbar := ⟨ha.trans hab.le, hb⟩
  rw [phis_eq hM hE haI, phis_eq hM hE hbI]
  have i1 := intOn_subD hE (is_ hE) (D V a)
  have i2 := intOn_subD hE (is_ hE) (D V b)
  rw [← intervalIntegral.integral_add_adjacent_intervals (ii_of_intOn hD i2 le_rfl ha haI.2)
    (ii_of_intOn hD i2 ha hab.le hb)]
  have hsplit : (∫ x in (0:ℝ)..a, (D V b - D V x) * μ.μs x)
      - ∫ x in (0:ℝ)..a, (D V a - D V x) * μ.μs x = (D V b - D V a) * μ.Fs a := by
    rw [← intervalIntegral.integral_sub (ii_of_intOn hD i2 le_rfl ha haI.2)
      (ii_of_intOn hD i1 le_rfl ha haI.2), Densities.Fs, ← intervalIntegral.integral_const_mul]
    congr 1; ext x; ring
  have hmid0 : 0 ≤ ∫ x in a..b, (D V b - D V x) * μ.μs x :=
    intervalIntegral.integral_nonneg hab.le (fun x hx => mul_nonneg
      (by linarith [D_mono_le hM hE ⟨ha.trans hx.1, hx.2.trans hb⟩ hbI hx.2])
      (hnn x ⟨ha.trans hx.1, hx.2.trans hb⟩).2.1)
  have hmid1 : ∫ x in a..b, (D V b - D V x) * μ.μs x ≤ (D V b - D V a) * (μ.Fs b - μ.Fs a) := by
    rw [Fs_sub hE ha hab.le hb, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hab.le (ii_of_intOn hD i2 ha hab.le hb)
      ((ii_of_intOn hD (is_ hE) ha hab.le hb).const_mul _)
    intro x hx
    have hxI : x ∈ Icc 0 M.Δbar := ⟨ha.trans hx.1, hx.2.trans hb⟩
    exact mul_le_mul_of_nonneg_right (by linarith [D_mono_le hM hE haI hxI hx.1]) (hnn x hxI).2.1
  constructor <;> nlinarith

/-- Difference quotients of `φb ∘ D` and `φs ∘ D`. -/
noncomputable def Qb (M : Params) (μ : Densities) (V : Values) (Δ y : ℝ) : ℝ :=
  (phib M μ V (D V Δ) - phib M μ V (D V y)) / (D V y - D V Δ)

noncomputable def Rs (M : Params) (μ : Densities) (V : Values) (Δ y : ℝ) : ℝ :=
  (phis M μ V (D V y) - phis M μ V (D V Δ)) / (D V y - D V Δ)

lemma Qb_bound (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) {Δ y : ℝ}
    (hΔ : Δ ∈ Icc 0 M.Δbar) (hy : y ∈ Icc 0 M.Δbar) (hne : y ≠ Δ) :
    |Qb M μ V Δ y - Tb M μ Δ| ≤ |Tb M μ y - Tb M μ Δ| ∧ 0 ≤ Qb M μ V Δ y := by
  have hT0 : ∀ z ∈ Icc 0 M.Δbar, 0 ≤ Tb M μ z := fun z hz =>
    intervalIntegral.integral_nonneg hz.2 (fun u hu => (hE.2.2.2.1.1 u ⟨hz.1.trans hu.1, hu.2⟩).1)
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨b1, b2⟩ := phib_bracket hM hE hy.1 h hΔ.2
    have hd := (D_strict hM hE hy hΔ h).1
    have hpos : 0 < D V Δ - D V y := by linarith
    have e : Qb M μ V Δ y = (phib M μ V (D V y) - phib M μ V (D V Δ)) / (D V Δ - D V y) := by
      unfold Qb; rw [← neg_sub (D V Δ), div_neg, ← neg_div, neg_sub]
    rw [e]
    have l1 : Tb M μ Δ ≤ (phib M μ V (D V y) - phib M μ V (D V Δ)) / (D V Δ - D V y) := by
      rw [le_div_iff₀ hpos]; linarith
    have l2 : (phib M μ V (D V y) - phib M μ V (D V Δ)) / (D V Δ - D V y) ≤ Tb M μ y := by
      rw [div_le_iff₀ hpos]; linarith
    refine ⟨?_, le_trans (hT0 Δ hΔ) l1⟩
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
  · obtain ⟨b1, b2⟩ := phib_bracket hM hE hΔ.1 h hy.2
    have hd := (D_strict hM hE hΔ hy h).1
    have hpos : 0 < D V y - D V Δ := by linarith
    have l1 : Tb M μ y ≤ Qb M μ V Δ y := by
      unfold Qb; rw [le_div_iff₀ hpos]; linarith
    have l2 : Qb M μ V Δ y ≤ Tb M μ Δ := by
      unfold Qb; rw [div_le_iff₀ hpos]; linarith
    refine ⟨?_, le_trans (hT0 y hy) l1⟩
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith

lemma Rs_bound (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) {Δ y : ℝ}
    (hΔ : Δ ∈ Icc 0 M.Δbar) (hy : y ∈ Icc 0 M.Δbar) (hne : y ≠ Δ) :
    |Rs M μ V Δ y - μ.Fs Δ| ≤ |μ.Fs y - μ.Fs Δ| ∧ 0 ≤ Rs M μ V Δ y := by
  have hF0 : ∀ z ∈ Icc 0 M.Δbar, 0 ≤ μ.Fs z := fun z hz =>
    intervalIntegral.integral_nonneg hz.1 (fun u hu => (hE.2.2.2.1.1 u ⟨hu.1, hu.2.trans hz.2⟩).2.1)
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨b1, b2⟩ := phis_bracket hM hE hy.1 h hΔ.2
    have hd := (D_strict hM hE hy hΔ h).1
    have hpos : 0 < D V Δ - D V y := by linarith
    have e : Rs M μ V Δ y = (phis M μ V (D V Δ) - phis M μ V (D V y)) / (D V Δ - D V y) := by
      unfold Rs; rw [← neg_sub (D V Δ), div_neg, ← neg_div, neg_sub]
    rw [e]
    have l1 : μ.Fs y ≤ (phis M μ V (D V Δ) - phis M μ V (D V y)) / (D V Δ - D V y) := by
      rw [le_div_iff₀ hpos]; linarith
    have l2 : (phis M μ V (D V Δ) - phis M μ V (D V y)) / (D V Δ - D V y) ≤ μ.Fs Δ := by
      rw [div_le_iff₀ hpos]; linarith
    refine ⟨?_, le_trans (hF0 y hy) l1⟩
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  · obtain ⟨b1, b2⟩ := phis_bracket hM hE hΔ.1 h hy.2
    have hd := (D_strict hM hE hΔ hy h).1
    have hpos : 0 < D V y - D V Δ := by linarith
    have l1 : μ.Fs Δ ≤ Rs M μ V Δ y := by
      unfold Rs; rw [le_div_iff₀ hpos]; linarith
    have l2 : Rs M μ V Δ y ≤ μ.Fs y := by
      unfold Rs; rw [div_le_iff₀ hpos]; linarith
    refine ⟨?_, le_trans (hF0 Δ hΔ) l1⟩
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith

lemma Tb_contAt (hE : IsIntermEq M Δb Δs μ V) {Δ : ℝ} (hΔ : Δ ∈ Ioo 0 M.Δbar) :
    ContinuousAt (Tb M μ) Δ := by
  have hD := (E_hD hE).le
  have := intervalIntegral.continuousOn_primitive_interval_left (μ := volume) (f := μ.μb)
    (a := 0) (b := M.Δbar) (by rw [uIcc_of_le hD]; exact ib hE)
  rw [uIcc_of_le hD] at this
  exact this.continuousAt (Icc_mem_nhds hΔ.1 hΔ.2)

lemma Fs_contAt (hE : IsIntermEq M Δb Δs μ V) {Δ : ℝ} (hΔ : Δ ∈ Ioo 0 M.Δbar) :
    ContinuousAt μ.Fs Δ := by
  have hD := (E_hD hE).le
  have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (f := μ.μs)
    (a := 0) (b := M.Δbar) (by rw [uIcc_of_le hD]; exact is_ hE)
  rw [uIcc_of_le hD] at this
  exact this.continuousAt (Icc_mem_nhds hΔ.1 hΔ.2)

lemma tendsto_of_abs_le {q g : ℝ → ℝ} {l : Filter ℝ} {a : ℝ}
    (hb : ∀ᶠ y in l, |q y - a| ≤ |g y - a|) (hg : Tendsto g l (𝓝 a)) : Tendsto q l (𝓝 a) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at hg ⊢
  exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) (by simpa using hb) hg

lemma Qb_tendsto (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) {Δ : ℝ}
    (hΔ : Δ ∈ Ioo 0 M.Δbar) : Tendsto (Qb M μ V Δ) (𝓝[≠] Δ) (𝓝 (Tb M μ Δ)) := by
  have hΔI : Δ ∈ Icc 0 M.Δbar := Ioo_subset_Icc_self hΔ
  refine tendsto_of_abs_le ?_ ((Tb_contAt hE hΔ).tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Icc_mem_nhds hΔ.1 hΔ.2)] with y hy1 hy2
  exact (Qb_bound hM hE hΔI hy2 hy1).1

lemma Rs_tendsto (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) {Δ : ℝ}
    (hΔ : Δ ∈ Ioo 0 M.Δbar) : Tendsto (Rs M μ V Δ) (𝓝[≠] Δ) (𝓝 (μ.Fs Δ)) := by
  have hΔI : Δ ∈ Icc 0 M.Δbar := Ioo_subset_Icc_self hΔ
  refine tendsto_of_abs_le ?_ ((Fs_contAt hE hΔ).tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Icc_mem_nhds hΔ.1 hΔ.2)] with y hy1 hy2
  exact (Rs_bound hM hE hΔI hy2 hy1).1

/-- In the middle region, the slope identity for `D`. -/
lemma D_slope_mid (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) {Δ y : ℝ}
    (hΔ : Δ ∈ Ioo Δb Δs) (hy : y ∈ Ioo Δb Δs) (hne : y ≠ Δ) :
    (D V y - D V Δ) / (y - Δ) = 1 / (M.κ + M.r + M.lam * (1 - M.η) * Qb M μ V Δ y
      + M.lam * M.η * Rs M μ V Δ y) := by
  obtain ⟨h0, h1, h2, -⟩ := id hE
  have hk := kr_pos hM
  have hΔI : Δ ∈ Icc 0 M.Δbar := ⟨by linarith [hΔ.1], by linarith [hΔ.2]⟩
  have hyI : y ∈ Icc 0 M.Δbar := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hDne : D V y - D V Δ ≠ 0 := by
    rcases lt_or_gt_of_ne hne with h | h
    · linarith [(D_strict hM hE hyI hΔI h).1]
    · linarith [(D_strict hM hE hΔI hyI h).1]
  have hQ := (Qb_bound hM hE hΔI hyI hne).2
  have hR := (Rs_bound hM hE hΔI hyI hne).2
  have hl1 : 0 ≤ M.lam * (1 - M.η) := mul_nonneg hM.2.2.1.le (by linarith [hM.2.2.2.2.2.2.1])
  have hl2 : 0 ≤ M.lam * M.η := mul_nonneg hM.2.2.1.le hM.2.2.2.2.2.1.le
  have hden : 0 < M.κ + M.r + M.lam * (1 - M.η) * Qb M μ V Δ y + M.lam * M.η * Rs M μ V Δ y := by
    positivity
  -- D = Vs - Vb in the middle
  have hDm : ∀ z ∈ Ioo Δb Δs, (M.κ + M.r) * D V z = 1 + z + M.lam * (1 - M.η) * phib M μ V (D V z)
      + M.κ * M.E V.V1 - M.lam * M.η * phis M μ V (D V z) - M.κ * M.E V.V0 := by
    intro z hz
    have hzI : z ∈ Icc 0 M.Δbar := ⟨by linarith [hz.1], by linarith [hz.2]⟩
    obtain ⟨-, e9, -, e11⟩ := bell hE hzI
    have : D V z = V.Vs z - V.Vb z := by
      unfold D; rw [V1_Vs hE ⟨by linarith [hz.1], hz.2⟩, V0_Vb hE ⟨hz.1, by linarith [hz.2]⟩]
    rw [show (M.κ + M.r) * D V z = (M.κ + M.r) * V.Vs z - (M.κ + M.r) * V.Vb z by rw [this]; ring,
      e9, e11]; ring
  have eΔ := hDm Δ hΔ
  have ey := hDm y hy
  have hQd : phib M μ V (D V Δ) - phib M μ V (D V y) = Qb M μ V Δ y * (D V y - D V Δ) := by
    unfold Qb; field_simp
  have hRd : phis M μ V (D V y) - phis M μ V (D V Δ) = Rs M μ V Δ y * (D V y - D V Δ) := by
    unfold Rs; field_simp
  have hyΔ : y - Δ ≠ 0 := sub_ne_zero.2 hne
  rw [div_eq_div_iff hyΔ hden.ne']
  linear_combination ey - eΔ - M.lam * (1 - M.η) * hQd - M.lam * M.η * hRd


lemma ev_mid {Δ : ℝ} (hΔ : Δ ∈ Ioo Δb Δs) : ∀ᶠ y in 𝓝[≠] Δ, y ∈ Ioo Δb Δs ∧ y ≠ Δ := by
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioo_mem_nhds hΔ.1 hΔ.2)] with y h1 h2
  exact ⟨h2, h1⟩

/-- The denominator of (77)–(78). -/
noncomputable def denMid (M : Params) (μ : Densities) (Δ : ℝ) : ℝ :=
  M.κ + M.r + M.lam * (1 - M.η) * (μ.Nb M - μ.Fb Δ) + M.lam * M.η * μ.Fs Δ

lemma denMid_pos (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) {Δ : ℝ}
    (hΔ : Δ ∈ Icc 0 M.Δbar) : 0 < denMid M μ Δ := by
  have hk := kr_pos hM
  have hT : 0 ≤ μ.Nb M - μ.Fb Δ := by
    rw [← Tb_eq hE hΔ]
    exact intervalIntegral.integral_nonneg hΔ.2 (fun u hu => (hE.2.2.2.1.1 u ⟨hΔ.1.trans hu.1, hu.2⟩).1)
  have hF : 0 ≤ μ.Fs Δ :=
    intervalIntegral.integral_nonneg hΔ.1 (fun u hu => (hE.2.2.2.1.1 u ⟨hu.1, hu.2.trans hΔ.2⟩).2.1)
  have hl1 : 0 ≤ M.lam * (1 - M.η) := mul_nonneg hM.2.2.1.le (by linarith [hM.2.2.2.2.2.2.1])
  have hl2 : 0 ≤ M.lam * M.η := mul_nonneg hM.2.2.1.le hM.2.2.2.2.2.1.le
  unfold denMid; positivity

lemma Qb_lim (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) {Δ : ℝ} (hΔ : Δ ∈ Ioo Δb Δs) :
    Tendsto (Qb M μ V Δ) (𝓝[≠] Δ) (𝓝 (μ.Nb M - μ.Fb Δ)) := by
  obtain ⟨h0, h1, h2, -⟩ := id hE
  have hΔ' : Δ ∈ Ioo 0 M.Δbar := ⟨by linarith [hΔ.1], by linarith [hΔ.2]⟩
  rw [← Tb_eq hE (Ioo_subset_Icc_self hΔ')]
  exact Qb_tendsto hM hE hΔ'

lemma Rs_lim (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) {Δ : ℝ} (hΔ : Δ ∈ Ioo Δb Δs) :
    Tendsto (Rs M μ V Δ) (𝓝[≠] Δ) (𝓝 (μ.Fs Δ)) := by
  obtain ⟨h0, h1, h2, -⟩ := id hE
  exact Rs_tendsto hM hE ⟨by linarith [hΔ.1], by linarith [hΔ.2]⟩

lemma S_lim (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) {Δ : ℝ} (hΔ : Δ ∈ Ioo Δb Δs) :
    Tendsto (fun y => 1 / (M.κ + M.r + M.lam * (1 - M.η) * Qb M μ V Δ y
      + M.lam * M.η * Rs M μ V Δ y)) (𝓝[≠] Δ) (𝓝 (1 / denMid M μ Δ)) := by
  obtain ⟨h0, h1, h2, -⟩ := id hE
  have hpos := denMid_pos hM hE (Δ := Δ) ⟨by linarith [hΔ.1], by linarith [hΔ.2]⟩
  apply tendsto_const_nhds.div _ hpos.ne'
  exact ((tendsto_const_nhds.add (tendsto_const_nhds.mul (Qb_lim hM hE hΔ))).add
    (tendsto_const_nhds.mul (Rs_lim hM hE hΔ)))

lemma hasDerivAt_D_mid (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) {Δ : ℝ}
    (hΔ : Δ ∈ Ioo Δb Δs) : HasDerivAt (D V) (1 / denMid M μ Δ) Δ := by
  rw [hasDerivAt_iff_tendsto_slope]
  refine (S_lim hM hE hΔ).congr' ?_
  filter_upwards [ev_mid hΔ] with y hy
  rw [slope_def_field]
  exact (D_slope_mid hM hE hΔ hy.1 hy.2).symm

lemma hasDerivAt_Vs_mid (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) {Δ : ℝ}
    (hΔ : Δ ∈ Ioo Δb Δs) : HasDerivAt V.Vs (slopeVsMid M μ Δ) Δ := by
  obtain ⟨h0, h1, h2, -⟩ := id hE
  have hk := kr_pos hM
  have hΔI : Δ ∈ Icc 0 M.Δbar := ⟨by linarith [hΔ.1], by linarith [hΔ.2]⟩
  have hpos := denMid_pos hM hE hΔI
  rw [hasDerivAt_iff_tendsto_slope]
  have hlim : Tendsto (fun y => (1 - M.lam * (1 - M.η) * Qb M μ V Δ y *
      (1 / (M.κ + M.r + M.lam * (1 - M.η) * Qb M μ V Δ y + M.lam * M.η * Rs M μ V Δ y)))
        / (M.κ + M.r)) (𝓝[≠] Δ)
      (𝓝 ((1 - M.lam * (1 - M.η) * (μ.Nb M - μ.Fb Δ) * (1 / denMid M μ Δ)) / (M.κ + M.r))) :=
    ((tendsto_const_nhds.sub ((tendsto_const_nhds.mul (Qb_lim hM hE hΔ)).mul
      (S_lim hM hE hΔ))).div_const _)
  have heq : (1 - M.lam * (1 - M.η) * (μ.Nb M - μ.Fb Δ) * (1 / denMid M μ Δ)) / (M.κ + M.r)
      = slopeVsMid M μ Δ := by
    unfold slopeVsMid; unfold denMid at hpos ⊢
    field_simp
    ring
  rw [← heq]
  refine hlim.congr' ?_
  filter_upwards [ev_mid hΔ] with y hy
  have hyI : y ∈ Icc 0 M.Δbar := ⟨by linarith [hy.1.1], by linarith [hy.1.2]⟩
  have hS := D_slope_mid hM hE hΔ hy.1 hy.2
  rw [slope_def_field, ← hS]
  have eΔ := (bell hE hΔI).2.1
  have ey := (bell hE hyI).2.1
  have hDne : D V y - D V Δ ≠ 0 := by
    rcases lt_or_gt_of_ne hy.2 with h | h
    · linarith [(D_strict hM hE hyI hΔI h).1]
    · linarith [(D_strict hM hE hΔI hyI h).1]
  have hQd : phib M μ V (D V Δ) - phib M μ V (D V y) = Qb M μ V Δ y * (D V y - D V Δ) := by
    unfold Qb; field_simp
  have hyΔ : y - Δ ≠ 0 := sub_ne_zero.2 hy.2
  have key : (M.κ + M.r) * (V.Vs y - V.Vs Δ)
      = (y - Δ) - M.lam * (1 - M.η) * Qb M μ V Δ y * (D V y - D V Δ) := by
    linear_combination ey - eΔ - M.lam * (1 - M.η) * hQd
  have hk' : M.κ + M.r ≠ 0 := hk.ne'
  symm
  calc (V.Vs y - V.Vs Δ) / (y - Δ)
      = ((y - Δ) - M.lam * (1 - M.η) * Qb M μ V Δ y * (D V y - D V Δ)) / ((M.κ + M.r) * (y - Δ)) := by
        rw [← key]; field_simp
    _ = _ := by field_simp; try ring

lemma hasDerivAt_Vb_mid (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) {Δ : ℝ}
    (hΔ : Δ ∈ Ioo Δb Δs) : HasDerivAt V.Vb (slopeVbMid M μ Δ) Δ := by
  obtain ⟨h0, h1, h2, -⟩ := id hE
  have hk := kr_pos hM
  have hΔI : Δ ∈ Icc 0 M.Δbar := ⟨by linarith [hΔ.1], by linarith [hΔ.2]⟩
  have hpos := denMid_pos hM hE hΔI
  rw [hasDerivAt_iff_tendsto_slope]
  have hlim : Tendsto (fun y => M.lam * M.η * Rs M μ V Δ y *
      (1 / (M.κ + M.r + M.lam * (1 - M.η) * Qb M μ V Δ y + M.lam * M.η * Rs M μ V Δ y))
        / (M.κ + M.r)) (𝓝[≠] Δ)
      (𝓝 (M.lam * M.η * μ.Fs Δ * (1 / denMid M μ Δ) / (M.κ + M.r))) :=
    (((tendsto_const_nhds.mul (Rs_lim hM hE hΔ)).mul (S_lim hM hE hΔ)).div_const _)
  have heq : M.lam * M.η * μ.Fs Δ * (1 / denMid M μ Δ) / (M.κ + M.r) = slopeVbMid M μ Δ := by
    unfold slopeVbMid; unfold denMid at hpos ⊢
    field_simp
  rw [← heq]
  refine hlim.congr' ?_
  filter_upwards [ev_mid hΔ] with y hy
  have hyI : y ∈ Icc 0 M.Δbar := ⟨by linarith [hy.1.1], by linarith [hy.1.2]⟩
  have hS := D_slope_mid hM hE hΔ hy.1 hy.2
  rw [slope_def_field, ← hS]
  have eΔ := (bell hE hΔI).2.2.2
  have ey := (bell hE hyI).2.2.2
  have hDne : D V y - D V Δ ≠ 0 := by
    rcases lt_or_gt_of_ne hy.2 with h | h
    · linarith [(D_strict hM hE hyI hΔI h).1]
    · linarith [(D_strict hM hE hΔI hyI h).1]
  have hRd : phis M μ V (D V y) - phis M μ V (D V Δ) = Rs M μ V Δ y * (D V y - D V Δ) := by
    unfold Rs; field_simp
  have hyΔ : y - Δ ≠ 0 := sub_ne_zero.2 hy.2
  have key : (M.κ + M.r) * (V.Vb y - V.Vb Δ)
      = M.lam * M.η * Rs M μ V Δ y * (D V y - D V Δ) := by
    linear_combination ey - eΔ + M.lam * M.η * hRd
  have hk' : M.κ + M.r ≠ 0 := hk.ne'
  symm
  calc (V.Vb y - V.Vb Δ) / (y - Δ)
      = (M.lam * M.η * Rs M μ V Δ y * (D V y - D V Δ)) / ((M.κ + M.r) * (y - Δ)) := by
        rw [← key]; field_simp
    _ = _ := by field_simp; try ring

lemma hasDerivAt_Vs_low (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) {Δ : ℝ}
    (hΔ : Δ ∈ Ioo 0 Δb) : HasDerivAt V.Vs (slopeVsLow M μ) Δ := by
  obtain ⟨h0, h1, h2, -⟩ := id hE
  obtain ⟨C, hC⟩ := D_low hM hE
  set vn := M.κ * M.E V.V0 / (M.κ + M.r)
  set den := M.κ + M.r + M.lam * (1 - M.η) * μ.Nb M
  have hlin : HasDerivAt (fun y => (y + C) / den + vn) (1 / den) Δ := by
    have := (((hasDerivAt_id Δ).add_const C).div_const den).add_const vn
    simpa using this
  refine hlin.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hΔ.1 hΔ.2] with y hy
  have hyI : y ∈ Icc 0 M.Δbar := ⟨hy.1.le, by linarith [hy.2]⟩
  have := hC y ⟨hy.1.le, hy.2.le⟩
  unfold D at this
  rw [V1_Vs hE ⟨hy.1.le, by linarith [hy.2]⟩, V0_Vn hE ⟨hy.1.le, hy.2⟩, Vn_eq hM hE hyI] at this
  linarith

lemma hasDerivAt_Vb_high (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) {Δ : ℝ}
    (hΔ : Δ ∈ Ioo Δs M.Δbar) : HasDerivAt V.Vb (slopeVbHigh M μ) Δ := by
  obtain ⟨h0, h1, h2, -⟩ := id hE
  have hk := kr_pos hM
  obtain ⟨C, hC⟩ := D_high hM hE
  set den := M.κ + M.r + M.lam * M.η * μ.Ns M
  have hden : 0 < den := by
    have := Ns_nonneg hE
    have hl2 : 0 ≤ M.lam * M.η := mul_nonneg hM.2.2.1.le hM.2.2.2.2.2.1.le
    positivity
  have hlin : HasDerivAt (fun y => (1 + y + M.κ * M.E V.V1) / (M.κ + M.r) - (y + C + 1) / den)
      (1 / (M.κ + M.r) - 1 / den) Δ := by
    have a := (((hasDerivAt_id Δ).const_add 1).add_const (M.κ * M.E V.V1)).div_const (M.κ + M.r)
    have b := (((hasDerivAt_id Δ).add_const C).add_const 1).div_const den
    exact a.sub b
  have heq : 1 / (M.κ + M.r) - 1 / den = slopeVbHigh M μ := by
    unfold slopeVbHigh; simp only [den] at hden ⊢; field_simp; ring
  rw [← heq]
  refine hlin.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hΔ.1 hΔ.2] with y hy
  have hyI : y ∈ Icc 0 M.Δbar := ⟨by linarith [hy.1], hy.2.le⟩
  have := hC y ⟨hy.1.le, hy.2.le⟩
  unfold D at this
  rw [V1_Vh hE ⟨hy.1, hy.2.le⟩, V0_Vb hE ⟨by linarith [hy.1], hy.2.le⟩, Vh_eq hM hE hyI] at this
  show V.Vb y = _
  linarith


lemma Fs_contOn (hE : IsIntermEq M Δb Δs μ V) : ContinuousOn μ.Fs (Icc 0 M.Δbar) := by
  have hD := (E_hD hE).le
  have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (f := μ.μs)
    (a := 0) (b := M.Δbar) (by rw [uIcc_of_le hD]; exact is_ hE)
  rw [uIcc_of_le hD] at this
  exact this

lemma Fb_contOn (hE : IsIntermEq M Δb Δs μ V) : ContinuousOn μ.Fb (Icc 0 M.Δbar) := by
  have hD := (E_hD hE).le
  have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (f := μ.μb)
    (a := 0) (b := M.Δbar) (by rw [uIcc_of_le hD]; exact ib hE)
  rw [uIcc_of_le hD] at this
  exact this

lemma slopeVsMid_contOn (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) :
    ContinuousOn (slopeVsMid M μ) (Icc 0 M.Δbar) := by
  unfold slopeVsMid
  apply continuousOn_const.mul
  apply ContinuousOn.div
  · exact continuousOn_const.add (continuousOn_const.mul (Fs_contOn hE))
  · exact (continuousOn_const.add (continuousOn_const.mul (continuousOn_const.sub (Fb_contOn hE)))).add
      (continuousOn_const.mul (Fs_contOn hE))
  · intro z hz; exact (denMid_pos hM hE hz).ne'

lemma slopeVbMid_contOn (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) :
    ContinuousOn (slopeVbMid M μ) (Icc 0 M.Δbar) := by
  unfold slopeVbMid
  apply continuousOn_const.mul
  apply ContinuousOn.div
  · exact continuousOn_const.mul (Fs_contOn hE)
  · exact (continuousOn_const.add (continuousOn_const.mul (continuousOn_const.sub (Fb_contOn hE)))).add
      (continuousOn_const.mul (Fs_contOn hE))
  · intro z hz; exact (denMid_pos hM hE hz).ne'

/-- (83): `S(x, y) = ∫_y^x ξ` on the middle region. -/
lemma surplus_mid (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) {x y : ℝ}
    (hx : x ∈ Ioo Δb Δs) (hy : y ∈ Ioo Δb Δs) :
    surplus V x y = ∫ z in y..x, (slopeVsMid M μ z - slopeVbMid M μ z) := by
  obtain ⟨h0, h1, h2, -⟩ := id hE
  have hsub : uIcc y x ⊆ Ioo Δb Δs := by
    intro z hz
    rw [mem_uIcc] at hz
    rcases hz with hz | hz
    · exact ⟨lt_of_lt_of_le hy.1 hz.1, lt_of_le_of_lt hz.2 hx.2⟩
    · exact ⟨lt_of_lt_of_le hx.1 hz.1, lt_of_le_of_lt hz.2 hy.2⟩
  have hsub2 : uIcc y x ⊆ Icc 0 M.Δbar := fun z hz =>
    ⟨by linarith [(hsub hz).1], by linarith [(hsub hz).2]⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun z => V.Vs z - V.Vb z)
    (fun z hz => (hasDerivAt_Vs_mid hM hE (hsub hz)).sub (hasDerivAt_Vb_mid hM hE (hsub hz)))
    (((slopeVsMid_contOn hM hE).sub (slopeVbMid_contOn hM hE)).mono hsub2).intervalIntegrable,
    surplus_eq]
  have hD : ∀ z ∈ Ioo Δb Δs, D V z = V.Vs z - V.Vb z := by
    intro z hz
    unfold D; rw [V1_Vs hE ⟨by linarith [hz.1], hz.2⟩, V0_Vb hE ⟨hz.1, by linarith [hz.2]⟩]
  rw [hD x hx, hD y hy]

/-- (7): trade iff `x > y`. -/
lemma trade_rule (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V) {x y : ℝ}
    (hx : x ∈ Ioc Δb M.Δbar) (hy : y ∈ Ico 0 Δs) : 0 < surplus V x y ↔ y < x := by
  obtain ⟨h0, h1, h2, -⟩ := id hE
  have hxI : x ∈ Icc 0 M.Δbar := ⟨by linarith [hx.1], hx.2⟩
  have hyI : y ∈ Icc 0 M.Δbar := ⟨hy.1, by linarith [hy.2]⟩
  rw [surplus_eq]
  constructor
  · intro h
    by_contra hc; push Not at hc
    have := D_mono_le hM hE hxI hyI hc
    linarith
  · intro h
    have := (D_strict hM hE hyI hxI h).1
    linarith

end D

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

lemma midB_eq_mB (x : ℝ) : M.N * M.f x / 2 * (1 + (M.N - M.N * M.F x - M.X - M.κ / M.lam
      + 2 * M.κ * (M.N - M.X) / (M.lam * M.N)) /
        Real.sqrt ((M.N - M.N * M.F x - M.X - M.κ / M.lam) ^ 2
          + 4 * (M.κ / M.lam) * (M.N - M.X) * (1 - M.F x))) = mB M x := by
  unfold mB dNb Ry qy kk; unfold Ay; ring

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


open Set MeasureTheory OTCChain.Equilibrium Filter Topology

namespace OTCAux

section H

variable {M : Params} {Δb Δs : ℝ} {μ : Densities}

/-- Every steady state agrees with the candidate densities off the two cutoffs. -/
lemma agree (hM : M.Standing) (h0 : 0 < Δb) (h1 : Δb < Δs) (h2 : Δs < M.Δbar)
    (hSS : IsSteadyState M Δb Δs μ) {x : ℝ} (hx : x ∈ Icc 0 M.Δbar) (hb : x ≠ Δb) (hs : x ≠ Δs) :
    μ.μb x = (candDensities M Δb Δs).μb x ∧ μ.μs x = (candDensities M Δb Δs).μs x := by
  have hNb := (eq_65_66_Nb M hM Δb Δs h0 h1 h2 μ hSS).2
  have hNs := (eq_64_Ns M hM Δb Δs h0 h1 h2 μ hSS).2
  rcases lt_or_gt_of_ne hb with hl | hl
  · obtain ⟨e1, -, -, e4⟩ := eq_55_57 M hM Δb Δs h0 h1 h2 μ hSS x ⟨hx.1, hl⟩
    obtain ⟨c1, c2, -, -⟩ := cand_low M Δb Δs hl h1
    rw [e1, e4, c1, c2, hNb]; exact ⟨rfl, rfl⟩
  · rcases lt_or_gt_of_ne hs with hm | hm
    · obtain ⟨-, -, -, e4, e5⟩ := mid_unique hM h0 h1 h2 hSS x ⟨hl, hm⟩
      obtain ⟨c1, c2, -, -⟩ := cand_mid M Δb Δs hl.le hm
      rw [e5, e4, c1, c2, midB_eq_mB]; exact ⟨rfl, rfl⟩
    · obtain ⟨-, e2, e3, -⟩ := eq_61_63 M hM Δb Δs h0 h1 h2 μ hSS x ⟨hm, hx.2⟩
      obtain ⟨c1, c2, -, -⟩ := cand_high M Δb Δs hm.le h1
      rw [e2, e3, c1, c2, hNs]; exact ⟨rfl, rfl⟩

lemma int_agree {g h : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (he : ∀ x ∈ Icc a b, x ≠ Δb → x ≠ Δs → g x = h x) :
    ∫ x in a..b, g x = ∫ x in a..b, h x := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne volume Δb, Measure.ae_ne volume Δs] with x h1 h2 hx
  rw [uIoc_of_le hab] at hx
  exact he x (Ioc_subset_Icc_self hx) h1 h2

variable (hM : M.Standing) (h0 : 0 < Δb) (h1 : Δb < Δs) (h2 : Δs < M.Δbar)
  (hSS : IsSteadyState M Δb Δs μ)
include hM h0 h1 h2 hSS

lemma agree_Fs {x : ℝ} (hx : x ∈ Icc 0 M.Δbar) : μ.Fs x = (candDensities M Δb Δs).Fs x :=
  int_agree hx.1 (fun z hz hb hs => (agree hM h0 h1 h2 hSS ⟨hz.1, hz.2.trans hx.2⟩ hb hs).2)

lemma agree_Fb {x : ℝ} (hx : x ∈ Icc 0 M.Δbar) : μ.Fb x = (candDensities M Δb Δs).Fb x :=
  int_agree hx.1 (fun z hz hb hs => (agree hM h0 h1 h2 hSS ⟨hz.1, hz.2.trans hx.2⟩ hb hs).1)

lemma agree_Nb : μ.Nb M = (candDensities M Δb Δs).Nb M :=
  int_agree hM.2.2.2.2.2.2.2.2.1.le (fun z hz hb hs => (agree hM h0 h1 h2 hSS hz hb hs).1)

lemma agree_Ns : μ.Ns M = (candDensities M Δb Δs).Ns M :=
  int_agree hM.2.2.2.2.2.2.2.2.1.le (fun z hz hb hs => (agree hM h0 h1 h2 hSS hz hb hs).2)

lemma agree_sVsM {x : ℝ} (hx : x ∈ Icc 0 M.Δbar) :
    slopeVsMid M μ x = slopeVsMid M (candDensities M Δb Δs) x := by
  unfold slopeVsMid
  rw [agree_Fs hM h0 h1 h2 hSS hx, agree_Fb hM h0 h1 h2 hSS hx, agree_Nb hM h0 h1 h2 hSS]

lemma agree_sVbM {x : ℝ} (hx : x ∈ Icc 0 M.Δbar) :
    slopeVbMid M μ x = slopeVbMid M (candDensities M Δb Δs) x := by
  unfold slopeVbMid
  rw [agree_Fs hM h0 h1 h2 hSS hx, agree_Fb hM h0 h1 h2 hSS hx, agree_Nb hM h0 h1 h2 hSS]

lemma agree_sL : slopeVsLow M μ = slopeVsLow M (candDensities M Δb Δs) := by
  unfold slopeVsLow; rw [agree_Nb hM h0 h1 h2 hSS]

lemma agree_sH : slopeVbHigh M μ = slopeVbHigh M (candDensities M Δb Δs) := by
  unfold slopeVbHigh; rw [agree_Ns hM h0 h1 h2 hSS]

end H


section H2

variable {M : Params} {Δb Δs : ℝ} {μ : Densities} {V : Values}
variable (hM : M.Standing) (hE : IsIntermEq M Δb Δs μ V)
include hM hE

lemma Vb_mid_formula {x : ℝ} (hx : x ∈ Icc Δb Δs) :
    V.Vb x = M.κ * M.E V.V0 / (M.κ + M.r) + ∫ z in Δb..x, slopeVbMid M μ z := by
  obtain ⟨h0, h1, h2, -⟩ := id hE
  have hsub : Icc Δb x ⊆ Icc 0 M.Δbar := Icc_subset_Icc h0.le (hx.2.trans h2.le)
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1
    ((Vb_cont hM hE).mono hsub)
    (fun z hz => hasDerivAt_Vb_mid hM hE ⟨hz.1, hz.2.trans_le hx.2⟩)
    (((slopeVbMid_contOn hM hE).mono hsub).intervalIntegrable_of_Icc hx.1)
  rw [this, indiff_b hM hE, Vn_eq hM hE ⟨h0.le, by linarith⟩]
  ring

lemma Vb_high_formula {x : ℝ} (hx : x ∈ Icc Δs M.Δbar) :
    V.Vb x = V.Vb Δs + slopeVbHigh M μ * (x - Δs) := by
  obtain ⟨h0, h1, h2, -⟩ := id hE
  have hsub : Icc Δs x ⊆ Icc 0 M.Δbar := Icc_subset_Icc (by linarith) hx.2
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1
    ((Vb_cont hM hE).mono hsub)
    (fun z hz => hasDerivAt_Vb_high hM hE ⟨hz.1, hz.2.trans_le hx.2⟩)
    (intervalIntegrable_const (c := slopeVbHigh M μ))
  rw [intervalIntegral.integral_const, smul_eq_mul] at this
  linarith

lemma Vs_mid_formula {x : ℝ} (hx : x ∈ Icc Δb Δs) :
    V.Vs x = V.Vs Δb + ∫ z in Δb..x, slopeVsMid M μ z := by
  obtain ⟨h0, h1, h2, -⟩ := id hE
  have hsub : Icc Δb x ⊆ Icc 0 M.Δbar := Icc_subset_Icc h0.le (hx.2.trans h2.le)
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1
    ((Vs_cont hM hE).mono hsub)
    (fun z hz => hasDerivAt_Vs_mid hM hE ⟨hz.1, hz.2.trans_le hx.2⟩)
    (((slopeVsMid_contOn hM hE).mono hsub).intervalIntegrable_of_Icc hx.1)
  linarith

lemma Vs_low_formula {x : ℝ} (hx : x ∈ Icc 0 Δb) :
    V.Vs x = V.Vs Δb + slopeVsLow M μ * (x - Δb) := by
  obtain ⟨h0, h1, h2, -⟩ := id hE
  have hsub : Icc x Δb ⊆ Icc 0 M.Δbar := Icc_subset_Icc hx.1 (by linarith)
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.2
    ((Vs_cont hM hE).mono hsub)
    (fun z hz => hasDerivAt_Vs_low hM hE ⟨hx.1.trans_lt hz.1, hz.2⟩)
    (intervalIntegrable_const (c := slopeVsLow M μ))
  rw [intervalIntegral.integral_const, smul_eq_mul] at this
  linarith

lemma V0_formula {x : ℝ} (hx : x ∈ Icc 0 M.Δbar) :
    V.V0 x = if x ≤ Δb then M.κ * M.E V.V0 / (M.κ + M.r) else V.Vb x := by
  obtain ⟨h0, h1, h2, -⟩ := id hE
  split_ifs with h
  · rcases h.lt_or_eq with h' | h'
    · rw [V0_Vn hE ⟨hx.1, h'⟩, Vn_eq hM hE hx]
    · subst h'
      show max (V.Vn _) (V.Vb _) = _
      rw [indiff_b hM hE, max_self, Vn_eq hM hE hx]
  · exact V0_Vb hE ⟨not_le.1 h, hx.2⟩

lemma V1_formula {x : ℝ} (hx : x ∈ Icc 0 M.Δbar) :
    V.V1 x = if x ≤ Δs then V.Vs x else V.Vh x := by
  obtain ⟨h0, h1, h2, -⟩ := id hE
  split_ifs with h
  · rcases h.lt_or_eq with h' | h'
    · exact V1_Vs hE ⟨hx.1, h'⟩
    · subst h'
      show max (V.Vh _) (V.Vs _) = _
      rw [indiff_s hM hE, max_self]
  · exact V1_Vh hE ⟨not_le.1 h, hx.2⟩

lemma V0_bdd_int : IntegrableOn (fun x => V.V0 x * M.f x) (Icc 0 M.Δbar) := by
  obtain ⟨B, -, hB⟩ := bound hE
  obtain ⟨-, -, -, -, ⟨-, -, -, hn, hb, -⟩, -⟩ := id hE
  refine Integrable.bdd_mul (c := B) hM.2.2.2.2.2.2.2.2.2.2.1 (hn.sup hb) ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  obtain ⟨-, -, h3, h4⟩ := hB x hx
  rw [Real.norm_eq_abs]
  show |max (V.Vn x) (V.Vb x)| ≤ B
  rw [abs_le] at *
  constructor
  · linarith [le_max_left (V.Vn x) (V.Vb x)]
  · exact max_le h3.2 h4.2

lemma V1_bdd_int : IntegrableOn (fun x => V.V1 x * M.f x) (Icc 0 M.Δbar) := by
  obtain ⟨B, -, hB⟩ := bound hE
  obtain ⟨-, -, -, -, ⟨-, hh, hs, -, -, -⟩, -⟩ := id hE
  refine Integrable.bdd_mul (c := B) hM.2.2.2.2.2.2.2.2.2.2.1 (hh.sup hs) ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  obtain ⟨h1, h2, -, -⟩ := hB x hx
  rw [Real.norm_eq_abs]
  show |max (V.Vh x) (V.Vs x)| ≤ B
  rw [abs_le] at *
  constructor
  · linarith [le_max_left (V.Vh x) (V.Vs x)]
  · exact max_le h1.2 h2.2

lemma split3c {g : ℝ → ℝ} (hg : IntegrableOn g (Icc 0 M.Δbar)) :
    ∫ x in (0:ℝ)..M.Δbar, g x
      = (∫ x in (0:ℝ)..Δb, g x) + (∫ x in Δb..Δs, g x) + ∫ x in Δs..M.Δbar, g x := by
  obtain ⟨h0, h1, h2, -⟩ := id hE
  have ii : ∀ a b, 0 ≤ a → a ≤ b → b ≤ M.Δbar → IntervalIntegrable g volume a b := by
    intro a b ha hab hb
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact hg.mono_set (Icc_subset_Icc ha hb)
  rw [← intervalIntegral.integral_add_adjacent_intervals (ii 0 Δb le_rfl h0.le (by linarith))
    (ii Δb M.Δbar h0.le (by linarith) le_rfl),
    ← intervalIntegral.integral_add_adjacent_intervals (ii Δb Δs h0.le h1.le h2.le)
    (ii Δs M.Δbar (by linarith) h2.le le_rfl)]
  ring

lemma prim_contOn' {k : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hk : ContinuousOn k (Icc a b)) :
    ContinuousOn (fun x => ∫ t in a..x, k t) (Icc a b) := by
  have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (f := k) (a := a) (b := b)
    (by rw [uIcc_of_le hab]; exact hk.integrableOn_Icc)
  rwa [uIcc_of_le hab] at this

/-- The closed form of `Vn`. -/
lemma Vn_closed : M.κ * M.E V.V0 / (M.κ + M.r) =
    M.κ / M.r * ((∫ z in Δb..Δs, slopeVbMid M μ z) - ∫ z in Δb..Δs, slopeVbMid M μ z * M.F z)
    + M.κ / M.r * slopeVbHigh M μ * J M Δs := by
  obtain ⟨h0, h1, h2, -⟩ := id hE
  have hk := kr_pos hM
  have hr := hM.2.2.2.2.1
  set vn := M.κ * M.E V.V0 / (M.κ + M.r) with hvn
  set G := fun x => ∫ z in Δb..x, slopeVbMid M μ z with hG
  have hsubm : Icc Δb Δs ⊆ Icc 0 M.Δbar := Icc_subset_Icc h0.le h2.le
  have hcm := (slopeVbMid_contOn hM hE).mono hsubm
  have hGc : ContinuousOn G (Icc Δb Δs) := prim_contOn' hM hE h1.le hcm
  have hE0 : M.E V.V0 = ∫ x in (0:ℝ)..M.Δbar, V.V0 x * M.f x := rfl
  rw [split3c hM hE (V0_bdd_int hM hE)] at hE0
  have p1 : ∫ x in (0:ℝ)..Δb, V.V0 x * M.f x = vn * M.F Δb := by
    rw [intervalIntegral.integral_congr (g := fun x => vn * M.f x), int_cf M hM le_rfl h0.le
      (by linarith), F_zero, sub_zero]
    intro x hx
    rw [uIcc_of_le h0.le] at hx
    simp only
    rw [V0_formula hM hE ⟨hx.1, by linarith [hx.2]⟩, if_pos hx.2]
  have p2 : ∫ x in Δb..Δs, V.V0 x * M.f x
      = vn * (M.F Δs - M.F Δb) + (G Δs * M.F Δs - ∫ x in Δb..Δs, slopeVbMid M μ x * M.F x) := by
    rw [intervalIntegral.integral_congr (g := fun x => vn * M.f x + G x * M.f x)]
    · rw [intervalIntegral.integral_add ((ii_Icc h1.le (f_intOn M hM h0.le h2.le)).const_mul _)
        (ii_Icc h1.le (IntegrableOn.continuousOn_mul hGc (f_intOn M hM h0.le h2.le) isCompact_Icc)),
        int_cf M hM h0.le h1.le h2.le, int_prim_mul_f M hM h0.le h1.le h2.le
          (hcm.intervalIntegrable_of_Icc h1.le)]
    intro x hx
    rw [uIcc_of_le h1.le] at hx
    simp only
    rw [V0_formula hM hE ⟨h0.le.trans hx.1, hx.2.trans h2.le⟩]
    split_ifs with h
    · have : x = Δb := le_antisymm h hx.1
      subst this; simp only [G, intervalIntegral.integral_same]; ring
    · rw [Vb_mid_formula hM hE hx]; ring
  have hVbs : V.Vb Δs = vn + G Δs := Vb_mid_formula hM hE ⟨h1.le, le_rfl⟩
  have p3 : ∫ x in Δs..M.Δbar, V.V0 x * M.f x
      = (vn + G Δs + slopeVbHigh M μ * (M.Δbar - Δs)) - (vn + G Δs) * M.F Δs
        - slopeVbHigh M μ * ∫ x in Δs..M.Δbar, M.F x := by
    rw [intervalIntegral.integral_congr (g := fun x => ((vn + G Δs - slopeVbHigh M μ * Δs)
      + slopeVbHigh M μ * x) * M.f x), int_affine_mul_f M hM (by linarith) h2.le le_rfl, F_bar M hM]
    · ring
    intro x hx
    rw [uIcc_of_le h2.le] at hx
    simp only
    rw [V0_formula hM hE ⟨by linarith [hx.1], hx.2⟩, if_neg (by linarith [hx.1]),
      Vb_high_formula hM hE hx, hVbs]
    ring
  rw [p1, p2, p3] at hE0
  have hJ : J M Δs = (M.Δbar - Δs) - ∫ x in Δs..M.Δbar, M.F x := by
    unfold J
    rw [intervalIntegral.integral_sub intervalIntegrable_const (F_ii M hM (by linarith) h2.le le_rfl)]
    simp
  rw [hJ]
  have hvn' : (M.κ + M.r) * vn = M.κ * M.E V.V0 := by rw [hvn]; field_simp
  rw [hE0] at hvn'
  field_simp
  linear_combination hvn'

/-- The closed form of `Vh(∆s)`. -/
lemma Vh_closed : V.Vh Δs =
    (1 + Δs) / M.r - M.κ / M.r * (slopeVsLow M μ * I M Δb)
    - M.κ / M.r * (∫ z in Δb..Δs, slopeVsMid M μ z * M.F z)
    + M.κ / M.r * (J M Δs / (M.κ + M.r)) := by
  obtain ⟨h0, h1, h2, -⟩ := id hE
  have hk := kr_pos hM
  have hr := hM.2.2.2.2.1
  set H := fun x => ∫ z in Δb..x, slopeVsMid M μ z with hH
  set VsB := V.Vs Δb
  have hsubm : Icc Δb Δs ⊆ Icc 0 M.Δbar := Icc_subset_Icc h0.le h2.le
  have hcm := (slopeVsMid_contOn hM hE).mono hsubm
  have hHc : ContinuousOn H (Icc Δb Δs) := prim_contOn' hM hE h1.le hcm
  have hsI : Δs ∈ Icc 0 M.Δbar := ⟨by linarith, h2.le⟩
  have hVhs : V.Vh Δs = VsB + H Δs := by
    rw [← indiff_s hM hE, Vs_mid_formula hM hE ⟨h1.le, le_rfl⟩]
  have hE1 : M.E V.V1 = ∫ x in (0:ℝ)..M.Δbar, V.V1 x * M.f x := rfl
  rw [split3c hM hE (V1_bdd_int hM hE)] at hE1
  have p1 : ∫ x in (0:ℝ)..Δb, V.V1 x * M.f x = VsB * M.F Δb - slopeVsLow M μ * I M Δb := by
    rw [intervalIntegral.integral_congr (g := fun x => ((VsB - slopeVsLow M μ * Δb)
      + slopeVsLow M μ * x) * M.f x), int_affine_mul_f M hM le_rfl h0.le (by linarith), F_zero]
    · unfold I; ring
    intro x hx
    rw [uIcc_of_le h0.le] at hx
    simp only
    rw [V1_formula hM hE ⟨hx.1, by linarith [hx.2]⟩, if_pos (by linarith [hx.2]),
      Vs_low_formula hM hE hx]
    ring
  have p2 : ∫ x in Δb..Δs, V.V1 x * M.f x
      = VsB * (M.F Δs - M.F Δb) + (H Δs * M.F Δs - ∫ x in Δb..Δs, slopeVsMid M μ x * M.F x) := by
    rw [intervalIntegral.integral_congr (g := fun x => VsB * M.f x + H x * M.f x)]
    · rw [intervalIntegral.integral_add ((ii_Icc h1.le (f_intOn M hM h0.le h2.le)).const_mul _)
        (ii_Icc h1.le (IntegrableOn.continuousOn_mul hHc (f_intOn M hM h0.le h2.le) isCompact_Icc)),
        int_cf M hM h0.le h1.le h2.le, int_prim_mul_f M hM h0.le h1.le h2.le
          (hcm.intervalIntegrable_of_Icc h1.le)]
    intro x hx
    rw [uIcc_of_le h1.le] at hx
    simp only
    rw [V1_formula hM hE ⟨h0.le.trans hx.1, hx.2.trans h2.le⟩, if_pos hx.2,
      Vs_mid_formula hM hE hx]
    ring
  have p3 : ∫ x in Δs..M.Δbar, V.V1 x * M.f x
      = (V.Vh Δs + (M.Δbar - Δs) / (M.κ + M.r)) - V.Vh Δs * M.F Δs
        - 1 / (M.κ + M.r) * ∫ x in Δs..M.Δbar, M.F x := by
    rw [intervalIntegral.integral_congr (g := fun x => ((V.Vh Δs - 1 / (M.κ + M.r) * Δs)
      + 1 / (M.κ + M.r) * x) * M.f x), int_affine_mul_f M hM (by linarith) h2.le le_rfl, F_bar M hM]
    · field_simp; ring
    intro x hx
    rw [uIcc_of_le h2.le] at hx
    simp only
    have hxI : x ∈ Icc 0 M.Δbar := ⟨by linarith [hx.1], hx.2⟩
    rcases hx.1.lt_or_eq with hlt | heq
    · rw [V1_formula hM hE hxI, if_neg (by linarith), Vh_eq hM hE hxI, Vh_eq hM hE hsI]
      field_simp; ring
    · subst heq
      rw [V1_formula hM hE hxI, if_pos le_rfl, indiff_s hM hE]; ring
  rw [p1, p2, p3] at hE1
  have hJ : J M Δs = (M.Δbar - Δs) - ∫ x in Δs..M.Δbar, M.F x := by
    unfold J
    rw [intervalIntegral.integral_sub intervalIntegrable_const (F_ii M hM (by linarith) h2.le le_rfl)]
    simp
  have e8 := (bell hE hsI).1
  rw [hE1, hVhs] at e8
  rw [hJ, hVhs]
  field_simp
  field_simp at e8
  linear_combination e8

lemma int_agree_mid {g h : ℝ → ℝ} (he : ∀ x ∈ Icc 0 M.Δbar, g x = h x) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ M.Δbar) : ∫ x in a..b, g x = ∫ x in a..b, h x := by
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hab] at hx
  exact he x ⟨ha.trans hx.1, hx.2.trans hb⟩

lemma closed_forms : ∀ Δ ∈ Icc 0 M.Δbar,
      V.Vn Δ = candVn M Δb Δs ∧
      V.Vh Δ = candVhAtS M Δb Δs + (Δ - Δs) / (M.κ + M.r) ∧
      V.V0 Δ = candV0 M Δb Δs Δ ∧ V.V1 Δ = candV1 M Δb Δs Δ := by
  obtain ⟨h0, h1, h2, hSS, -⟩ := id hE
  have hk := kr_pos hM
  have hr := hM.2.2.2.2.1
  set c := candDensities M Δb Δs
  have aVb : ∀ x ∈ Icc 0 M.Δbar, slopeVbMid M c x = slopeVbMid M μ x :=
    fun x hx => (agree_sVbM hM h0 h1 h2 hSS hx).symm
  have aVs : ∀ x ∈ Icc 0 M.Δbar, slopeVsMid M c x = slopeVsMid M μ x :=
    fun x hx => (agree_sVsM hM h0 h1 h2 hSS hx).symm
  have aVsF : ∀ x ∈ Icc 0 M.Δbar, slopeVsMid M c x * M.F x = slopeVsMid M μ x * M.F x :=
    fun x hx => by rw [aVs x hx]
  have aVb1F : ∀ x ∈ Icc 0 M.Δbar, slopeVbMid M c x * (1 - M.F x)
      = slopeVbMid M μ x - slopeVbMid M μ x * M.F x := fun x hx => by rw [aVb x hx]; ring
  have hsubm : Icc Δb Δs ⊆ Icc 0 M.Δbar := Icc_subset_Icc h0.le h2.le
  have hcb := (slopeVbMid_contOn hM hE).mono hsubm
  have hFc := (F_cont M hM).mono hsubm
  have hVnC : candVn M Δb Δs = M.κ * M.E V.V0 / (M.κ + M.r) := by
    rw [Vn_closed hM hE]
    simp only [candVn]
    rw [int_agree_mid hM hE aVb1F h0.le h1.le h2.le,
      intervalIntegral.integral_sub (f := slopeVbMid M μ) (g := fun x => slopeVbMid M μ x * M.F x)
        (hcb.intervalIntegrable_of_Icc h1.le)
        ((hcb.mul hFc).intervalIntegrable_of_Icc h1.le), ← agree_sH hM h0 h1 h2 hSS]
    rfl
  have hVhC : candVhAtS M Δb Δs = V.Vh Δs := by
    rw [Vh_closed hM hE]
    simp only [candVhAtS]
    rw [int_agree_mid hM hE aVsF h0.le h1.le h2.le, ← agree_Nb hM h0 h1 h2 hSS]
    unfold slopeVsLow I J
    ring
  have hsI : Δs ∈ Icc 0 M.Δbar := ⟨by linarith, h2.le⟩
  have hVsB : candVsAtB M Δb Δs = V.Vs Δb := by
    simp only [candVsAtB]
    rw [hVhC, int_agree_mid hM hE aVs h0.le h1.le h2.le, ← indiff_s hM hE,
      Vs_mid_formula hM hE ⟨h1.le, le_rfl⟩]
    ring
  intro Δ hΔ
  refine ⟨by rw [Vn_eq hM hE hΔ, hVnC], ?_, ?_, ?_⟩
  · rw [hVhC, Vh_eq hM hE hΔ, Vh_eq hM hE hsI]; field_simp; ring
  · rw [V0_formula hM hE hΔ]
    simp only [candV0]
    rcases le_or_gt Δ Δb with ha | ha
    · rw [if_pos ha, if_pos ha]; exact hVnC.symm
    · rw [if_neg (not_le.2 ha), if_neg (not_le.2 ha)]
      rcases le_or_gt Δ Δs with hb | hb
      · rw [if_pos hb, Vb_mid_formula hM hE ⟨ha.le, hb⟩, hVnC,
          int_agree_mid hM hE aVb h0.le ha.le (hb.trans h2.le)]
      · rw [if_neg (not_le.2 hb), Vb_high_formula hM hE ⟨hb.le, hΔ.2⟩,
          Vb_mid_formula hM hE ⟨h1.le, le_rfl⟩, hVnC,
          int_agree_mid hM hE aVb h0.le h1.le h2.le, agree_sH hM h0 h1 h2 hSS]
  · rw [V1_formula hM hE hΔ]
    simp only [candV1]
    rcases le_or_gt Δ Δb with ha | ha
    · rw [if_pos (ha.trans h1.le), if_pos ha, Vs_low_formula hM hE ⟨hΔ.1, ha⟩, hVsB,
        agree_sL hM h0 h1 h2 hSS]
      unfold slopeVsLow; field_simp
    · rw [if_neg (not_le.2 ha)]
      rcases le_or_gt Δ Δs with hb | hb
      · rw [if_pos hb, if_pos hb, Vs_mid_formula hM hE ⟨ha.le, hb⟩, hVsB,
          int_agree_mid hM hE aVs h0.le ha.le (hb.trans h2.le)]
      · rw [if_neg (not_le.2 hb), if_neg (not_le.2 hb), hVhC, Vh_eq hM hE hΔ, Vh_eq hM hE hsI]
        field_simp; ring

end H2

end OTCAux


open Set OTCChain.Equilibrium

theorem solution (M : Params) (hM : M.Standing) (hc : 0 < M.c) (hcs : M.c < cStar M)
    (Δb Δs : ℝ) (μ : Densities) (V : Values) (hE : IsIntermEq M Δb Δs μ V) :
    ∀ Δ ∈ Icc 0 M.Δbar,
      V.Vn Δ = candVn M Δb Δs ∧
      V.Vh Δ = candVhAtS M Δb Δs + (Δ - Δs) / (M.κ + M.r) ∧
      V.V0 Δ = candV0 M Δb Δs Δ ∧ V.V1 Δ = candV1 M Δb Δs Δ :=
  OTCAux.closed_forms hM hE
