-- Prove2me | solution 1 for OrgDiversity.Optimal.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T09:23:15.310878+00:00
-- url     : https://prove2.me/submissions/83eff97d-5fa9-47da-9684-22891b971a86

import Mathlib
import Definitions.Def_OrgDiversity_Optimal_Model

set_option autoImplicit false

namespace ODF75

open OrgDiversity.Optimal

lemma F_pos (P : Params) (hP : P.Standing) {x : ℝ} (hx : 0 < x) : 0 < P.F x := by
  obtain ⟨-, -, -, -, hF0, hmono, -⟩ := hP
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx.le) hx
  simpa [hF0] using this

lemma F_nonneg (P : Params) (hP : P.Standing) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ P.F x := by
  rcases hx.lt_or_eq with h | h
  · exact (F_pos P hP h).le
  · obtain ⟨-, -, -, -, hF0, -⟩ := hP
    rw [← h, hF0]

lemma F_le (P : Params) (hP : P.Standing) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    P.F x ≤ P.F y := by
  obtain ⟨-, -, -, -, -, hmono, -⟩ := hP
  exact hmono.monotoneOn (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr (hx.trans hxy)) hxy

lemma F_lt (P : Params) (hP : P.Standing) {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    P.F x < P.F y := by
  obtain ⟨-, -, -, -, -, hmono, -⟩ := hP
  exact hmono (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr (hx.trans hxy.le)) hxy

lemma phi_le (P : Params) (hP : P.Standing) {x y b : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hb : 0 ≤ b) :
    x * P.F (x * b) ≤ y * P.F (y * b) := by
  have h1 : P.F (x * b) ≤ P.F (y * b) :=
    F_le P hP (mul_nonneg hx hb) (mul_le_mul_of_nonneg_right hxy hb)
  have h2 : 0 ≤ P.F (x * b) := F_nonneg P hP (mul_nonneg hx hb)
  exact mul_le_mul hxy h1 h2 (hx.trans hxy)

lemma phi_lt (P : Params) (hP : P.Standing) {x y b : ℝ} (hx : 0 ≤ x) (hxy : x < y) (hb : 0 < b) :
    x * P.F (x * b) < y * P.F (y * b) := by
  have h1 : P.F (x * b) ≤ P.F (y * b) :=
    F_le P hP (mul_nonneg hx hb.le) (mul_le_mul_of_nonneg_right hxy.le hb.le)
  have h3 : 0 < P.F (y * b) := F_pos P hP (mul_pos (hx.trans_lt hxy) hb)
  calc x * P.F (x * b) ≤ x * P.F (y * b) := mul_le_mul_of_nonneg_left h1 hx
    _ < y * P.F (y * b) := mul_lt_mul_of_pos_right hxy h3

/-- generic threshold comparison -/
lemma thresh (P : Params) (hP : P.Standing) {b1 b2 a α W1 W2 : ℝ} (hb1 : 0 < b1) (hb2 : 0 < b2)
    (hW1 : 0 < W1) (hW2 : 0 < W2) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (heq : a * P.F (a * b1) * W1 = (1 - a) * P.F ((1 - a) * b2) * W2) :
    (α ≤ a → α * P.F (α * b1) * W1 ≤ (1 - α) * P.F ((1 - α) * b2) * W2) ∧
    (a < α → (1 - α) * P.F ((1 - α) * b2) * W2 < α * P.F (α * b1) * W1) := by
  constructor
  · intro h
    have h1 := phi_le P hP hα0 h hb1.le
    have h2 := phi_le P hP (by linarith : (0:ℝ) ≤ 1 - a) (by linarith : 1 - a ≤ 1 - α) hb2.le
    have h1' := mul_le_mul_of_nonneg_right h1 hW1.le
    have h2' := mul_le_mul_of_nonneg_right h2 hW2.le
    linarith
  · intro h
    have h1 := phi_lt P hP ha0 h hb1
    have h2 := phi_le P hP (by linarith : (0:ℝ) ≤ 1 - α) (by linarith : 1 - α ≤ 1 - a) hb2.le
    have h1' := mul_lt_mul_of_pos_right h1 hW1
    have h2' := mul_le_mul_of_nonneg_right h2 hW2.le
    linarith

lemma Kint_hasDerivAt (P : Params) (hP : P.Standing) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (Kint P) (P.F x) x := by
  obtain ⟨-, -, -, -, -, -, hcont, hderiv, -, -⟩ := hP
  have hcO : ContinuousOn P.F (Set.Ioi 0) := hcont.mono Set.Ioi_subset_Ici_self
  show HasDerivAt (fun x => ∫ c in (0:ℝ)..x, P.F c) (P.F x) x
  apply intervalIntegral.integral_hasDerivAt_right
  · apply ContinuousOn.intervalIntegrable
    exact hcont.mono (by intro y hy; rw [Set.uIcc_of_le hx.le] at hy; exact hy.1)
  · exact hcO.stronglyMeasurableAtFilter isOpen_Ioi x hx
  · exact (hderiv x hx).continuousAt

lemma Kint_lt (P : Params) (hP : P.Standing) {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    Kint P x < Kint P y := by
  have hm : StrictMonoOn (Kint P) (Set.Ioi 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
    · intro z hz; exact (Kint_hasDerivAt P hP hz).continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Ioi] at hz
      rw [(Kint_hasDerivAt P hP hz).deriv]
      exact F_pos P hP hz
  exact hm hx (show (0:ℝ) < y by linarith) hxy

lemma int_cf (P : Params) (hP : P.Standing) {x : ℝ} (hx : 0 < x) :
    ∫ c in (0:ℝ)..x, c * P.f c = x * P.F x - Kint P x := by
  obtain ⟨-, -, -, -, hF0, -, hcont, hderiv, hint, -⟩ := hP
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun c => c) (u' := fun _ => (1:ℝ)) (v := P.F) (v' := P.f) (a := 0) (b := x)
    continuousOn_id (hcont.mono (by intro y hy; rw [Set.uIcc_of_le hx.le] at hy; exact hy.1))
    (fun c _ => hasDerivAt_id' c)
    (fun c hc => hderiv c (by simp only [hx.le, min_eq_left, max_eq_right, Set.mem_Ioo] at hc; exact hc.1))
    intervalIntegrable_const (hint x hx.le).1
  rw [h]
  simp [Kint, hF0]

lemma netBen_eq (P : Params) (hP : P.Standing) (o : Org) (α : ℝ) (d : Proj) (σ : Sig)
    (h : 0 < post α d σ * imBen P o d) :
    netBen P o α d σ = Kint P (post α d σ * imBen P o d) := by
  unfold netBen succ
  rw [int_cf P hP h]
  ring

lemma psi_convex (P : Params) (hP : P.Standing) (hA3 : P.Assumption3) :
    StrictConvexOn ℝ (Set.Ici 0) (fun x => x * P.F x) := by
  have hP' := hP
  obtain ⟨-, -, -, -, -, hmono, hcont, hderiv, -, -⟩ := hP'
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Ici 0)
  · exact continuousOn_id.mul hcont
  · rw [interior_Ici]
    have hd : ∀ x ∈ Set.Ioi (0:ℝ), deriv (fun x => x * P.F x) x = P.F x + x * P.f x := by
      intro x hx
      have : HasDerivAt (fun y => y * P.F y) (1 * P.F x + x * P.f x) x :=
        (hasDerivAt_id' x).mul (hderiv x hx)
      rw [this.deriv]; ring
    intro x hx y hy hxy
    rw [hd x hx, hd y hy]
    have hx' : (0:ℝ) < x := hx
    have hy' : (0:ℝ) < y := hy
    have h1 : P.F x < P.F y := F_lt P hP hx'.le hxy
    have h2 : x * P.f x ≤ y * P.f y := hA3 hx hy hxy.le
    linarith

lemma psi_mid (P : Params) (hP : P.Standing) (hA3 : P.Assumption3) {u v : ℝ} (hu : 0 ≤ u)
    (hv : 0 ≤ v) : 2 * ((u + v) / 2 * P.F ((u + v) / 2)) ≤ u * P.F u + v * P.F v := by
  have := (psi_convex P hP hA3).convexOn.2 (Set.mem_Ici.mpr hu) (Set.mem_Ici.mpr hv)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simp only [smul_eq_mul] at this
  have e : 1/2*u + 1/2*v = (u+v)/2 := by ring
  rw [e] at this
  linarith

/-- The weighted inequality `F(b/2) ≤ α F(α b) + (1-α) F((1-α) b)`. -/
lemma conv_ineq (P : Params) (hP : P.Standing) (hA3 : P.Assumption3) {α b : ℝ} (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) (hb : 0 < b) :
    P.F (1 / 2 * b) ≤ α * P.F (α * b) + (1 - α) * P.F ((1 - α) * b) := by
  have h := psi_mid P hP hA3 (mul_nonneg hα0 hb.le) (mul_nonneg (by linarith : (0:ℝ) ≤ 1 - α) hb.le)
  have e : (α * b + (1 - α) * b) / 2 = 1 / 2 * b := by ring
  rw [e] at h
  have h2 : b * P.F (1 / 2 * b) ≤ b * (α * P.F (α * b) + (1 - α) * P.F ((1 - α) * b)) := by
    nlinarith
  exact le_of_mul_le_mul_left h2 hb

lemma H_mono (P : Params) (hP : P.Standing) (hA3 : P.Assumption3) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) {b1 b2 : ℝ} (hb1 : 0 < b1) (hb12 : b1 ≤ b2) :
    (1/2) * Kint P (α * b1) + (1/2) * Kint P ((1 - α) * b1) - Kint P (1/2 * b1) ≤
    (1/2) * Kint P (α * b2) + (1/2) * Kint P ((1 - α) * b2) - Kint P (1/2 * b2) := by
  set H : ℝ → ℝ := fun b =>
    (1/2) * Kint P (α * b) + (1/2) * Kint P ((1 - α) * b) - Kint P (1/2 * b) with hHdef
  have hd : ∀ b, 0 < b → HasDerivAt H ((1/2) * (P.F (α * b) * α) +
      (1/2) * (P.F ((1 - α) * b) * (1 - α)) - P.F (1/2 * b) * (1/2)) b := by
    intro b hb
    have h1 := (Kint_hasDerivAt P hP (mul_pos hα0 hb)).comp b ((hasDerivAt_id' b).const_mul α)
    have h2 := (Kint_hasDerivAt P hP (mul_pos (by linarith : (0:ℝ) < 1 - α) hb)).comp b
      ((hasDerivAt_id' b).const_mul (1 - α))
    have h3 := (Kint_hasDerivAt P hP (mul_pos (by norm_num : (0:ℝ) < 1/2) hb)).comp b
      ((hasDerivAt_id' b).const_mul (1/2))
    have := ((h1.const_mul (1/2)).add (h2.const_mul (1/2))).sub h3
    simp only [mul_one] at this
    exact this
  have hmono : MonotoneOn H (Set.Ioi 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    · intro z hz; exact (hd z hz).continuousAt.continuousWithinAt
    · intro z hz; rw [interior_Ioi] at hz; exact (hd z hz).differentiableAt.differentiableWithinAt
    · intro z hz
      rw [interior_Ioi] at hz
      have hz' : (0:ℝ) < z := hz
      rw [(hd z hz').deriv]
      have := conv_ineq P hP hA3 hα0.le hα1.le hz'
      nlinarith
  exact hmono hb1 (show (0:ℝ) < b2 by linarith) hb12

lemma opt_eff {X Y k π : ℝ} (hk : 0 < k) (hπ : π ∈ Set.Icc (0:ℝ) 1)
    (h : ∀ π' ∈ Set.Icc (0:ℝ) 1,
      π' * X + (1 - π') * Y - π' ^ 2 / (2 * k) ≤ π * X + (1 - π) * Y - π ^ 2 / (2 * k)) :
    π = max 0 (min (k * (X - Y)) 1) := by
  obtain ⟨h0, h1⟩ := hπ
  have h' : ∀ t ∈ Set.Icc (0:ℝ) 1, 2 * k * (t * (X - Y)) - t ^ 2 ≤ 2 * k * (π * (X - Y)) - π ^ 2 := by
    intro t ht
    have := h t ht
    have e : ∀ s : ℝ, s * X + (1 - s) * Y - s ^ 2 / (2 * k) =
        Y + (2 * k * (s * (X - Y)) - s ^ 2) / (2 * k) := by
      intro s; field_simp; ring
    rw [e t, e π] at this
    have h2k : (0:ℝ) < 2 * k := by positivity
    exact (div_le_div_iff_of_pos_right h2k).mp (by linarith)
  rcases le_total (k * (X - Y)) 0 with hM | hM
  · have := h' 0 ⟨le_rfl, zero_le_one⟩
    have e : max 0 (min (k * (X - Y)) 1) = 0 := max_eq_left (min_le_of_left_le hM)
    rw [e]
    nlinarith
  · rcases le_total (k * (X - Y)) 1 with hM1 | hM1
    · have := h' (k * (X - Y)) ⟨hM, hM1⟩
      rw [min_eq_left hM1, max_eq_right hM]
      nlinarith
    · have := h' 1 ⟨zero_le_one, le_rfl⟩
      rw [min_eq_right hM1, max_eq_right zero_le_one]
      nlinarith

lemma clamp_ratio {m s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    s * max 0 (min (t * m) 1) ≤ t * max 0 (min (s * m) 1) := by
  rcases le_total m 0 with hm | hm
  · have h1 : min (s * m) 1 ≤ 0 := min_le_of_left_le (mul_nonpos_of_nonneg_of_nonpos hs hm)
    have h2 : min (t * m) 1 ≤ 0 :=
      min_le_of_left_le (mul_nonpos_of_nonneg_of_nonpos (hs.trans hst) hm)
    rw [max_eq_left h1, max_eq_left h2]; simp
  · rw [max_eq_right (le_min (mul_nonneg hs hm) zero_le_one),
      max_eq_right (le_min (mul_nonneg (hs.trans hst) hm) zero_le_one)]
    rcases min_cases (s * m) 1 with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
      rcases min_cases (t * m) 1 with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;> rw [h1, h2] <;> nlinarith

lemma part1_gen {a A c C m1 m2 k p1 p2 : ℝ} (hk : 0 < k) (hac : a < c) (hAC : A < C)
    (hcC : c ≤ C) (hm : m1 ≤ m2) (hp1 : p1 = max 0 (min (k * m1) 1))
    (hp2 : p2 = max 0 (min (k * m2) 1)) :
    p1 * A + (1 - p1) * a < p2 * C + (1 - p2) * c := by
  have h12 : p1 ≤ p2 := by
    rw [hp1, hp2]
    exact max_le_max le_rfl (min_le_min_right 1 (mul_le_mul_of_nonneg_left hm hk.le))
  have h0 : 0 ≤ p1 := by rw [hp1]; exact le_max_left _ _
  have h1 : p2 ≤ 1 := by rw [hp2]; exact max_le zero_le_one (min_le_right _ _)
  have hp11 : p1 ≤ 1 := h12.trans h1
  have key : p1 * A + (1 - p1) * a < p1 * C + (1 - p1) * c := by
    rcases lt_or_eq_of_le hp11 with h | h
    · nlinarith [mul_pos (sub_pos.mpr h) (sub_pos.mpr hac), mul_nonneg h0 (sub_pos.mpr hAC).le]
    · rw [h]; linarith
  nlinarith [mul_le_mul_of_nonneg_right h12 (sub_nonneg.mpr hcC)]

lemma crossing {a A c C m1 m2 : ℝ} (ph pm : ℝ → ℝ) (hm1 : 0 < m1) (hac : a < c) (hcC : c ≤ C)
    (hCA : C ≤ A) (hor : C < A ∨ (m2 < m1 ∧ c < C))
    (hph : ∀ k, 0 < k → ph k = max 0 (min (k * m1) 1))
    (hpm : ∀ k, 0 < k → pm k = max 0 (min (k * m2) 1)) :
    ∃ kα : ℝ, 0 < kα ∧ ph kα < 1 ∧
      (∀ k : ℝ, 0 < k → k < kα → ph k * A + (1 - ph k) * a < pm k * C + (1 - pm k) * c) ∧
      (∀ k : ℝ, kα ≤ k → pm k * C + (1 - pm k) * c ≤ ph k * A + (1 - ph k) * a) ∧
      (∀ k : ℝ, kα < k → pm k < 1 →
        pm k * C + (1 - pm k) * c < ph k * A + (1 - ph k) * a) := by
  set q : ℝ → ℝ := fun k => max 0 (min (k * m2) 1) with hq
  set D : ℝ → ℝ := fun k => (max 0 (min (k * m1) 1)) * A + (1 - max 0 (min (k * m1) 1)) * a -
    (q k * C + (1 - q k) * c) with hD
  have hq01 : ∀ k, 0 ≤ q k ∧ q k ≤ 1 := fun k =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  set ks := 1 / m1 with hks
  have hks0 : 0 < ks := by positivity
  have hlin : ∀ k, 0 ≤ k → k ≤ ks → max 0 (min (k * m1) 1) = k * m1 := by
    intro k hk0 hk1
    have : k * m1 ≤ 1 := by rw [hks] at hk1; rwa [le_div_iff₀ hm1] at hk1
    rw [min_eq_left this, max_eq_right (mul_nonneg hk0 hm1.le)]
  have hcap : ∀ k, ks ≤ k → max 0 (min (k * m1) 1) = 1 := by
    intro k hk
    have : 1 ≤ k * m1 := by rw [hks] at hk; rwa [div_le_iff₀ hm1] at hk
    rw [min_eq_right this, max_eq_right zero_le_one]
  have hD0 : D 0 = a - c := by simp [hD, hq]
  have hDcont : Continuous D := by
    simp only [hD, hq]; fun_prop
  have hDks : 0 < D ks := by
    simp only [hD]
    rw [hcap ks le_rfl]
    rcases hor with h | ⟨h1, h2⟩
    · have := hq01 ks; nlinarith
    · have hqlt : q ks < 1 := by
        simp only [hq]
        have : ks * m2 < 1 := by
          rw [hks, div_mul_eq_mul_div, one_mul, div_lt_one hm1]; exact h1
        exact max_lt zero_lt_one (min_lt_of_left_lt this)
      have := hq01 ks; nlinarith
  have hJ : ∀ s t, 0 < s → s ≤ t → t ≤ ks → t * D s ≤ (t - s) * D 0 + s * D t := by
    intro s t hs hst htk
    have h1 := hlin s hs.le (hst.trans htk)
    have h2 := hlin t (hs.le.trans hst) htk
    have h3 : s * q t ≤ t * q s := clamp_ratio hs.le hst
    have h4 := mul_le_mul_of_nonneg_left h3 (sub_nonneg.mpr hcC)
    rw [hD0]
    simp only [hD, h1, h2]
    nlinarith [h4]
  have hIVT := intermediate_value_Ioo hks0.le hDcont.continuousOn
  have h0mem : (0:ℝ) ∈ Set.Ioo (D 0) (D ks) := ⟨by rw [hD0]; linarith, hDks⟩
  obtain ⟨r, ⟨hr0, hrks⟩, hDr⟩ := hIVT h0mem
  have hrel : ∀ k, 0 < k →
      ph k * A + (1 - ph k) * a - (pm k * C + (1 - pm k) * c) = D k := by
    intro k hk
    rw [hph k hk, hpm k hk]
  have hpos : ∀ k, r < k → k ≤ ks → 0 < D k := by
    intro k hrk hkks
    have := hJ r k hr0 hrk.le hkks
    rw [hDr, hD0] at this
    nlinarith
  have hbig : ∀ k, ks ≤ k → ph k * A + (1 - ph k) * a = A := by
    intro k hk
    rw [hph k (hks0.trans_le hk), hcap k hk]; ring
  refine ⟨r, hr0, ?_, ?_, ?_, ?_⟩
  · rw [hph r hr0, hlin r hr0.le hrks.le]
    have := (lt_div_iff₀ hm1).mp (show r < 1 / m1 from hrks)
    linarith
  · intro k hk hkr
    have := hJ k r hk hkr.le hrks.le
    rw [hDr, hD0] at this
    have hDk : D k < 0 := by nlinarith
    have := hrel k hk
    linarith
  · intro k hrk
    have hk0 : 0 < k := hr0.trans_le hrk
    by_cases hkks : k ≤ ks
    · rcases eq_or_lt_of_le hrk with h | h
      · subst h; have := hrel _ hk0; linarith [hDr]
      · have := hpos k h hkks; have := hrel k hk0; linarith
    · push Not at hkks
      rw [hbig k hkks.le, hpm k hk0]
      have := hq01 k
      simp only [hq] at this
      nlinarith
  · intro k hrk hpm1
    have hk0 : 0 < k := hr0.trans hrk
    by_cases hkks : k ≤ ks
    · have := hpos k hrk hkks; have := hrel k hk0; linarith
    · push Not at hkks
      rw [hbig k hkks.le]
      have h01 : 0 ≤ pm k := by rw [hpm k hk0]; exact le_max_left _ _
      rcases hor with h | ⟨h1, h2⟩
      · nlinarith
      · nlinarith [mul_pos (sub_pos.mpr hpm1) (sub_pos.mpr h2)]

/-- IM's marginal benefit of information. -/
noncomputable def MB (P : Params) (o : Org) (α : ℝ) : ℝ :=
  ((1 / 2) * netBen P o α (dStar P o α .one) .one + (1 / 2) * netBen P o α (dStar P o α .two) .two) -
    netBen P o α (dStar P o α .phi) .phi

noncomputable def SI (P : Params) (o : Org) (α : ℝ) : ℝ :=
  (1 / 2) * succ P o α (dStar P o α .one) .one + (1 / 2) * succ P o α (dStar P o α .two) .two

noncomputable def SP (P : Params) (o : Org) (α : ℝ) : ℝ :=
  succ P o α (dStar P o α .phi) .phi

lemma eff (P : Params) (o : Org) {α k π : ℝ} (hk : 0 < k) (h : IsOptimalEffort P o α k π) :
    π = max 0 (min (k * MB P o α) 1) :=
  opt_eff hk h.1 h.2

lemma sp_eq (P : Params) (o : Org) (α π : ℝ) :
    successProb P o α π = π * SI P o α + (1 - π) * SP P o α := rfl

lemma dStar_one_of (P : Params) (o : Org) (α : ℝ) (σ : Sig)
    (h : ¬ (succ P o α .one σ * dmBen P .one < succ P o α .two σ * dmBen P .two)) :
    dStar P o α σ = .one := by
  unfold dStar; rw [if_neg h]

lemma dStar_two_of (P : Params) (o : Org) (α : ℝ) (σ : Sig)
    (h : succ P o α .one σ * dmBen P .one < succ P o α .two σ * dmBen P .two) :
    dStar P o α σ = .two := by
  unfold dStar; rw [if_pos h]

end ODF75

open OrgDiversity.Optimal in
theorem solution (P : Params) (hP : P.Standing) (hA1 : P.Assumption1)
    (hA2 : P.Assumption2) (hA3 : P.Assumption3) (αhom αhet αhat : ℝ)
    (hhom : P.IsAlphaHom αhom) (hhet : P.IsAlphaHet αhet) (hhat : P.IsAlphaHat αhat)
    (α : ℝ) (hα : 1 / 2 < α) (hα1 : α ≤ 1)
    (πhom πhet : ℝ → ℝ)
    (hπhom : ∀ k : ℝ, 0 < k → IsOptimalEffort P .hom α k (πhom k))
    (hπhet : ∀ k : ℝ, 0 < k → IsOptimalEffort P .het α k (πhet k)) :
    (α ≤ αhet →
      ∀ k : ℝ, 0 < k → successProb P .het α (πhet k) < successProb P .hom α (πhom k)) ∧
    (max αhet αhat < α →
      ∃ kα : ℝ, 0 < kα ∧ πhet kα < 1 ∧
      (∀ k : ℝ, 0 < k → k < kα →
        successProb P .het α (πhet k) < successProb P .hom α (πhom k)) ∧
      (∀ k : ℝ, kα ≤ k → successProb P .hom α (πhom k) ≤ successProb P .het α (πhet k)) ∧
      (∀ k : ℝ, kα < k → πhom k < 1 →
        successProb P .hom α (πhom k) < successProb P .het α (πhet k))) := by
  have hP0 := hP
  obtain ⟨hbL, hbLH, hBL, hBLH, -, -, -, -, -, -⟩ := hP0
  have hbH : 0 < P.bH := by linarith
  have hBH : 0 < P.BH := by linarith
  have hα0 : 0 < α := by linarith
  have hhL : (0:ℝ) < 1 / 2 * P.bL := by positivity
  have hhH : (0:ℝ) < 1 / 2 * P.bH := by positivity
  have hα1m : (0:ℝ) ≤ 1 - α := by linarith
  have hA1' : P.F (1 / 2 * P.bH) * P.BL ≤ P.F (1 / 2 * P.bL) * P.BH := by
    have hFL := ODF75.F_pos P hP hhL
    have h := hA1
    unfold Params.Assumption1 at h
    have e1 : P.bH / 2 = 1 / 2 * P.bH := by ring
    have e2 : P.bL / 2 = 1 / 2 * P.bL := by ring
    rw [e1, e2, div_le_div_iff₀ hFL hBL] at h
    linarith
  have dhom_phi : dStar P .hom α .phi = .one := by
    apply ODF75.dStar_one_of; apply not_lt.mpr
    simp only [succ, post, imBen, dmBen]
    have h1 := ODF75.F_le P hP hhL.le (by linarith : 1 / 2 * P.bL ≤ 1 / 2 * P.bH)
    have h2 := ODF75.F_nonneg P hP hhL.le
    nlinarith [mul_le_mul_of_nonneg_right h1 hBL.le,
      mul_le_mul_of_nonneg_left hBLH.le (h2.trans h1)]
  have dhet_phi : dStar P .het α .phi = .one := by
    apply ODF75.dStar_one_of; apply not_lt.mpr
    simp only [succ, post, imBen, dmBen]
    nlinarith [hA1']
  have hFαLH : α * P.F (α * P.bL) ≤ α * P.F (α * P.bH) :=
    mul_le_mul_of_nonneg_left (ODF75.F_le P hP (mul_nonneg hα0.le hbL.le)
      (mul_le_mul_of_nonneg_left hbLH.le hα0.le)) hα0.le
  have hFαLH' : α * P.F (α * P.bL) < α * P.F (α * P.bH) :=
    mul_lt_mul_of_pos_left (ODF75.F_lt P hP (mul_nonneg hα0.le hbL.le)
      (mul_lt_mul_of_pos_left hbLH hα0)) hα0
  have hF1αLH : (1 - α) * P.F ((1 - α) * P.bL) ≤ (1 - α) * P.F ((1 - α) * P.bH) :=
    mul_le_mul_of_nonneg_left (ODF75.F_le P hP (mul_nonneg hα1m hbL.le)
      (mul_le_mul_of_nonneg_left hbLH.le hα1m)) hα1m
  have dhom_one : dStar P .hom α .one = .one := by
    apply ODF75.dStar_one_of; apply not_lt.mpr
    simp only [succ, post, imBen, dmBen]
    have h1 := ODF75.phi_le P hP hα1m (by linarith : 1 - α ≤ α) hbL.le
    have h3 : 0 ≤ α * P.F (α * P.bH) :=
      mul_nonneg hα0.le (ODF75.F_nonneg P hP (mul_nonneg hα0.le hbH.le))
    nlinarith [mul_le_mul_of_nonneg_right (h1.trans hFαLH) hBL.le,
      mul_le_mul_of_nonneg_left hBLH.le h3]
  have dhet_one : dStar P .het α .one = .one := by
    apply ODF75.dStar_one_of; apply not_lt.mpr
    simp only [succ, post, imBen, dmBen]
    have h1 := ODF75.phi_le P hP (by norm_num : (0:ℝ) ≤ 1 / 2) hα.le hbL.le
    have h2 := ODF75.phi_le P hP hα1m (by linarith : 1 - α ≤ 1 / 2) hbH.le
    nlinarith [mul_le_mul_of_nonneg_right h2 hBL.le, mul_le_mul_of_nonneg_right h1 hBH.le, hA1']
  have heqhet : αhet * P.F (αhet * P.bH) * P.BL =
      (1 - αhet) * P.F ((1 - αhet) * P.bL) * P.BH := by
    rw [hhet.2]; field_simp [hBL.ne']
  have hT := ODF75.thresh P hP hbH hbL hBL hBH (by linarith [hhet.1.1]) hhet.1.2.le hα0.le hα1 heqhet
  have hSPhet : ODF75.SP P .het α = 1 / 2 * P.F (1 / 2 * P.bL) := by
    simp only [ODF75.SP, dhet_phi, succ, post, imBen]
  have hSPhom : ODF75.SP P .hom α = 1 / 2 * P.F (1 / 2 * P.bH) := by
    simp only [ODF75.SP, dhom_phi, succ, post, imBen]
  have hac : ODF75.SP P .het α < ODF75.SP P .hom α := by
    rw [hSPhet, hSPhom]
    have := ODF75.F_lt P hP hhL.le (by linarith : 1 / 2 * P.bL < 1 / 2 * P.bH)
    linarith
  have hconvH := ODF75.conv_ineq P hP hA3 hα0.le hα1 hbH
  have hph : ∀ k, 0 < k → πhet k = max 0 (min (k * ODF75.MB P .het α) 1) :=
    fun k hk => ODF75.eff P .het hk (hπhet k hk)
  have hpm : ∀ k, 0 < k → πhom k = max 0 (min (k * ODF75.MB P .hom α) 1) :=
    fun k hk => ODF75.eff P .hom hk (hπhom k hk)
  constructor
  · intro hle k hk
    have hα1' : α < 1 := lt_of_le_of_lt hle hhet.1.2
    have hα1p : (0:ℝ) < 1 - α := by linarith
    have hTa := hT.1 hle
    have dhet_two : dStar P .het α .two = .one := by
      apply ODF75.dStar_one_of; apply not_lt.mpr
      simp only [succ, post, imBen, dmBen]
      exact hTa
    have dhom_two : dStar P .hom α .two = .one := by
      apply ODF75.dStar_one_of; apply not_lt.mpr
      simp only [succ, post, imBen, dmBen]
      nlinarith [mul_le_mul_of_nonneg_right hFαLH hBL.le, mul_le_mul_of_nonneg_right hF1αLH hBH.le]
    have hSIhet : ODF75.SI P .het α =
        1 / 2 * (α * P.F (α * P.bL)) + 1 / 2 * ((1 - α) * P.F ((1 - α) * P.bL)) := by
      simp only [ODF75.SI, dhet_one, dhet_two, succ, post, imBen]
    have hSIhom : ODF75.SI P .hom α =
        1 / 2 * (α * P.F (α * P.bH)) + 1 / 2 * ((1 - α) * P.F ((1 - α) * P.bH)) := by
      simp only [ODF75.SI, dhom_one, dhom_two, succ, post, imBen]
    have hMBhet : ODF75.MB P .het α = (1 / 2) * Kint P (α * P.bL) +
        (1 / 2) * Kint P ((1 - α) * P.bL) - Kint P (1 / 2 * P.bL) := by
      simp only [ODF75.MB, dhet_one, dhet_two, dhet_phi]
      rw [ODF75.netBen_eq P hP .het α .one .one (by simp only [post, imBen]; exact mul_pos hα0 hbL),
        ODF75.netBen_eq P hP .het α .one .two (by simp only [post, imBen]; exact mul_pos hα1p hbL),
        ODF75.netBen_eq P hP .het α .one .phi (by simp only [post, imBen]; exact hhL)]
      simp only [post, imBen]
    have hMBhom : ODF75.MB P .hom α = (1 / 2) * Kint P (α * P.bH) +
        (1 / 2) * Kint P ((1 - α) * P.bH) - Kint P (1 / 2 * P.bH) := by
      simp only [ODF75.MB, dhom_one, dhom_two, dhom_phi]
      rw [ODF75.netBen_eq P hP .hom α .one .one (by simp only [post, imBen]; exact mul_pos hα0 hbH),
        ODF75.netBen_eq P hP .hom α .one .two (by simp only [post, imBen]; exact mul_pos hα1p hbH),
        ODF75.netBen_eq P hP .hom α .one .phi (by simp only [post, imBen]; exact hhH)]
      simp only [post, imBen]
    have hM : ODF75.MB P .het α ≤ ODF75.MB P .hom α := by
      rw [hMBhet, hMBhom]; exact ODF75.H_mono P hP hA3 hα0 hα1' hbL hbLH.le
    have hAC : ODF75.SI P .het α < ODF75.SI P .hom α := by
      rw [hSIhet, hSIhom]; linarith
    have hcC : ODF75.SP P .hom α ≤ ODF75.SI P .hom α := by
      rw [hSPhom, hSIhom]; linarith
    rw [ODF75.sp_eq, ODF75.sp_eq]
    exact ODF75.part1_gen hk hac hAC hcC hM (hph k hk) (hpm k hk)
  · intro hgt
    have hgt1 : αhet < α := lt_of_le_of_lt (le_max_left _ _) hgt
    have hgt2 : αhat < α := lt_of_le_of_lt (le_max_right _ _) hgt
    have dhet_two : dStar P .het α .two = .two := by
      apply ODF75.dStar_two_of
      simp only [succ, post, imBen, dmBen]
      exact (hT.2 hgt1)
    have hSIhet : ODF75.SI P .het α =
        1 / 2 * (α * P.F (α * P.bL)) + 1 / 2 * (α * P.F (α * P.bH)) := by
      simp only [ODF75.SI, dhet_one, dhet_two, succ, post, imBen]
    have hMBhet : ODF75.MB P .het α = (1 / 2) * Kint P (α * P.bL) +
        (1 / 2) * Kint P (α * P.bH) - Kint P (1 / 2 * P.bL) := by
      simp only [ODF75.MB, dhet_one, dhet_two, dhet_phi]
      rw [ODF75.netBen_eq P hP .het α .one .one (by simp only [post, imBen]; exact mul_pos hα0 hbL),
        ODF75.netBen_eq P hP .het α .two .two (by simp only [post, imBen]; exact mul_pos hα0 hbH),
        ODF75.netBen_eq P hP .het α .one .phi (by simp only [post, imBen]; exact hhL)]
      simp only [post, imBen]
    have hm1 : 0 < ODF75.MB P .het α := by
      rw [hMBhet]
      have h1 := ODF75.Kint_lt P hP hhL (by nlinarith : 1 / 2 * P.bL < α * P.bL)
      have h2 := ODF75.Kint_lt P hP hhL (by nlinarith : 1 / 2 * P.bL < α * P.bH)
      linarith
    simp only [ODF75.sp_eq]
    by_cases hR : (1 - α) * P.F ((1 - α) * P.bH) * P.BH < α * P.F (α * P.bL) * P.BL
    · have dhom_two : dStar P .hom α .two = .two := by
        apply ODF75.dStar_two_of
        simp only [succ, post, imBen, dmBen]
        exact hR
      have hSIhom : ODF75.SI P .hom α =
          1 / 2 * (α * P.F (α * P.bH)) + 1 / 2 * (α * P.F (α * P.bL)) := by
        simp only [ODF75.SI, dhom_one, dhom_two, succ, post, imBen]
      have hMBhom : ODF75.MB P .hom α = (1 / 2) * Kint P (α * P.bH) +
          (1 / 2) * Kint P (α * P.bL) - Kint P (1 / 2 * P.bH) := by
        simp only [ODF75.MB, dhom_one, dhom_two, dhom_phi]
        rw [ODF75.netBen_eq P hP .hom α .one .one (by simp only [post, imBen]; exact mul_pos hα0 hbH),
          ODF75.netBen_eq P hP .hom α .two .two (by simp only [post, imBen]; exact mul_pos hα0 hbL),
          ODF75.netBen_eq P hP .hom α .one .phi (by simp only [post, imBen]; exact hhH)]
        simp only [post, imBen]
      have hRL : (1 - α) * P.F ((1 - α) * P.bH) < α * P.F (α * P.bL) := by
        have h0 : 0 ≤ (1 - α) * P.F ((1 - α) * P.bH) :=
          mul_nonneg hα1m (ODF75.F_nonneg P hP (mul_nonneg hα1m hbH.le))
        have h1 : (1 - α) * P.F ((1 - α) * P.bH) * P.BL < α * P.F (α * P.bL) * P.BL := by
          nlinarith [mul_le_mul_of_nonneg_left hBLH.le h0]
        exact lt_of_mul_lt_mul_right h1 hBL.le
      have hcC : ODF75.SP P .hom α ≤ ODF75.SI P .hom α := by
        rw [hSPhom, hSIhom]; linarith
      have hcC' : ODF75.SP P .hom α < ODF75.SI P .hom α := by
        rw [hSPhom, hSIhom]; linarith
      have hCA : ODF75.SI P .hom α ≤ ODF75.SI P .het α := by
        rw [hSIhom, hSIhet]; linarith
      have hMlt : ODF75.MB P .hom α < ODF75.MB P .het α := by
        rw [hMBhom, hMBhet]
        have := ODF75.Kint_lt P hP hhL (by linarith : 1 / 2 * P.bL < 1 / 2 * P.bH)
        linarith
      exact ODF75.crossing πhet πhom hm1 hac hcC hCA (Or.inr ⟨hMlt, hcC'⟩) hph hpm
    · have dhom_two : dStar P .hom α .two = .one := by
        apply ODF75.dStar_one_of
        simp only [succ, post, imBen, dmBen]
        exact hR
      have hSIhom : ODF75.SI P .hom α =
          1 / 2 * (α * P.F (α * P.bH)) + 1 / 2 * ((1 - α) * P.F ((1 - α) * P.bH)) := by
        simp only [ODF75.SI, dhom_one, dhom_two, succ, post, imBen]
      have heqhat : αhat * P.F (αhat * P.bL) * 1 = (1 - αhat) * P.F ((1 - αhat) * P.bH) * 1 := by
        rw [mul_one, mul_one]; exact hhat.2
      have hTh := (ODF75.thresh P hP hbL hbH one_pos one_pos (by linarith [hhat.1.1])
        hhat.1.2.le hα0.le hα1 heqhat).2 hgt2
      have hcC : ODF75.SP P .hom α ≤ ODF75.SI P .hom α := by
        rw [hSPhom, hSIhom]; linarith
      have hCA' : ODF75.SI P .hom α < ODF75.SI P .het α := by
        rw [hSIhom, hSIhet]; linarith
      exact ODF75.crossing πhet πhom hm1 hac hcC hCA'.le (Or.inl hCA') hph hpm
