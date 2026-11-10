-- Prove2me | solution 1 for SideConstrainedDTA.Existence.claim_7
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-11-09T17:05:51.552018+00:00
-- url     : https://prove2.me/submissions/6bab92f1-d684-4858-9abc-3d2a38f8f8af

import Mathlib
import Definitions.Def_SideConstrainedDTA_Existence_Setting

/-! Disproof draft for SideConstrainedDTA.Existence.claim_7 (999aa317).
Counterexample (prefix case of devMNS, Delta = 0): see scratch/bailed/999aa317.md.
This file holds the model and the easy assumption lemmas; the hard lemmas are listed in
scratch/probe/999aa317.progress.md. -/

set_option autoImplicit false

open MeasureTheory Set Filter Topology

namespace Cex999

open SideConstrainedDTA.Existence

/-- amplitude: `rho s = s` for `0 ≤ s ≤ 1/8`, zero for `s ≤ 0` and `s ≥ 1/4`. -/
noncomputable def rho (s : ℝ) : ℝ := max 0 (min s (1 / 4 - s))

/-- peak position of the pattern inside one period (fraction of the period). -/
noncomputable def ustar (s : ℝ) : ℝ := (3 / 4 - s) / (1 - s)

/-- period of the pattern in the cumulative coordinate `y = θ - 1`. -/
noncomputable def per (s : ℝ) : ℝ := (1 - s) * (8 * s)

/-- envelope: zero for `y ≤ 0` and `y ≥ 1 - s`, one on `[2s, 1 - 3s]`. -/
noncomputable def env (s y : ℝ) : ℝ := max 0 (min 1 (min y (1 - s - y) / (2 * s)))

/-- the oscillating excess load on the shared edge, as a function of `s = massZ h`. -/
noncomputable def Phi (s θ : ℝ) : ℝ :=
  rho s * env s (θ - 1) * max 0 (Real.cos (2 * Real.pi * ((θ - 1) / per s - ustar s)))

/-- cumulative inflow of the two walks that use the edge. -/
noncomputable def C (h : Fin 3 → ℝ → ℝ) (r : ℝ) : ℝ := ∫ t in (0 : ℝ)..r, (h 0 t + h 1 t)

/-- mass of the edge-free walk `2`. -/
noncomputable def massZ (h : Fin 3 → ℝ → ℝ) : ℝ := ∫ t in Icc (0 : ℝ) 1, h 2 t

/-- walks: `0 = p = [e]` (delay 1), `1 = q = [e]` (delay 0), `2 = z = []` (delay 1). -/
noncomputable def N : Model Unit (Fin 3) Unit where
  com := fun _ => ()
  edges := ![[()], [()], []]
  t0 := 0
  tf := 1
  Q := fun _ => 1
  B := ![1, 1, 10]
  Psi := fun _ w _ => if w = 1 then 0 else 1
  tau := fun h _ j t => if j = 0 then 1 + C h t else 3
  f := fun h _ θ => Phi (massZ h) θ
  c := fun _ _ => 0

lemma rho_nonneg (s : ℝ) : 0 ≤ rho s := le_max_left _ _

lemma env_nonneg (s y : ℝ) : 0 ≤ env s y := le_max_left _ _

lemma env_le_one (s y : ℝ) : env s y ≤ 1 := max_le zero_le_one (min_le_left _ _)

lemma Phi_nonneg (s θ : ℝ) : 0 ≤ Phi s θ :=
  mul_nonneg (mul_nonneg (rho_nonneg s) (env_nonneg s _)) (le_max_left _ _)

lemma rho_eq_zero_of_nonpos {s : ℝ} (hs : s ≤ 0) : rho s = 0 := by
  unfold rho
  apply le_antisymm _ (le_max_left _ _)
  apply max_le le_rfl
  exact le_trans (min_le_left _ _) hs

lemma env_eq_zero_of_nonpos {s y : ℝ} (hs : 0 < s) (hy : y ≤ 0) : env s y = 0 := by
  unfold env
  apply le_antisymm _ (le_max_left _ _)
  apply max_le le_rfl
  refine le_trans (min_le_right _ _) ?_
  apply div_nonpos_of_nonpos_of_nonneg
  · exact le_trans (min_le_left _ _) hy
  · linarith

lemma Phi_eq_zero_of_le_one (s θ : ℝ) (hθ : θ ≤ 1) : Phi s θ = 0 := by
  unfold Phi
  rcases le_or_gt s 0 with hs | hs
  · rw [rho_eq_zero_of_nonpos hs]; ring
  · rw [env_eq_zero_of_nonpos hs (by linarith)]; ring

lemma hA2 : A2 N := fun _ => ⟨0, rfl⟩

lemma hA11 : A11 N := fun _ _ _ => le_refl 0

lemma hA12 : A12 N := fun _ => monotoneOn_const

lemma hA22 : A22 N := fun _ => continuousOn_const

lemma hA9 : A9 N := by
  intro e h _
  show Phi (massZ h) 0 ≤ 0
  rw [Phi_eq_zero_of_le_one _ _ (by norm_num)]

lemma hA5 : A5 N := by
  intro h _ p
  exact continuousOn_const

lemma hA19 : A19 N := by
  refine ⟨1, fun h _ p => Filter.Eventually.of_forall (fun t => ?_)⟩
  show (if p = 1 then (0 : ℝ) else 1) ≤ 1
  split_ifs <;> norm_num

lemma hA18 : A18 N := by
  refine ⟨fun h _ p => continuousOn_const, fun hs h _ p => ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  exact Filter.Eventually.of_forall (fun n t _ => by
    show dist (if p = 1 then (0 : ℝ) else 1) (if p = 1 then (0 : ℝ) else 1) < ε
    simpa using hε)

/-- A17 holds because `tau h w j t` does not depend on the walk `w`. -/
lemma hA17 : A17 N := by
  intro p q k _ _ _ h _ j _ t _
  rfl


/-! ## L2: the sequence and the exact cumulative-inflow formula -/

noncomputable def mm (n : ℕ) : ℝ := (n : ℝ) + 1

noncomputable def dd (n : ℕ) : ℝ := 1 / (8 * mm n)

lemma mm_pos (n : ℕ) : 0 < mm n := by unfold mm; positivity

lemma mm_ge_one (n : ℕ) : 1 ≤ mm n := by
  unfold mm; have := (Nat.cast_nonneg n : (0:ℝ) ≤ n); linarith

lemma dd_pos (n : ℕ) : 0 < dd n := by unfold dd; have := mm_pos n; positivity

lemma dd_le (n : ℕ) : dd n ≤ 1 / 8 := by
  unfold dd; have := mm_ge_one n
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith

lemma eight_mm_dd (n : ℕ) : 8 * mm n * dd n = 1 := by
  unfold dd; have := mm_pos n; field_simp

/-- cell pattern of walk `p` (r-block `(0, 1/4]`). -/
noncomputable def Pp (n : ℕ) (u : ℝ) : ℝ := if u ∈ Ioc (0:ℝ) (1/4) then 1 - 4 * dd n else 0

/-- cell pattern of walk `q` (zero on the r'-block `(1/2, 3/4]`). -/
noncomputable def Pq (u : ℝ) : ℝ := if u ∈ Ioc (1/2 : ℝ) (3/4) then 0 else 1

noncomputable def hs (n : ℕ) (w : Fin 3) (t : ℝ) : ℝ :=
  if t ∈ Icc (0:ℝ) 1 then
    (if w = 0 then Pp n (Int.fract (mm n * t)) else
      if w = 1 then Pq (Int.fract (mm n * t)) else dd n)
  else 0

noncomputable def hstar (w : Fin 3) (t : ℝ) : ℝ :=
  if t ∈ Icc (0:ℝ) 1 then (if w = 0 then 1/4 else if w = 1 then 3/4 else 0) else 0

lemma Pp_meas (n : ℕ) : Measurable (Pp n) := by
  unfold Pp; exact Measurable.ite measurableSet_Ioc measurable_const measurable_const

lemma Pq_meas : Measurable Pq := by
  unfold Pq; exact Measurable.ite measurableSet_Ioc measurable_const measurable_const

lemma Pp_abs (n : ℕ) (u : ℝ) : |Pp n u| ≤ 1 := by
  have := dd_pos n; have := dd_le n
  unfold Pp; split_ifs
  · rw [abs_le]; constructor <;> linarith
  · simp

lemma Pq_abs (u : ℝ) : |Pq u| ≤ 1 := by unfold Pq; split_ifs <;> simp

lemma ii_of_bdd {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ x, |f x| ≤ M) (a b : ℝ) :
    IntervalIntegrable f volume a b :=
  (intervalIntegrable_const (c := M)).mono_fun hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      simp only [Real.norm_eq_abs]; exact (hM x).trans (le_abs_self M))

lemma integral_eq_const_of_Ioc {f : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)
    (h : ∀ x ∈ Ioc a b, f x = c) : ∫ x in a..b, f x = (b - a) * c := by
  rw [intervalIntegral.integral_congr_ae (g := fun _ => c)
    (Filter.Eventually.of_forall fun x hx => h x (by rwa [Set.uIoc_of_le hab] at hx))]
  simp

/-- integral of a cell pattern composed with `fract (m t)`. -/
lemma integral_fract_pattern (P : ℝ → ℝ) (hP : Measurable P) (M : ℝ) (hM : ∀ u, |P u| ≤ M)
    {m : ℝ} (hm : 0 < m) (t : ℝ) :
    ∫ τ in (0:ℝ)..t, P (Int.fract (m * τ)) =
      m⁻¹ * ((⌊m * t⌋ : ℝ) * (∫ x in (0:ℝ)..1, P (Int.fract x)) +
        ∫ x in (0:ℝ)..Int.fract (m * t), P x) := by
  have hper : Function.Periodic (fun x => P (Int.fract x)) 1 := fun x => by
    simp only [Int.fract_add_one]
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun x => P (Int.fract x)) volume a b :=
    ii_of_bdd (hP.comp measurable_fract) (fun x => hM _)
  have h1 := intervalIntegral.integral_comp_mul_left (f := fun x => P (Int.fract x))
    (a := 0) (b := t) hm.ne'
  simp only [mul_zero] at h1
  rw [h1, smul_eq_mul]
  congr 1
  set k := ⌊m * t⌋ with hk
  set u := Int.fract (m * t) with hu
  have hsplit : m * t = (0 + k • (1:ℝ)) + u := by
    rw [zsmul_eq_mul, mul_one, zero_add, hk, hu, Int.floor_add_fract]
  rw [hsplit, ← intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _),
    hper.intervalIntegral_add_zsmul_eq k 0 hint, zsmul_eq_mul, zero_add]
  congr 1
  have h2 := intervalIntegral.integral_comp_add_right (fun x => P (Int.fract x))
    (a := 0) (b := u) (k : ℝ)
  simp only [Int.fract_add_intCast, zero_add] at h2
  rw [show (0:ℝ) + k • (1:ℝ) = (k : ℝ) by rw [zsmul_eq_mul, mul_one, zero_add],
    add_comm (k : ℝ) u, ← h2]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le (Int.fract_nonneg _)] at hx
  have : Int.fract x = x := Int.fract_eq_self.2 ⟨hx.1, lt_of_le_of_lt hx.2 (Int.fract_lt_one _)⟩
  simp only [this]

lemma int_Pp_unit (n : ℕ) : ∫ x in (0:ℝ)..1, Pp n (Int.fract x) = (1 - 4 * dd n) / 4 := by
  have hii : ∀ a b : ℝ, IntervalIntegrable (fun x => Pp n (Int.fract x)) volume a b :=
    ii_of_bdd ((Pp_meas n).comp measurable_fract) (fun x => Pp_abs n _)
  have e1 : ∫ x in (0:ℝ)..1/4, Pp n (Int.fract x) = (1/4 - 0) * (1 - 4 * dd n) :=
    integral_eq_const_of_Ioc (by norm_num) (fun x hx => by
      have : Int.fract x = x := Int.fract_eq_self.2 ⟨hx.1.le, by linarith [hx.2]⟩
      rw [Pp, this, if_pos hx])
  have e2 : ∫ x in (1/4:ℝ)..1, Pp n (Int.fract x) = (1 - 1/4) * 0 :=
    integral_eq_const_of_Ioc (by norm_num) (fun x hx => by
      simp only [Pp]
      rcases eq_or_lt_of_le hx.2 with h | h
      · subst h; simp
      · have : Int.fract x = x := Int.fract_eq_self.2 ⟨by linarith [hx.1], h⟩
        rw [this, if_neg]; intro h'; linarith [h'.2, hx.1])
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1/4) (hii _ _) (hii _ _), e1, e2]
  ring

lemma int_Pq_unit : ∫ x in (0:ℝ)..1, Pq (Int.fract x) = 3 / 4 := by
  have hii : ∀ a b : ℝ, IntervalIntegrable (fun x => Pq (Int.fract x)) volume a b :=
    ii_of_bdd (Pq_meas.comp measurable_fract) (fun x => Pq_abs _)
  have e1 : ∫ x in (0:ℝ)..1/2, Pq (Int.fract x) = (1/2 - 0) * 1 :=
    integral_eq_const_of_Ioc (by norm_num) (fun x hx => by
      have : Int.fract x = x := Int.fract_eq_self.2 ⟨hx.1.le, by linarith [hx.2]⟩
      rw [Pq, this, if_neg]; intro h'; linarith [h'.1, hx.2])
  have e2 : ∫ x in (1/2:ℝ)..3/4, Pq (Int.fract x) = (3/4 - 1/2) * 0 :=
    integral_eq_const_of_Ioc (by norm_num) (fun x hx => by
      have : Int.fract x = x := Int.fract_eq_self.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩
      rw [Pq, this, if_pos hx])
  have e3 : ∫ x in (3/4:ℝ)..1, Pq (Int.fract x) = (1 - 3/4) * 1 :=
    integral_eq_const_of_Ioc (by norm_num) (fun x hx => by
      simp only [Pq]
      rcases eq_or_lt_of_le hx.2 with h | h
      · subst h; simp
      · have : Int.fract x = x := Int.fract_eq_self.2 ⟨by linarith [hx.1], h⟩
        rw [this, if_neg]; intro h'; linarith [h'.2, hx.1])
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1/2) (hii _ _) (hii _ _),
    ← intervalIntegral.integral_add_adjacent_intervals (a := 1/2) (b := 3/4) (hii _ _) (hii _ _),
    e1, e2, e3]
  norm_num

/-- `hs n 0 + hs n 1` on `[0, t] ⊆ [0,1]` is the composed pattern. -/
lemma C_hs_eq (n : ℕ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    C (hs n) t = (mm n)⁻¹ * ((⌊mm n * t⌋ : ℝ) * (1 - dd n) +
      ((∫ x in (0:ℝ)..Int.fract (mm n * t), Pp n x) +
        ∫ x in (0:ℝ)..Int.fract (mm n * t), Pq x)) := by
  have e1 : C (hs n) t = ∫ τ in (0:ℝ)..t, (Pp n (Int.fract (mm n * τ)) + Pq (Int.fract (mm n * τ))) := by
    unfold C
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le ht.1] at hx
    have hx' : x ∈ Icc (0:ℝ) 1 := ⟨hx.1, hx.2.trans ht.2⟩
    simp [hs, hx']
  have hiip : ∀ a b : ℝ, IntervalIntegrable (fun x => Pp n (Int.fract (mm n * x))) volume a b :=
    ii_of_bdd ((Pp_meas n).comp (measurable_fract.comp (measurable_const_mul (mm n))))
    (fun x => Pp_abs n _)
  have hiiq : ∀ a b : ℝ, IntervalIntegrable (fun x => Pq (Int.fract (mm n * x))) volume a b :=
    ii_of_bdd (Pq_meas.comp (measurable_fract.comp (measurable_const_mul (mm n))))
    (fun x => Pq_abs _)
  rw [e1, intervalIntegral.integral_add (hiip 0 t) (hiiq 0 t),
    integral_fract_pattern (Pp n) (Pp_meas n) 1 (Pp_abs n) (mm_pos n),
    integral_fract_pattern Pq Pq_meas 1 Pq_abs (mm_pos n), int_Pp_unit, int_Pq_unit]
  ring

lemma C_hs_r (n : ℕ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (hu : Int.fract (mm n * t) ∈ Ioc (0:ℝ) (1/4)) :
    C (hs n) t = (mm n)⁻¹ * ((⌊mm n * t⌋ : ℝ) * (1 - dd n) +
      Int.fract (mm n * t) * (2 - 4 * dd n)) := by
  rw [C_hs_eq n ht,
    integral_eq_const_of_Ioc (c := 1 - 4 * dd n) hu.1.le (fun x hx => by
      rw [Pp, if_pos ⟨hx.1, hx.2.trans hu.2⟩]),
    integral_eq_const_of_Ioc (c := 1) hu.1.le (fun x hx => by
      rw [Pq, if_neg]; intro h'; linarith [h'.1, hx.2, hu.2])]
  ring

lemma C_hs_r' (n : ℕ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (hu : Int.fract (mm n * t) ∈ Ioc (1/2 : ℝ) (3/4)) :
    C (hs n) t = (mm n)⁻¹ * ((⌊mm n * t⌋ : ℝ) * (1 - dd n) + (3/4 - dd n)) := by
  have hiip := ii_of_bdd (Pp_meas n) (Pp_abs n)
  have hiiq := ii_of_bdd Pq_meas Pq_abs
  rw [C_hs_eq n ht,
    ← intervalIntegral.integral_add_adjacent_intervals (b := 1/4) (hiip _ _) (hiip _ _),
    ← intervalIntegral.integral_add_adjacent_intervals (b := 1/2) (hiiq _ _) (hiiq _ _),
    integral_eq_const_of_Ioc (c := 1 - 4 * dd n) (by norm_num) (fun x hx => by
      rw [Pp, if_pos hx]),
    integral_eq_const_of_Ioc (c := 0) (by linarith [hu.1]) (fun x hx => by
      rw [Pp, if_neg]; intro h'; linarith [h'.2, hx.1]),
    integral_eq_const_of_Ioc (c := 1) (by norm_num) (fun x hx => by
      rw [Pq, if_neg]; intro h'; linarith [h'.1, hx.2]),
    integral_eq_const_of_Ioc (c := 0) hu.1.le (fun x hx => by
      rw [Pq, if_pos ⟨hx.1, hx.2.trans hu.2⟩])]
  ring


/-! ## L3: `hs n` is a DTC equilibrium for the penalty `lamS n = 8 (n+1)` (ν = 1) -/

noncomputable def lamS (n : ℕ) : ℝ := 8 * mm n

lemma lamS_pos (n : ℕ) : 0 < lamS n := by unfold lamS; have := mm_pos n; positivity

lemma Phi_le_rho (s θ : ℝ) : Phi s θ ≤ rho s := by
  unfold Phi
  have h1 := rho_nonneg s
  have h2 := env_nonneg s (θ - 1)
  have h3 := env_le_one s (θ - 1)
  have h4 : max 0 (Real.cos (2 * Real.pi * ((θ - 1) / per s - ustar s))) ≤ 1 :=
    max_le zero_le_one (Real.cos_le_one _)
  have h5 : 0 ≤ max 0 (Real.cos (2 * Real.pi * ((θ - 1) / per s - ustar s))) := le_max_left _ _
  have h6 : rho s * env s (θ - 1) ≤ rho s := by nlinarith
  have h7 : 0 ≤ rho s * env s (θ - 1) := mul_nonneg h1 h2
  nlinarith

lemma rho_dd (n : ℕ) : rho (dd n) = dd n := by
  have hd := dd_pos n; have hd8 := dd_le n
  unfold rho; rw [min_eq_left (by linarith), max_eq_right hd.le]

lemma mm_inv (n : ℕ) : (mm n)⁻¹ = 8 * dd n := by
  have := mm_pos n; unfold dd; field_simp

lemma lam_xi_le (n : ℕ) (θ : ℝ) : lamS n * max 0 (Phi (dd n) θ) ≤ 1 := by
  have h1 := Phi_le_rho (dd n) θ
  rw [rho_dd] at h1
  rw [max_eq_right (Phi_nonneg _ _)]
  have h2 := eight_mm_dd n
  have h3 := mm_pos n
  unfold lamS
  nlinarith

lemma massZ_hs (n : ℕ) : massZ (hs n) = dd n := by
  unfold massZ
  rw [setIntegral_congr_fun measurableSet_Icc (g := fun _ => dd n) (fun t ht => by simp [hs, ht])]
  simp

lemma xiWalk_e (h : Fin 3 → ℝ → ℝ) (w : Fin 3) (hw : w ≠ 2) (t : ℝ) :
    xiWalk N h w t = max 0 (Phi (massZ h) (1 + C h t)) := by
  have hlen : (N.edges w).length = 1 := by
    rcases (by decide : ∀ w : Fin 3, w = 0 ∨ w = 1 ∨ w = 2) w with rfl | rfl | rfl
    · rfl
    · rfl
    · exact absurd rfl hw
  unfold xiWalk
  rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin (N.edges w).length)]
  · simp only [xi]
    show max 0 (Phi (massZ h) (if (0:ℕ) = 0 then 1 + C h t else 3) - 0) = _
    simp
  · intro j _ hj; exfalso; apply hj; ext; have := j.2; simp only [Fin.val_mk]; omega
  · intro h'; exact absurd (Finset.mem_univ _) h'

lemma xiWalk_z (h : Fin 3 → ℝ → ℝ) (t : ℝ) : xiWalk N h 2 t = 0 := by
  unfold xiWalk
  apply Finset.sum_eq_zero
  intro j _
  exact absurd j.2 (by show ¬ ((j : ℕ) < 0); omega)

lemma Phi_r (n : ℕ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (hu : Int.fract (mm n * t) ∈ Ioc (0:ℝ) (1/4)) :
    Phi (dd n) (1 + C (hs n) t) = 0 := by
  have hd := dd_pos n; have hd8 := dd_le n
  have hC := C_hs_r n ht hu
  rw [mm_inv] at hC
  generalize ⌊mm n * t⌋ = k at hC
  generalize Int.fract (mm n * t) = u at hC hu
  unfold Phi
  rw [show 1 + C (hs n) t - 1 = C (hs n) t by ring, hC]
  have hX : 8 * dd n * (k * (1 - dd n) + u * (2 - 4 * dd n)) / per (dd n) - ustar (dd n) =
      k + (u * (2 - 4 * dd n) - (3/4 - dd n)) / (1 - dd n) := by
    unfold per ustar
    have h1 : (1 - dd n) ≠ 0 := by linarith
    have h2 : dd n ≠ 0 := hd.ne'
    field_simp; ring
  have hx1 : -(3/4 : ℝ) ≤ (u * (2 - 4 * dd n) - (3/4 - dd n)) / (1 - dd n) := by
    rw [le_div_iff₀ (by linarith)]; nlinarith [hu.1, hu.2]
  have hx2 : (u * (2 - 4 * dd n) - (3/4 - dd n)) / (1 - dd n) ≤ -(1/4 : ℝ) := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [hu.1, hu.2]
  have hcos : Real.cos (2 * Real.pi * (8 * dd n * (k * (1 - dd n) + u * (2 - 4 * dd n)) /
      per (dd n) - ustar (dd n))) ≤ 0 := by
    rw [hX, show 2 * Real.pi * ((k:ℝ) + (u * (2 - 4 * dd n) - (3/4 - dd n)) / (1 - dd n)) =
      2 * Real.pi * ((u * (2 - 4 * dd n) - (3/4 - dd n)) / (1 - dd n)) + k * (2 * Real.pi) by ring,
      Real.cos_add_int_mul_two_pi, ← Real.cos_neg]
    have p1 := mul_le_mul_of_nonneg_left hx2 Real.pi_pos.le
    have p2 := mul_le_mul_of_nonneg_left hx1 Real.pi_pos.le
    apply Real.cos_nonpos_of_pi_div_two_le_of_le <;> linarith
  rw [max_eq_left hcos]; ring

lemma Phi_r' (n : ℕ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (hu : Int.fract (mm n * t) ∈ Ioc (1/2:ℝ) (3/4)) :
    Phi (dd n) (1 + C (hs n) t) = dd n := by
  have hd := dd_pos n; have hd8 := dd_le n
  have hm8 := eight_mm_dd n
  have hk0 : (0:ℝ) ≤ ⌊mm n * t⌋ := by
    exact_mod_cast Int.floor_nonneg.2 (mul_nonneg (mm_pos n).le ht.1)
  have hkn : (⌊mm n * t⌋ : ℝ) ≤ mm n - 1 := by
    have h1 : (⌊mm n * t⌋ : ℝ) + Int.fract (mm n * t) = mm n * t := Int.floor_add_fract _
    have h2 : mm n * t ≤ mm n := by nlinarith [mm_pos n, ht.2]
    have hmn : mm n = (n:ℝ) + 1 := rfl
    have h3 : (⌊mm n * t⌋ : ℝ) < (n:ℝ) + 1 := by linarith [hu.1]
    have h4 : ⌊mm n * t⌋ < (n:ℤ) + 1 := by exact_mod_cast h3
    have h5 : ⌊mm n * t⌋ ≤ (n:ℤ) := Int.lt_add_one_iff.mp h4
    have h6 : (⌊mm n * t⌋ : ℝ) ≤ (n:ℝ) := by exact_mod_cast h5
    linarith
  have hC := C_hs_r' n ht hu
  rw [mm_inv] at hC
  generalize ⌊mm n * t⌋ = k at hC hk0 hkn
  have hk8 : 8 * dd n * k ≤ 1 - 8 * dd n := by
    have := mul_le_mul_of_nonneg_left hkn (by linarith : (0:ℝ) ≤ 8 * dd n)
    nlinarith
  unfold Phi
  rw [show 1 + C (hs n) t - 1 = C (hs n) t by ring, hC, rho_dd]
  have hcos : 2 * Real.pi * (8 * dd n * (k * (1 - dd n) + (3/4 - dd n)) / per (dd n) -
      ustar (dd n)) = k * (2 * Real.pi) := by
    unfold per ustar
    have h1 : (1 - dd n) ≠ 0 := by linarith
    have h2 : dd n ≠ 0 := hd.ne'
    field_simp; ring
  rw [hcos, Real.cos_int_mul_two_pi, max_eq_right zero_le_one]
  have henv : env (dd n) (8 * dd n * (k * (1 - dd n) + (3/4 - dd n))) = 1 := by
    unfold env
    have hA : 2 * dd n ≤ 8 * dd n * (k * (1 - dd n) + (3/4 - dd n)) := by
      nlinarith [mul_nonneg (mul_nonneg hd.le hk0) (by linarith : (0:ℝ) ≤ 1 - dd n)]
    have hB : 2 * dd n ≤ 1 - dd n - 8 * dd n * (k * (1 - dd n) + (3/4 - dd n)) := by
      nlinarith [mul_le_mul_of_nonneg_right hk8 (by linarith : (0:ℝ) ≤ 1 - dd n)]
    have hR : 1 ≤ min (8 * dd n * (k * (1 - dd n) + (3/4 - dd n)))
        (1 - dd n - 8 * dd n * (k * (1 - dd n) + (3/4 - dd n))) / (2 * dd n) := by
      rw [le_div_iff₀ (by linarith), one_mul]; exact le_min hA hB
    rw [min_eq_left hR, max_eq_right zero_le_one]
  rw [henv]; ring

lemma hs_meas (n : ℕ) (w : Fin 3) : Measurable (hs n w) := by
  unfold hs
  exact Measurable.ite measurableSet_Icc
    (Measurable.ite (MeasurableSet.const _)
      ((Pp_meas n).comp (measurable_fract.comp (measurable_const_mul (mm n))))
      (Measurable.ite (MeasurableSet.const _)
        (Pq_meas.comp (measurable_fract.comp (measurable_const_mul (mm n)))) measurable_const))
    measurable_const

lemma hs_bounds (n : ℕ) (w : Fin 3) (t : ℝ) :
    (t ∈ Icc (0:ℝ) 1 → 0 ≤ hs n w t ∧ hs n w t ≤ N.B w) ∧
      (t ∉ Icc (0:ℝ) 1 → hs n w t = 0) := by
  have hd := dd_pos n; have hd8 := dd_le n
  refine ⟨fun ht => ?_, fun ht => by simp [hs, ht]⟩
  rcases (by decide : ∀ w : Fin 3, w = 0 ∨ w = 1 ∨ w = 2) w with rfl | rfl | rfl
  · have hv : hs n 0 t = Pp n (Int.fract (mm n * t)) := by simp [hs, ht]
    rw [hv, show N.B 0 = 1 by simp [N]]
    unfold Pp; split_ifs <;> constructor <;> linarith
  · have hv : hs n 1 t = Pq (Int.fract (mm n * t)) := by simp [hs, ht]
    rw [hv, show N.B 1 = 1 by simp [N]]
    unfold Pq; split_ifs <;> constructor <;> norm_num
  · have hv : hs n 2 t = dd n := by simp [hs, ht]
    rw [hv, show N.B 2 = 10 by simp [N]]
    constructor <;> linarith

lemma setInt_pattern (n : ℕ) (P : ℝ → ℝ) (hP : Measurable P) (hPb : ∀ u, |P u| ≤ 1) :
    ∫ t in Icc (0:ℝ) 1, P (Int.fract (mm n * t)) = ∫ x in (0:ℝ)..1, P (Int.fract x) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    integral_fract_pattern P hP 1 hPb (mm_pos n)]
  have h1 : mm n * 1 = ((n + 1 : ℕ) : ℝ) := by simp [mm]
  rw [h1, Int.floor_natCast, Int.fract_natCast]
  simp only [intervalIntegral.integral_same, add_zero, Int.cast_natCast]
  have := mm_pos n
  rw [show ((n + 1 : ℕ) : ℝ) = mm n by simp [mm]]
  field_simp

lemma hs_Lam (n : ℕ) : Lam N (hs n) := by
  refine ⟨hs_meas n, fun w => Filter.Eventually.of_forall (hs_bounds n w), fun i => ?_⟩
  have hf : Finset.univ.filter (fun p : Fin 3 => N.com p = i) = Finset.univ := by
    ext p; simp
  rw [hf, Fin.sum_univ_three]
  show (∫ t in Icc (0:ℝ) 1, hs n 0 t) + (∫ t in Icc (0:ℝ) 1, hs n 1 t) +
    (∫ t in Icc (0:ℝ) 1, hs n 2 t) = 1
  have e0 : ∫ t in Icc (0:ℝ) 1, hs n 0 t = (1 - 4 * dd n) / 4 := by
    rw [setIntegral_congr_fun measurableSet_Icc
      (g := fun t => Pp n (Int.fract (mm n * t))) (fun t ht => by simp [hs, ht]),
      setInt_pattern n (Pp n) (Pp_meas n) (Pp_abs n), int_Pp_unit]
  have e1 : ∫ t in Icc (0:ℝ) 1, hs n 1 t = 3 / 4 := by
    rw [setIntegral_congr_fun measurableSet_Icc
      (g := fun t => Pq (Int.fract (mm n * t))) (fun t ht => by simp [hs, ht]),
      setInt_pattern n Pq Pq_meas Pq_abs, int_Pq_unit]
  have e2 : ∫ t in Icc (0:ℝ) 1, hs n 2 t = dd n := massZ_hs n
  rw [e0, e1, e2]
  ring

lemma eq_p (n : ℕ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    (0 < hs n 0 t → PsiPen N (lamS n) (hs n) 0 t ≤ 1) ∧
      (hs n 0 t < N.B 0 → 1 ≤ PsiPen N (lamS n) (hs n) 0 t) := by
  have hv : hs n 0 t = Pp n (Int.fract (mm n * t)) := by simp [hs, ht]
  have hP : PsiPen N (lamS n) (hs n) 0 t =
      1 + lamS n * max 0 (Phi (dd n) (1 + C (hs n) t)) := by
    rw [PsiPen, xiWalk_e (hs n) 0 (by decide), massZ_hs]; simp [N]
  rw [hv, hP]
  constructor
  · intro hpos
    have hu : Int.fract (mm n * t) ∈ Ioc (0:ℝ) (1/4) := by
      by_contra hu; rw [Pp, if_neg hu] at hpos; exact lt_irrefl _ hpos
    rw [Phi_r n ht hu]; simp
  · intro _
    have := mul_nonneg (lamS_pos n).le (le_max_left 0 (Phi (dd n) (1 + C (hs n) t)))
    linarith

lemma eq_q (n : ℕ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    (0 < hs n 1 t → PsiPen N (lamS n) (hs n) 1 t ≤ 1) ∧
      (hs n 1 t < N.B 1 → 1 ≤ PsiPen N (lamS n) (hs n) 1 t) := by
  have hv : hs n 1 t = Pq (Int.fract (mm n * t)) := by simp [hs, ht]
  have hP : PsiPen N (lamS n) (hs n) 1 t = lamS n * max 0 (Phi (dd n) (1 + C (hs n) t)) := by
    rw [PsiPen, xiWalk_e (hs n) 1 (by decide), massZ_hs]; simp [N]
  rw [hv, hP, show N.B 1 = 1 by simp [N]]
  constructor
  · intro _; exact lam_xi_le n _
  · intro hlt
    have hu : Int.fract (mm n * t) ∈ Ioc (1/2:ℝ) (3/4) := by
      by_contra hu; rw [Pq, if_neg hu] at hlt; exact lt_irrefl _ hlt
    rw [Phi_r' n ht hu, max_eq_right (dd_pos n).le]
    unfold lamS; linarith [eight_mm_dd n]

lemma eq_z (n : ℕ) (t : ℝ) :
    (0 < hs n 2 t → PsiPen N (lamS n) (hs n) 2 t ≤ 1) ∧
      (hs n 2 t < N.B 2 → 1 ≤ PsiPen N (lamS n) (hs n) 2 t) := by
  have hP : PsiPen N (lamS n) (hs n) 2 t = 1 := by
    rw [PsiPen, xiWalk_z]; simp [N]
  rw [hP]; exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩

lemma hs_eq (n : ℕ) : IsDTCEq N (PsiPen N (lamS n)) (hs n) := by
  refine ⟨hs_Lam n, fun i => ⟨1, fun w _ => ?_⟩⟩
  rw [ae_restrict_iff' measurableSet_Icc]
  refine Filter.Eventually.of_forall (fun t ht => ?_)
  change t ∈ Icc (0:ℝ) 1 at ht
  rcases (by decide : ∀ w : Fin 3, w = 0 ∨ w = 1 ∨ w = 2) w with rfl | rfl | rfl
  · exact eq_p n ht
  · exact eq_q n ht
  · exact eq_z n t


/-! ## L4 (part): the limit `hstar` -/

lemma hstar_Lam : Lam N hstar := by
  refine ⟨fun w => ?_, fun w => Filter.Eventually.of_forall (fun t => ?_), fun i => ?_⟩
  · unfold hstar; exact Measurable.ite measurableSet_Icc measurable_const measurable_const
  · refine ⟨fun ht => ?_, fun ht => by change t ∉ Icc (0:ℝ) 1 at ht; simp [hstar, ht]⟩
    change t ∈ Icc (0:ℝ) 1 at ht
    rcases (by decide : ∀ w : Fin 3, w = 0 ∨ w = 1 ∨ w = 2) w with rfl | rfl | rfl <;>
      simp [hstar, ht, N] <;> norm_num
  · have hf : Finset.univ.filter (fun p : Fin 3 => N.com p = i) = Finset.univ := by
      ext p; simp
    rw [hf, Fin.sum_univ_three]
    show (∫ t in Icc (0:ℝ) 1, hstar 0 t) + (∫ t in Icc (0:ℝ) 1, hstar 1 t) +
      (∫ t in Icc (0:ℝ) 1, hstar 2 t) = 1
    have e : ∀ w : Fin 3, ∫ t in Icc (0:ℝ) 1, hstar w t =
        (if w = 0 then 1/4 else if w = 1 then 3/4 else 0) := by
      intro w
      rw [setIntegral_congr_fun measurableSet_Icc
        (g := fun _ => (if w = 0 then (1/4:ℝ) else if w = 1 then 3/4 else 0))
        (fun t ht => by simp only [hstar, if_pos ht])]
      simp
    have h10 : (1:Fin 3) ≠ 0 := by decide
    have h20 : (2:Fin 3) ≠ 0 := by decide
    have h21 : (2:Fin 3) ≠ 1 := by decide
    simp only [e, h10, h20, h21, if_true, if_false]
    norm_num

lemma massZ_hstar : massZ hstar = 0 := by
  unfold massZ
  have : ∀ t, hstar 2 t = 0 := fun t => by simp [hstar]
  simp [this]

lemma hstar_feas : capFeasible N hstar := by
  refine ⟨hstar_Lam, fun e θ _ => ?_⟩
  show Phi (massZ hstar) θ ≤ 0
  rw [massZ_hstar]; unfold Phi; rw [rho_eq_zero_of_nonpos le_rfl]; simp

lemma lamS_tendsto : Tendsto lamS atTop atTop := by
  have : Tendsto (fun n : ℕ => (n:ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  exact this.const_mul_atTop (by norm_num : (0:ℝ) < 8)

/-! ## L6: the prefix deviation `(q, 0)` is admissible for `p` at `t = 1/2` -/

lemma admDev_half : ((1 : Fin 3), (0:ℝ)) ∈ admDev N (devMNS N) hstar 0 (1/2) := by
  refine ⟨rfl, fun δ hδ ε hε => ?_⟩
  set δ' := min δ (1/2) with hδ'
  set c := min ε (1/4) with hc
  have hδ'pos : 0 < δ' := lt_min hδ (by norm_num)
  have hcpos : 0 < c := lt_min hε (by norm_num)
  have hc4 : c ≤ 1/4 := min_le_right _ _
  have hsub : Icc (1/2 - δ') (1/2 + δ') ⊆ Icc (0:ℝ) 1 := by
    intro s hs; have := min_le_right δ (1/2); exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  let γ : ℝ → ℝ := (Icc (1/2 - δ') (1/2 + δ')).indicator (fun _ => c)
  have hγm : Measurable γ := measurable_const.indicator measurableSet_Icc
  have hγb : ∀ s, 0 ≤ γ s ∧ γ s ≤ c := fun s => by
    simp only [γ, Set.indicator_apply]; split_ifs <;> constructor <;> linarith
  have hγout : ∀ s, s ∉ Icc (0:ℝ) 1 → γ s = 0 := fun s hs => by
    simp only [γ, Set.indicator_apply]; rw [if_neg (fun h => hs (hsub h))]
  have hγint : ∫ s in Icc (0:ℝ) 1, γ s = (2 * δ') * c := by
    simp only [γ]
    rw [setIntegral_indicator measurableSet_Icc, Set.inter_eq_right.2 hsub]
    simp [Real.volume_Icc]
    left; rw [max_eq_left (by linarith)]; ring
  have hγi : Integrable γ (volume.restrict (Icc (0:ℝ) 1)) :=
    (integrable_const c).indicator measurableSet_Icc
  refine ⟨γ, hγm, fun s => ⟨(hγb s).1, (hγb s).2.trans (min_le_left _ _)⟩, fun s hs => ?_, ?_, ?_⟩
  · simp only [γ, Set.indicator_apply]
    rw [if_neg]
    intro h; apply hs
    exact ⟨⟨by linarith [h.1, min_le_left δ (1/2)], by linarith [h.2, min_le_left δ (1/2)]⟩, hsub h⟩
  · show 0 < ∫ s in Icc (0:ℝ) 1, γ s
    rw [hγint]; positivity
  · refine ⟨⟨fun w => ?_, fun w => Filter.Eventually.of_forall (fun t => ?_), fun i => ?_⟩, Or.inl
      ⟨rfl, 1, le_rfl, le_rfl, rfl, fun s _ j hj hj' => absurd hj' (by show ¬ (j < 1); omega)⟩⟩
    · unfold deviate; simp only [sub_zero]
      exact ((hstar_Lam.1 w).sub (Measurable.ite (MeasurableSet.const _) hγm measurable_const)).add
        (Measurable.ite (MeasurableSet.const _) hγm measurable_const)
    · unfold deviate; simp only [sub_zero]
      refine ⟨fun ht => ?_, fun ht => ?_⟩
      · change t ∈ Icc (0:ℝ) 1 at ht
        have hb := hγb t
        rcases (by decide : ∀ w : Fin 3, w = 0 ∨ w = 1 ∨ w = 2) w with rfl | rfl | rfl <;>
          simp [hstar, ht, N] <;> constructor <;> linarith
      · change t ∉ Icc (0:ℝ) 1 at ht
        have h0 := hγout t ht
        simp [hstar, ht, h0]
    · have hf : Finset.univ.filter (fun p : Fin 3 => N.com p = i) = Finset.univ := by
        ext p; simp
      rw [hf, Fin.sum_univ_three]
      show (∫ t in Icc (0:ℝ) 1, deviate hstar 0 1 γ 0 0 t) +
        (∫ t in Icc (0:ℝ) 1, deviate hstar 0 1 γ 0 1 t) +
        (∫ t in Icc (0:ℝ) 1, deviate hstar 0 1 γ 0 2 t) = 1
      have e0 : ∫ t in Icc (0:ℝ) 1, deviate hstar 0 1 γ 0 0 t = 1/4 - 2 * δ' * c := by
        rw [setIntegral_congr_fun measurableSet_Icc (g := fun t => 1/4 - γ t)
          (fun t ht => by simp [deviate, hstar, ht]), integral_sub (integrable_const _) hγi,
          hγint]
        simp
      have e1 : ∫ t in Icc (0:ℝ) 1, deviate hstar 0 1 γ 0 1 t = 3/4 + 2 * δ' * c := by
        rw [setIntegral_congr_fun measurableSet_Icc (g := fun t => 3/4 + γ t)
          (fun t ht => by simp [deviate, hstar, ht]), integral_add (integrable_const _) hγi,
          hγint]
        simp
      have e2 : ∫ t in Icc (0:ℝ) 1, deviate hstar 0 1 γ 0 2 t = 0 := by
        rw [setIntegral_congr_fun measurableSet_Icc (g := fun _ => 0)
          (fun t ht => by simp [deviate, hstar, ht])]
        simp
      rw [e0, e1, e2]; ring

/-! ## L7: assembly (open inputs: Standing, A10, A13-A16, weak convergence) -/

lemma not_scde : ¬ IsSCDE N N.Psi (capFeasible N) (devMNS N) hstar := by
  intro H
  have := H.2 0 (1/2) ⟨show (0:ℝ) ≤ 1/2 by norm_num, show (1/2:ℝ) ≤ 1 by norm_num⟩ _ admDev_half
  have h1 : N.Psi hstar 0 (1/2) = 1 := by simp [N]
  have h2 : N.Psi hstar 1 (1/2 + 0) = 0 := by simp [N]
  rw [h1, h2] at this
  norm_num at this

theorem disproof_of (hSt : N.Standing) (h10 : A10 N) (h13 : A13 N) (h14 : A14 N)
    (h15 : A15 N) (h16 : A16 N) (hW : WeakTendsto N hs hstar) :
    ¬ (∀ {I W E : Type} [Fintype I] [Fintype W] [Fintype E] [DecidableEq I]
      [DecidableEq W] [DecidableEq E] (N : Model I W E) (hN : N.Standing)
      (h2 : A2 N) (h3 : A3 N) (h5 : A5 N) (h9 : A9 N) (h10 : A10 N) (h11 : A11 N) (h12 : A12 N)
      (h13 : A13 N) (h14 : A14 N) (h15 : A15 N) (h16 : A16 N) (h17 : A17 N) (h18 : A18 N)
      (h19 : A19 N) (h22 : A22 N)
      (lam : ℕ → ℝ) (hlam : ∀ n, 0 < lam n) (hlam' : Tendsto lam atTop atTop)
      (hs : ℕ → W → ℝ → ℝ) (heq : ∀ n, IsDTCEq N (PsiPen N (lam n)) (hs n))
      (hstar : W → ℝ → ℝ) (hLam : Lam N hstar) (hweak : WeakTendsto N hs hstar)
      (hfeas : capFeasible N hstar),
      IsSCDE N N.Psi (capFeasible N) (devMNS N) hstar) := by
  intro H
  exact not_scde (H N hSt hA2 ⟨hstar, hstar_Lam⟩ hA5 hA9 h10 hA11 hA12 h13 h14 h15 h16 hA17
    hA18 hA19 hA22 lamS lamS_pos lamS_tendsto hs hs_eq hstar hstar_Lam hW hstar_feas)


/-! ## L5 (part): A13 and A10 -/

lemma env_cont (s : ℝ) : Continuous (env s) := by
  unfold env
  exact continuous_const.max (continuous_const.min
    ((continuous_id.min (continuous_const.sub continuous_id)).div_const _))

lemma Phi_cont (s : ℝ) : Continuous (Phi s) := by
  unfold Phi
  refine (continuous_const.mul ((env_cont s).comp (continuous_id.sub continuous_const))).mul
    (continuous_const.max (Real.continuous_cos.comp (continuous_const.mul
      (((continuous_id.sub continuous_const).div_const _).sub continuous_const))))

lemma hA13 : A13 N := fun _ h _ => (Phi_cont (massZ h)).continuousOn

lemma hA10 : A10 N := by
  intro h hL i
  refine ⟨2, rfl, {t | t ∈ Icc (0:ℝ) 1 ∧ h 2 t < 10}, fun t ht => ht.1,
    measurableSet_Icc.inter (measurableSet_lt (hL.1 2) measurable_const), ?_,
    fun t ht => ⟨ht.2, fun j hj => absurd hj (by show ¬ (j < 0); omega)⟩⟩
  by_contra hJ
  have hJ0 : volume {t | t ∈ Icc (0:ℝ) 1 ∧ h 2 t < 10} = 0 := le_antisymm (not_lt.1 hJ) bot_le
  have hae : ∀ᵐ t ∂(volume.restrict (Icc (0:ℝ) 1)), 10 ≤ h 2 t := by
    rw [ae_restrict_iff' measurableSet_Icc]
    have : ∀ᵐ t ∂volume, t ∉ {t | t ∈ Icc (0:ℝ) 1 ∧ h 2 t < 10} :=
      measure_eq_zero_iff_ae_notMem.1 hJ0
    filter_upwards [this] with t ht ht'
    by_contra hlt; exact ht ⟨ht', not_le.1 hlt⟩
  have hbd : ∀ w, ∀ᵐ t ∂(volume.restrict (Icc (0:ℝ) 1)), 0 ≤ h w t ∧ h w t ≤ N.B w := by
    intro w
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hL.2.1 w] with t ht ht'
    exact ht.1 ht'
  have hint2 : Integrable (h 2) (volume.restrict (Icc (0:ℝ) 1)) := by
    refine (integrable_const (10:ℝ)).mono' (hL.1 2).aestronglyMeasurable ?_
    filter_upwards [hbd 2] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg ht.1]; exact ht.2
  have h10 : (10:ℝ) ≤ ∫ t in Icc (0:ℝ) 1, h 2 t := by
    have := integral_mono_ae (integrable_const (10:ℝ)) hint2 hae
    simpa using this
  have h0 : 0 ≤ ∫ t in Icc (0:ℝ) 1, h 0 t := integral_nonneg_of_ae (by
    filter_upwards [hbd 0] with t ht; exact ht.1)
  have h1 : 0 ≤ ∫ t in Icc (0:ℝ) 1, h 1 t := integral_nonneg_of_ae (by
    filter_upwards [hbd 1] with t ht; exact ht.1)
  have hm := hL.2.2 ()
  have hf : Finset.univ.filter (fun p : Fin 3 => N.com p = ()) = Finset.univ := by
    ext p; simp
  rw [hf, Fin.sum_univ_three] at hm
  change (∫ t in Icc (0:ℝ) 1, h 0 t) + (∫ t in Icc (0:ℝ) 1, h 1 t) +
    (∫ t in Icc (0:ℝ) 1, h 2 t) = 1 at hm
  linarith


/-! ## L5 (part): Standing and A15 -/

lemma lam_bound {h : Fin 3 → ℝ → ℝ} (hL : Lam N h) (w : Fin 3) :
    ∀ᵐ t, ‖h w t‖ ≤ (Icc (0:ℝ) 1).indicator (fun _ => (10:ℝ)) t := by
  filter_upwards [hL.2.1 w] with t ht
  by_cases hti : t ∈ Icc (0:ℝ) 1
  · rw [indicator_of_mem hti, Real.norm_eq_abs, abs_of_nonneg (ht.1 hti).1]
    have h1 := (ht.1 hti).2
    have hB : N.B w ≤ 10 := by fin_cases w <;> norm_num [N]
    linarith
  · rw [indicator_of_notMem hti, ht.2 hti]; simp

lemma lam_int {h : Fin 3 → ℝ → ℝ} (hL : Lam N h) (w : Fin 3) : Integrable (h w) :=
  Integrable.mono' ((continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc)
    (hL.1 w).aestronglyMeasurable (lam_bound hL w)

lemma C_cont {h : Fin 3 → ℝ → ℝ} (hL : Lam N h) : Continuous (C h) := by
  unfold C
  exact intervalIntegral.continuous_primitive
    (fun a b => ((lam_int hL 0).add (lam_int hL 1)).intervalIntegrable) 0

lemma int_nonneg {h : Fin 3 → ℝ → ℝ} (hL : Lam N h) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hv : v ≤ 1) : 0 ≤ ∫ t in u..v, (h 0 t + h 1 t) := by
  rw [intervalIntegral.integral_of_le huv]
  refine integral_nonneg_of_ae ((ae_restrict_iff' measurableSet_Ioc).2 ?_)
  filter_upwards [hL.2.1 0, hL.2.1 1] with x h0 h1 hx
  have hx' : x ∈ Icc (0:ℝ) 1 := ⟨hu.trans hx.1.le, hx.2.trans hv⟩
  have a0 := (h0.1 hx').1
  have a1 := (h1.1 hx').1
  show (0:ℝ) ≤ h 0 x + h 1 x
  linarith

lemma C_sub {h : Fin 3 → ℝ → ℝ} (hL : Lam N h) (u v : ℝ) :
    C h v - C h u = ∫ t in u..v, (h 0 t + h 1 t) := by
  unfold C
  have hi : ∀ a b, IntervalIntegrable (fun t => h 0 t + h 1 t) volume a b :=
    fun a b => ((lam_int hL 0).add (lam_int hL 1)).intervalIntegrable
  exact intervalIntegral.integral_interval_sub_left (hi 0 v) (hi 0 u)

lemma C_mono {h : Fin 3 → ℝ → ℝ} (hL : Lam N h) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hv : v ≤ 1) : C h u ≤ C h v := by
  have h1 := C_sub hL u v
  have h2 := int_nonneg hL hu huv hv
  linarith

lemma C_zero (h : Fin 3 → ℝ → ℝ) : C h 0 = 0 := by unfold C; simp

lemma C_nonneg {h : Fin 3 → ℝ → ℝ} (hL : Lam N h) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    0 ≤ C h t := by
  have := C_mono hL (le_refl 0) ht.1 ht.2
  rwa [C_zero] at this

lemma C_one {h : Fin 3 → ℝ → ℝ} (hL : Lam N h) : C h 1 = 1 - massZ h := by
  have hm := hL.2.2 ()
  have hf : Finset.univ.filter (fun p : Fin 3 => N.com p = ()) = Finset.univ := by
    ext p; simp
  rw [hf, Fin.sum_univ_three] at hm
  change (∫ t in Icc (0:ℝ) 1, h 0 t) + (∫ t in Icc (0:ℝ) 1, h 1 t) +
    (∫ t in Icc (0:ℝ) 1, h 2 t) = 1 at hm
  have i0 : IntegrableOn (h 0) (Ioc (0:ℝ) 1) := (lam_int hL 0).integrableOn
  have i1 : IntegrableOn (h 1) (Ioc (0:ℝ) 1) := (lam_int hL 1).integrableOn
  unfold C massZ
  rw [intervalIntegral.integral_of_le zero_le_one, integral_add i0 i1,
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
  linarith

lemma hStanding : N.Standing := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · norm_num [N]
  · norm_num [N]
  · intro i; norm_num [N]
  · intro p; fin_cases p <;> norm_num [N]
  intro h hL p
  refine ⟨fun t _ => ?_, fun j _ => ⟨?_, fun t ht => ?_⟩⟩
  · show 0 ≤ (if p = 1 then (0:ℝ) else 1)
    split_ifs <;> norm_num
  · show Measurable (fun t : Icc (0:ℝ) 1 => if j = 0 then 1 + C h t else 3)
    split_ifs
    · exact (measurable_const.add (C_cont hL).measurable).comp measurable_subtype_coe
    · exact measurable_const
  · show 0 ≤ (if j = 0 then 1 + C h t else 3)
    split_ifs
    · linarith [C_nonneg hL ht]
    · norm_num

lemma pos_set {f : ℝ → ℝ} (hf : Measurable f) {u v : ℝ} (hpos : 0 < ∫ t in Ioc u v, f t) :
    0 < volume {t | t ∈ Ioc u v ∧ 0 < f t} := by
  by_contra hJ
  have hJ0 : volume {t | t ∈ Ioc u v ∧ 0 < f t} = 0 := le_antisymm (not_lt.1 hJ) bot_le
  have hae : ∀ᵐ t ∂(volume.restrict (Ioc u v)), f t ≤ 0 := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hJ0] with t ht ht'
    by_contra hlt; exact ht ⟨ht', not_le.1 hlt⟩
  have := integral_nonpos_of_ae hae
  linarith

lemma Phi_zero_of_rho {s θ : ℝ} (h : rho s = 0) : Phi s θ = 0 :=
  le_antisymm (h ▸ Phi_le_rho s θ) (Phi_nonneg s θ)

lemma rho_eq_zero_of_ge {s : ℝ} (hs : 1 / 4 ≤ s) : rho s = 0 := by
  unfold rho; apply max_eq_left; exact min_le_of_right_le (by linarith)

lemma Phi_zero_of_ge {s θ : ℝ} (hs : 0 < s) (hθ : 2 - s ≤ θ) : Phi s θ = 0 := by
  have hm : min (θ - 1) (1 - s - (θ - 1)) ≤ 0 := min_le_of_right_le (by linarith)
  have hd : min (θ - 1) (1 - s - (θ - 1)) / (2 * s) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hm (by linarith)
  have : env s (θ - 1) = 0 := by
    unfold env; apply max_eq_left; exact min_le_of_right_le hd
  unfold Phi; rw [this]; ring

lemma hA15 : A15 N := by
  intro h hL e a b ha hab hfa hlt
  change Phi (massZ h) a < Phi (massZ h) b at hlt
  have hpa := Phi_nonneg (massZ h) a
  have hs0 : 0 < massZ h := by
    by_contra hc
    have := Phi_zero_of_rho (θ := b) (rho_eq_zero_of_nonpos (not_lt.1 hc))
    linarith
  have hs1 : massZ h < 1 / 4 := by
    by_contra hc
    have := Phi_zero_of_rho (θ := b) (rho_eq_zero_of_ge (not_lt.1 hc))
    linarith
  have hb1 : 1 < b := by
    by_contra hc
    have := Phi_eq_zero_of_le_one (massZ h) b (not_lt.1 hc)
    linarith
  have ha2 : a < 2 - massZ h := by
    by_contra hc
    have h1 := Phi_zero_of_ge (θ := a) hs0 (not_lt.1 hc)
    have h2 := Phi_zero_of_ge (θ := b) hs0 (by linarith [not_lt.1 hc])
    linarith
  have hab' : a < b := by
    rcases eq_or_lt_of_le hab with h' | h'
    · rw [h'] at hlt; exact absurd hlt (lt_irrefl _)
    · exact h'
  have hA1 : a ≤ max a 1 := le_max_left _ _
  have hA2 : 1 ≤ max a 1 := le_max_right _ _
  have hB1 : min b (2 - massZ h) ≤ b := min_le_left _ _
  have hB2 : min b (2 - massZ h) ≤ 2 - massZ h := min_le_right _ _
  have ha'b' : max a 1 < min b (2 - massZ h) :=
    max_lt (lt_min hab' ha2) (lt_min hb1 (by linarith))
  have hC1 : C h 1 = 1 - massZ h := C_one hL
  have hcont : ContinuousOn (C h) (Icc (0:ℝ) 1) := (C_cont hL).continuousOn
  have hivt := intermediate_value_Icc zero_le_one hcont
  rw [C_zero, hC1] at hivt
  have ha'm : max a 1 - 1 ∈ Icc (0:ℝ) (1 - massZ h) := ⟨by linarith, by linarith⟩
  have hb'm : min b (2 - massZ h) - 1 ∈ Icc (0:ℝ) (1 - massZ h) := ⟨by linarith, by linarith⟩
  obtain ⟨t1, ht1, hCt1⟩ := hivt ha'm
  obtain ⟨t2, ht2, hCt2⟩ := hivt hb'm
  have ht12 : t1 < t2 := by
    by_contra hc
    have := C_mono hL ht2.1 (not_lt.1 hc) ht1.2
    linarith
  have hint : 0 < ∫ t in Ioc t1 t2, (h 0 t + h 1 t) := by
    have := C_sub hL t1 t2
    rw [intervalIntegral.integral_of_le ht12.le] at this
    linarith
  have i0 : IntegrableOn (h 0) (Ioc t1 t2) := (lam_int hL 0).integrableOn
  have i1 : IntegrableOn (h 1) (Ioc t1 t2) := (lam_int hL 1).integrableOn
  rw [integral_add i0 i1] at hint
  have key : ∀ w : Fin 3, w ≠ 2 → 0 < ∫ t in Ioc t1 t2, h w t →
      ∃ p j, ∃ hj : j < (N.edges p).length, (N.edges p)[j] = e ∧
        ∃ J ⊆ Icc N.t0 N.tf, MeasurableSet J ∧ 0 < volume J ∧
          ∀ t ∈ J, 0 < h p t ∧ N.tau h p j t ∈ Icc a b := by
    intro w hw hpos
    have hlen : 0 < (N.edges w).length := by fin_cases w <;> simp [N] at hw ⊢
    refine ⟨w, 0, hlen, rfl, {t | t ∈ Ioc t1 t2 ∧ 0 < h w t},
      fun t ht => ⟨ht1.1.trans ht.1.1.le, ht.1.2.trans ht2.2⟩,
      measurableSet_Ioc.inter (measurableSet_lt measurable_const (hL.1 w)),
      pos_set (hL.1 w) hpos, fun t ht => ⟨ht.2, ?_⟩⟩
    have hm1 := C_mono hL ht1.1 ht.1.1.le (ht.1.2.trans ht2.2)
    have hm2 := C_mono hL (ht1.1.trans ht.1.1.le) ht.1.2 ht2.2
    show (if (0:ℕ) = 0 then 1 + C h t else 3) ∈ Icc a b
    rw [if_pos rfl]
    constructor <;> linarith
  rcases lt_or_ge 0 (∫ t in Ioc t1 t2, h 0 t) with h0 | h0
  · exact key 0 (by decide) h0
  · exact key 1 (by decide) (by linarith)


/-! ## L5 (part): A16 -/

lemma lam_abs2 {h : Fin 3 → ℝ → ℝ} (hL : Lam N h) : ∀ᵐ t, ‖h 0 t + h 1 t‖ ≤ 2 := by
  filter_upwards [hL.2.1 0, hL.2.1 1] with t h0 h1
  by_cases hti : t ∈ Icc (0:ℝ) 1
  · have a0 := h0.1 hti
    have a1 := h1.1 hti
    have hB0 : N.B 0 = 1 := by norm_num [N]
    have hB1 : N.B 1 = 1 := by norm_num [N]
    rw [hB0] at a0
    rw [hB1] at a1
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [a0.1, a0.2, a1.1, a1.2]
  · rw [h0.2 hti, h1.2 hti]; norm_num

lemma C_lip {h : Fin 3 → ℝ → ℝ} (hL : Lam N h) {u v : ℝ} (huv : u ≤ v) :
    |C h v - C h u| ≤ 2 * (v - u) := by
  rw [C_sub hL, ← Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_of_norm_le (g := fun _ => (2:ℝ)) huv ?_
    intervalIntegrable_const).trans ?_
  · filter_upwards [lam_abs2 hL] with t ht _
    exact ht
  · rw [intervalIntegral.integral_const, smul_eq_mul]; linarith

noncomputable def G (t : ℝ) (w : Fin 3) (x : ℝ) : ℝ :=
  (if w = 2 then 0 else 1) * (Ioc (0:ℝ) t).indicator (fun _ => (1:ℝ)) x

lemma G_mul (t : ℝ) (w : Fin 3) (hw : w ≠ 2) (f : ℝ → ℝ) :
    (fun x => G t w x * f x) = (Ioc (0:ℝ) t).indicator f := by
  funext x
  by_cases hx : x ∈ Ioc (0:ℝ) t <;> simp [G, hw, hx]

lemma G_two (t x : ℝ) : G t 2 x = 0 := by simp [G]

lemma G_memLp (t : ℝ) (w : Fin 3) : MemLp (G t w) 2 (volume.restrict (Icc N.t0 N.tf)) := by
  haveI : IsFiniteMeasure (volume.restrict (Icc N.t0 N.tf)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
  refine MemLp.of_bound ?_ 1 (Eventually.of_forall fun x => ?_)
  · exact (measurable_const.mul (measurable_const.indicator measurableSet_Ioc)).aestronglyMeasurable
  · by_cases hw : w = 2
    · simp [G, hw]
    · by_cases hx : x ∈ Ioc (0:ℝ) t <;> simp [G, hw, hx]

lemma C_eq_pair {g : Fin 3 → ℝ → ℝ} (hL : Lam N g) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    C g t = pair N (G t) g := by
  unfold pair
  rw [Fin.sum_univ_three, G_mul t 0 (by decide), G_mul t 1 (by decide)]
  simp only [G_two, zero_mul, integral_zero, add_zero]
  change C g t = (∫ x in Icc (0:ℝ) 1, (Ioc (0:ℝ) t).indicator (g 0) x) +
    (∫ x in Icc (0:ℝ) 1, (Ioc (0:ℝ) t).indicator (g 1) x)
  have hsub : Icc (0:ℝ) 1 ∩ Ioc 0 t = Ioc 0 t :=
    inter_eq_right.2 (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl ht.2))
  rw [setIntegral_indicator measurableSet_Ioc, setIntegral_indicator measurableSet_Ioc, hsub]
  have i0 : IntegrableOn (g 0) (Ioc (0:ℝ) t) := (lam_int hL 0).integrableOn
  have i1 : IntegrableOn (g 1) (Ioc (0:ℝ) t) := (lam_int hL 1).integrableOn
  unfold C
  rw [intervalIntegral.integral_of_le ht.1, integral_add i0 i1]

lemma C_tendsto {hs : ℕ → Fin 3 → ℝ → ℝ} {h : Fin 3 → ℝ → ℝ} (hW : WeakConvSeq N hs h)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : Tendsto (fun n => C (hs n) t) atTop (𝓝 (C h t)) := by
  have := hW.2.2 (G t) (fun w => G_memLp t w)
  rw [← C_eq_pair hW.2.1 ht] at this
  exact this.congr (fun n => (C_eq_pair (hW.1 n) ht).symm)

lemma unif_of_lip {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hF : ∀ n u v, 0 ≤ u → u ≤ v → v ≤ 1 → |F n v - F n u| ≤ 2 * (v - u))
    (hf : ∀ u v, 0 ≤ u → u ≤ v → v ≤ 1 → |f v - f u| ≤ 2 * (v - u))
    (hpt : ∀ t ∈ Icc (0:ℝ) 1, Tendsto (fun n => F n t) atTop (𝓝 (f t))) :
    TendstoUniformlyOn F f atTop (Icc (0:ℝ) 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨M, hM⟩ := exists_nat_gt (12 / ε)
  have hMpos : (0:ℝ) < M := lt_trans (by positivity) hM
  have hMε : 4 / (M:ℝ) < ε / 3 := by
    rw [div_lt_iff₀ hMpos]; rw [div_lt_iff₀ hε] at hM; linarith
  have hgrid : ∀ᶠ n in atTop, ∀ k : Fin (M + 1),
      dist (F n (((k:ℕ):ℝ) / M)) (f (((k:ℕ):ℝ) / M)) < ε / 3 := by
    rw [Filter.eventually_all]
    intro k
    have hk : ((k:ℕ):ℝ) / M ∈ Icc (0:ℝ) 1 := ⟨by positivity, by
      rw [div_le_iff₀ hMpos, one_mul]; exact_mod_cast Nat.lt_succ_iff.1 k.2⟩
    exact Metric.tendsto_nhds.1 (hpt _ hk) (ε / 3) (by positivity)
  filter_upwards [hgrid] with n hn x hx
  obtain ⟨k, hk⟩ : ∃ k, k = ⌊x * M⌋₊ := ⟨_, rfl⟩
  have hxM : 0 ≤ x * M := mul_nonneg hx.1 hMpos.le
  have hk1 : (k:ℝ) ≤ x * M := by rw [hk]; exact Nat.floor_le hxM
  have hk2 : x * M < k + 1 := by rw [hk]; exact Nat.lt_floor_add_one _
  have hkM : k ≤ M := by
    have : (k:ℝ) ≤ M := hk1.trans (by nlinarith [hx.2])
    exact_mod_cast this
  have hg : dist (F n ((k:ℝ) / M)) (f ((k:ℝ) / M)) < ε / 3 := hn ⟨k, Nat.lt_succ_of_le hkM⟩
  have hxk1 : (k:ℝ) / M ≤ x := by rw [div_le_iff₀ hMpos]; linarith
  have hxk2 : x ≤ ((k:ℝ) + 1) / M := by rw [le_div_iff₀ hMpos]; linarith
  have hsplit : ((k:ℝ) + 1) / M = k / M + 1 / M := by ring
  have hk0 : 0 ≤ (k:ℝ) / M := by positivity
  have e1 := hF n _ _ hk0 hxk1 hx.2
  have e2 := hf _ _ hk0 hxk1 hx.2
  rw [Real.dist_eq] at hg ⊢
  have h4 : 4 / (M:ℝ) = 4 * (1 / M) := by ring
  rw [abs_le] at e1 e2
  rw [abs_lt] at hg ⊢
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, hg.1, hg.2]

lemma hA16 : A16 N := by
  intro hs h hW p j _
  have hL := hW.2.1
  have hLn := hW.1
  rcases eq_or_ne j 0 with hj0 | hj0
  · subst hj0
    show TendstoUniformlyOn (fun n t => 1 + C (hs n) t) (fun t => 1 + C h t) atTop
      (Icc (0:ℝ) 1)
    refine unif_of_lip (fun n u v _ huv _ => ?_) (fun u v _ huv _ => ?_) (fun t ht => ?_)
    · rw [add_sub_add_left_eq_sub]; exact C_lip (hLn n) huv
    · rw [add_sub_add_left_eq_sub]; exact C_lip hL huv
    · exact (C_tendsto hW ht).const_add 1
  · show TendstoUniformlyOn (fun n t => if j = 0 then 1 + C (hs n) t else 3)
      (fun t => if j = 0 then 1 + C h t else 3) atTop (Icc (0:ℝ) 1)
    simp only [hj0, ↓reduceIte]
    exact Metric.tendstoUniformlyOn_iff.2 fun ε hε =>
      Eventually.of_forall fun n x _ => by simpa using hε


/-! ## L5 (part): A14 -/

lemma rho_cont : Continuous rho :=
  continuous_const.max (continuous_id.min (continuous_const.sub continuous_id))

lemma Phi_contAt {p : ℝ × ℝ} (h1 : 0 < p.1) (h2 : p.1 < 1 / 4) :
    ContinuousAt (fun q : ℝ × ℝ => Phi q.1 q.2) p := by
  have hfst : Continuous (fun q : ℝ × ℝ => q.1) := continuous_fst
  have hsnd : Continuous (fun q : ℝ × ℝ => q.2) := continuous_snd
  have hrho : ContinuousAt (fun q : ℝ × ℝ => rho q.1) p := (rho_cont.comp hfst).continuousAt
  have henv : ContinuousAt (fun q : ℝ × ℝ => env q.1 (q.2 - 1)) p := by
    unfold env
    refine continuousAt_const.max (continuousAt_const.min (ContinuousAt.div ?_ ?_ ?_))
    · exact ((hsnd.sub continuous_const).min
        ((continuous_const.sub hfst).sub (hsnd.sub continuous_const))).continuousAt
    · exact (continuous_const.mul hfst).continuousAt
    · exact (by linarith : (0:ℝ) < 2 * p.1).ne'
  have hin : ContinuousAt (fun q : ℝ × ℝ =>
      2 * Real.pi * ((q.2 - 1) / per q.1 - ustar q.1)) p := by
    unfold per ustar
    refine continuousAt_const.mul (ContinuousAt.sub (ContinuousAt.div ?_ ?_ ?_)
      (ContinuousAt.div ?_ ?_ ?_))
    · exact (hsnd.sub continuous_const).continuousAt
    · exact ((continuous_const.sub hfst).mul (continuous_const.mul hfst)).continuousAt
    · exact (mul_pos (by linarith) (by linarith)).ne'
    · exact (continuous_const.sub hfst).continuousAt
    · exact (continuous_const.sub hfst).continuousAt
    · exact (by linarith : (0:ℝ) < 1 - p.1).ne'
  have hcos : ContinuousAt (fun q : ℝ × ℝ =>
      max 0 (Real.cos (2 * Real.pi * ((q.2 - 1) / per q.1 - ustar q.1)))) p :=
    continuousAt_const.max (Real.continuous_cos.continuousAt.comp hin)
  exact (hrho.mul henv).mul hcos

lemma Phi_unif {s : ℕ → ℝ} {s0 : ℝ} (hs : Tendsto s atTop (𝓝 s0)) :
    TendstoUniformlyOn (fun n θ => Phi (s n) θ) (fun θ => Phi s0 θ) atTop (Ici 0) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_cases hr : rho s0 = 0
  · have hrt : Tendsto (fun n => rho (s n)) atTop (𝓝 0) := by
      have := (rho_cont.tendsto s0).comp hs
      rw [hr] at this
      exact this
    filter_upwards [hrt.eventually (gt_mem_nhds hε)] with n hn θ _
    show dist (Phi s0 θ) (Phi (s n) θ) < ε
    rw [Phi_zero_of_rho hr, dist_zero_left, Real.norm_eq_abs, abs_of_nonneg (Phi_nonneg _ _)]
    exact lt_of_le_of_lt (Phi_le_rho _ _) hn
  · have hpos : 0 < s0 := by
      by_contra hc; exact hr (rho_eq_zero_of_nonpos (not_lt.1 hc))
    have hlt : s0 < 1 / 4 := by
      by_contra hc; exact hr (rho_eq_zero_of_ge (not_lt.1 hc))
    have hS : IsCompact (Icc (s0 / 2) ((s0 + 1 / 4) / 2) ×ˢ Icc (1:ℝ) 2) :=
      isCompact_Icc.prod isCompact_Icc
    have hcont : ContinuousOn (fun q : ℝ × ℝ => Phi q.1 q.2)
        (Icc (s0 / 2) ((s0 + 1 / 4) / 2) ×ˢ Icc (1:ℝ) 2) :=
      fun q hq => (Phi_contAt (by linarith [hq.1.1]) (by linarith [hq.1.2])).continuousWithinAt
    obtain ⟨δ, hδ, hU⟩ :=
      Metric.uniformContinuousOn_iff.1 (hS.uniformContinuousOn_of_continuous hcont) ε hε
    have hev1 : ∀ᶠ n in atTop, s n ∈ Ioo (s0 / 2) ((s0 + 1 / 4) / 2) :=
      hs.eventually (Ioo_mem_nhds (by linarith) (by linarith))
    have hev2 : ∀ᶠ n in atTop, dist (s n) s0 < δ := Metric.tendsto_nhds.1 hs δ hδ
    filter_upwards [hev1, hev2] with n hn1 hn2 θ _
    show dist (Phi s0 θ) (Phi (s n) θ) < ε
    by_cases hθ1 : θ ≤ 1
    · rw [Phi_eq_zero_of_le_one _ _ hθ1, Phi_eq_zero_of_le_one _ _ hθ1, dist_self]; exact hε
    by_cases hθ2 : 2 ≤ θ
    · rw [Phi_zero_of_ge hpos (by linarith),
        Phi_zero_of_ge (by linarith [hn1.1] : 0 < s n) (by linarith [hn1.1]), dist_self]
      exact hε
    push_neg at hθ1 hθ2
    exact hU (s0, θ) ⟨⟨by linarith, by linarith⟩, ⟨hθ1.le, hθ2.le⟩⟩ (s n, θ)
      ⟨⟨hn1.1.le, hn1.2.le⟩, ⟨hθ1.le, hθ2.le⟩⟩
      (by rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, dist_comm]; exact hn2)

lemma massZ_eq_pair (g : Fin 3 → ℝ → ℝ) :
    massZ g = pair N (fun w _ => if w = 2 then (1:ℝ) else 0) g := by
  unfold pair massZ
  simp [Fin.sum_univ_three, N]

lemma massZ_tendsto {hs : ℕ → Fin 3 → ℝ → ℝ} {h : Fin 3 → ℝ → ℝ} (hW : WeakConvSeq N hs h) :
    Tendsto (fun n => massZ (hs n)) atTop (𝓝 (massZ h)) := by
  haveI : IsFiniteMeasure (volume.restrict (Icc N.t0 N.tf)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
  have := hW.2.2 (fun w _ => if w = 2 then (1:ℝ) else 0) (fun w => memLp_const _)
  rw [← massZ_eq_pair h] at this
  exact this.congr fun n => (massZ_eq_pair _).symm

lemma hA14 : A14 N := fun _ _ hW _ => Phi_unif (massZ_tendsto hW)


/-! ## L1: weak convergence of fract patterns -/

lemma cell_zero {Q : ℝ → ℝ} (hQ : Measurable Q) {K : ℝ} (hK : ∀ u, |Q u| ≤ K)
    (h0 : ∫ x in (0:ℝ)..1, Q (Int.fract x) = 0) {M : ℕ} (hM : (0:ℝ) < M) (k : ℕ) :
    ∫ t in (0:ℝ)..((k:ℝ) / M), Q (Int.fract ((M:ℝ) * t)) = 0 := by
  rw [integral_fract_pattern Q hQ K hK hM, h0,
    show (M:ℝ) * ((k:ℝ) / M) = k by field_simp, Int.fract_natCast]
  simp

lemma pat_ii {Q : ℝ → ℝ} (hQ : Measurable Q) {K : ℝ} (hK : ∀ u, |Q u| ≤ K) (c a b : ℝ) :
    IntervalIntegrable (fun t => Q (Int.fract (c * t))) volume a b :=
  ii_of_bdd (hQ.comp (measurable_fract.comp (measurable_const.mul measurable_id)))
    (fun x => hK _) a b

lemma cell_int {Q : ℝ → ℝ} (hQ : Measurable Q) {K : ℝ} (hK : ∀ u, |Q u| ≤ K)
    (h0 : ∫ x in (0:ℝ)..1, Q (Int.fract x) = 0) {M : ℕ} (hM : (0:ℝ) < M) (k : ℕ) :
    ∫ t in ((k:ℝ) / M)..(((k:ℝ) + 1) / M), Q (Int.fract ((M:ℝ) * t)) = 0 := by
  have h1 := cell_zero hQ hK h0 hM (k + 1)
  have h2 := cell_zero hQ hK h0 hM k
  push_cast at h1
  rw [← intervalIntegral.integral_interval_sub_left (pat_ii hQ hK _ 0 _) (pat_ii hQ hK _ 0 _),
    h1, h2, sub_zero]

lemma cell_bound {f Q : ℝ → ℝ} {M : ℕ} (hMr : (0:ℝ) < M) {k : ℕ} {C : ℝ}
    (hC : ∀ x ∈ Ioc ((k:ℝ) / M) (((k:ℝ) + 1) / M),
      |(f x - f ((k:ℝ) / M)) * Q (Int.fract ((M:ℝ) * x))| ≤ C)
    (hcell : ∫ t in ((k:ℝ) / M)..(((k:ℝ) + 1) / M), Q (Int.fract ((M:ℝ) * t)) = 0)
    (hfi : IntervalIntegrable (fun t => f t * Q (Int.fract ((M:ℝ) * t))) volume
      ((k:ℝ) / M) (((k:ℝ) + 1) / M))
    (hQi : IntervalIntegrable (fun t => Q (Int.fract ((M:ℝ) * t))) volume
      ((k:ℝ) / M) (((k:ℝ) + 1) / M)) :
    |∫ t in ((k:ℝ) / M)..(((k:ℝ) + 1) / M), f t * Q (Int.fract ((M:ℝ) * t))| ≤ C * (1 / M) := by
  have e : ∫ t in ((k:ℝ) / M)..(((k:ℝ) + 1) / M), f t * Q (Int.fract ((M:ℝ) * t)) =
      ∫ t in ((k:ℝ) / M)..(((k:ℝ) + 1) / M),
        (f t - f ((k:ℝ) / M)) * Q (Int.fract ((M:ℝ) * t)) := by
    simp only [sub_mul]
    rw [intervalIntegral.integral_sub hfi (hQi.const_mul _), intervalIntegral.integral_const_mul,
      hcell, mul_zero, sub_zero]
  rw [e, ← Real.norm_eq_abs]
  have hle : (k:ℝ) / M ≤ ((k:ℝ) + 1) / M := div_le_div_of_nonneg_right (by linarith) hMr.le
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (k:ℝ) / M)
    (b := ((k:ℝ) + 1) / M) (C := C)
    (f := fun t => (f t - f ((k:ℝ) / M)) * Q (Int.fract ((M:ℝ) * t)))
    (fun x hx => by rw [uIoc_of_le hle] at hx; rw [Real.norm_eq_abs]; exact hC x hx)
  rw [show ((k:ℝ) + 1) / M - k / M = 1 / M by ring,
    abs_of_pos (by positivity : (0:ℝ) < 1 / M)] at hb
  exact hb

lemma cont_bound {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (0:ℝ) 1)) {Q : ℝ → ℝ} (hQ : Measurable Q)
    {K : ℝ} (hK : ∀ u, |Q u| ≤ K) (h0 : ∫ x in (0:ℝ)..1, Q (Int.fract x) = 0) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ M : ℕ, N0 ≤ M → 0 < M →
      |∫ t in (0:ℝ)..1, f t * Q (Int.fract ((M:ℝ) * t))| ≤ ε := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  obtain ⟨δ, hδ, hU⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) (ε / (K + 1)) (by positivity)
  obtain ⟨N0, hN0⟩ := exists_nat_gt (1 / δ)
  refine ⟨N0, fun M hM hMpos => ?_⟩
  have hMr : (0:ℝ) < M := by exact_mod_cast hMpos
  have hMδ : 1 / (M:ℝ) < δ := by
    have h1 : (N0:ℝ) ≤ M := by exact_mod_cast hM
    rw [div_lt_iff₀ hMr]; rw [div_lt_iff₀ hδ] at hN0; nlinarith
  have hsub : ∀ k < M, Icc ((k:ℝ) / M) (((k:ℝ) + 1) / M) ⊆ Icc (0:ℝ) 1 := by
    intro k hk
    have : ((k:ℝ) + 1) ≤ M := by exact_mod_cast hk
    exact Icc_subset_Icc (by positivity) (by rw [div_le_iff₀ hMr]; linarith)
  have hle : ∀ k : ℕ, (k:ℝ) / M ≤ ((k:ℝ) + 1) / M :=
    fun k => div_le_div_of_nonneg_right (by linarith) hMr.le
  have hfi : ∀ k < M, IntervalIntegrable (fun t => f t * Q (Int.fract ((M:ℝ) * t))) volume
      ((k:ℝ) / M) (((k:ℝ) + 1) / M) := by
    intro k hk
    exact (pat_ii hQ hK _ _ _).continuousOn_mul
      (hf.mono (by rw [uIcc_of_le (hle k)]; exact hsub k hk))
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ => (k:ℝ) / M) (f := fun t => f t * Q (Int.fract ((M:ℝ) * t)))
    (μ := volume) (n := M) (fun k hk => by simpa [Nat.cast_succ] using hfi k hk)
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div, div_self hMr.ne'] at hsum
  rw [← hsum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum
    (g := fun _ => ε / (K + 1) * K * (1 / M)) fun k hk => ?_).trans ?_)
  · have hk' : k < M := Finset.mem_range.1 hk
    refine cell_bound hMr (fun x hx => ?_) (cell_int hQ hK h0 hMr k) (hfi k hk')
      (pat_ii hQ hK _ _ _)
    have hx01 : x ∈ Icc (0:ℝ) 1 := hsub k hk' ⟨hx.1.le, hx.2⟩
    have hk01 : (k:ℝ) / M ∈ Icc (0:ℝ) 1 := hsub k hk' ⟨le_rfl, hle k⟩
    have hsplit : ((k:ℝ) + 1) / M = k / M + 1 / M := by ring
    have hd : dist x ((k:ℝ) / M) < δ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hx.1])]; linarith [hx.2]
    have hfx := hU x hx01 _ hk01 hd
    rw [Real.dist_eq] at hfx
    rw [abs_mul]
    exact mul_le_mul hfx.le (hK _) (abs_nonneg _) (div_pos hε (by linarith)).le
  · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm, mul_assoc,
      one_div_mul_cancel hMr.ne', mul_one, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith

lemma weak_pattern {f : ℝ → ℝ} (hf : IntegrableOn f (Icc (0:ℝ) 1)) {Q : ℝ → ℝ}
    (hQ : Measurable Q) {K : ℝ} (hK : ∀ u, |Q u| ≤ K)
    (h0 : ∫ x in (0:ℝ)..1, Q (Int.fract x) = 0) :
    Tendsto (fun n => ∫ t in Icc (0:ℝ) 1, f t * Q (Int.fract (mm n * t))) atTop (𝓝 0) := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hfi : Integrable ((Icc (0:ℝ) 1).indicator f) := hf.integrable_indicator measurableSet_Icc
  obtain ⟨g, -, hgf, hgc, hgi⟩ :=
    hfi.exists_hasCompactSupport_integral_sub_le (ε := ε / (2 * (K + 1))) (by positivity)
  obtain ⟨N0, hN0⟩ := cont_bound hgc.continuousOn hQ hK h0 (ε := ε / 3) (by positivity)
  refine ⟨N0, fun n hn => ?_⟩
  have hMn : mm n = ((n + 1 : ℕ) : ℝ) := by unfold mm; push_cast; ring
  have hb := hN0 (n + 1) (by omega) (by omega)
  rw [← hMn] at hb
  have hPm : Measurable (fun t => Q (Int.fract (mm n * t))) :=
    hQ.comp (measurable_fract.comp (measurable_const.mul measurable_id))
  have hPb : ∀ t, ‖Q (Int.fract (mm n * t))‖ ≤ K := fun t => by
    rw [Real.norm_eq_abs]; exact hK _
  have hgI : IntegrableOn g (Icc (0:ℝ) 1) := hgi.integrableOn
  have hA : IntegrableOn (fun t => (f t - g t) * Q (Int.fract (mm n * t))) (Icc (0:ℝ) 1) :=
    (hf.sub hgI).mul_bdd hPm.aestronglyMeasurable (Eventually.of_forall hPb)
  have i2 : IntegrableOn (fun t => g t * Q (Int.fract (mm n * t))) (Icc (0:ℝ) 1) :=
    hgI.mul_bdd hPm.aestronglyMeasurable (Eventually.of_forall hPb)
  have split : ∫ t in Icc (0:ℝ) 1, f t * Q (Int.fract (mm n * t)) =
      (∫ t in Icc (0:ℝ) 1, (f t - g t) * Q (Int.fract (mm n * t))) +
        ∫ t in (0:ℝ)..1, g t * Q (Int.fract (mm n * t)) := by
    have e1 : ∫ t in Icc (0:ℝ) 1, f t * Q (Int.fract (mm n * t)) =
        ∫ t in Icc (0:ℝ) 1, ((f t - g t) * Q (Int.fract (mm n * t)) +
          g t * Q (Int.fract (mm n * t))) := by
      congr 1; funext t; ring
    rw [e1, integral_add hA i2, intervalIntegral.integral_of_le zero_le_one,
      ← integral_Icc_eq_integral_Ioc]
  have hfirst : |∫ t in Icc (0:ℝ) 1, (f t - g t) * Q (Int.fract (mm n * t))| ≤
      K * (ε / (2 * (K + 1))) := by
    rw [← Real.norm_eq_abs]
    calc ‖∫ t in Icc (0:ℝ) 1, (f t - g t) * Q (Int.fract (mm n * t))‖
        ≤ ∫ t in Icc (0:ℝ) 1, K * ‖(Icc (0:ℝ) 1).indicator f t - g t‖ := by
          refine norm_integral_le_of_norm_le ((hfi.sub hgi).norm.const_mul K).integrableOn ?_
          rw [ae_restrict_iff' measurableSet_Icc]
          refine Eventually.of_forall fun t ht => ?_
          rw [indicator_of_mem ht, norm_mul]
          exact (mul_le_mul_of_nonneg_left (hPb t) (norm_nonneg _)).trans_eq (mul_comm _ _)
      _ ≤ ∫ t, K * ‖(Icc (0:ℝ) 1).indicator f t - g t‖ :=
          setIntegral_le_integral ((hfi.sub hgi).norm.const_mul K)
            (Eventually.of_forall fun t => mul_nonneg hK0 (norm_nonneg _))
      _ = K * ∫ t, ‖(Icc (0:ℝ) 1).indicator f t - g t‖ := integral_const_mul _ _
      _ ≤ K * (ε / (2 * (K + 1))) := mul_le_mul_of_nonneg_left hgf hK0
  have hKe : K * (ε / (2 * (K + 1))) ≤ ε / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  rw [Real.dist_eq, sub_zero, split]
  refine lt_of_le_of_lt (abs_add_le _ _) ?_
  linarith


/-! ## L4b: WeakTendsto N hs hstar -/

noncomputable def Q1 (u : ℝ) : ℝ := Pp 0 u - 1 / 8

noncomputable def Q2 (u : ℝ) : ℝ := Pq u - 3 / 4

lemma dd_zero : dd 0 = 1 / 8 := by unfold dd mm; norm_num

lemma Pp_scale (n : ℕ) (u : ℝ) : Pp n u = 2 * (1 - 4 * dd n) * Pp 0 u := by
  unfold Pp; rw [dd_zero]; split_ifs <;> ring

lemma Q1_meas : Measurable Q1 := (Pp_meas 0).sub measurable_const

lemma Q2_meas : Measurable Q2 := Pq_meas.sub measurable_const

lemma Q1_abs (u : ℝ) : |Q1 u| ≤ 2 := by
  unfold Q1
  obtain ⟨h1, h2⟩ := abs_le.1 (Pp_abs 0 u)
  rw [abs_le]; constructor <;> linarith

lemma Q2_abs (u : ℝ) : |Q2 u| ≤ 2 := by
  unfold Q2
  obtain ⟨h1, h2⟩ := abs_le.1 (Pq_abs u)
  rw [abs_le]; constructor <;> linarith

lemma Q1_mean : ∫ x in (0:ℝ)..1, Q1 (Int.fract x) = 0 := by
  unfold Q1
  rw [intervalIntegral.integral_sub
    (ii_of_bdd (f := fun x => Pp 0 (Int.fract x)) ((Pp_meas 0).comp measurable_fract)
      (fun x => Pp_abs 0 _) 0 1)
    intervalIntegrable_const, int_Pp_unit, intervalIntegral.integral_const, dd_zero]
  norm_num

lemma Q2_mean : ∫ x in (0:ℝ)..1, Q2 (Int.fract x) = 0 := by
  unfold Q2
  rw [intervalIntegral.integral_sub
    (ii_of_bdd (f := fun x => Pq (Int.fract x)) (Pq_meas.comp measurable_fract)
      (fun x => Pq_abs _) 0 1)
    intervalIntegrable_const, int_Pq_unit, intervalIntegral.integral_const]
  norm_num

lemma dd_tendsto : Tendsto dd atTop (𝓝 0) := by
  have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1 / 8 : ℝ)
  rw [mul_zero] at this
  refine this.congr (fun n => ?_)
  unfold dd mm; field_simp

lemma pair_hs (g : Fin 3 → ℝ → ℝ) (hint : ∀ w, IntegrableOn (g w) (Icc (0:ℝ) 1)) (n : ℕ) :
    pair N g (hs n) =
      2 * (1 - 4 * dd n) * ((∫ t in Icc (0:ℝ) 1, g 0 t * Q1 (Int.fract (mm n * t))) +
        1 / 8 * ∫ t in Icc (0:ℝ) 1, g 0 t) +
      ((∫ t in Icc (0:ℝ) 1, g 1 t * Q2 (Int.fract (mm n * t))) +
        3 / 4 * ∫ t in Icc (0:ℝ) 1, g 1 t) +
      dd n * ∫ t in Icc (0:ℝ) 1, g 2 t := by
  unfold pair
  rw [Fin.sum_univ_three]
  change (∫ t in Icc (0:ℝ) 1, g 0 t * hs n 0 t) + (∫ t in Icc (0:ℝ) 1, g 1 t * hs n 1 t) +
    (∫ t in Icc (0:ℝ) 1, g 2 t * hs n 2 t) = _
  have hm1 : Measurable (fun t => Q1 (Int.fract (mm n * t))) :=
    Q1_meas.comp (measurable_fract.comp (measurable_const.mul measurable_id))
  have hm2 : Measurable (fun t => Q2 (Int.fract (mm n * t))) :=
    Q2_meas.comp (measurable_fract.comp (measurable_const.mul measurable_id))
  have iA : IntegrableOn (fun t => g 0 t * Q1 (Int.fract (mm n * t))) (Icc (0:ℝ) 1) :=
    (hint 0).mul_bdd hm1.aestronglyMeasurable
      (Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact Q1_abs _)
  have iB : IntegrableOn (fun t => g 1 t * Q2 (Int.fract (mm n * t))) (Icc (0:ℝ) 1) :=
    (hint 1).mul_bdd hm2.aestronglyMeasurable
      (Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact Q2_abs _)
  have h0 : EqOn (fun t => g 0 t * hs n 0 t)
      (fun t => 2 * (1 - 4 * dd n) * (g 0 t * Q1 (Int.fract (mm n * t)) + 1 / 8 * g 0 t))
      (Icc (0:ℝ) 1) := fun t ht => by
    dsimp only
    rw [show hs n 0 t = Pp n (Int.fract (mm n * t)) from by simp [hs, ht], Pp_scale]
    unfold Q1; ring
  have h1 : EqOn (fun t => g 1 t * hs n 1 t)
      (fun t => g 1 t * Q2 (Int.fract (mm n * t)) + 3 / 4 * g 1 t) (Icc (0:ℝ) 1) := fun t ht => by
    dsimp only
    rw [show hs n 1 t = Pq (Int.fract (mm n * t)) from by simp [hs, ht]]
    unfold Q2; ring
  have h2 : EqOn (fun t => g 2 t * hs n 2 t) (fun t => dd n * g 2 t) (Icc (0:ℝ) 1) :=
    fun t ht => by
      dsimp only
      rw [show hs n 2 t = dd n from by simp [hs, ht]]
      ring
  rw [setIntegral_congr_fun measurableSet_Icc h0, setIntegral_congr_fun measurableSet_Icc h1,
    setIntegral_congr_fun measurableSet_Icc h2, integral_const_mul,
    integral_add iA ((hint 0).const_mul _), integral_const_mul,
    integral_add iB ((hint 1).const_mul _), integral_const_mul, integral_const_mul]

lemma pair_hstar (g : Fin 3 → ℝ → ℝ) :
    pair N g hstar = 1 / 4 * (∫ t in Icc (0:ℝ) 1, g 0 t) + 3 / 4 * ∫ t in Icc (0:ℝ) 1, g 1 t := by
  unfold pair
  rw [Fin.sum_univ_three]
  change (∫ t in Icc (0:ℝ) 1, g 0 t * hstar 0 t) + (∫ t in Icc (0:ℝ) 1, g 1 t * hstar 1 t) +
    (∫ t in Icc (0:ℝ) 1, g 2 t * hstar 2 t) = _
  have h0 : EqOn (fun t => g 0 t * hstar 0 t) (fun t => 1 / 4 * g 0 t) (Icc (0:ℝ) 1) :=
    fun t ht => by dsimp only; rw [show hstar 0 t = 1 / 4 from by simp [hstar, ht]]; ring
  have h1 : EqOn (fun t => g 1 t * hstar 1 t) (fun t => 3 / 4 * g 1 t) (Icc (0:ℝ) 1) :=
    fun t ht => by dsimp only; rw [show hstar 1 t = 3 / 4 from by simp [hstar, ht]]; ring
  have h2 : EqOn (fun t => g 2 t * hstar 2 t) (fun _ => (0:ℝ)) (Icc (0:ℝ) 1) :=
    fun t ht => by dsimp only; rw [show hstar 2 t = 0 from by simp [hstar, ht]]; ring
  rw [setIntegral_congr_fun measurableSet_Icc h0, setIntegral_congr_fun measurableSet_Icc h1,
    setIntegral_congr_fun measurableSet_Icc h2, integral_const_mul, integral_const_mul,
    integral_zero, add_zero]

lemma hW : WeakTendsto N hs hstar := by
  intro g hg
  haveI : IsFiniteMeasure (volume.restrict (Icc N.t0 N.tf)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
  have hint : ∀ w, IntegrableOn (g w) (Icc (0:ℝ) 1) := fun w => (hg w).integrable one_le_two
  have T0 := weak_pattern (hint 0) Q1_meas Q1_abs Q1_mean
  have T1 := weak_pattern (hint 1) Q2_meas Q2_abs Q2_mean
  have Tc : Tendsto (fun n => 2 * (1 - 4 * dd n)) atTop (𝓝 (2 * (1 - 4 * 0))) :=
    (tendsto_const_nhds.sub (dd_tendsto.const_mul 4)).const_mul 2
  have hlim := ((Tc.mul (T0.add (tendsto_const_nhds (x := 1 / 8 * ∫ t in Icc (0:ℝ) 1, g 0 t)))).add
    (T1.add (tendsto_const_nhds (x := 3 / 4 * ∫ t in Icc (0:ℝ) 1, g 1 t)))).add
    (dd_tendsto.mul (tendsto_const_nhds (x := ∫ t in Icc (0:ℝ) 1, g 2 t)))
  rw [pair_hstar]
  have e : (fun n => pair N g (hs n)) = fun n =>
      2 * (1 - 4 * dd n) * ((∫ t in Icc (0:ℝ) 1, g 0 t * Q1 (Int.fract (mm n * t))) +
        1 / 8 * ∫ t in Icc (0:ℝ) 1, g 0 t) +
      ((∫ t in Icc (0:ℝ) 1, g 1 t * Q2 (Int.fract (mm n * t))) +
        3 / 4 * ∫ t in Icc (0:ℝ) 1, g 1 t) +
      dd n * ∫ t in Icc (0:ℝ) 1, g 2 t := funext fun n => pair_hs g hint n
  rw [e]
  convert hlim using 2
  ring

end Cex999

open SideConstrainedDTA.Existence in
theorem solution :
    ¬ (∀ {I W E : Type} [Fintype I] [Fintype W] [Fintype E] [DecidableEq I]
      [DecidableEq W] [DecidableEq E] (N : Model I W E) (hN : N.Standing)
      (h2 : A2 N) (h3 : A3 N) (h5 : A5 N) (h9 : A9 N) (h10 : A10 N) (h11 : A11 N) (h12 : A12 N)
      (h13 : A13 N) (h14 : A14 N) (h15 : A15 N) (h16 : A16 N) (h17 : A17 N) (h18 : A18 N)
      (h19 : A19 N) (h22 : A22 N)
      (lam : ℕ → ℝ) (hlam : ∀ n, 0 < lam n) (hlam' : Tendsto lam atTop atTop)
      (hs : ℕ → W → ℝ → ℝ) (heq : ∀ n, IsDTCEq N (PsiPen N (lam n)) (hs n))
      (hstar : W → ℝ → ℝ) (hLam : Lam N hstar) (hweak : WeakTendsto N hs hstar)
      (hfeas : capFeasible N hstar),
      IsSCDE N N.Psi (capFeasible N) (devMNS N) hstar) := by
  exact Cex999.disproof_of Cex999.hStanding Cex999.hA10 Cex999.hA13 Cex999.hA14 Cex999.hA15
    Cex999.hA16 Cex999.hW
