-- Prove2me | solution 1 for SustainableFashion.Variety.proposition_4_i
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:15:54.473993+00:00
-- url     : https://prove2.me/submissions/b6ad7832-ad84-41ab-8e90-d564b99f256d

import Mathlib
import Definitions.Def_SustainableFashion_Variety_Setting

set_option autoImplicit false
open SustainableFashion.Variety

noncomputable def ff (P : Params) (m q : ℝ) : ℝ :=
  m * P.k * q + P.k' * ((P.nbar - q) ^ 2 / (2 * P.nbar))

noncomputable def qh (P : Params) (m : ℝ) : ℝ :=
  if m * P.k ≤ P.k' then P.nbar * (1 - m * P.k / P.k') else 0

noncomputable def ffs (P : Params) (m : ℝ) : ℝ := ff P m (qh P m)

noncomputable def Bf (P : Params) (m : ℝ) : ℝ :=
  (P.a + P.γ / 2 - P.γ / (4 * m)) * (P.nbar / 2) - P.β * m

lemma expProfit_eq (P : Params) (m u q : ℝ) :
    expProfit P m u q = Bf P m + P.θ * P.nbar / 2 * u - u ^ 2 / 2 * ff P m q := by
  unfold expProfit Bf ff; ring

lemma qh_mem (P : Params) (hk : 0 < P.k) (hk' : 0 < P.k') (hn : 0 < P.nbar) (m : ℝ) (hm : 0 < m) :
    0 ≤ qh P m ∧ qh P m ≤ P.nbar := by
  unfold qh
  split_ifs with h
  · have h1 : m * P.k / P.k' ≤ 1 := by rw [div_le_one hk']; exact h
    have h2 : 0 ≤ m * P.k / P.k' := by positivity
    constructor
    · exact mul_nonneg hn.le (by linarith)
    · nlinarith
  · exact ⟨le_refl _, hn.le⟩

lemma ff_ge (P : Params) (hk : 0 < P.k) (hk' : 0 < P.k') (hn : 0 < P.nbar) (m : ℝ) (hm : 0 < m)
    (q : ℝ) (hq0 : 0 ≤ q) :
    ff P m (qh P m) + P.k' / (2 * P.nbar) * (q - qh P m) ^ 2 ≤ ff P m q := by
  by_cases h : m * P.k ≤ P.k'
  · have e : qh P m = P.nbar * (1 - m * P.k / P.k') := by unfold qh; rw [if_pos h]
    rw [e]
    apply le_of_eq
    unfold ff
    field_simp
    ring
  · have e : qh P m = 0 := by unfold qh; rw [if_neg h]
    rw [e]
    have h' : P.k' < m * P.k := not_le.mp h
    have : ff P m q - (ff P m 0 + P.k' / (2 * P.nbar) * (q - 0) ^ 2) = (m * P.k - P.k') * q := by
      unfold ff
      field_simp
      ring
    nlinarith [mul_nonneg (sub_nonneg.mpr h'.le) hq0]

lemma ffs_case1 (P : Params) (hk' : 0 < P.k') (hn : 0 < P.nbar) (m : ℝ) (h : m * P.k ≤ P.k') :
    ffs P m = m * P.k * P.nbar * (2 * P.k' - m * P.k) / (2 * P.k') := by
  unfold ffs qh ff
  rw [if_pos h]
  field_simp
  ring

lemma ffs_case2 (P : Params) (hn : 0 < P.nbar) (m : ℝ) (h : ¬ m * P.k ≤ P.k') :
    ffs P m = P.k' * P.nbar / 2 := by
  unfold ffs qh ff
  rw [if_neg h]
  field_simp
  ring

lemma ffs_pos (P : Params) (hk : 0 < P.k) (hk' : 0 < P.k') (hn : 0 < P.nbar) (m : ℝ) (hm : 0 < m) :
    0 < ffs P m := by
  by_cases h : m * P.k ≤ P.k'
  · rw [ffs_case1 P hk' hn m h]
    have : 0 < 2 * P.k' - m * P.k := by linarith
    positivity
  · rw [ffs_case2 P hn m h]
    positivity

lemma quad_id (s t u : ℝ) (hs : 0 < s) :
    t * u - u ^ 2 * s / 2 = t ^ 2 / (2 * s) - s / 2 * (u - t / s) ^ 2 := by
  field_simp
  ring

lemma optGiven_iff (P : Params) (hk : 0 < P.k) (hk' : 0 < P.k') (hθ : 0 < P.θ) (hn : 0 < P.nbar)
    (m : ℝ) (hm : 0 < m) (u q : ℝ) :
    IsOptimalGiven P m u q ↔ (u = P.θ * P.nbar / (2 * ffs P m) ∧ q = qh P m) := by
  have hs := ffs_pos P hk hk' hn m hm
  have hmem := qh_mem P hk hk' hn m hm
  set s := ffs P m with hsdef
  set t := P.θ * P.nbar / 2 with htdef
  have ht : 0 < t := by positivity
  have hu0 : P.θ * P.nbar / (2 * s) = t / s := by rw [htdef]; field_simp
  rw [hu0]
  have hc : 0 < P.k' / (2 * P.nbar) := by positivity
  constructor
  · rintro ⟨⟨hu, hq0, hq1⟩, hopt⟩
    have h1 := hopt (t / s) (qh P m) (by positivity) hmem.1 hmem.2
    rw [expProfit_eq, expProfit_eq, ← htdef] at h1
    have hge := ff_ge P hk hk' hn m hm q hq0
    have e3 : ff P m (qh P m) = s := rfl
    rw [e3] at hge
    have e1 := quad_id s t u hs
    have e2 : t * (t / s) - (t / s) ^ 2 * s / 2 = t ^ 2 / (2 * s) := by field_simp; ring
    have hsq : 0 ≤ P.k' / (2 * P.nbar) * (q - qh P m) ^ 2 := by positivity
    have hD : 0 ≤ ff P m q - s := by linarith
    have hprod : 0 ≤ u ^ 2 / 2 * (ff P m q - s) := by positivity
    have key : s / 2 * (u - t / s) ^ 2 + u ^ 2 / 2 * (ff P m q - s) ≤ 0 := by
      rw [e3] at h1
      nlinarith [e1, e2]
    have hA : 0 ≤ s / 2 * (u - t / s) ^ 2 := by positivity
    have hA0 : s / 2 * (u - t / s) ^ 2 = 0 := by linarith
    have hB0 : u ^ 2 / 2 * (ff P m q - s) = 0 := by linarith
    have hus : u = t / s := by
      have : (u - t / s) ^ 2 = 0 := by
        rcases mul_eq_zero.mp hA0 with h | h
        · exact absurd h (by positivity)
        · exact h
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      linarith
    refine ⟨hus, ?_⟩
    have hupos : 0 < u := by rw [hus]; positivity
    have hDz : ff P m q - s = 0 := by
      rcases mul_eq_zero.mp hB0 with h | h
      · exact absurd h (by positivity)
      · exact h
    have : P.k' / (2 * P.nbar) * (q - qh P m) ^ 2 = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hc.ne'
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
      linarith
  · rintro ⟨hu, hq⟩
    subst hu
    subst hq
    refine ⟨⟨by positivity, hmem.1, hmem.2⟩, ?_⟩
    intro u' q' hu' hq0' hq1'
    rw [expProfit_eq, expProfit_eq, ← htdef]
    have hge := ff_ge P hk hk' hn m hm q' hq0'
    have e3 : ff P m (qh P m) = s := rfl
    rw [e3] at hge
    have hsq : 0 ≤ P.k' / (2 * P.nbar) * (q' - qh P m) ^ 2 := by positivity
    have e1 := quad_id s t u' hs
    have e2 : t * (t / s) - (t / s) ^ 2 * s / 2 = t ^ 2 / (2 * s) := by field_simp; ring
    have hA : 0 ≤ s / 2 * (u' - t / s) ^ 2 := by positivity
    have hprod : 0 ≤ u' ^ 2 / 2 * (ff P m q' - s) := by
      apply mul_nonneg (by positivity); linarith
    rw [e3]
    nlinarith [e1, e2]

noncomputable def Vst (P : Params) (m : ℝ) : ℝ :=
  Bf P m + (P.θ * P.nbar / 2) ^ 2 / (2 * ffs P m)

lemma Vst_attained (P : Params) (hk : 0 < P.k) (hk' : 0 < P.k') (hθ : 0 < P.θ) (hn : 0 < P.nbar)
    (m : ℝ) (hm : 0 < m) :
    IsOptimalGiven P m (P.θ * P.nbar / (2 * ffs P m)) (qh P m) ∧
    expProfit P m (P.θ * P.nbar / (2 * ffs P m)) (qh P m) = Vst P m := by
  refine ⟨(optGiven_iff P hk hk' hθ hn m hm _ _).mpr ⟨rfl, rfl⟩, ?_⟩
  have hs := ffs_pos P hk hk' hn m hm
  rw [expProfit_eq]
  have e3 : ff P m (qh P m) = ffs P m := rfl
  rw [e3]
  unfold Vst
  field_simp
  ring

lemma le_Vst (P : Params) (hk : 0 < P.k) (hk' : 0 < P.k') (hθ : 0 < P.θ) (hn : 0 < P.nbar)
    (m : ℝ) (hm : 0 < m) (u q : ℝ) (hu : 0 ≤ u) (hq0 : 0 ≤ q) (hq1 : q ≤ P.nbar) :
    expProfit P m u q ≤ Vst P m := by
  obtain ⟨h1, h2⟩ := Vst_attained P hk hk' hθ hn m hm
  rw [← h2]
  exact h1.2 u q hu hq0 hq1

noncomputable def sgf (P : Params) (m : ℝ) : ℝ :=
  min (m * P.k) P.k' * (2 * P.k' - min (m * P.k) P.k') / (2 * P.k')

lemma ffs_eq_sg (P : Params) (hk' : 0 < P.k') (hn : 0 < P.nbar) (m : ℝ) :
    ffs P m = P.nbar * sgf P m := by
  unfold sgf
  by_cases h : m * P.k ≤ P.k'
  · rw [ffs_case1 P hk' hn m h, min_eq_left h]
    field_simp
  · rw [ffs_case2 P hn m h, min_eq_right (not_le.mp h).le]
    field_simp
    ring

lemma sgf_pos (P : Params) (hk : 0 < P.k) (hk' : 0 < P.k') (m : ℝ) (hm : 0 < m) :
    0 < sgf P m := by
  unfold sgf
  have hx : 0 < min (m * P.k) P.k' := lt_min (mul_pos hm hk) hk'
  have hy : min (m * P.k) P.k' ≤ P.k' := min_le_right _ _
  apply div_pos (mul_pos hx (by linarith)) (by linarith)

lemma sgf_mono (P : Params) (hk : 0 < P.k) (hk' : 0 < P.k') (m₁ m₂ : ℝ) (hm₁ : 0 < m₁)
    (h : m₁ ≤ m₂) : sgf P m₁ ≤ sgf P m₂ := by
  unfold sgf
  have hx : 0 < min (m₁ * P.k) P.k' := lt_min (mul_pos hm₁ hk) hk'
  have hxy : min (m₁ * P.k) P.k' ≤ min (m₂ * P.k) P.k' :=
    min_le_min (mul_le_mul_of_nonneg_right h hk.le) le_rfl
  have hy : min (m₂ * P.k) P.k' ≤ P.k' := min_le_right _ _
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith

lemma u_of_given (P : Params) (hk : 0 < P.k) (hk' : 0 < P.k') (hθ : 0 < P.θ) (hn : 0 < P.nbar)
    (m : ℝ) (hm : 0 < m) (u q : ℝ) (h : IsOptimalGiven P m u q) : u = P.θ / (2 * sgf P m) := by
  rw [optGiven_iff P hk hk' hθ hn m hm] at h
  have := sgf_pos P hk hk' m hm
  rw [h.1, ffs_eq_sg P hk' hn m]
  field_simp

lemma given_of_opt (P : Params) (m u q : ℝ) (h : IsOptimal P m u q) : IsOptimalGiven P m u q := by
  obtain ⟨⟨hm, hu, hq0, hq1⟩, hmax⟩ := h
  exact ⟨⟨hu, hq0, hq1⟩, fun u' q' h1 h2 h3 => hmax m u' q' ⟨hm, h1, h2, h3⟩⟩

lemma Vst_eq (P : Params) (hk : 0 < P.k) (hk' : 0 < P.k') (hn : 0 < P.nbar) (m : ℝ) (hm : 0 < m) :
    Vst P m = P.nbar * ((P.a + P.γ / 2 - P.γ / (4 * m)) / 2 + P.θ ^ 2 / (8 * sgf P m))
      - P.β * m := by
  have := sgf_pos P hk hk' m hm
  unfold Vst Bf
  rw [ffs_eq_sg P hk' hn m]
  field_simp
  ring

def MaxV (P : Params) (m : ℝ) : Prop := 1 ≤ m ∧ ∀ m', 1 ≤ m' → Vst P m' ≤ Vst P m

lemma maxV_of_opt (P : Params) (hk : 0 < P.k) (hk' : 0 < P.k') (hθ : 0 < P.θ) (hn : 0 < P.nbar)
    (m u q : ℝ) (h : IsOptimal P m u q) : MaxV P m := by
  obtain ⟨⟨hm, hu, hq0, hq1⟩, hmax⟩ := h
  refine ⟨hm, fun m' hm' => ?_⟩
  obtain ⟨hopt', hval'⟩ := Vst_attained P hk hk' hθ hn m' (by linarith)
  have h1 := hmax m' _ _ ⟨hm', hopt'.1.1, hopt'.1.2.1, hopt'.1.2.2⟩
  have h2 := le_Vst P hk hk' hθ hn m (by linarith) u q hu hq0 hq1
  rw [hval'] at h1
  linarith

lemma opt_of_maxV (P : Params) (hk : 0 < P.k) (hk' : 0 < P.k') (hθ : 0 < P.θ) (hn : 0 < P.nbar)
    (m : ℝ) (h : MaxV P m) :
    IsOptimal P m (P.θ * P.nbar / (2 * ffs P m)) (qh P m) := by
  obtain ⟨hm, hmax⟩ := h
  obtain ⟨hopt1, hval⟩ := Vst_attained P hk hk' hθ hn m (by linarith)
  refine ⟨⟨hm, hopt1.1.1, hopt1.1.2.1, hopt1.1.2.2⟩, ?_⟩
  rintro m' u' q' ⟨hm', hu', hq0', hq1'⟩
  rw [hval]
  exact (le_Vst P hk hk' hθ hn m' (by linarith) u' q' hu' hq0' hq1').trans (hmax m' hm')

lemma exists_maxV (P : Params) (hP : P.Admissible) : ∃ m, MaxV P m := by
  obtain ⟨hk, hkk', hθ, hγ0, hβ, hn⟩ := hP
  have hk' : 0 < P.k' := by linarith
  have hs1 := sgf_pos P hk hk' 1 one_pos
  set C : ℝ := P.nbar * ((P.a + P.γ / 2) / 2 + P.θ ^ 2 / (8 * sgf P 1)) with hC
  have hbound : ∀ m, 1 ≤ m → Vst P m ≤ C - P.β * m := by
    intro m hm
    rw [Vst_eq P hk hk' hn m (by linarith)]
    have h1 : sgf P 1 ≤ sgf P m := sgf_mono P hk hk' 1 m one_pos hm
    have h2 : P.θ ^ 2 / (8 * sgf P m) ≤ P.θ ^ 2 / (8 * sgf P 1) := by
      apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
    have h3 : 0 ≤ P.γ / (4 * m) := by
      have : 0 < m := by linarith
      positivity
    have h4 : (P.a + P.γ / 2 - P.γ / (4 * m)) / 2 + P.θ ^ 2 / (8 * sgf P m) ≤
        (P.a + P.γ / 2) / 2 + P.θ ^ 2 / (8 * sgf P 1) := by linarith
    have h5 := mul_le_mul_of_nonneg_left h4 hn.le
    rw [hC]
    linarith
  set M : ℝ := max 1 ((C - Vst P 1) / P.β) + 1 with hM
  have hM1 : 1 ≤ M := by
    have := le_max_left 1 ((C - Vst P 1) / P.β)
    linarith
  have hs : Continuous (fun m : ℝ => sgf P m) := by
    unfold sgf
    exact ((((continuous_id.mul continuous_const).min continuous_const).mul
      (continuous_const.sub ((continuous_id.mul continuous_const).min continuous_const))).div_const _)
  have hcont0 : ContinuousOn (fun m : ℝ => P.nbar * ((P.a + P.γ / 2 - P.γ / (4 * m)) / 2 +
      P.θ ^ 2 / (8 * sgf P m)) - P.β * m) (Set.Icc 1 M) := by
    apply ContinuousOn.sub
    · apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.add
      · apply ContinuousOn.div_const
        apply ContinuousOn.sub continuousOn_const
        apply ContinuousOn.div continuousOn_const (by fun_prop)
        intro m hm
        have : (1 : ℝ) ≤ m := hm.1
        exact ne_of_gt (by linarith)
      · apply ContinuousOn.div continuousOn_const (by fun_prop)
        intro m hm
        have : (1 : ℝ) ≤ m := hm.1
        have := sgf_pos P hk hk' m (by linarith)
        exact ne_of_gt (by linarith)
    · fun_prop
  have hcont : ContinuousOn (fun m => Vst P m) (Set.Icc 1 M) := by
    apply hcont0.congr
    intro m hm
    have : (1 : ℝ) ≤ m := hm.1
    exact Vst_eq P hk hk' hn m (by linarith)
  obtain ⟨m0, hm0, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hM1) hcont
  refine ⟨m0, hm0.1, fun m' hm' => ?_⟩
  by_cases hle : m' ≤ M
  · exact isMaxOn_iff.mp hmax m' ⟨hm', hle⟩
  · push_neg at hle
    have h1 := hbound m' hm'
    have h2 : (C - Vst P 1) / P.β < m' := by
      have := le_max_right 1 ((C - Vst P 1) / P.β)
      linarith
    have h3 : C - Vst P 1 < P.β * m' := by
      rw [div_lt_iff₀ hβ, mul_comm] at h2
      exact h2
    have h5 : Vst P 1 ≤ Vst P m0 := isMaxOn_iff.mp hmax 1 ⟨le_refl _, hM1⟩
    linarith

lemma cmp_gamma (P : Params) (hk : 0 < P.k) (hk' : 0 < P.k') (hθ : 0 < P.θ) (hn : 0 < P.nbar)
    (γ₂ : ℝ) (hlt : P.γ < γ₂) (m₁ m₂ : ℝ) (h1 : MaxV P m₁) (h2 : MaxV { P with γ := γ₂ } m₂) :
    m₁ ≤ m₂ := by
  by_contra hc
  push_neg at hc
  have a1 := h1.2 m₂ h2.1
  have a2 := h2.2 m₁ h1.1
  have eq : ∀ m : ℝ, 0 < m → Vst { P with γ := γ₂ } m =
      Vst P m + (γ₂ - P.γ) * P.nbar / 4 - (γ₂ - P.γ) * P.nbar / (8 * m) := by
    intro m hm
    have e : ffs { P with γ := γ₂ } m = ffs P m := rfl
    unfold Vst Bf
    rw [e]
    dsimp only
    field_simp
    ring
  have hm₂ : 0 < m₂ := by linarith [h2.1]
  have hm₁ : 0 < m₁ := by linarith [h1.1]
  rw [eq m₁ hm₁, eq m₂ hm₂] at a2
  have : (γ₂ - P.γ) * P.nbar / (8 * m₁) < (γ₂ - P.γ) * P.nbar / (8 * m₂) :=
    div_lt_div_of_pos_left (by nlinarith) (by positivity) (by linarith)
  linarith

lemma cmp_beta (P : Params) (hk : 0 < P.k) (hk' : 0 < P.k') (hθ : 0 < P.θ) (hn : 0 < P.nbar)
    (β₂ : ℝ) (hlt : P.β < β₂) (m₁ m₂ : ℝ) (h1 : MaxV P m₁) (h2 : MaxV { P with β := β₂ } m₂) :
    m₂ ≤ m₁ := by
  by_contra hc
  push_neg at hc
  have a1 := h1.2 m₂ h2.1
  have a2 := h2.2 m₁ h1.1
  have eq : ∀ m : ℝ, Vst { P with β := β₂ } m = Vst P m - (β₂ - P.β) * m := by
    intro m
    have e : ffs { P with β := β₂ } m = ffs P m := rfl
    unfold Vst Bf
    rw [e]
    dsimp only
    ring
  rw [eq m₁, eq m₂] at a2
  nlinarith

lemma cmp_nbar (P : Params) (hk : 0 < P.k) (hk' : 0 < P.k') (hθ : 0 < P.θ) (hn : 0 < P.nbar)
    (hβ : 0 < P.β)
    (n₂ : ℝ) (hlt : P.nbar < n₂) (m₁ m₂ : ℝ) (h1 : MaxV P m₁) (h2 : MaxV { P with nbar := n₂ } m₂) :
    m₁ ≤ m₂ := by
  by_contra hc
  push_neg at hc
  have a1 := h1.2 m₂ h2.1
  have a2 := h2.2 m₁ h1.1
  have hn2 : 0 < n₂ := by linarith
  have hm₂ : 0 < m₂ := by linarith [h2.1]
  have hm₁ : 0 < m₁ := by linarith [h1.1]
  rw [Vst_eq P hk hk' hn m₁ hm₁, Vst_eq P hk hk' hn m₂ hm₂] at a1
  rw [Vst_eq { P with nbar := n₂ } hk hk' hn2 m₁ hm₁, Vst_eq { P with nbar := n₂ } hk hk' hn2 m₂ hm₂] at a2
  have e1 : sgf { P with nbar := n₂ } m₁ = sgf P m₁ := rfl
  have e2 : sgf { P with nbar := n₂ } m₂ = sgf P m₂ := rfl
  rw [e1, e2] at a2
  dsimp only at a2
  set G₁ := (P.a + P.γ / 2 - P.γ / (4 * m₁)) / 2 + P.θ ^ 2 / (8 * sgf P m₁)
  set G₂ := (P.a + P.γ / 2 - P.γ / (4 * m₂)) / 2 + P.θ ^ 2 / (8 * sgf P m₂)
  have hbe : 0 < P.β * (m₁ - m₂) := mul_pos hβ (by linarith)
  have hd : 0 < G₁ - G₂ := by
    by_contra h
    push_neg at h
    nlinarith [mul_nonneg hn.le (neg_nonneg.2 h)]
  nlinarith [mul_pos (sub_pos.2 hlt) hd]

noncomputable def Psi (u x : ℝ) : ℝ := 2 / (x * (2 - x * u))

lemma inv_sgf (P : Params) (hk : 0 < P.k) (hk' : 0 < P.k') (m : ℝ) (hm : 0 < m) :
    1 / sgf P m = Psi (1 / P.k') (min (m * P.k) P.k') := by
  have hx : 0 < min (m * P.k) P.k' := lt_min (mul_pos hm hk) hk'
  have hxK : min (m * P.k) P.k' ≤ P.k' := min_le_right _ _
  have h2 : 0 < 2 * P.k' - min (m * P.k) P.k' := by linarith
  unfold sgf Psi
  field_simp

lemma Psi_dec (K x y : ℝ) (hK : 0 < K) (hx : 0 < x) (hxy : x < y) (hy : y ≤ K) :
    Psi (1 / K) y < Psi (1 / K) x := by
  unfold Psi
  have h1 : 0 < 2 - x * (1 / K) := by
    have : x * (1 / K) < 1 := by
      rw [mul_one_div, div_lt_one hK]; linarith
    linarith
  have h2 : 0 < 2 - y * (1 / K) := by
    have : y * (1 / K) ≤ 1 := by
      rw [mul_one_div, div_le_one hK]; exact hy
    linarith
  apply div_lt_div_of_pos_left (by norm_num) (by positivity)
  have : (x + y) * (1 / K) < 2 := by
    have : (x + y) * (1 / K) < 2 * 1 := by
      rw [mul_one_div, div_lt_iff₀ hK]; nlinarith
    linarith
  nlinarith

lemma Psi_F (a b κ K : ℝ) (ha : 0 < a) (hab : a < b) (hbκ : b ≤ κ) (hκ : 0 < κ) (hκK : κ < K) :
    Psi (1 / K) b - Psi (1 / K) a < Psi (1 / κ) b - Psi (1 / κ) a := by
  have hK : 0 < K := by linarith
  set u := 1 / K with hu
  set v := 1 / κ with hv
  have huv : u < v := by
    rw [hu, hv]; exact one_div_lt_one_div_of_lt hκ hκK
  have hu0 : 0 < u := by positivity
  have hbv : b * v ≤ 1 := by rw [hv, mul_one_div, div_le_one hκ]; exact hbκ
  have hbu : b * u < 1 := by nlinarith
  have hb0 : 0 < b := by linarith
  have hav : a * v < 1 := by nlinarith
  have hau : a * u < 1 := by nlinarith
  have hbu' : 0 < 2 - b * u := by linarith
  have hbv' : 0 < 2 - b * v := by linarith
  have hau' : 0 < 2 - a * u := by linarith
  have hav' : 0 < 2 - a * v := by linarith
  have e1 : Psi v b - Psi u b = 2 * (v - u) / ((2 - b * u) * (2 - b * v)) := by
    unfold Psi; field_simp; ring
  have e2 : Psi v a - Psi u a = 2 * (v - u) / ((2 - a * u) * (2 - a * v)) := by
    unfold Psi; field_simp; ring
  have h3 : 2 * (v - u) / ((2 - a * u) * (2 - a * v)) < 2 * (v - u) / ((2 - b * u) * (2 - b * v)) := by
    apply div_lt_div_of_pos_left (by linarith) (by positivity)
    exact mul_lt_mul'' (by nlinarith) (by nlinarith) hbu'.le hbv'.le
  linarith

lemma id_strict (P : Params) (hk : 0 < P.k) (hk' : 0 < P.k') (K : ℝ) (hlt : P.k' < K)
    (m₁ m₂ : ℝ) (hm₁ : 0 < m₁) (h12 : m₁ < m₂) (hnd : m₁ * P.k < K) :
    1 / sgf { P with k' := K } m₂ - 1 / sgf { P with k' := K } m₁ <
      1 / sgf P m₂ - 1 / sgf P m₁ := by
  have hm₂ : 0 < m₂ := by linarith
  have hK : 0 < K := by linarith
  rw [inv_sgf { P with k' := K } hk hK m₂ hm₂, inv_sgf { P with k' := K } hk hK m₁ hm₁,
    inv_sgf P hk hk' m₂ hm₂, inv_sgf P hk hk' m₁ hm₁]
  dsimp only
  set a := m₁ * P.k with ha
  set b := m₂ * P.k with hb
  have ha0 : 0 < a := mul_pos hm₁ hk
  have hab : a < b := mul_lt_mul_of_pos_right h12 hk
  have hmaK : min a K = a := min_eq_left hnd.le
  rw [hmaK]
  by_cases hκa : a < P.k'
  · rw [min_eq_left hκa.le]
    by_cases hbκ : b ≤ P.k'
    · rw [min_eq_left hbκ, min_eq_left (hbκ.trans hlt.le)]
      exact Psi_F a b P.k' K ha0 hab hbκ hk' hlt
    · push_neg at hbκ
      rw [min_eq_right hbκ.le]
      have hy : P.k' < min b K := lt_min hbκ hlt
      have h1 := Psi_dec K P.k' (min b K) hK hk' hy (min_le_right _ _)
      have h2 := Psi_F a P.k' P.k' K ha0 hκa le_rfl hk' hlt
      linarith
  · push_neg at hκa
    rw [min_eq_right hκa, min_eq_right (hκa.trans hab.le)]
    have hy : a < min b K := lt_min hab hnd
    have h1 := Psi_dec K a (min b K) hK ha0 hy (min_le_right _ _)
    linarith

lemma sgf_big (P : Params) (hk' : 0 < P.k') (m : ℝ) (h : P.k' ≤ m * P.k) : sgf P m = P.k' / 2 := by
  unfold sgf
  rw [min_eq_right h]
  field_simp
  ring

lemma cmp_kprime (P : Params) (hk : 0 < P.k) (hk' : 0 < P.k') (hθ : 0 < P.θ) (hn : 0 < P.nbar)
    (hγ : 0 < P.γ) (hβ : 0 < P.β)
    (K : ℝ) (hlt : P.k' < K) (m₁ m₂ : ℝ) (h1 : MaxV P m₁) (h2 : MaxV { P with k' := K } m₂) :
    m₂ ≤ m₁ := by
  by_contra hc
  push_neg at hc
  have hK : 0 < K := by linarith
  have hm₁ : 0 < m₁ := by linarith [h1.1]
  have hm₂ : 0 < m₂ := by linarith
  have a1 := h1.2 m₂ h2.1
  have a2 := h2.2 m₁ h1.1
  by_cases hnd : m₁ * P.k < K
  · have hid := id_strict P hk hk' K hlt m₁ m₂ hm₁ hc hnd
    rw [Vst_eq P hk hk' hn m₁ hm₁, Vst_eq P hk hk' hn m₂ hm₂] at a1
    rw [Vst_eq { P with k' := K } hk hK hn m₁ hm₁, Vst_eq { P with k' := K } hk hK hn m₂ hm₂] at a2
    dsimp only at a2
    have s1 := sgf_pos P hk hk' m₁ hm₁
    have s2 := sgf_pos P hk hk' m₂ hm₂
    have s3 := sgf_pos { P with k' := K } hk hK m₁ hm₁
    have s4 := sgf_pos { P with k' := K } hk hK m₂ hm₂
    have e : ∀ s : ℝ, P.θ ^ 2 / (8 * s) = P.θ ^ 2 / 8 * (1 / s) := by
      intro s; field_simp
    rw [e (sgf P m₁), e (sgf P m₂)] at a1
    rw [e (sgf { P with k' := K } m₁), e (sgf { P with k' := K } m₂)] at a2
    have hpos : 0 < P.nbar * (P.θ ^ 2 / 8) := by positivity
    nlinarith [mul_lt_mul_of_pos_left hid hpos]
  · push_neg at hnd
    have hs1 : sgf P m₁ = P.k' / 2 := sgf_big P hk' m₁ (by linarith)
    have hs2 : sgf P m₂ = P.k' / 2 :=
      sgf_big P hk' m₂ (by nlinarith)
    have hs3 : sgf { P with k' := K } m₁ = K / 2 := sgf_big { P with k' := K } hK m₁ hnd
    have hs4 : sgf { P with k' := K } m₂ = K / 2 :=
      sgf_big { P with k' := K } hK m₂ (by dsimp only; nlinarith)
    set m₃ := (m₁ + m₂) / 2 with hm₃
    have hm₃0 : 0 < m₃ := by rw [hm₃]; linarith
    have hs5 : sgf P m₃ = P.k' / 2 := sgf_big P hk' m₃ (by rw [hm₃]; nlinarith)
    have a3 := h1.2 m₃ (by rw [hm₃]; linarith [h1.1])
    rw [Vst_eq P hk hk' hn m₁ hm₁, Vst_eq P hk hk' hn m₂ hm₂, hs1, hs2] at a1
    rw [Vst_eq { P with k' := K } hk hK hn m₁ hm₁, Vst_eq { P with k' := K } hk hK hn m₂ hm₂,
      hs3, hs4] at a2
    rw [Vst_eq P hk hk' hn m₃ hm₃0, Vst_eq P hk hk' hn m₁ hm₁, hs5, hs1] at a3
    dsimp only at a2
    have hE : P.nbar * (P.γ / (4 * m₁) - P.γ / (4 * m₂)) / 2 = P.β * (m₂ - m₁) := by
      apply le_antisymm <;> nlinarith [a1, a2]
    have hE3 : P.nbar * (P.γ / (4 * m₁) - P.γ / (4 * m₃)) / 2 ≤ P.β * (m₃ - m₁) := by
      nlinarith [a3]
    have ht : m₂ - m₁ ≠ 0 := by linarith
    have hβe : P.β * (m₂ - m₁) = P.nbar * P.γ / (8 * m₁ * m₂) * (m₂ - m₁) := by
      rw [← hE]; field_simp; ring
    have hβe' : P.β = P.nbar * P.γ / (8 * m₁ * m₂) := mul_right_cancel₀ ht hβe
    rw [hβe'] at hE3
    have hm₃1 : m₁ < m₃ := by rw [hm₃]; linarith
    have hm₃2 : m₃ < m₂ := by rw [hm₃]; linarith
    set Q := P.nbar * P.γ * (m₃ - m₁) / (8 * m₁) with hQ
    have hQ0 : 0 < Q := by
      rw [hQ]
      have : 0 < m₃ - m₁ := by linarith
      positivity
    have l1 : P.nbar * (P.γ / (4 * m₁) - P.γ / (4 * m₃)) / 2 = Q / m₃ := by
      rw [hQ]; field_simp; ring
    have l2 : P.nbar * P.γ / (8 * m₁ * m₂) * (m₃ - m₁) = Q / m₂ := by
      rw [hQ]; field_simp
    rw [l1, l2] at hE3
    have := (div_le_div_iff_of_pos_left hQ0 hm₃0 hm₂).mp hE3
    linarith

theorem solution (P : Params) (hP : P.Admissible) :
    (∃ m u q, IsOptimal P m u q) ∧
    (∀ γ₂, P.γ < γ₂ → ∀ m₁ u₁ q₁ m₂ u₂ q₂,
        IsOptimal P m₁ u₁ q₁ → IsOptimal { P with γ := γ₂ } m₂ u₂ q₂ → m₁ ≤ m₂) ∧
    (∀ β₂, P.β < β₂ → ∀ m₁ u₁ q₁ m₂ u₂ q₂,
        IsOptimal P m₁ u₁ q₁ → IsOptimal { P with β := β₂ } m₂ u₂ q₂ → m₂ ≤ m₁) ∧
    (∀ k₂', P.k' < k₂' → ∀ m₁ u₁ q₁ m₂ u₂ q₂,
        IsOptimal P m₁ u₁ q₁ → IsOptimal { P with k' := k₂' } m₂ u₂ q₂ → m₂ ≤ m₁) ∧
    (∀ n₂, P.nbar < n₂ → ∀ m₁ u₁ q₁ m₂ u₂ q₂,
        IsOptimal P m₁ u₁ q₁ → IsOptimal { P with nbar := n₂ } m₂ u₂ q₂ → m₁ ≤ m₂) := by
  have hP' := hP
  obtain ⟨hk, hkk', hθ, hγ0, hβ, hn⟩ := hP'
  have hk' : 0 < P.k' := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨m, hm⟩ := exists_maxV P hP
    exact ⟨m, _, _, opt_of_maxV P hk hk' hθ hn m hm⟩
  · intro γ₂ hlt m₁ u₁ q₁ m₂ u₂ q₂ h1 h2
    exact cmp_gamma P hk hk' hθ hn γ₂ hlt m₁ m₂ (maxV_of_opt P hk hk' hθ hn _ _ _ h1)
      (maxV_of_opt { P with γ := γ₂ } hk hk' hθ hn _ _ _ h2)
  · intro β₂ hlt m₁ u₁ q₁ m₂ u₂ q₂ h1 h2
    exact cmp_beta P hk hk' hθ hn β₂ hlt m₁ m₂ (maxV_of_opt P hk hk' hθ hn _ _ _ h1)
      (maxV_of_opt { P with β := β₂ } hk hk' hθ hn _ _ _ h2)
  · intro k₂' hlt m₁ u₁ q₁ m₂ u₂ q₂ h1 h2
    have hk2 : 0 < k₂' := by linarith
    exact cmp_kprime P hk hk' hθ hn hγ0 hβ k₂' hlt m₁ m₂ (maxV_of_opt P hk hk' hθ hn _ _ _ h1)
      (maxV_of_opt { P with k' := k₂' } hk hk2 hθ hn _ _ _ h2)
  · intro n₂ hlt m₁ u₁ q₁ m₂ u₂ q₂ h1 h2
    have hn2 : 0 < n₂ := by linarith
    exact cmp_nbar P hk hk' hθ hn hβ n₂ hlt m₁ m₂ (maxV_of_opt P hk hk' hθ hn _ _ _ h1)
      (maxV_of_opt { P with nbar := n₂ } hk hk' hθ hn2 _ _ _ h2)
