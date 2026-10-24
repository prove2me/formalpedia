-- Prove2me | solution 1 for RideHailing.Central.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T21:18:05.783994+00:00
-- url     : https://prove2.me/submissions/4813be75-c080-4d08-b02b-7d7f203c3f6d

import Mathlib
import Definitions.Def_RideHailing_Central_Setting

set_option autoImplicit false

namespace RHC1
open RideHailing.Central

noncomputable def g (M : Model) : ℝ := M.gbar * M.p - M.c
noncomputable def T (M : Model) : ℝ := M.t12 + M.t21
noncomputable def D (M : Model) : ℝ := g M * M.Sbar - M.c * M.t12 * (M.Λ21 - M.Λ12)
noncomputable def L (M : Model) (n : ℝ) : ℝ :=
  ((g M * M.t21 - M.c * M.t12) * n + M.nC1 * M.t12 * (g M + M.c)) / T M
noncomputable def V (M : Model) (n : ℝ) : ℝ :=
  min (min n ((M.t21 * n + M.t12 * M.nC1) / T M)) M.Sbar
noncomputable def m (M : Model) (n : ℝ) : ℝ := min (min (g M * n) (L M n)) (D M)
noncomputable def P (M : Model) (n : ℝ) : ℝ := m M n / n

variable {M : Model}

lemma nC1_eq (M : Model) : M.nC1 = M.S11 + M.S12 + M.S22 + M.Λ12 * M.t21 := by
  unfold Model.nC1 Model.Sbar Model.S21; ring

lemma Sbar_eq (M : Model) : M.Sbar = M.nC1 + (M.Λ21 - M.Λ12) * M.t21 := by
  unfold Model.nC1; ring

lemma nC1_pos (hM : M.Standing) : 0 < M.nC1 := by
  rw [nC1_eq]; unfold Model.S11 Model.S12 Model.S22
  linarith [mul_nonneg hM.Λ11_nonneg hM.t11_pos.le, mul_pos hM.Λ12_pos hM.t12_pos,
    mul_nonneg hM.Λ22_nonneg hM.t22_pos.le, mul_pos hM.Λ12_pos hM.t21_pos]

lemma g_pos (hM : M.Standing) : 0 < g M := hM.profit_pos

lemma T_pos (hM : M.Standing) : 0 < T M := by unfold T; linarith [hM.t12_pos, hM.t21_pos]

lemma A_pos (hM : M.Standing) : 0 < g M * M.t21 - M.c * M.t12 := by
  have := hM.assm2_12; unfold g; linarith

lemma D_eq (M : Model) :
    D M = g M * M.nC1 + (M.Λ21 - M.Λ12) * (g M * M.t21 - M.c * M.t12) := by
  unfold D; rw [Sbar_eq]; ring

lemma D_pos (hM : M.Standing) : 0 < D M := by
  rw [D_eq]
  have h : 0 < M.Λ21 - M.Λ12 := by linarith [hM.Λ12_lt_Λ21]
  linarith [mul_pos (g_pos hM) (nC1_pos hM), mul_pos h (A_pos hM)]

lemma key {n : ℝ} {x : Alloc} (hM : M.Standing) (hx : M.InCC n x) :
    M.t12 * x.sbar ≤ M.t12 * M.nC1 + M.t21 * x.r12 := by
  obtain ⟨hf, -, ⟨-, h11b⟩, ⟨-, h12b⟩, -, ⟨-, h22b⟩, -, hr21, -, -⟩ := hx
  have t12 := hM.t12_pos
  have t21 := hM.t21_pos
  rw [div_eq_div_iff t12.ne' t21.ne'] at hf
  rw [nC1_eq]; unfold Alloc.sbar
  unfold Model.S12 at h12b ⊢
  linarith [mul_le_mul_of_nonneg_left h11b t12.le, mul_le_mul_of_nonneg_left h22b t12.le,
    mul_le_mul_of_nonneg_left h12b t21.le, mul_le_mul_of_nonneg_left h12b t12.le,
    mul_nonneg t12.le hr21]

lemma sbar_le_Sbar {n : ℝ} {x : Alloc} (hx : M.InCC n x) : x.sbar ≤ M.Sbar := by
  obtain ⟨-, -, ⟨-, h11⟩, ⟨-, h12⟩, ⟨-, h21⟩, ⟨-, h22⟩, -⟩ := hx
  unfold Model.Sbar Alloc.sbar; linarith

lemma sbar_le_V {n : ℝ} {x : Alloc} (hM : M.Standing) (hx : M.InCC n x) :
    x.sbar ≤ V M n := by
  have hk := key hM hx
  have hT := T_pos hM
  have hSb := sbar_le_Sbar hx
  obtain ⟨-, ht, -, -, -, -, hr12, hr21, hq1, hq2⟩ := hx
  unfold Alloc.rbar Alloc.qbar at ht
  have hs : x.sbar ≤ n := by linarith
  unfold V
  refine le_min (le_min hs ?_) hSb
  rw [le_div_iff₀ hT]; unfold T
  have : x.r12 ≤ n - x.sbar := by linarith
  nlinarith [mul_le_mul_of_nonneg_left this hM.t21_pos.le]

lemma val_le {n : ℝ} {x : Alloc} (hM : M.Standing) (hx : M.InCC n x) :
    g M * x.sbar - M.c * x.rbar ≤ m M n := by
  have hk := key hM hx
  have hT := T_pos hM
  have hA := A_pos hM
  have hg := g_pos hM
  have hc := hM.c_pos
  have t21 := hM.t21_pos
  have hSb : x.sbar ≤ M.Sbar := sbar_le_Sbar hx
  obtain ⟨-, ht, -, -, -, -, hr12, hr21, hq1, hq2⟩ := hx
  unfold Alloc.qbar at ht
  have hrb : x.r12 ≤ x.rbar := by unfold Alloc.rbar; linarith
  have hrb0 : 0 ≤ x.rbar := by unfold Alloc.rbar; linarith
  have hsn : x.sbar + x.rbar ≤ n := by linarith
  have key' : M.t12 * x.sbar ≤ M.t12 * M.nC1 + M.t21 * x.rbar := by
    linarith [mul_le_mul_of_nonneg_left hrb t21.le]
  unfold m
  refine le_min (le_min ?_ ?_) ?_
  · linarith [mul_le_mul_of_nonneg_left hsn hg.le, mul_nonneg hg.le hrb0, mul_nonneg hc.le hrb0]
  · rw [L, le_div_iff₀ hT]; unfold T
    have hgc : 0 ≤ g M + M.c := by linarith
    linarith [mul_le_mul_of_nonneg_left hsn hA.le, mul_le_mul_of_nonneg_left key' hgc]
  · have hS' : M.c * M.t12 * M.Sbar = M.c * M.t12 * (M.nC1 + (M.Λ21 - M.Λ12) * M.t21) := by
      rw [← Sbar_eq]
    have h : M.t21 * (g M * x.sbar - M.c * x.rbar) ≤ M.t21 * D M := by
      unfold D
      linarith [mul_le_mul_of_nonneg_left hSb hA.le, mul_le_mul_of_nonneg_left key' hc.le]
    exact le_of_mul_le_mul_left h t21

lemma exists_opt (hM : M.Standing) {n : ℝ} (hn : 0 < n) :
    ∃ x : Alloc, M.InCC n x ∧ V M n ≤ x.sbar ∧ m M n ≤ g M * x.sbar - M.c * x.rbar := by
  have h1 := nC1_pos hM
  have hT := T_pos hM
  have t12 := hM.t12_pos
  have t21 := hM.t21_pos
  have hΛ := hM.Λ12_pos
  have hd : 0 < M.Λ21 - M.Λ12 := by linarith [hM.Λ12_lt_Λ21]
  have hS11 : 0 ≤ M.S11 := mul_nonneg hM.Λ11_nonneg hM.t11_pos.le
  have hS12 : 0 ≤ M.S12 := mul_nonneg hM.Λ12_pos.le t12.le
  have hS22 : 0 ≤ M.S22 := mul_nonneg hM.Λ22_nonneg hM.t22_pos.le
  have hS21 : M.Λ12 * M.t21 ≤ M.S21 :=
    mul_le_mul_of_nonneg_right hM.Λ12_lt_Λ21.le t21.le
  rcases le_or_gt n M.nC1 with hle | hlt
  · obtain ⟨k, hk⟩ : ∃ k, k = n / M.nC1 := ⟨_, rfl⟩
    have hk0 : 0 < k := hk ▸ div_pos hn h1
    have hk1 : k ≤ 1 := hk ▸ (div_le_one h1).mpr hle
    have hkn : k * M.nC1 = n := by rw [hk]; exact div_mul_cancel₀ n h1.ne'
    have e : k * M.S11 + k * M.S12 + k * (M.Λ12 * M.t21) + k * M.S22 = n := by
      rw [← hkn, nC1_eq]; ring
    refine ⟨⟨k * M.S11, k * M.S12, k * (M.Λ12 * M.t21), k * M.S22, 0, 0, 0, 0⟩,
      ⟨?_, ?_, ⟨mul_nonneg hk0.le hS11, mul_le_of_le_one_left hS11 hk1⟩,
        ⟨mul_nonneg hk0.le hS12, mul_le_of_le_one_left hS12 hk1⟩,
        ⟨mul_nonneg hk0.le (mul_pos hΛ t21).le,
          (mul_le_of_le_one_left (mul_pos hΛ t21).le hk1).trans hS21⟩,
        ⟨mul_nonneg hk0.le hS22, mul_le_of_le_one_left hS22 hk1⟩,
        le_rfl, le_rfl, le_rfl, le_rfl⟩, ?_, ?_⟩
    · show (k * M.S12 + 0) / M.t12 = (k * (M.Λ12 * M.t21) + 0) / M.t21
      rw [div_eq_div_iff t12.ne' t21.ne']; unfold Model.S12; ring
    · show k * M.S11 + k * M.S12 + k * (M.Λ12 * M.t21) + k * M.S22 + (0 + 0) + (0 + 0) = n
      rw [← e]; ring
    · show V M n ≤ k * M.S11 + k * M.S12 + k * (M.Λ12 * M.t21) + k * M.S22
      rw [e]; unfold V; exact (min_le_left _ _).trans (min_le_left _ _)
    · show m M n ≤ g M * (k * M.S11 + k * M.S12 + k * (M.Λ12 * M.t21) + k * M.S22)
        - M.c * (0 + 0)
      rw [e]; unfold m
      have : g M * n - M.c * (0 + 0) = g M * n := by ring
      rw [this]; exact (min_le_left _ _).trans (min_le_left _ _)
  · obtain ⟨θ, hθ⟩ : ∃ θ, θ = min ((n - M.nC1) / T M) (M.Λ21 - M.Λ12) := ⟨_, rfl⟩
    have hθ0 : 0 ≤ θ := hθ ▸ le_min (div_nonneg (by linarith) hT.le) hd.le
    have hθ1 : θ ≤ (n - M.nC1) / T M := hθ ▸ min_le_left _ _
    have hθ2 : θ ≤ M.Λ21 - M.Λ12 := hθ ▸ min_le_right _ _
    have hθT : θ * T M ≤ n - M.nC1 := (le_div_iff₀ hT).mp hθ1
    have e : M.S11 + M.S12 + (M.Λ12 + θ) * M.t21 + M.S22 = M.nC1 + θ * M.t21 := by
      rw [nC1_eq]; ring
    refine ⟨⟨M.S11, M.S12, (M.Λ12 + θ) * M.t21, M.S22, θ * M.t12, 0,
        n - M.nC1 - θ * T M, 0⟩,
      ⟨?_, ?_, ⟨hS11, le_rfl⟩, ⟨hS12, le_rfl⟩,
        ⟨mul_nonneg (by linarith) t21.le, ?_⟩, ⟨hS22, le_rfl⟩,
        mul_nonneg hθ0 t12.le, le_rfl, by linarith, le_rfl⟩, ?_, ?_⟩
    · show (M.S12 + θ * M.t12) / M.t12 = ((M.Λ12 + θ) * M.t21 + 0) / M.t21
      rw [div_eq_div_iff t12.ne' t21.ne']; unfold Model.S12; ring
    · show M.S11 + M.S12 + (M.Λ12 + θ) * M.t21 + M.S22 + (θ * M.t12 + 0)
        + (n - M.nC1 - θ * T M + 0) = n
      rw [nC1_eq]; unfold T; ring
    · show (M.Λ12 + θ) * M.t21 ≤ M.S21
      unfold Model.S21
      exact mul_le_mul_of_nonneg_right (by linarith) t21.le
    · show V M n ≤ M.S11 + M.S12 + (M.Λ12 + θ) * M.t21 + M.S22
      rw [e]; unfold V
      rcases min_choice ((n - M.nC1) / T M) (M.Λ21 - M.Λ12) with h | h <;> rw [h] at hθ
      · refine (min_le_left _ _).trans ((min_le_right _ _).trans (le_of_eq ?_))
        rw [hθ]; field_simp; unfold T; ring
      · refine (min_le_right _ _).trans (le_of_eq ?_)
        rw [hθ, Sbar_eq]
    · show m M n ≤ g M * (M.S11 + M.S12 + (M.Λ12 + θ) * M.t21 + M.S22)
        - M.c * (θ * M.t12 + 0)
      rw [e]; unfold m
      rcases min_choice ((n - M.nC1) / T M) (M.Λ21 - M.Λ12) with h | h <;> rw [h] at hθ
      · refine (min_le_left _ _).trans ((min_le_right _ _).trans (le_of_eq ?_))
        unfold L; rw [hθ]; field_simp; unfold T; ring
      · refine (min_le_right _ _).trans (le_of_eq ?_)
        rw [hθ, D_eq]; ring

lemma opt_spec (hM : M.Standing) {n : ℝ} (hn : 0 < n) :
    ∃ x : Alloc, M.InCC n x ∧ (∀ y, M.InCC n y → M.Rev y ≤ M.Rev x) ∧
      (∀ y, M.InCC n y → M.prof y n ≤ M.prof x n) ∧
      M.Rev x = M.γ * M.p * V M n ∧ M.prof x n = P M n := by
  obtain ⟨x, hx, hV, hm⟩ := exists_opt hM hn
  have hs : x.sbar = V M n := le_antisymm (sbar_le_V hM hx) hV
  have hv : g M * x.sbar - M.c * x.rbar = m M n := le_antisymm (val_le hM hx) hm
  have hγp : 0 ≤ M.γ * M.p := (mul_pos hM.γ_pos hM.p_pos).le
  refine ⟨x, hx, fun y hy => ?_, fun y hy => ?_, ?_, ?_⟩
  · unfold Model.Rev; rw [hs]; exact mul_le_mul_of_nonneg_left (sbar_le_V hM hy) hγp
  · unfold Model.prof
    apply div_le_div_of_nonneg_right _ hn.le
    have := val_le hM hy
    unfold g at this hv
    linarith
  · unfold Model.Rev; rw [hs]
  · unfold Model.prof P; rw [← hv]; rfl

lemma piC_eq (hM : M.Standing) {n : ℝ} (hn : 0 < n) : M.piC n = P M n := by
  obtain ⟨x, hx, hR, hpr, -, hP⟩ := opt_spec hM hn
  have hopt : x ∈ M.OptC n := ⟨hx, hR⟩
  have : IsGreatest ((fun y => M.prof y n) '' M.OptC n) (M.prof x n) :=
    ⟨⟨x, hopt, rfl⟩, by rintro _ ⟨y, hy, rfl⟩; exact hpr y hy.1⟩
  unfold Model.piC; rw [this.csSup_eq, hP]

lemma PiC_eq (hM : M.Standing) {n : ℝ} (hn : 0 < n) : M.PiC n = M.γ * M.p * V M n := by
  obtain ⟨x, hx, hR, -, hRev, -⟩ := opt_spec hM hn
  have : IsGreatest (M.Rev '' {y | M.InCC n y}) (M.Rev x) :=
    ⟨⟨x, hx, rfl⟩, by rintro _ ⟨y, hy, rfl⟩; exact hR y hy⟩
  unfold Model.PiC; rw [this.csSup_eq, hRev]

lemma P_eq {n : ℝ} (hn : 0 < n) : P M n = min (min (g M) (L M n / n)) (D M / n) := by
  unfold P m
  rw [← min_div_div_right hn.le, ← min_div_div_right hn.le, mul_div_cancel_right₀ _ hn.ne']

lemma beta_pos (hM : M.Standing) : 0 < M.nC1 * M.t12 * (g M + M.c) :=
  mul_pos (mul_pos (nC1_pos hM) hM.t12_pos) (add_pos (g_pos hM) hM.c_pos)

lemma Lq_le (hM : M.Standing) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    L M b / b ≤ L M a / a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  rw [div_le_div_iff₀ hb ha]; unfold L
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right (T_pos hM)]
  nlinarith [mul_le_mul_of_nonneg_left hab (beta_pos hM).le]

lemma Lq_lt (hM : M.Standing) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    L M b / b < L M a / a := by
  have hb : 0 < b := lt_trans ha hab
  rw [div_lt_div_iff₀ hb ha]; unfold L
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_lt_div_iff_of_pos_right (T_pos hM)]
  nlinarith [mul_lt_mul_of_pos_left hab (beta_pos hM)]

lemma Lq_le_g (hM : M.Standing) {a : ℝ} (ha : 0 < a) (h : M.nC1 ≤ a) : L M a / a ≤ g M := by
  rw [div_le_iff₀ ha]; unfold L
  rw [div_le_iff₀ (T_pos hM)]; unfold T
  have h0 : 0 ≤ M.t12 * (g M + M.c) := (mul_pos hM.t12_pos (add_pos (g_pos hM) hM.c_pos)).le
  nlinarith [mul_le_mul_of_nonneg_left h h0]

lemma g_le_Lq (hM : M.Standing) {a : ℝ} (ha : 0 < a) (h : a ≤ M.nC1) : g M ≤ L M a / a := by
  rw [le_div_iff₀ ha]; unfold L
  rw [le_div_iff₀ (T_pos hM)]; unfold T
  have h0 : 0 ≤ M.t12 * (g M + M.c) := (mul_pos hM.t12_pos (add_pos (g_pos hM) hM.c_pos)).le
  nlinarith [mul_le_mul_of_nonneg_left h h0]

lemma P_small (hM : M.Standing) {n : ℝ} (hn : 0 < n) (h : n ≤ M.nC1) : P M n = g M := by
  rw [P_eq hn]
  apply le_antisymm ((min_le_left _ _).trans (min_le_left _ _))
  refine le_min (le_min le_rfl (g_le_Lq hM hn h)) ?_
  rw [le_div_iff₀ hn, D_eq]
  have hd : 0 < M.Λ21 - M.Λ12 := by linarith [hM.Λ12_lt_Λ21]
  nlinarith [mul_le_mul_of_nonneg_left h (g_pos hM).le, mul_pos hd (A_pos hM)]

lemma P_le_g {n : ℝ} (hn : 0 < n) : P M n ≤ g M := by
  rw [P_eq hn]; exact (min_le_left _ _).trans (min_le_left _ _)

lemma P_cont : ContinuousOn (P M) (Set.Ioi 0) := by
  have hc : Continuous (m M) := by
    unfold m L
    exact ((continuous_const.mul continuous_id).min
      (((continuous_const.mul continuous_id).add continuous_const).div_const _)).min
      continuous_const
  show ContinuousOn (fun n => m M n / n) (Set.Ioi 0)
  exact hc.continuousOn.div continuousOn_id (fun x hx => (Set.mem_Ioi.mp hx).ne')

lemma piC_cont (hM : M.Standing) : ContinuousOn M.piC (Set.Ioi 0) :=
  P_cont.congr (fun n hn => piC_eq hM hn)

lemma piC_anti (hM : M.Standing) : AntitoneOn M.piC (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha' : 0 < a := ha
  have hb' : 0 < b := hb
  rw [piC_eq hM ha', piC_eq hM hb', P_eq ha', P_eq hb']
  exact min_le_min (min_le_min le_rfl (Lq_le hM ha' hab))
    (div_le_div_of_nonneg_left (D_pos hM).le ha' hab)

lemma piC_santi (hM : M.Standing) : StrictAntiOn M.piC (Set.Ioi M.nC1) := by
  intro a ha b hb hab
  have ha1 : M.nC1 < a := ha
  have ha' : 0 < a := lt_trans (nC1_pos hM) ha1
  have hb' : 0 < b := lt_trans ha' hab
  rw [piC_eq hM ha', piC_eq hM hb', P_eq ha', P_eq hb',
    min_eq_right (Lq_le_g hM ha' ha1.le)]
  have h1 := Lq_lt hM ha' hab
  have h2 : D M / b < D M / a := div_lt_div_of_pos_left (D_pos hM) ha' hab
  calc min (min (g M) (L M b / b)) (D M / b) ≤ min (L M b / b) (D M / b) :=
        min_le_min (min_le_right _ _) le_rfl
    _ < min (L M a / a) (D M / a) := by
        rcases min_choice (L M b / b) (D M / b) with h | h <;> rw [h] <;>
          refine lt_min ?_ ?_ <;> linarith [min_le_left (L M b / b) (D M / b),
            min_le_right (L M b / b) (D M / b)]

lemma F_mono (M : Model) : Monotone M.F := by
  intro a b h; unfold Model.F; exact (ProbabilityTheory.cdf M.μ).mono h

lemma F_le_one (M : Model) (x : ℝ) : M.F x ≤ 1 := by
  unfold Model.F; exact ProbabilityTheory.cdf_le_one M.μ x

lemma g_lt_cbar (hM : M.Standing) : g M < M.cbar := by
  have := hM.cbar_ge
  have := mul_pos hM.γ_pos hM.p_pos
  unfold g Model.gbar; nlinarith

lemma F_g_pos (hM : M.Standing) : 0 < M.F (g M) := by
  have hc := g_lt_cbar hM
  have hg := g_pos hM
  have := hM.F_strictMonoOn ⟨le_refl 0, by linarith⟩ ⟨hg.le, hc.le⟩ hg
  rw [hM.F_zero] at this; exact this

lemma F_g_lt_one (hM : M.Standing) : M.F (g M) < 1 := by
  have hc := g_lt_cbar hM
  have hg := g_pos hM
  have := hM.F_strictMonoOn ⟨hg.le, hc.le⟩ ⟨by linarith, le_rfl⟩ hc
  rw [hM.F_cbar] at this; exact this

lemma piC_le_g (hM : M.Standing) {n : ℝ} (hn : 0 < n) : M.piC n ≤ g M := by
  rw [piC_eq hM hn]; exact P_le_g hn

lemma fix_le (hM : M.Standing) {a b : ℝ} (ha : 0 < a) (hab : a ≤ M.N * M.F (M.piC a))
    (hb : 0 < b) (hbfix : b = M.N * M.F (M.piC b)) : a ≤ b := by
  by_contra h0
  have h : b < a := lt_of_not_ge h0
  have h1 : M.piC a ≤ M.piC b := piC_anti hM hb ha h.le
  have h2 : M.N * M.F (M.piC a) ≤ M.N * M.F (M.piC b) :=
    mul_le_mul_of_nonneg_left (F_mono M h1) hM.N_pos.le
  linarith

lemma exists_unique_fix (hM : M.Standing) :
    ∃! n : ℝ, 0 < n ∧ n = M.N * M.F (M.piC n) := by
  have h1 := nC1_pos hM
  have hN := hM.N_pos
  have hF0 := F_g_pos hM
  have hF1 := F_g_lt_one hM
  obtain ⟨n0, hn0e⟩ : ∃ n0, n0 = min M.nC1 (M.N * M.F (g M) / 2) := ⟨_, rfl⟩
  have hNF : 0 < M.N * M.F (g M) := mul_pos hN hF0
  have hn0 : 0 < n0 := hn0e ▸ lt_min h1 (by linarith)
  have hn0a : n0 ≤ M.nC1 := hn0e ▸ min_le_left _ _
  have hn0b : n0 ≤ M.N * M.F (g M) / 2 := hn0e ▸ min_le_right _ _
  have hNF1 : M.N * M.F (g M) ≤ M.N := mul_le_of_le_one_right hN.le hF1.le
  have hn0N : n0 ≤ M.N := by linarith
  have hcont : ContinuousOn (fun n => n - M.N * M.F (M.piC n)) (Set.Icc n0 M.N) := by
    apply ContinuousOn.sub continuousOn_id
    apply ContinuousOn.mul continuousOn_const
    exact hM.F_continuous.comp_continuousOn
      ((piC_cont hM).mono (fun x hx => lt_of_lt_of_le hn0 hx.1))
  have hlow : n0 - M.N * M.F (M.piC n0) ≤ 0 := by
    rw [piC_eq hM hn0, P_small hM hn0 hn0a]; linarith
  have hhigh : 0 ≤ M.N - M.N * M.F (M.piC M.N) := by
    have := mul_le_of_le_one_right hN.le (F_le_one M (M.piC M.N)); linarith
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc hn0N hcont ⟨hlow, hhigh⟩
  have hc0' : c - M.N * M.F (M.piC c) = 0 := hc0
  have hcpos : 0 < c := lt_of_lt_of_le hn0 hc.1
  have hcfix : c = M.N * M.F (M.piC c) := by linarith
  refine ⟨c, ⟨hcpos, hcfix⟩, fun y hy => le_antisymm ?_ ?_⟩
  · exact fix_le hM hy.1 hy.2.le hcpos hcfix
  · exact fix_le hM hcpos hcfix.le hy.1 hy.2

lemma piC_greatest (hM : M.Standing) {n : ℝ} (hn : 0 < n) :
    IsGreatest ((fun x => M.prof x n) '' {x | M.InCC n x}) (M.piC n) := by
  obtain ⟨x, hx, -, hpr, -, hP⟩ := opt_spec hM hn
  rw [piC_eq hM hn, ← hP]
  exact ⟨⟨x, hx, rfl⟩, by rintro _ ⟨y, hy, rfl⟩; exact hpr y hy⟩

lemma V_mono (hM : M.Standing) {a b : ℝ} (h : a ≤ b) : V M a ≤ V M b := by
  unfold V
  exact min_le_min (min_le_min h (div_le_div_of_nonneg_right
    (by linarith [mul_le_mul_of_nonneg_left h hM.t21_pos.le]) (T_pos hM).le)) le_rfl

lemma item4 (hM : M.Standing) {nC : ℝ} (hnC : 0 < nC) (hfix : nC = M.N * M.F (M.piC nC)) :
    nC < M.N ∧
      IsGreatest {v | ∃ x n, M.Feas13 x n ∧ v = M.Rev x} (M.PiC nC) ∧
      (M.SelC nC).Nonempty ∧
      ∀ x ∈ M.SelC nC, M.Feas13 x nC ∧ M.Rev x = M.PiC nC := by
  obtain ⟨x, hx, hR, hpr, hRev, hP⟩ := opt_spec hM hnC
  have hpx : M.prof x nC = M.piC nC := by rw [hP, piC_eq hM hnC]
  have hPi : M.PiC nC = M.Rev x := by rw [PiC_eq hM hnC, hRev]
  have hopt : x ∈ M.OptC nC := ⟨hx, hR⟩
  have hγp : 0 ≤ M.γ * M.p := (mul_pos hM.γ_pos hM.p_pos).le
  refine ⟨?_, ⟨⟨x, nC, ⟨hnC, hx, by rw [hpx]; exact hfix⟩, hPi⟩, ?_⟩,
    ⟨x, hopt, fun y hy => hpr y hy.1⟩, ?_⟩
  · have h1 : M.F (M.piC nC) < 1 :=
      lt_of_le_of_lt (F_mono M (piC_le_g hM hnC)) (F_g_lt_one hM)
    calc nC = M.N * M.F (M.piC nC) := hfix
      _ < M.N := mul_lt_of_lt_one_right hM.N_pos h1
  · rintro v ⟨y, n, ⟨hn, hy, hyfix⟩, rfl⟩
    have hle : n ≤ M.N * M.F (M.piC n) := by
      have h1 : M.prof y n ≤ M.piC n := (piC_greatest hM hn).2 ⟨y, hy, rfl⟩
      calc n = M.N * M.F (M.prof y n) := hyfix
        _ ≤ M.N * M.F (M.piC n) := mul_le_mul_of_nonneg_left (F_mono M h1) hM.N_pos.le
    have hnle : n ≤ nC := fix_le hM hn hle hnC hfix
    rw [PiC_eq hM hnC]
    calc M.Rev y ≤ M.γ * M.p * V M n := by
          unfold Model.Rev; exact mul_le_mul_of_nonneg_left (sbar_le_V hM hy) hγp
      _ ≤ M.γ * M.p * V M nC := mul_le_mul_of_nonneg_left (V_mono hM hnle) hγp
  · rintro y ⟨⟨hy, hyR⟩, hyP⟩
    have hRy : M.Rev y = M.Rev x := le_antisymm (hR y hy) (hyR x hx)
    have hpy : M.prof y nC = M.prof x nC := le_antisymm (hpr y hy) (hyP x hopt)
    exact ⟨⟨hnC, hy, by rw [hpy, hpx]; exact hfix⟩, by rw [hRy, hPi]⟩

end RHC1

open RideHailing.Central in
theorem solution (M : Model) (hM : M.Standing) :
    ContinuousOn M.piC (Set.Ioi 0) ∧ AntitoneOn M.piC (Set.Ioi 0) ∧
    StrictAntiOn M.piC (Set.Ioi M.nC1) ∧
    (∃! n : ℝ, 0 < n ∧ n = M.N * M.F (M.piC n)) ∧
    (∀ n, 0 < n → n ≤ M.N →
      IsGreatest ((fun x => M.prof x n) '' {x | M.InCC n x}) (M.piC n)) ∧
    (∀ nC, 0 < nC → nC = M.N * M.F (M.piC nC) →
      nC < M.N ∧
      IsGreatest {v | ∃ x n, M.Feas13 x n ∧ v = M.Rev x} (M.PiC nC) ∧
      (M.SelC nC).Nonempty ∧
      ∀ x ∈ M.SelC nC, M.Feas13 x nC ∧ M.Rev x = M.PiC nC) := by
  exact ⟨RHC1.piC_cont hM, RHC1.piC_anti hM, RHC1.piC_santi hM, RHC1.exists_unique_fix hM,
    fun n hn _ => RHC1.piC_greatest hM hn, fun nC hnC hfix => RHC1.item4 hM hnC hfix⟩
