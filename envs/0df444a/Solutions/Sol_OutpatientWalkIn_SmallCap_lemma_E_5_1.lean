-- Prove2me | solution 1 for OutpatientWalkIn.SmallCap.lemma_E_5_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T16:39:23.117127+00:00
-- url     : https://prove2.me/submissions/ce3a78fa-f5b3-42d0-bbcf-31777c4bd251

import Mathlib
import Definitions.Def_OutpatientWalkIn_SmallCap_MD1Queue
import Definitions.Def_OutpatientWalkIn_SmallCap_Setting
import Theorems.Thm_OutpatientWalkIn_SmallCap_proposition_C_2_delta

open OutpatientWalkIn.SmallCap

theorem solution (M : Model) (hM : M.Standing) (μS : ℝ) (hμS : μS ∈ Set.Ico 0 M.mu)
    (u : UnobsStrategy) (hu : M.IsUnobsEq μS u) (e : ObsStrategy) (he : M.IsObsEq μS e)
    (hrate : M.lam * (1 - blockProb M.lam (dbar μS u.lamS) μS) ≥ u.lamS) :
    M.obsCost μS e ≤ M.unobsCost μS u := by
  have hlam := hM.lam_pos
  have hlamE := hM.lamE_nonneg
  have hR := hM.R_pos
  have hCD := hM.CD_pos
  have hCW := hM.CW_pos
  have hW : 0 < M.mu - μS := sub_pos.2 hμS.2
  have hpW := he.pW_nonneg
  have hpB := he.pB_nonneg
  have hs := he.sum_pos
  have hwnn : ∀ x : ℝ, 0 ≤ x → 0 ≤ M.w x := by
    intro x hx
    rw [← hM.w_zero]
    exact hM.w_strictMono.monotoneOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
  -- notation
  set xo := (M.lamE + e.pW * M.lam) / (M.mu - μS) with hxo
  set xu := (u.lamW + M.lamE) / (M.mu - μS) with hxu
  have hxo0 : 0 ≤ xo := div_nonneg (by positivity) hW.le
  have hxu0 : 0 ≤ xu := div_nonneg (by linarith [hu.lamW_nonneg]) hW.le
  set Wo := M.u2W μS e.pW with hWo
  set Wu := M.u1W μS u.lamW with hWu
  have hWo' : Wo = M.R - M.CW * M.w xo := rfl
  have hWu' : Wu = M.R - M.CW * M.w xu := rfl
  have hWuR : Wu ≤ M.R := by rw [hWu']; nlinarith [hwnn xu hxu0]
  set V := e.pW / (e.pW + e.pB) * Wo + e.pB / (e.pW + e.pB) * u2B with hV
  have hV' : V = e.pW / (e.pW + e.pB) * Wo := by rw [hV]; simp [u2B]
  have ht0 : 0 ≤ e.pW / (e.pW + e.pB) := div_nonneg hpW hs.le
  have ht1 : e.pW / (e.pW + e.pB) ≤ 1 := (div_le_one hs).2 (by linarith)
  -- R - C_D δ = V
  have hδV : M.R - M.CD * e.delta = V := by
    have h1 := he.cond6 e.delta he.delta_nonneg le_rfl
    unfold Model.u2S at h1
    by_contra hne
    have hgt : M.R - M.CD * e.delta > V := lt_of_le_of_ne h1 (Ne.symm hne)
    have h2 := he.cond7 (e.delta + (M.R - M.CD * e.delta - V) / (2 * M.CD)) (by
      have : 0 < (M.R - M.CD * e.delta - V) / (2 * M.CD) := div_pos (by linarith) (by positivity)
      linarith)
    unfold Model.u2S at h2
    have : M.CD * (e.delta + (M.R - M.CD * e.delta - V) / (2 * M.CD)) =
        M.CD * e.delta + (M.R - M.CD * e.delta - V) / 2 := by field_simp
    rw [this] at h2
    linarith
  -- d̄ facts
  set db := dbar μS u.lamS with hdb
  have hdbS : 0 < u.lamS → M.CD * db = M.R - M.u1S μS u.lamS := by
    intro _; unfold Model.u1S; rw [hdb]; ring
  have hdbZ : u.lamS = 0 → db = 0 := by intro h; rw [hdb, h]; simp [dbar]
  have hdb0 : 0 ≤ db := by
    rcases eq_or_lt_of_le hu.lamS_nonneg with h | h
    · rw [hdbZ h.symm]
    · have hμ0 : 0 < μS := by
        rcases eq_or_lt_of_le hμS.1 with h0 | h0
        · have := hu.unavailable h0.symm; linarith
        · exact h0
      have := hu.stable hμ0
      rw [hdb]; unfold dbar
      apply div_nonneg h.le
      have : 0 < μS - u.lamS := by linarith
      positivity
  -- monotonicity of π
  have hmono : db ≤ e.delta → blockProb M.lam e.delta μS ≤ blockProb M.lam db μS := by
    intro hle
    rcases eq_or_lt_of_le hμS.1 with h0 | h0
    · rw [← h0]; unfold blockProb; simp
    · exact ((proposition_C_2_delta M.lam hlam μS h0).1.antitoneOn) (Set.mem_Ici.2 hdb0)
        (Set.mem_Ici.2 he.delta_nonneg) hle
  have hrate' : M.lam * blockProb M.lam db μS ≤ u.lamW + u.lamB := by
    have := hu.total; nlinarith
  have hc8 := he.cond8
  have hwmono : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a < b → M.w a < M.w b := fun a b ha hb hab =>
    hM.w_strictMono (Set.mem_Ici.2 ha) (Set.mem_Ici.2 hb) hab
  -- Claim A
  have hA : e.pW * M.lam ≤ u.lamW := by
    by_contra hcon
    push Not at hcon
    have hpW0 : 0 < e.pW := by
      by_contra h; push Not at h
      have : e.pW = 0 := le_antisymm h hpW
      rw [this, zero_mul] at hcon; linarith [hu.lamW_nonneg]
    have hWo0 : 0 ≤ Wo := by
      rcases he.cond9 with h | h
      · linarith
      · simpa [u2B] using h
    have hxlt : xu < xo := by
      rw [hxo, hxu]; apply div_lt_div_of_pos_right _ hW; linarith
    have hWlt : Wo < Wu := by
      rw [hWo', hWu']
      have := mul_lt_mul_of_pos_left (hwmono xu xo hxu0 hxo0 hxlt) hCW
      linarith
    have hB0 : u.lamB = 0 := by
      rcases eq_or_lt_of_le hu.lamB_nonneg with h | h
      · exact h.symm
      · have := (hu.balk_best h).1; linarith
    have hVWo : V ≤ Wo := by rw [hV']; nlinarith [mul_nonneg (sub_nonneg.2 ht1) hWo0]
    have hle : db ≤ e.delta := by
      rcases eq_or_lt_of_le hu.lamS_nonneg with h | h
      · rw [hdbZ h.symm]; exact he.delta_nonneg
      · have h1 := (hu.sched_best h).1
        have h2 := hdbS h
        have : M.CD * db ≤ M.CD * e.delta := by linarith
        exact le_of_mul_le_mul_left this hCD
    have := hmono hle
    have : M.lam * (e.pW + e.pB) ≤ u.lamW := by
      rw [hc8]; nlinarith
    nlinarith
  -- Claim B
  have hB : e.pB * M.lam ≤ u.lamB := by
    by_contra hcon
    push Not at hcon
    have hpB0 : 0 < e.pB := by
      by_contra h; push Not at h
      have : e.pB = 0 := le_antisymm h hpB
      rw [this, zero_mul] at hcon; linarith [hu.lamB_nonneg]
    have hWo0 : Wo ≤ 0 := by
      rcases he.cond10 with h | h
      · linarith
      · simpa [u2B] using h
    have hxle : xo ≤ xu := by
      rw [hxo, hxu]; apply div_le_div_of_nonneg_right _ hW.le; linarith
    have hWle : Wu ≤ Wo := by
      rw [hWo', hWu']
      rcases eq_or_lt_of_le hxle with h | h
      · rw [h]
      · have := mul_lt_mul_of_pos_left (hwmono xo xu hxo0 hxu0 h) hCW
        linarith
    have hV0 : V ≤ 0 := by rw [hV']; exact mul_nonpos_of_nonneg_of_nonpos ht0 hWo0
    have hle : db ≤ e.delta := by
      rcases eq_or_lt_of_le hu.lamS_nonneg with h | h
      · rw [hdbZ h.symm]; exact he.delta_nonneg
      · have h1 := (hu.sched_best h).2
        have h2 := hdbS h
        have : M.CD * db ≤ M.CD * e.delta := by linarith
        exact le_of_mul_le_mul_left this hCD
    have hm := mul_le_mul_of_nonneg_left (hmono hle) hlam.le
    have hsum : M.lam * (e.pW + e.pB) ≤ u.lamW + u.lamB := by
      rw [hc8]; linarith
    have hpWl : 0 ≤ e.pW * M.lam := mul_nonneg hpW hlam.le
    rcases eq_or_lt_of_le hu.lamW_nonneg with h | h
    · linarith
    · have h1 := (hu.walk_best h).1
      have hWu0 : Wu = 0 := le_antisymm (by linarith) h1
      have hWo00 : Wo = 0 := le_antisymm hWo0 (by linarith)
      have hweq : M.w xo = M.w xu := by
        have : M.CW * M.w xo = M.CW * M.w xu := by rw [hWo', hWu'] at *; linarith
        exact mul_left_cancel₀ hCW.ne' this
      have hxeq : xo = xu := hM.w_strictMono.injOn (Set.mem_Ici.2 hxo0) (Set.mem_Ici.2 hxu0) hweq
      have : e.pW * M.lam = u.lamW := by
        rw [hxo, hxu] at hxeq
        have := (div_left_inj' hW.ne').1 hxeq
        linarith
      linarith
  -- cost comparison
  unfold Model.obsCost Model.unobsCost
  have hCL := hM.CL_nonneg
  have hCO := hM.CO_nonneg
  have h1 : M.CL * e.pB * M.lam ≤ M.CL * u.lamB := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hB hCL
  have hx' : (e.pW * M.lam + M.lamE) / (M.mu - μS) = xo := by rw [hxo]; ring_nf
  have hxle : xo ≤ xu := by
    rw [hxo, hxu]; apply div_le_div_of_nonneg_right _ hW.le; linarith
  have h2 : M.o xo ≤ M.o xu :=
    hM.o_strictMono.monotoneOn (Set.mem_Ici.2 hxo0) (Set.mem_Ici.2 hxu0) hxle
  rw [hx']
  linarith [mul_le_mul_of_nonneg_left h2 hCO]
