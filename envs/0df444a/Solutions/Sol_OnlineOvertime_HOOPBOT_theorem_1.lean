-- Prove2me | solution 1 for OnlineOvertime.HOOPBOT.theorem_1
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-10-20T14:13:02.216273+00:00
-- url     : https://prove2.me/submissions/374cede6-1ce2-420a-a1e2-d7e185b4da11

import Mathlib
import Definitions.Def_OnlineOvertime_HOOPBOT_Model

open OnlineOvertime.HOOPBOT

/-- The counterexample instance: one server, one day, two customers. -/
noncomputable def cexI : Instance 1 1 2 :=
  ⟨fun _ _ => 3, fun _ _ => 0, fun _ => 0,
    fun j _ => if j = 0 then 1/10 else 1, fun j _ => if j = 0 then 1/10 else 1⟩

lemma cex_gamma : gammaMax cexI = 1 := by
  have h : ∀ (j : Fin 2) (i : Fin 1), cexI.c j i / cexI.b j i = 1 := by
    intro j i; fin_cases j <;> simp [cexI]
  simp only [gammaMax, h, ciSup_const]

lemma cex_dMax : dMax cexI = 0 := by
  simp [dMax, cexI]

lemma cex_lam : lam cexI = 1 := by
  have h : ∀ (j : Fin 2) (i : Fin 1), cexI.c j i / cexI.b j i - cexI.d i = 1 := by
    intro j i; fin_cases j <;> simp [cexI]
  simp only [lam, h, ciSup_const]; norm_num

lemma cex_zeta : zeta cexI = 0 := by
  simp [zeta, cex_dMax, cex_gamma]

lemma cex_Rmax : Rmax cexI = 1/3 := by
  unfold Rmax
  simp only [ciSup_unique]
  apply le_antisymm
  · apply ciSup_le; intro j; fin_cases j <;> norm_num [cexI]
  · refine le_ciSup_of_le (Set.finite_range _).bddAbove 1 ?_
    norm_num [cexI]

lemma cex_alpha : alpha cexI = 64/27 := by
  rw [alpha, cex_Rmax]
  rw [show (1:ℝ) / (1/3) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  norm_num

lemma cex_theta : thetaStar cexI = 9/7 := by
  rw [thetaStar, cex_Rmax, cex_alpha, cex_zeta, cex_lam]
  have : Real.sqrt ((1 + 1/3) ^ 2 * (0 + 1) ^ 2 + 4 * (1 + 1/3) * (64/27 - (1 + 1/3)) * 0 * 1)
      = 4/3 := by
    rw [show ((1:ℝ) + 1/3) ^ 2 * (0 + 1) ^ 2 + 4 * (1 + 1/3) * (64/27 - (1 + 1/3)) * 0 * 1
      = (4/3)^2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [this]; norm_num

lemma cex_ratio : ratio cexI = 7/48 := by
  rw [ratio, cex_gamma, cex_Rmax, cex_theta]; norm_num

lemma cex_standing : cexI.Standing := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i t; simp [cexI]
  · intro i t; simp [cexI]
  · intro i; simp [cexI]
  · intro j i; fin_cases j <;> norm_num [cexI]
  · intro j i; fin_cases j <;> norm_num [cexI]
  · rw [cex_Rmax]; norm_num

noncomputable def cexSel : (Fin 1 × Fin 1 → ℝ) → Fin 1 × Fin 1 := fun _ => (0, 0)

lemma cex_sel : IsArgmaxSelector cexSel := by
  intro f q
  have : q = cexSel f := Subsingleton.elim _ _
  rw [this]

lemma cex_run_y1 :
    (run cexI (thetaStar cexI) (thetaStar cexI) cexSel).y 1 0 0 = 0 := by
  rw [cex_theta]
  have hl : (List.finRange 2).take 2 = [0, 1] := by decide
  simp only [run, runPrefix, hl, List.foldl_cons, List.foldl_nil]
  simp [step, init, upd, cbar, cexSel, cexI]
  norm_num

theorem solution : ¬ (∀ {n T m : ℕ} (I : Instance n T m) (hS : I.Standing)
    (sel : (Fin n × Fin T → ℝ) → Fin n × Fin T) (hsel : IsArgmaxSelector sel),
    let s := run I (thetaStar I) (thetaStar I) sel
    ∃ (yt : Fin m → Fin n → Fin T → ℝ) (vt : Fin n → Fin T → ℝ),
      Feasible I yt vt ∧ (∀ j i t, yt j i t ≤ s.y j i t) ∧ (∀ i t, vt i t ≤ s.v i t) ∧
      (∀ i t, (Finset.univ.filter (fun j => yt j i t ≠ s.y j i t)).card ≤ 2) ∧
      ∀ fstar : ℝ,
        IsGreatest {f : ℝ | ∃ (y : Fin m → Fin n → Fin T → ℝ) (v : Fin n → Fin T → ℝ),
          Feasible I y v ∧ obj I y v = f} fstar →
        ratio I * fstar ≤ obj I yt vt) := by
  intro h
  obtain ⟨yt, vt, hF, hy, -, -, hr⟩ := h cexI cex_standing cexSel cex_sel
  have hG : IsGreatest {f : ℝ | ∃ (y : Fin 2 → Fin 1 → Fin 1 → ℝ) (v : Fin 1 → Fin 1 → ℝ),
      Feasible cexI y v ∧ obj cexI y v = f} (11/10) := by
    constructor
    · refine ⟨fun _ _ _ => 1, fun _ _ => 0, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · intros; right; rfl
      · intro j; simp
      · intro i t; simp [Fin.sum_univ_two, cexI]; norm_num
      · intro i t; simp [cexI]
      · intro i t; simp
      · simp [obj, Fin.sum_univ_two, cexI]; norm_num
    · rintro f ⟨y, v, ⟨h01, -, -, -, -⟩, rfl⟩
      have a0 : y 0 0 0 ≤ 1 := by rcases h01 0 0 0 with h | h <;> rw [h] <;> norm_num
      have a1 : y 1 0 0 ≤ 1 := by rcases h01 1 0 0 with h | h <;> rw [h] <;> norm_num
      simp [obj, Fin.sum_univ_two, cexI]
      linarith
  have h1 := hr _ hG
  rw [cex_ratio] at h1
  obtain ⟨h01, -, -, -, -⟩ := hF
  have b1 : yt 1 0 0 ≤ 0 := by
    have := hy 1 0 0
    rwa [cex_run_y1] at this
  have a0 : yt 0 0 0 ≤ 1 := by rcases h01 0 0 0 with h | h <;> rw [h] <;> norm_num
  have : obj cexI yt vt = 1/10 * yt 0 0 0 + yt 1 0 0 := by
    simp [obj, Fin.sum_univ_two, cexI]
  rw [this] at h1
  linarith
