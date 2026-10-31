-- Prove2me | solution 1 for StartupLaunch.Strategy.lemma_1_i
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T03:08:26.838544+00:00
-- url     : https://prove2.me/submissions/7d0fa040-a01b-4343-8f3f-6f955380b27e

import Mathlib
import Definitions.Def_StartupLaunch_Strategy_Model

open StartupLaunch.Strategy

namespace StartupP2AuxL1

/-- Contraction principle: a function bounded above that is, at every point, either
nonpositive or at most `b` times its value at another point (with `0 ≤ b < 1`) is nonpositive. -/
theorem contr {X : Type} (φ : X → ℝ) (K b : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hK : ∀ x, φ x ≤ K) (h : ∀ x, φ x ≤ 0 ∨ ∃ y, φ x ≤ b * φ y) : ∀ x, φ x ≤ 0 := by
  have hK'pos : 0 < max K 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have key : ∀ n : ℕ, ∀ x, φ x ≤ b ^ n * max K 1 := by
    intro n
    induction n with
    | zero => intro x; simpa using (hK x).trans (le_max_left _ _)
    | succ n ih =>
      intro x
      rcases h x with h0 | ⟨y, hy⟩
      · exact h0.trans (by positivity)
      · calc φ x ≤ b * φ y := hy
          _ ≤ b * (b ^ n * max K 1) := mul_le_mul_of_nonneg_left (ih y) hb0
          _ = b ^ (n+1) * max K 1 := by ring
  intro x
  by_contra hx
  push_neg at hx
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hx hK'pos) hb1
  have := key n x
  rw [lt_div_iff₀ hK'pos] at hn
  linarith

/-- The established firm's equations (1)–(2) have a solution at every `q ∈ [0,1]`. -/
theorem est_exists (P : Params) (hP : P.Standing) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∃ Pi0 Pi1, EstBellman P q Pi0 Pi1 := by
  obtain ⟨hvo, hvova, hvoc, hδ0, hδ1, hα0, hα1⟩ := hP
  obtain ⟨B, hBd⟩ : ∃ B, B = (1 - q) * P.δ := ⟨_, rfl⟩
  have hB : 0 < 1 - B := by rw [hBd]; nlinarith
  obtain ⟨A, hAd⟩ : ∃ A, A = P.vo - P.c + q * (1 - P.α) * P.δ * P.Va := ⟨_, rfl⟩
  obtain ⟨D, hDd⟩ : ∃ D, D = -P.c + q * (P.δ * P.Va) := ⟨_, rfl⟩
  have hLC : ∀ x, piLC P q x = A + B * x := by intro x; rw [hAd, hBd]; unfold piLC; ring
  have hDC : ∀ x, piDC P q x = D + B * x := by intro x; rw [hDd, hBd]; unfold piDC; ring
  have hF : A + B * (A / (1 - B)) = A / (1 - B) := by field_simp; ring
  have hG : D + B * (D / (1 - B)) = D / (1 - B) := by field_simp; ring
  have h1 : max (piLS P) (A / (1 - B)) =
      max (piLS P) (piLC P q (max (piLS P) (A / (1 - B)))) := by
    rw [hLC]
    rcases le_total (A / (1 - B)) (piLS P) with h | h
    · rw [max_eq_left h]
      have : A ≤ piLS P * (1 - B) := by rwa [div_le_iff₀ hB] at h
      rw [max_eq_left (show A + B * piLS P ≤ piLS P by linarith)]
    · rw [max_eq_right h, hF, max_eq_right h]
  refine ⟨max (max (piLS P) (A / (1 - B))) (D / (1 - B)), max (piLS P) (A / (1 - B)), ?_, h1⟩
  rw [← h1, hDC]
  rcases le_total (D / (1 - B)) (max (piLS P) (A / (1 - B))) with h | h
  · rw [max_eq_left h]
    have : D ≤ max (piLS P) (A / (1 - B)) * (1 - B) := by rwa [div_le_iff₀ hB] at h
    rw [max_eq_left (show D + B * max (piLS P) (A / (1 - B)) ≤ max (piLS P) (A / (1 - B)) by
      linarith)]
  · rw [max_eq_right h, hG, max_eq_right h]

theorem ls_facts (P : Params) (hP : P.Standing) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (h : EstLaunchStop P q) :
    piLC P q (piLS P) ≤ piLS P ∧ piDC P q (piLS P) ≤ piLS P := by
  obtain ⟨Pi0, Pi1, hB⟩ := est_exists P hP q hq0 hq1
  obtain ⟨h0, h1⟩ := h Pi0 Pi1 hB
  obtain ⟨e0, e1⟩ := hB
  rw [h0, h1] at e0
  rw [h1] at e1
  constructor
  · exact (le_max_right (piLS P) (piLC P q (piLS P))).trans (le_of_eq e1.symm)
  · exact (le_max_right (max (piLS P) (piLC P q (piLS P))) (piDC P q (piLS P))).trans
      (le_of_eq e0.symm)

theorem lc_facts (P : Params) (hP : P.Standing) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (h : EstLaunchContinue P q) :
    piLS P ≤ piLC P q (piLS P) ∧ ∀ x, piDC P q x ≤ piLC P q x := by
  have hP' := hP
  obtain ⟨hvo, hvova, hvoc, hδ0, hδ1, hα0, hα1⟩ := hP'
  obtain ⟨Pi0, Pi1, hB⟩ := est_exists P hP q hq0 hq1
  obtain ⟨h0, h1⟩ := h Pi0 Pi1 hB
  obtain ⟨e0, e1⟩ := hB
  have hge : piLS P ≤ Pi1 := (le_max_left (piLS P) (piLC P q Pi1)).trans (le_of_eq e1.symm)
  have hD : piDC P q Pi0 ≤ Pi0 :=
    (le_max_right (max (piLS P) (piLC P q Pi1)) (piDC P q Pi0)).trans (le_of_eq e0.symm)
  have hB1 : 0 ≤ 1 - (1 - q) * P.δ := by nlinarith
  constructor
  · unfold piLC at *
    nlinarith [mul_nonneg hB1 (sub_nonneg.2 hge)]
  · intro x
    rw [h0, ← h1] at hD
    unfold piLC piDC at *
    linarith

end StartupP2AuxL1

open StartupP2AuxL1 in
theorem solution (P : Params) (hP : P.Standing) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (p1 p2 : ℝ) (hth : IsThresholds P p1 p2) (R0 R1 : ℝ → ℝ) (hR : StartupBellman P p R0 R1)
    (hp : p < p1) :
    ∀ E : ℝ, 0 < E → RDC P p R0 E < RLS P E ∧ RLC P p R1 E < RLS P E := by
  have hP' := hP
  obtain ⟨hvo, hvova, hvoc, hδ0, hδ1, hα0, hα1⟩ := hP'
  obtain ⟨hR1, hR0, M, hM⟩ := hR
  have hVo : 0 < piLS P := by unfold piLS Params.Vo; exact div_pos hvo (by linarith)
  have hvoeq : P.vo - piLS P * (1 - P.δ) = 0 := by
    have h1d : (1 : ℝ) - P.δ ≠ 0 := by linarith
    unfold piLS Params.Vo; field_simp; ring
  have hVaVo : piLS P ≤ P.Va := by
    unfold piLS Params.Vo Params.Va; exact div_le_div_of_nonneg_right hvova (by linarith)
  have hb0 : 0 ≤ (1 - p) * P.δ := mul_nonneg (by linarith) hδ0.le
  have hb1 : (1 - p) * P.δ < 1 := by nlinarith
  have hRLS : ∀ x, RLS P x = x + piLS P := fun x => rfl
  have hELmul : ∀ x, P.δ * EL P x = x + P.vo - P.c := by
    intro x; unfold EL; field_simp
  have hEDmul : ∀ x, P.δ * ED P x = x - P.c := by
    intro x; unfold ED; field_simp
  have hLCe : ∀ x, RLC P p R1 x = x + piLC P p (R1 (EL P x) - EL P x) := by
    intro x; unfold RLC piLC; linear_combination (1 - p) * hELmul x
  have hDCe : ∀ x, P.c ≤ x → RDC P p R0 x = x + piDC P p (R0 (ED P x) - ED P x) := by
    intro x hx; unfold RDC piDC; rw [if_pos hx]; linear_combination (1 - p) * hEDmul x
  have hDClt : ∀ x, x < P.c → RDC P p R0 x = x := by
    intro x hx; unfold RDC; rw [if_neg (not_le.2 hx)]
  have hLCs : ∀ x y, piLC P p x - piLC P p y = (1 - p) * P.δ * (x - y) := by
    intro x y; unfold piLC; ring
  have hDCs : ∀ x y, piDC P p x - piDC P p y = (1 - p) * P.δ * (x - y) := by
    intro x y; unfold piDC; ring
  have hM1 : ∀ x, R1 x - x ≤ M := fun x => (abs_le.1 (hM x).2).2
  have hM0 : ∀ x, R0 x - x ≤ M := fun x => (abs_le.1 (hM x).1).2
  have hM1' : ∀ x, -M ≤ R1 x - x := fun x => (abs_le.1 (hM x).2).1
  have hS1ge : ∀ x, piLS P ≤ R1 x - x := by
    intro x; rw [hR1 x]; split_ifs
    · have := le_max_left (RLS P x) (RLC P p R1 x); linarith [hRLS x]
    · linarith [hRLS x]
  have hS0ge : ∀ x, piLS P ≤ R0 x - x := by
    intro x; rw [hR0 x]; split_ifs
    · have := (le_max_left (RLS P x) (RDC P p R0 x)).trans
        (le_max_left (max (RLS P x) (RDC P p R0 x)) (RLC P p R1 x))
      linarith [hRLS x]
    · have := le_max_left (RLS P x) (RDC P p R0 x); linarith [hRLS x]
  obtain ⟨s, hsd⟩ : ∃ s, s = (1 - P.α) * P.δ * P.Va - P.δ * piLS P := ⟨_, rfl⟩
  have e1 : ∀ q, piLC P q (piLS P) - piLS P = -P.c + q * s := by
    intro q; unfold piLC; rw [hsd]; linear_combination hvoeq
  have e2 : ∀ q, piDC P q (piLS P) - piLS P = -P.c - P.vo + q * (P.δ * P.Va - P.δ * piLS P) := by
    intro q; unfold piDC; linear_combination hvoeq
  have hp1le : p1 ≤ 1 := hth.2.1
  have hq := (hth.2.2.2 ((p + p1) / 2) (by linarith) (by linarith)).1 (by linarith)
  obtain ⟨hq1, hq2⟩ := ls_facts P hP ((p + p1) / 2) (by linarith) (by linarith) hq
  have hLCp : piLC P p (piLS P) < piLS P := by
    have a1 := e1 p
    have a2 := e1 ((p + p1) / 2)
    rcases le_or_gt s 0 with hs | hs
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos hp0 hs]
    · nlinarith [mul_lt_mul_of_pos_right (show p < (p + p1) / 2 by linarith) hs]
  have hDCp : piDC P p (piLS P) < piLS P := by
    have a1 := e2 p
    have a2 := e2 ((p + p1) / 2)
    have ht : 0 ≤ P.δ * P.Va - P.δ * piLS P := by nlinarith
    rcases eq_or_lt_of_le ht with ht0 | ht0
    · rw [← ht0] at a1; linarith
    · nlinarith [mul_lt_mul_of_pos_right (show p < (p + p1) / 2 by linarith) ht0]
  have hφ := contr (fun x => R1 x - x - piLS P) (M - piLS P) ((1 - p) * P.δ) hb0 hb1
    (fun x => by linarith [hM1 x]) (by
      intro x
      try simp only
      rw [hR1 x]
      split_ifs with hf
      · rcases le_total (RLS P x) (RLC P p R1 x) with hh | hh
        · right
          refine ⟨EL P x, ?_⟩
          rw [max_eq_right hh, hLCe x]
          have := hLCs (R1 (EL P x) - EL P x) (piLS P)
          linarith
        · left; rw [max_eq_left hh, hRLS]; linarith
      · left; rw [hRLS]; linarith)
  have hS1 : ∀ x, R1 x - x = piLS P := fun x => le_antisymm (by linarith [hφ x]) (hS1ge x)
  have hLCv : ∀ x, RLC P p R1 x < RLS P x := by
    intro x; rw [hLCe, hRLS, hS1]; linarith
  have hψ := contr (fun x => R0 x - x - piLS P) (M - piLS P) ((1 - p) * P.δ) hb0 hb1
    (fun x => by linarith [hM0 x]) (by
      intro x
      try simp only
      have hR0' : R0 x = max (RLS P x) (RDC P p R0 x) := by
        rw [hR0 x]; split_ifs
        · exact max_eq_left ((hLCv x).le.trans (le_max_left _ _))
        · rfl
      rw [hR0']
      rcases le_total (RLS P x) (RDC P p R0 x) with hh | hh
      · rw [max_eq_right hh]
        by_cases hc : P.c ≤ x
        · right
          refine ⟨ED P x, ?_⟩
          rw [hDCe x hc]
          have := hDCs (R0 (ED P x) - ED P x) (piLS P)
          linarith
        · left; rw [hDClt x (not_le.1 hc)]; linarith
      · left; rw [max_eq_left hh, hRLS]; linarith)
  have hS0 : ∀ x, R0 x - x = piLS P := fun x => le_antisymm (by linarith [hψ x]) (hS0ge x)
  intro E _
  refine ⟨?_, hLCv E⟩
  by_cases hc : P.c ≤ E
  · rw [hDCe E hc, hRLS, hS0]; linarith
  · rw [hDClt E (not_le.1 hc), hRLS]; linarith
