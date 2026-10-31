-- Prove2me | solution 1 for StartupLaunch.Strategy.lemma_1_ii_corrected
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T03:08:27.439138+00:00
-- url     : https://prove2.me/submissions/1872d576-c2f7-4da5-b089-3faccce311c3

import Mathlib
import Definitions.Def_StartupLaunch_Strategy_Model

open StartupLaunch.Strategy

namespace StartupP2AuxL2

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

end StartupP2AuxL2

open StartupP2AuxL2 in
theorem solution (P : Params) (hP : P.Standing) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (p1 p2 : ℝ) (hth : IsThresholds P p1 p2) (R0 R1 : ℝ → ℝ) (hR : StartupBellman P p R0 R1)
    (h12 : p1 < p2) (hp : p1 < p) (E : ℝ) (hE : P.c ≤ E + P.vo) :
    RLS P E < RLC P p R1 E := by
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
  obtain ⟨qs, hqsd⟩ : ∃ qs, qs = min p2 1 := ⟨_, rfl⟩
  have hqs1 : p1 < qs := by rw [hqsd]; exact lt_min h12 (by linarith)
  have hqsle1 : qs ≤ 1 := by rw [hqsd]; exact min_le_right _ _
  have hqsle2 : qs ≤ p2 := by rw [hqsd]; exact min_le_left _ _
  have hLCq : ∀ q, 0 ≤ q → p1 < q → q ≤ qs → EstLaunchContinue P q := fun q h0 h1 h2 =>
    (hth.2.2.2 q h0 (h2.trans hqsle1)).2.1 h1 (h2.trans hqsle2)
  have hp10 : 0 ≤ p1 := by
    by_contra hneg
    push_neg at hneg
    rcases le_or_gt 0 p2 with h2 | h2
    · have := (lc_facts P hP 0 le_rfl zero_le_one
        ((hth.2.2.2 0 le_rfl zero_le_one).2.1 hneg h2)).1
      have := e1 0
      linarith
    · have hdc := (hth.2.2.2 0 le_rfl zero_le_one).2.2 h2
      obtain ⟨Pi0, Pi1, hB⟩ := est_exists P hP 0 le_rfl zero_le_one
      have hfix := hdc Pi0 Pi1 hB
      obtain ⟨e0, e1'⟩ := hB
      have hge : piLS P ≤ Pi0 :=
        ((le_max_left (piLS P) (piLC P 0 Pi1)).trans
          (le_max_left (max (piLS P) (piLC P 0 Pi1)) (piDC P 0 Pi0))).trans (le_of_eq e0.symm)
      unfold piDC at hfix
      nlinarith
  obtain ⟨q0, hq0d⟩ : ∃ q0, q0 = (p1 + min p qs) / 2 := ⟨_, rfl⟩
  have hm1 : p1 < min p qs := lt_min hp hqs1
  have hm2 : min p qs ≤ p := min_le_left _ _
  have hm3 : min p qs ≤ qs := min_le_right _ _
  have hq0 := (lc_facts P hP q0 (by rw [hq0d]; linarith) (by rw [hq0d]; linarith)
    (hLCq q0 (by rw [hq0d]; linarith) (by rw [hq0d]; linarith) (by rw [hq0d]; linarith))).1
  have a0 := e1 q0
  have ap := e1 p
  have hq0pos : 0 < q0 := by rw [hq0d]; linarith
  have hspos : 0 < s := by
    by_contra hns
    push_neg at hns
    have : q0 * s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hq0pos.le hns
    linarith
  have hlt : q0 * s < p * s := mul_lt_mul_of_pos_right (by rw [hq0d]; linarith) hspos
  have hstrict : piLS P < piLC P p (piLS P) := by linarith
  rw [hLCe E, hRLS]
  have := hLCs (R1 (EL P E) - EL P E) (piLS P)
  nlinarith [mul_nonneg hb0 (sub_nonneg.2 (hS1ge (EL P E)))]
