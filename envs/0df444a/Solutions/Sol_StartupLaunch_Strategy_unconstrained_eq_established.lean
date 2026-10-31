-- Prove2me | solution 1 for StartupLaunch.Strategy.unconstrained_eq_established
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T03:10:30.718567+00:00
-- url     : https://prove2.me/submissions/4dc39ddf-f4c9-438c-bd8f-17f68cedaf7a

import Mathlib
import Definitions.Def_StartupLaunch_Strategy_Model

open StartupLaunch.Strategy

namespace StartupP2AuxM5

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

end StartupP2AuxM5

open StartupP2AuxM5 in
theorem solution (P : Params) (hP : P.Standing) (p : ℝ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (R0 R1 : ℝ → ℝ) (hR : StartupBellman P p R0 R1) (Pi0 Pi1 : ℝ)
    (hPi : EstBellman P p Pi0 Pi1) :
    (∀ E : ℝ, (P.c - P.vo) / (1 - P.δ) ≤ E → R1 E = E + Pi1) ∧
    (∀ E : ℝ, P.c / (1 - P.δ) ≤ E → R0 E = E + Pi0) := by
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
  obtain ⟨eP0, eP1⟩ := hPi
  have hc1 : 0 < 1 - P.δ := by linarith
  have hM0' : ∀ x, -M ≤ R0 x - x := fun x => (abs_le.1 (hM x).1).1
  have hbabs : ∀ y, |(1 - p) * P.δ * y| = (1 - p) * P.δ * |y| := by
    intro y; rw [abs_mul, abs_of_nonneg hb0]
  have hreg1 : ∀ x, (P.c - P.vo) / (1 - P.δ) ≤ x →
      P.c ≤ x + P.vo ∧ (P.c - P.vo) / (1 - P.δ) ≤ EL P x := by
    intro x hx
    rw [div_le_iff₀ hc1] at hx
    have hx0 : 0 < x := by nlinarith
    have hEL : x ≤ EL P x := by
      have := hELmul x
      by_contra hcon
      push_neg at hcon
      nlinarith
    refine ⟨by nlinarith, ?_⟩
    rw [div_le_iff₀ hc1]
    nlinarith
  have part1 : ∀ x, (P.c - P.vo) / (1 - P.δ) ≤ x → R1 x = x + Pi1 := by
    have := contr (fun x : {x : ℝ // (P.c - P.vo) / (1 - P.δ) ≤ x} => |R1 x.1 - x.1 - Pi1|)
      (M + |Pi1|) ((1 - p) * P.δ) hb0 hb1
      (fun x => by
        have h1 := hM1 x.1
        have h2 := hM1' x.1
        have h3 := abs_sub (R1 x.1 - x.1) Pi1
        have h4 : |R1 x.1 - x.1| ≤ M := (hM x.1).2
        linarith) (by
        rintro ⟨x, hx⟩
        right
        obtain ⟨hf, hEL⟩ := hreg1 x hx
        refine ⟨⟨EL P x, hEL⟩, ?_⟩
        try simp only
        have hS : R1 x - x = max (piLS P) (piLC P p (R1 (EL P x) - EL P x)) := by
          rw [hR1 x, if_pos hf, hRLS, hLCe x, max_add_add_left]; ring
        have hS' : R1 x - x - Pi1 = max (piLS P) (piLC P p (R1 (EL P x) - EL P x)) -
            max (piLS P) (piLC P p Pi1) := by rw [← hS, ← eP1]
        rw [hS']
        refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
        rw [sub_self, abs_zero, hLCs, hbabs]
        exact max_le (mul_nonneg hb0 (abs_nonneg _)) le_rfl)
    intro x hx
    have h := this ⟨x, hx⟩
    try simp only at h
    have := abs_nonpos_iff.1 h
    linarith
  refine ⟨part1, ?_⟩
  have hT : (P.c - P.vo) / (1 - P.δ) ≤ P.c / (1 - P.δ) :=
    div_le_div_of_nonneg_right (by linarith) hc1.le
  have hreg0 : ∀ x, P.c / (1 - P.δ) ≤ x →
      P.c ≤ x ∧ P.c ≤ x + P.vo ∧ P.c / (1 - P.δ) ≤ ED P x ∧ x ≤ EL P x := by
    intro x hx
    have hx' := hx
    rw [div_le_iff₀ hc1] at hx
    have hx0 : 0 < x := by nlinarith
    have hED : x ≤ ED P x := by
      have := hEDmul x
      by_contra hcon
      push_neg at hcon
      nlinarith
    have hEL : x ≤ EL P x := by
      have := hELmul x
      by_contra hcon
      push_neg at hcon
      nlinarith
    refine ⟨by nlinarith, by nlinarith, hx'.trans hED, hEL⟩
  have := contr (fun x : {x : ℝ // P.c / (1 - P.δ) ≤ x} => |R0 x.1 - x.1 - Pi0|)
    (M + |Pi0|) ((1 - p) * P.δ) hb0 hb1
    (fun x => by
      have h3 := abs_sub (R0 x.1 - x.1) Pi0
      have h4 : |R0 x.1 - x.1| ≤ M := (hM x.1).1
      linarith) (by
      rintro ⟨x, hx⟩
      right
      obtain ⟨hc, hf, hED, hEL⟩ := hreg0 x hx
      refine ⟨⟨ED P x, hED⟩, ?_⟩
      try simp only
      have hS1 : R1 (EL P x) - EL P x = Pi1 := by
        rw [part1 (EL P x) (hT.trans (hx.trans hEL))]; ring
      have hS : R0 x - x = max (max (piLS P) (piDC P p (R0 (ED P x) - ED P x))) (piLC P p Pi1) := by
        rw [hR0 x, if_pos hf, hRLS, hDCe x hc, hLCe x, hS1, max_add_add_left, max_add_add_left]
        ring
      have hPi0 : Pi0 = max (max (piLS P) (piDC P p Pi0)) (piLC P p Pi1) := by
        rw [max_right_comm, ← eP0]
      have hS' : R0 x - x - Pi0 = max (max (piLS P) (piDC P p (R0 (ED P x) - ED P x))) (piLC P p Pi1)
          - max (max (piLS P) (piDC P p Pi0)) (piLC P p Pi1) := by
        rw [← hS, ← hPi0]
      rw [hS']
      refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
      rw [sub_self, abs_zero]
      refine max_le ?_ (mul_nonneg hb0 (abs_nonneg _))
      refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
      rw [sub_self, abs_zero, hDCs, hbabs]
      exact max_le (mul_nonneg hb0 (abs_nonneg _)) le_rfl)
  intro x hx
  have h := this ⟨x, hx⟩
  try simp only at h
  have := abs_nonpos_iff.1 h
  linarith
