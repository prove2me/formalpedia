-- Prove2me | solution 1 for StartupLaunch.Strategy.proposition_2_i_ii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T03:03:22.377903+00:00
-- url     : https://prove2.me/submissions/4a7da6d5-e6ba-429a-a09c-886a34085df2

import Mathlib
import Definitions.Def_StartupLaunch_Strategy_Model

open StartupLaunch.Strategy

namespace StartupP2Aux

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

end StartupP2Aux

open StartupP2Aux in
theorem solution (P : Params) (hP : P.Standing) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (p1 p2 : ℝ) (hth : IsThresholds P p1 p2) (R0 R1 : ℝ → ℝ) (hR : StartupBellman P p R0 R1)
    (E : ℝ) (hE : 0 ≤ E) :
    ((p < p1 ∨ E + P.vo < P.c) →
      R0 E = RLS P E ∧ RDC P p R0 E < RLS P E ∧ (P.c ≤ E + P.vo → RLC P p R1 E < RLS P E)) ∧
    ((p1 ≤ p ∧ p < p2 ∧ P.c < E + P.vo) →
      R0 E = RLC P p R1 E ∧ ∀ E' : ℝ, 0 ≤ E' → P.c ≤ E' + P.vo → R1 E' = RLC P p R1 E') := by
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
  refine ⟨fun h => ?_, fun h => ?_⟩
  · -- part (i)
    rcases h with hp | hEc
    · have hp1le : p1 ≤ 1 := hth.2.1
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
      refine ⟨?_, ?_, fun _ => hLCv E⟩
      · rw [hRLS]; linarith [hS0 E]
      · by_cases hc : P.c ≤ E
        · rw [hDCe E hc, hRLS, hS0]; linarith
        · rw [hDClt E (not_le.1 hc), hRLS]; linarith
    · have hEc' : E < P.c := by linarith
      have hR0E : R0 E = max (RLS P E) (RDC P p R0 E) := by
        rw [hR0 E, if_neg (not_le.2 hEc)]
      rw [hDClt E hEc'] at hR0E
      refine ⟨?_, ?_, fun h => absurd h (not_le.2 hEc)⟩
      · rw [hR0E, hRLS]; exact max_eq_left (by linarith)
      · rw [hDClt E hEc', hRLS]; linarith
  · -- part (ii)
    obtain ⟨hpp1, hpp2, hcE⟩ := h
    have hp1lt : p1 < 1 := by
      rcases lt_or_eq_of_le hth.2.1 with h | h
      · exact h
      · have := hth.2.2.1 h; linarith
    obtain ⟨qs, hqsd⟩ : ∃ qs, qs = min p2 1 := ⟨_, rfl⟩
    have hqs1 : p1 < qs := by rw [hqsd]; exact lt_min (by linarith) hp1lt
    have hpqs : p ≤ qs := by rw [hqsd]; exact le_min hpp2.le hp1
    have hqsle1 : qs ≤ 1 := by rw [hqsd]; exact min_le_right _ _
    have hqsle2 : qs ≤ p2 := by rw [hqsd]; exact min_le_left _ _
    have hLCq : ∀ q, 0 ≤ q → p1 < q → q ≤ qs → EstLaunchContinue P q := fun q h0 h1 h2 =>
      (hth.2.2.2 q h0 (h2.trans hqsle1)).2.1 h1 (h2.trans hqsle2)
    obtain ⟨hq1, hq2⟩ := lc_facts P hP qs (by linarith) hqsle1 (hLCq qs (by linarith) hqs1 le_rfl)
    have hVa0 : 0 ≤ P.Va := by linarith
    have hDA : ∀ x, piDC P p x ≤ piLC P p x := by
      intro x
      have h' := hq2 x
      unfold piDC piLC at h' ⊢
      have : p * (P.α * P.δ * P.Va) ≤ qs * (P.α * P.δ * P.Va) :=
        mul_le_mul_of_nonneg_right hpqs (mul_nonneg (mul_nonneg hα0 hδ0.le) hVa0)
      linarith
    have hLCp : piLS P ≤ piLC P p (piLS P) := by
      rcases lt_or_eq_of_le hpp1 with hlt | heq
      · exact (lc_facts P hP p hp0 hp1 (hLCq p hp0 hlt hpqs)).1
      · by_contra hcon
        push_neg at hcon
        have ep := e1 p
        have eq := e1 qs
        have hqs0 : 0 < qs := by linarith
        have hspos : 0 < s := by
          by_contra hns
          push_neg at hns
          have : qs * s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hqs0.le hns
          linarith
        have hcps : 0 < P.c - p * s := by linarith
        obtain ⟨ε, hεd⟩ : ∃ ε, ε = min (qs - p) ((P.c - p * s) / (2 * s)) := ⟨_, rfl⟩
        have hε : 0 < ε := by rw [hεd]; exact lt_min (by linarith [heq ▸ hqs1]) (by positivity)
        have hε1 : ε ≤ qs - p := by rw [hεd]; exact min_le_left _ _
        have hε2 : ε * (2 * s) ≤ P.c - p * s := by
          rw [← le_div_iff₀ (by positivity), hεd]; exact min_le_right _ _
        have hq := (lc_facts P hP (p + ε) (by linarith) (by linarith)
          (hLCq (p + ε) (by linarith) (by rw [heq]; linarith) (by linarith))).1
        have eq2 := e1 (p + ε)
        nlinarith
    have hR1fix : ∀ x, P.c ≤ x + P.vo → R1 x = RLC P p R1 x := by
      intro x hx
      rw [hR1 x, if_pos hx]
      apply max_eq_right
      rw [hRLS, hLCe]
      have := hLCs (R1 (EL P x) - EL P x) (piLS P)
      nlinarith [mul_nonneg hb0 (sub_nonneg.2 (hS1ge (EL P x)))]
    have hmono : ∀ x y, x ≤ y → R1 x - x ≤ R1 y - y := by
      have := contr (fun pr : {pr : ℝ × ℝ // pr.1 ≤ pr.2} =>
          (R1 pr.1.1 - pr.1.1) - (R1 pr.1.2 - pr.1.2)) (M + M) ((1 - p) * P.δ) hb0 hb1
        (fun pr => by linarith [hM1 pr.1.1, hM1' pr.1.2]) (by
          rintro ⟨⟨x, y⟩, hxy⟩
          try simp only at hxy ⊢
          by_cases hf : P.c ≤ x + P.vo
          · right
            refine ⟨⟨(EL P x, EL P y), ?_⟩, ?_⟩
            · simp only; unfold EL; exact div_le_div_of_nonneg_right (by linarith) hδ0.le
            · simp only
              rw [hR1fix x hf, hR1fix y (by linarith), hLCe x, hLCe y]
              have := hLCs (R1 (EL P x) - EL P x) (R1 (EL P y) - EL P y)
              linarith
          · left
            have : R1 x = RLS P x := by rw [hR1 x, if_neg hf]
            rw [this, hRLS]; linarith [hS1ge y])
      intro x y hxy
      have := this ⟨(x, y), hxy⟩
      try simp only at this
      linarith
    have hvd : 0 < P.vo / P.δ := div_pos hvo hδ0
    have hB : ∀ x, R0 x - x ≤ R1 (x + P.vo / P.δ) - (x + P.vo / P.δ) := by
      have := contr (fun x => (R0 x - x) - (R1 (x + P.vo / P.δ) - (x + P.vo / P.δ))) (M + M)
        ((1 - p) * P.δ) hb0 hb1
        (fun x => by linarith [hM0 x, hM1' (x + P.vo / P.δ)]) (by
          intro x
          try simp only
          obtain ⟨y, hy⟩ : ∃ y, y = x + P.vo / P.δ := ⟨_, rfl⟩
          rw [← hy]
          obtain ⟨T, hT⟩ : ∃ T, T = (1 - p) * P.δ * ((R0 (ED P x) - ED P x) -
              (R1 (ED P x + P.vo / P.δ) - (ED P x + P.vo / P.δ))) := ⟨_, rfl⟩
          have hm0 := le_max_left 0 T
          have hm1 := le_max_right 0 T
          have hS1y := hS1ge y
          have tRLS : RLS P x ≤ x + ((R1 y - y) + max 0 T) := by rw [hRLS]; linarith
          have tRDC : RDC P p R0 x ≤ x + ((R1 y - y) + max 0 T) := by
            by_cases hc : P.c ≤ x
            · rw [hDCe x hc]
              have hyf : P.c ≤ y + P.vo := by rw [hy]; linarith
              have e := hR1fix y hyf
              rw [hLCe y] at e
              have hle : ED P x + P.vo / P.δ ≤ EL P y := by
                have : ED P x + P.vo / P.δ = (x - P.c + P.vo) / P.δ := by unfold ED; ring
                rw [this, hy]; unfold EL
                exact div_le_div_of_nonneg_right (by linarith) hδ0.le
              have hm := hmono _ _ hle
              have h1 := hDA (R0 (ED P x) - ED P x)
              have h2 := hLCs (R0 (ED P x) - ED P x)
                (R1 (ED P x + P.vo / P.δ) - (ED P x + P.vo / P.δ))
              have h3 := hLCs (R1 (ED P x + P.vo / P.δ) - (ED P x + P.vo / P.δ))
                (R1 (EL P y) - EL P y)
              have h4 : 0 ≤ (1 - p) * P.δ * ((R1 (EL P y) - EL P y) -
                  (R1 (ED P x + P.vo / P.δ) - (ED P x + P.vo / P.δ))) :=
                mul_nonneg hb0 (by linarith)
              linarith
            · rw [hDClt x (not_le.1 hc)]; linarith
          have tRLC : P.c ≤ x + P.vo → RLC P p R1 x ≤ x + ((R1 y - y) + max 0 T) := by
            intro hf
            have hyf : P.c ≤ y + P.vo := by rw [hy]; linarith
            have e := hR1fix y hyf
            rw [hLCe y] at e
            rw [hLCe x]
            have hle : EL P x ≤ EL P y := by
              unfold EL; exact div_le_div_of_nonneg_right (by rw [hy]; linarith) hδ0.le
            have hm := hmono _ _ hle
            have h3 := hLCs (R1 (EL P x) - EL P x) (R1 (EL P y) - EL P y)
            have h4 : 0 ≤ (1 - p) * P.δ * ((R1 (EL P y) - EL P y) - (R1 (EL P x) - EL P x)) :=
              mul_nonneg hb0 (by linarith)
            linarith
          have key : R0 x ≤ x + ((R1 y - y) + max 0 T) := by
            rw [hR0 x]
            split_ifs with hf
            · exact max_le (max_le tRLS tRDC) (tRLC hf)
            · exact max_le tRLS tRDC
          rcases le_total 0 T with hT0 | hT0
          · right
            refine ⟨ED P x, ?_⟩
            rw [max_eq_right hT0, hT] at key
            try simp only
            linarith
          · left
            rw [max_eq_left hT0] at key
            linarith)
      intro x
      have := this x
      try simp only at this
      linarith
    refine ⟨?_, fun E' _ hE' => hR1fix E' hE'⟩
    have hge1 : RLS P E ≤ RLC P p R1 E := by
      rw [← hR1fix E hcE.le, hRLS]; linarith [hS1ge E]
    have hge2 : RDC P p R0 E ≤ RLC P p R1 E := by
      by_cases hc : P.c ≤ E
      · rw [hDCe E hc, hLCe E]
        have h1 := hDA (R0 (ED P E) - ED P E)
        have h2 := hB (ED P E)
        have heq : ED P E + P.vo / P.δ = EL P E := by unfold ED EL; ring
        rw [heq] at h2
        have h3 := hLCs (R0 (ED P E) - ED P E) (R1 (EL P E) - EL P E)
        nlinarith [mul_nonneg hb0 (sub_nonneg.2 h2)]
      · rw [hDClt E (not_le.1 hc)]; linarith [hge1, hRLS E, hVo]
    rw [hR0 E, if_pos hcE.le]
    exact max_eq_right (max_le hge1 hge2)
