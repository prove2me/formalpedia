-- Prove2me | solution 1 for QAPooling.MaxMin.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T09:52:00.922091+00:00
-- url     : https://prove2.me/submissions/51d6542c-1919-42ae-a162-30d7fa39f02e

import Mathlib
import Definitions.Def_QAPooling_MaxMin_Model
import Theorems.Thm_QAPooling_MaxMin_proposition_3_4
import Theorems.Thm_QAPooling_MaxMin_claim_3_10
import Theorems.Thm_QAPooling_MaxMin_kkt_display
import Theorems.Thm_QAPooling_MaxMin_profit_identity

-- The two finite-score helpers are copied with namespace-only adaptation from
-- the accepted Bregman submission 1b448e51-2a85-4186-a865-cd2465c489e0,
-- source SHA256 2c769c1c10c2bad0148829c0f9344fe7bbe3f7cded22cc9306b0853e80dd95b5.
-- All directly needed helper proofs are inlined; imported theorems are called
-- only through their registered statements.


-- Inline checked module: FiniteScore


-- Complete finite-score helpers from the accepted Bregman proof; inlined for platform portability.
namespace QAPooling.MaxMin.MainProof

lemma coe_sum {ι : Type*} (t : Finset ι) (f : ι → ℝ) :
    ((∑ j ∈ t, f j : ℝ) : EReal) = ∑ j ∈ t, (f j : EReal) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih => simp [Finset.sum_insert hi, EReal.coe_add, ih]

lemma expectedScore_eq_coe_sum {n : ℕ} (s : ScoringRule n) (p q : Fin n → ℝ)
    (htop : ∀ j, s q j ≠ ⊤) (hzero : ∀ j, s q j = ⊥ → p j = 0) :
    expectedScore s p q = ((∑ j, p j * (s q j).toReal : ℝ) : EReal) := by
  rw [coe_sum]
  unfold expectedScore
  apply Finset.sum_congr rfl
  intro j _
  by_cases hb : s q j = ⊥
  · simp [hzero j hb]
  · rw [EReal.coe_mul, EReal.coe_toReal (htop j) hb]

end QAPooling.MaxMin.MainProof


-- Inline checked module: MaxMin


namespace QAPooling.MaxMin.MainProof

lemma exists_positive_coordinate {n : ℕ} {x : Fin n → ℝ}
    (hx : x ∈ stdSimplex ℝ (Fin n)) : ∃ j, 0 < x j := by
  by_contra hn
  push Not at hn
  have hsum : ∑ j, x j ≤ 0 := Finset.sum_nonpos fun j _ => hn j
  rw [hx.2] at hsum
  norm_num at hsum

lemma minProfit_of_corrections {n m : ℕ} (s : ScoringRule n)
    (p : Fin m → Fin n → ℝ) (w : Fin m → ℝ) (x : Fin n → ℝ)
    (hx : x ∈ stdSimplex ℝ (Fin n)) (C : ℝ) (mu : Fin n → ℝ)
    (hmu : ∀ j, 0 ≤ mu j) (hcs : ∀ j, 0 < x j → mu j=0)
    (hprofit : ∀ j, profit s p w x j = ((C+mu j : ℝ) : EReal)) :
    minProfit s p w x = (C : EReal) ∧
    ∀ j, 0 < x j → profit s p w x j = minProfit s p w x := by
  have hmin : minProfit s p w x = (C : EReal) := by
    apply le_antisymm
    · obtain ⟨j,hj⟩ := exists_positive_coordinate hx
      calc
        minProfit s p w x ≤ profit s p w x j := iInf_le _ j
        _ = C := by rw [hprofit j,hcs j hj,add_zero]
    · apply le_iInf
      intro j
      rw [hprofit]
      exact EReal.coe_le_coe_iff.mpr (le_add_of_nonneg_right (hmu j))
  refine ⟨hmin,?_⟩
  intro j hj
  rw [hmin,hprofit,hcs j hj,add_zero]

lemma unique_maxmin_of_support_flat {n m : ℕ} (s : ScoringRule n)
    (hreg : QAPooling.MaxMin.IsRegular s) (hprop : IsProper s)
    (p : Fin m → Fin n → ℝ) (w : Fin m → ℝ) (x : Fin n → ℝ)
    (hx : x ∈ forecastDomain s) (C : ℝ)
    (hmin : minProfit s p w x = (C : EReal))
    (hflat : ∀ j, 0 < x j → profit s p w x j = minProfit s p w x) :
    ∀ q ∈ stdSimplex ℝ (Fin n), q ≠ x → minProfit s p w q < minProfit s p w x := by
  intro q hq hne
  rw [hmin]
  by_contra hn
  have hqmin : (C : EReal) ≤ minProfit s p w q := le_of_not_gt hn
  have hqprofit (j : Fin n) : (C : EReal) ≤ profit s p w q j :=
    hqmin.trans (iInf_le _ j)
  have hqbot (j : Fin n) : s q j ≠ ⊥ := by
    intro hb
    have hh := hqprofit j
    unfold profit at hh
    rw [hb,EReal.bot_sub] at hh
    exact EReal.coe_ne_bot C (le_antisymm hh bot_le)
  have hreal (j : Fin n) :
      x j * (s x j).toReal ≤ x j * (s q j).toReal := by
    by_cases hj : 0 < x j
    · have hflatj := hflat j hj
      rw [hmin] at hflatj
      have hqj := hqprofit j
      unfold profit at hflatj hqj
      rw [← EReal.coe_toReal (hx.2 j).2 (hx.2 j).1, ← EReal.coe_sub] at hflatj
      rw [← EReal.coe_toReal (hreg q hq j).1 (hqbot j), ← EReal.coe_sub] at hqj
      have hf := EReal.coe_eq_coe_iff.mp hflatj
      have hq' := EReal.coe_le_coe_iff.mp hqj
      exact mul_le_mul_of_nonneg_left (by linarith) (hx.1.1 j)
    · have hj0 : x j=0 := le_antisymm (le_of_not_gt hj) (hx.1.1 j)
      simp only [hj0,zero_mul,le_refl]
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hreal j)
  have hreverse : expectedScore s x x ≤ expectedScore s x q := by
    rw [expectedScore_eq_coe_sum s x x (fun j => (hx.2 j).2)
      (fun j hj => ((hx.2 j).1 hj).elim)]
    rw [expectedScore_eq_coe_sum s x q (fun j => (hreg q hq j).1)
      (fun j hj => (hqbot j hj).elim)]
    exact EReal.coe_le_coe_iff.mpr hsum
  exact hne ((hprop x hx.1 q hq).2 (le_antisymm (hprop x hx.1 q hq).1 hreverse))

end QAPooling.MaxMin.MainProof


-- Inline checked module: Positivity


namespace QAPooling.MaxMin.MainProof

lemma divergence_sum_properties {n m : ℕ} (s : ScoringRule n) (g : (Fin n → ℝ) → Fin n → ℝ)
    (hreg : QAPooling.MaxMin.IsRegular s) (hprop : IsProper s) (hg : IsExposure s g)
    (p : Fin m → Fin n → ℝ) (hp : ∀ i, p i ∈ forecastDomain s)
    (w : Fin m → ℝ) (hw0 : ∀ i, 0 ≤ w i)
    (x : Fin n → ℝ) (hx : x ∈ stdSimplex ℝ (Fin n)) :
    0 ≤ ∑ i, w i * bregman s g x (p i) ∧
    ((∃ i i', 0 < w i ∧ 0 < w i' ∧ p i ≠ p i') →
      0 < ∑ i, w i * bregman s g x (p i)) := by
  have hd (i : Fin m) := proposition_3_4 s g hreg hprop hg (p i) (hp i) x hx
  have hterm (i : Fin m) : 0 ≤ w i * bregman s g x (p i) := mul_nonneg (hw0 i) (hd i).1
  refine ⟨Finset.sum_nonneg (fun i _ => hterm i), ?_⟩
  rintro ⟨i,j,hi,hj,hne⟩
  have hsome : ∃ k, 0 < w k ∧ x ≠ p k := by
    by_cases he : x=p i
    · exact ⟨j,hj,fun h => hne (he.symm.trans h)⟩
    · exact ⟨i,hi,he⟩
  obtain ⟨k,hk,hxk⟩ := hsome
  have hkdiv : 0 < bregman s g x (p k) :=
    lt_of_le_of_ne (hd k).1 (fun h => hxk ((hd k).2 h.symm))
  exact (mul_pos hk hkdiv).trans_le (Finset.single_le_sum (fun i _ => hterm i) (Finset.mem_univ k))

lemma theorem_of_profit_formula {n m : ℕ} (s : ScoringRule n)
    (g : (Fin n → ℝ) → Fin n → ℝ)
    (hreg : QAPooling.MaxMin.IsRegular s) (hprop : IsProper s) (hg : IsExposure s g)
    (p : Fin m → Fin n → ℝ) (hp : ∀ i, p i ∈ forecastDomain s)
    (w : Fin m → ℝ) (hw0 : ∀ i, 0 ≤ w i)
    (x : Fin n → ℝ) (hD : x ∈ forecastDomain s)
    (mu : Fin n → ℝ) (hmu : ∀ j, 0 ≤ mu j) (hcs : ∀ j, 0 < x j → mu j=0)
    (hprofit : ∀ j, profit s p w x j = ((∑ i, w i * bregman s g x (p i) + mu j : ℝ) : EReal)) :
    (∀ q ∈ stdSimplex ℝ (Fin n), q ≠ x → minProfit s p w q < minProfit s p w x) ∧
    (∀ j, 0 < x j → profit s p w x j = minProfit s p w x) ∧
    0 ≤ minProfit s p w x ∧
    ((∃ i i', 0 < w i ∧ 0 < w i' ∧ p i ≠ p i') → 0 < minProfit s p w x) := by
  obtain ⟨hmin,hflat⟩ := minProfit_of_corrections s p w x hD.1 _ mu hmu hcs hprofit
  have hdiv := divergence_sum_properties s g hreg hprop hg p hp w hw0 x hD.1
  refine ⟨unique_maxmin_of_support_flat s hreg hprop p w x hD _ hmin hflat,hflat,?_,?_⟩
  · rw [hmin]
    exact EReal.coe_le_coe_iff.mpr hdiv.1
  · intro h
    rw [hmin]
    exact EReal.coe_lt_coe_iff.mpr (hdiv.2 h)

end QAPooling.MaxMin.MainProof


-- Inline checked module: Main


namespace QAPooling.MaxMin

/-- Theorem 4.1 (p. 14). For a regular, proper, continuous scoring rule `s` with exposure function
`g`, forecasts `p_i ∈ D` and non-negative weights `w_i` adding to 1, let `p*` be their QA pool and
`u(q; j) = s(q; j) − Σ_i w_i s(p_i; j)`. Then:
1. every report `q ∈ Δⁿ` other than `p*` has `min_j u(q; j) < min_j u(p*; j)`;
2. `u(p*; j) = min_j u(p*; j)` for every `j` with `p*_j > 0`;
3. `min_j u(p*; j) ≥ 0`;
4. `min_j u(p*; j) > 0` unless all reports with positive weight are equal. -/
theorem _root_.solution {n m : ℕ} (s : ScoringRule n) (g : (Fin n → ℝ) → Fin n → ℝ)
    (hreg : IsRegular s) (hprop : IsProper s)
    (hcont : ∀ j, ContinuousOn (fun p => s p j) (stdSimplex ℝ (Fin n)))
    (hGcont : ContinuousOn (expectedReward s) (stdSimplex ℝ (Fin n)))
    (hg : IsExposure s g)
    (p : Fin m → Fin n → ℝ) (hp : ∀ i, p i ∈ forecastDomain s)
    (w : Fin m → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (pstar : Fin n → ℝ) (hpstar : IsQAPool s g p w pstar) :
    (∀ q ∈ stdSimplex ℝ (Fin n), q ≠ pstar → minProfit s p w q < minProfit s p w pstar) ∧
    (∀ j, 0 < pstar j → profit s p w pstar j = minProfit s p w pstar) ∧
    0 ≤ minProfit s p w pstar ∧
    ((∃ i i', 0 < w i ∧ 0 < w i' ∧ p i ≠ p i') → 0 < minProfit s p w pstar) := by
  have hD := claim_3_10 s g hreg hprop hcont hg p hp w hw0 hw1 pstar hpstar
  obtain ⟨lam,mu,hkkt,hmu,hcs⟩ := kkt_display s g hreg hprop hcont hGcont hg p hp w hw0 hw1 pstar hpstar
  have hprofit := profit_identity s g hg p hp w hw1 pstar hD lam mu hkkt hcs
  exact MainProof.theorem_of_profit_formula s g hreg hprop hg p hp w hw0 pstar hD mu hmu hcs hprofit

end QAPooling.MaxMin
