-- Prove2me | solution 1 for TwoStageRnQ.classical_le_Jjoint
-- status  : ACCEPTED   (prove)
-- author  : @beatlesmania
-- created : 2026-11-17T00:30:58.545868+00:00
-- url     : https://prove2.me/submissions/4391c44e-464a-4b43-9660-2061f009954d

import Theorems.Thm_TwoStageRnQ_exact_cost_classical
import Theorems.Thm_TwoStageRnQ_formula_policy_bound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
Reduction of eq. (22), first inequality,:

* `λ > 0`: Proposition 1 (`TwoStageRnQ.exact_cost_classical`) and the
  formula form of Lemma D.2 (`TwoStageRnQ.formula_policy_bound`), with an `ε`-argument;
* `λ = 0`: demand is almost surely constant and the zero-level classical rule costs `0`.
-/

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace TwoStageRnQ

namespace LeJ

/-- With zero demand rate, every increment vanishes almost surely. -/
lemma incr_zero_ae {P : Params} (hlam : P.lam = 0) (S : DemandSpace P) {s t : ℝ} (hst : s ≤ t) :
    ∀ᵐ ω ∂S.ν, S.N t ω = S.N s ω := by
  have hp : poisW 0 0 = 1 := by simp [poisW]
  have h := S.N_law s t hst 0
  rw [hlam, zero_mul, hp, ENNReal.ofReal_one] at h
  have h1 : Measurable (S.N t) := (S.N_adapted t).mono (S.𝓕.le t) le_rfl
  have h2 : Measurable (S.N s) := (S.N_adapted s).mono (S.𝓕.le s) le_rfl
  have hmeas : MeasurableSet {ω | S.N t ω - S.N s ω = ((0 : ℕ) : ℤ)} :=
    measurableSet_eq_fun (h1.sub h2) measurable_const
  have hc : S.ν {ω | S.N t ω - S.N s ω = ((0 : ℕ) : ℤ)}ᶜ = 0 :=
    (prob_compl_eq_zero_iff hmeas).mpr h
  have hae : ∀ᵐ ω ∂S.ν, S.N t ω - S.N s ω = ((0 : ℕ) : ℤ) := by
    rw [ae_iff]
    exact hc
  filter_upwards [hae] with ω hω
  push_cast at hω
  linarith

/-- With zero demand rate, demand is almost surely constant in time. -/
lemma N_const_ae {P : Params} (hlam : P.lam = 0) (S : DemandSpace P) :
    ∀ᵐ ω ∂S.ν, ∀ t, S.N t ω = S.N 0 ω := by
  have hq : ∀ᵐ ω ∂S.ν, ∀ q : ℚ, S.N q ω = S.N 0 ω := by
    rw [ae_all_iff]
    intro q
    rcases le_total (q : ℝ) 0 with h | h
    · filter_upwards [incr_zero_ae hlam S h] with ω hω using hω.symm
    · filter_upwards [incr_zero_ae hlam S h] with ω hω using hω
  filter_upwards [hq] with ω hω t
  obtain ⟨q1, hq1⟩ := exists_rat_lt t
  obtain ⟨q2, hq2⟩ := exists_rat_gt t
  have h1 : S.N q1 ω ≤ S.N t ω := S.N_mono ω hq1.le
  have h2 : S.N t ω ≤ S.N q2 ω := S.N_mono ω hq2.le
  rw [hω q1] at h1
  rw [hω q2] at h2
  exact le_antisymm h2 h1

/-- A long-run cost whose rates vanish almost surely is zero. -/
lemma longRunCost_eq_zero {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) (cI Z : ℝ → Ω → ℝ)
    (h : ∀ᵐ ω ∂ν, (∀ t, cI t ω = 0) ∧ ∀ T, Z T ω = 0) : longRunCost ν cI Z = 0 := by
  unfold longRunCost
  have hT : ∀ T : ℝ, ∫⁻ ω, ((∫⁻ t in Set.Ioc 0 T, ENNReal.ofReal (cI t ω))
      + ENNReal.ofReal (Z T ω)) ∂ν = 0 := by
    intro T
    rw [lintegral_congr_ae (g := fun _ => (0 : ℝ≥0∞))]
    · exact lintegral_zero
    filter_upwards [h] with ω hω
    simp [hω.1, hω.2]
  simp only [hT, mul_zero]
  exact limsup_const 0

/-- The zero-level classical controls `R₁ = R₂ = -1`, `Q = n = 1`, `ρ = 0`. -/
def c0 : ClassicalControls := ⟨(-1, -1, 1, 1, 0), by norm_num⟩

lemma classical_zero_rate {P : Params} (hlam : P.lam = 0) (S : DemandSpace P) :
    classicalLotCost P S c0 = 0 := by
  unfold classicalLotCost
  apply longRunCost_eq_zero
  filter_upwards [N_const_ae hlam S] with ω hω
  obtain ⟨n0, hn0⟩ : ∃ n0 : ℤ, ∀ t, S.N t ω = n0 := ⟨_, hω⟩
  refine ⟨fun t => ?_, fun T => ?_⟩
  · simp [Classical'.cI, costRate, netInv, Classical'.x1, Classical'.x2, Classical'.U1,
      Classical'.U2, Classical'.matchCount, Classical'.reqCount, Classical'.recvCount,
      Classical'.ordCount, c0, hn0]
  · simp [Classical'.matchCount, Classical'.reqCount, Classical'.recvCount,
      Classical'.ordCount, c0, hn0]

end LeJ

end TwoStageRnQ

namespace TwoStageRnQ

theorem _root_.solution (P : Params) (S : DemandSpace P) :
    (⨅ c : ClassicalControls, classicalLotCost P S c) ≤ ENNReal.ofReal (P.Jjoint P.k1 P.k2) := by
  rcases P.lam_nonneg.eq_or_lt with h0 | hpos
  · calc (⨅ c : ClassicalControls, classicalLotCost P S c)
          ≤ classicalLotCost P S LeJ.c0 := iInf_le _ _
      _ = 0 := LeJ.classical_zero_rate h0.symm S
      _ ≤ _ := by simp
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
    have hF := TwoStageRnQ.formula_policy_bound P
    obtain ⟨c', hc'⟩ := exists_lt_of_ciInf_lt (lt_add_of_pos_right
      (⨅ c : ℤ × ℤ × ℕ+ × ℕ+, P.classicalFormula c.1 c.2.1 c.2.2.1 c.2.2.2) hε')
    have hcost := (TwoStageRnQ.exact_cost_classical P hpos S c'.1 c'.2.1 c'.2.2.1 c'.2.2.2).1
    calc (⨅ c : ClassicalControls, classicalLotCost P S c)
          ≤ classicalLotCost P S ⟨(c'.1, c'.2.1, c'.2.2.1, c'.2.2.2, 0), c'.2.2.1.pos⟩ :=
            iInf_le _ _
      _ = ENNReal.ofReal (P.classicalFormula c'.1 c'.2.1 c'.2.2.1 c'.2.2.2) := hcost
      _ ≤ ENNReal.ofReal (P.Jjoint P.k1 P.k2 + ε) := ENNReal.ofReal_le_ofReal (by linarith)
      _ ≤ ENNReal.ofReal (P.Jjoint P.k1 P.k2) + ENNReal.ofReal ε := ENNReal.ofReal_add_le
      _ = ENNReal.ofReal (P.Jjoint P.k1 P.k2) + ε := by rw [ENNReal.ofReal_coe_nnreal]

end TwoStageRnQ
