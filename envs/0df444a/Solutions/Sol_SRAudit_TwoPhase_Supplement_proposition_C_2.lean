-- Prove2me | solution 1 for SRAudit.TwoPhase.Supplement.proposition_C_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:35:54.158886+00:00
-- url     : https://prove2.me/submissions/a0f733ea-9dd2-490a-b52b-3ed0f224e51f

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting
import Definitions.Def_SRAudit_TwoPhase_Supplement_Networks
import Definitions.Def_SRAudit_TwoPhase_Supplement_Production

open SRAudit
open SRAudit.TwoPhase
open SRAudit.TwoPhase.Supplement

open SRAudit.TwoPhase

theorem solution {ι : Type} [DecidableEq ι] (E : Demand) (hE : E.Standing)
    (g : Network ι) (hg : WellFormedNet g) :
    (∀ p2 : Firm → ℝ, ∃! q : Firm → ℝ, IsTier1Eq E g p2 q) ∧
    (∀ q : Firm → ℝ, (∀ x, x ∉ g.T1 → q x = 0) → ∀ i ∈ g.T1,
      invDemand2 E g q i = E.α - E.v0 - E.v1 - 4 * E.β * q i - 2 * E.β * ∑ i' ∈ g.T1.erase i, q i') := by
        classical
        have hb : 0 < E.β := hE.1
        have h2b : 2 * E.β ≠ 0 := by positivity
        have hquad (A B x : ℝ) (hB : 0 < B) :
            (∀ y : ℝ, (A - B * y) * y ≤ (A - B * x) * x) ↔ A = 2 * B * x := by
          constructor
          · intro h
            let y := A / (2 * B)
            have hy : 2 * B * y = A := by
              dsimp [y]
              field_simp [ne_of_gt hB] <;> ring
            have hid : (A - B * y) * y - (A - B * x) * x = B * (x - y) ^ 2 := by
              rw [← hy]
              ring
            have hm : B * (x - y) ^ 2 ≤ 0 := by
              rw [← hid]
              exact sub_nonpos.mpr (h y)
            have hs : (x - y) ^ 2 ≤ 0 := nonpos_of_mul_nonpos_right hm hB
            have hz : (x - y) ^ 2 = 0 := le_antisymm hs (sq_nonneg _)
            have hxy : x = y := sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
            rw [hxy]
            exact hy.symm
          · intro hx y
            rw [hx]
            nlinarith only [mul_nonneg hB.le (sq_nonneg (y - x))]
        have hbuyer (p x : ℝ) :
            IsBuyerOptimal E p x ↔ p = E.α - E.v0 - 2 * E.β * x := by
          have hr (z : ℝ) : (E.α - E.β * z - E.v0 - p) * z =
              ((E.α - E.v0 - p) - E.β * z) * z := by ring
          simp only [IsBuyerOptimal, buyerProfit]
          simp_rw [hr]
          rw [hquad _ _ _ hb]
          constructor <;> intro h <;> linarith only [h]
        have hinv1 (x : ℝ) : invDemand1 E x = E.α - E.v0 - 2 * E.β * x := by
          have hu : ∃! p : ℝ, IsBuyerOptimal E p x := by
            refine ⟨E.α - E.v0 - 2 * E.β * x, (hbuyer _ _).2 rfl, ?_⟩
            intro p hp
            exact (hbuyer _ _).1 hp
          rw [invDemand1, dif_pos hu]
          exact (hbuyer _ _).1 hu.exists.choose_spec
        have hsum (q : Firm → ℝ) (i : Firm) (hi : i ∈ g.T1) :
            (∑ j ∈ g.T1, q j) = (∑ j ∈ g.T1.erase i, q j) + q i :=
          (Finset.sum_erase_add _ _ hi).symm
        have hupdate (q : Firm → ℝ) (i : Firm) (hi : i ∈ g.T1) (y : ℝ) :
            (∑ j ∈ g.T1, (Function.update q i y) j) =
              (∑ j ∈ g.T1.erase i, q j) + y := by
          rw [hsum (Function.update q i y) i hi, Function.update_self]
          congr 1
          apply Finset.sum_congr rfl
          intro j hj
          simp [Function.update, Finset.ne_of_mem_erase hj]
        have hchar (p q : Firm → ℝ) :
            IsTier1Eq E g p q ↔
              (∀ x, x ∉ g.T1 → q x = 0) ∧
              ∀ i ∈ g.T1, q i + (∑ j ∈ g.T1, q j) =
                (E.α - E.v0 - E.v1 - p i) / (2 * E.β) := by
          have hbr (i : Firm) (hi : i ∈ g.T1) :
              (∀ y : ℝ, tier1Payoff E g p (Function.update q i y) i ≤
                tier1Payoff E g p q i) ↔
              E.α - E.v0 - E.v1 - p i - 2 * E.β * (∑ j ∈ g.T1.erase i, q j) =
                2 * (2 * E.β) * q i := by
            simp only [tier1Payoff, hinv1, Function.update_self]
            simp_rw [hupdate q i hi, hsum q i hi]
            have hr (z : ℝ) :
                (E.α - E.v0 - 2 * E.β * ((∑ j ∈ g.T1.erase i, q j) + z) -
                  E.v1 - p i) * z =
                ((E.α - E.v0 - E.v1 - p i -
                  2 * E.β * (∑ j ∈ g.T1.erase i, q j)) - (2 * E.β) * z) * z := by ring
            simp_rw [hr]
            exact hquad _ _ _ (by positivity)
          constructor
          · rintro ⟨hn, hq⟩
            refine ⟨hn, ?_⟩
            intro i hi
            have hf := (hbr i hi).1 (hq i hi)
            apply (eq_div_iff h2b).2
            rw [hsum q i hi]
            nlinarith only [hf]
          · rintro ⟨hn, hq⟩
            refine ⟨hn, ?_⟩
            intro i hi
            apply (hbr i hi).2
            have hf := (eq_div_iff h2b).mp (hq i hi)
            rw [hsum q i hi] at hf
            nlinarith only [hf]
        let f : (Firm → ℝ) → Firm → ℝ :=
          fun p i => (E.α - E.v0 - E.v1 - p i) / (2 * E.β)
        let S : (Firm → ℝ) → ℝ :=
          fun p => (∑ i ∈ g.T1, f p i) / ((g.T1.card : ℝ) + 1)
        have hden : (g.T1.card : ℝ) + 1 ≠ 0 := by positivity
        have hS (p : Firm → ℝ) :
            ((g.T1.card : ℝ) + 1) * S p = ∑ i ∈ g.T1, f p i := by
          dsimp [S]
          field_simp [hden] <;> ring
        have htotal (p q : Firm → ℝ) (hq : IsTier1Eq E g p q) :
            (∑ i ∈ g.T1, q i) = S p := by
          have hl := ((hchar p q).mp hq).2
          have ht : (∑ i ∈ g.T1, q i) =
              (∑ i ∈ g.T1, f p i) - (g.T1.card : ℝ) * (∑ i ∈ g.T1, q i) := by
            calc
              (∑ i ∈ g.T1, q i) =
                  ∑ i ∈ g.T1, (f p i - (∑ j ∈ g.T1, q j)) := by
                apply Finset.sum_congr rfl
                intro i hi
                have hf := hl i hi
                change q i + (∑ j ∈ g.T1, q j) = f p i at hf
                linarith only [hf]
              _ = _ := by simp [Finset.sum_sub_distrib, nsmul_eq_mul]
          apply mul_left_cancel₀ hden
          nlinarith only [ht, hS p]
        constructor
        · intro p
          let q : Firm → ℝ := fun i => if i ∈ g.T1 then f p i - S p else 0
          have hqsum : (∑ i ∈ g.T1, q i) = S p := by
            calc
              (∑ i ∈ g.T1, q i) = ∑ i ∈ g.T1, (f p i - S p) := by
                apply Finset.sum_congr rfl
                intro i hi
                simp only [q, if_pos hi]
              _ = (∑ i ∈ g.T1, f p i) - (g.T1.card : ℝ) * S p := by
                simp [Finset.sum_sub_distrib, nsmul_eq_mul]
              _ = S p := by nlinarith only [hS p]
          have hq : IsTier1Eq E g p q := by
            apply (hchar p q).2
            constructor
            · intro i hi
              simp [q, hi]
            · intro i hi
              rw [hqsum]
              change q i + S p = f p i
              simp only [q, if_pos hi]
              ring
          refine ⟨q, hq, ?_⟩
          intro r hr
          have hrsum := htotal p r hr
          have hrlinear := ((hchar p r).mp hr).2
          funext i
          by_cases hi : i ∈ g.T1
          · have hri := hrlinear i hi
            rw [hrsum] at hri
            change r i + S p = f p i at hri
            simp only [q, if_pos hi]
            linarith only [hri]
          · have hr0 := hr.1 i hi
            simp [q, hi, hr0]
        · intro q hq
          let p : Firm → ℝ := fun i => if i ∈ g.T1 then
            E.α - E.v0 - E.v1 - 2 * E.β * (q i + (∑ j ∈ g.T1, q j)) else 0
          have hp0 : ∀ i, i ∉ g.T1 → p i = 0 := by
            intro i hi
            simp [p, hi]
          have heq : IsTier1Eq E g p q := by
            apply (hchar p q).2
            refine ⟨hq, ?_⟩
            intro i hi
            apply (eq_div_iff h2b).2
            dsimp [p]
            rw [if_pos hi]
            ring
          have hu : ∃! r : Firm → ℝ,
              (∀ i, i ∉ g.T1 → r i = 0) ∧ IsTier1Eq E g r q := by
            refine ⟨p, ⟨hp0, heq⟩, ?_⟩
            intro r hr
            funext i
            by_cases hi : i ∈ g.T1
            · have hf := (eq_div_iff h2b).mp (((hchar r q).mp hr.2).2 i hi)
              dsimp [p]
              rw [if_pos hi]
              nlinarith only [hf]
            · simp [p, hi, hr.1 i hi]
          have hinv : invDemand2 E g q = p := by
            rw [invDemand2, dif_pos hu]
            exact hu.unique hu.exists.choose_spec ⟨hp0, heq⟩
          intro i hi
          rw [hinv]
          simp only [p, if_pos hi]
          rw [hsum q i hi]
          ring
