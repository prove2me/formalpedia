-- Prove2me | solution 1 for SubsetShrink.L1.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T01:27:22.527517+00:00
-- url     : https://prove2.me/submissions/7544b9e5-1d10-42c5-8fb0-5acd1ac9025b

import Mathlib
import Definitions.Def_SubsetShrink_L1_Model
import Theorems.Thm_SubsetShrink_L1_eq_37
import Theorems.Thm_SubsetShrink_L1_h_display
import Theorems.Thm_SubsetShrink_L1_f_case_a
import Theorems.Thm_SubsetShrink_L1_fast_l1_step

open SubsetShrink.L1

namespace L1Thm3Aux

lemma l2_eq_norm {m : ℕ} (v : Fin m → ℝ) :
    SubsetShrink.Events.l2 v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin m))‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold SubsetShrink.Events.l2
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [Real.norm_eq_abs, sq_abs]

lemma l2_nonneg {m : ℕ} (v : Fin m → ℝ) : 0 ≤ SubsetShrink.Events.l2 v :=
  Real.sqrt_nonneg _

lemma l2_sub_le {m : ℕ} (v w : Fin m → ℝ) :
    SubsetShrink.Events.l2 (v - w) ≤ SubsetShrink.Events.l2 v + SubsetShrink.Events.l2 w := by
  rw [l2_eq_norm, l2_eq_norm, l2_eq_norm, WithLp.toLp_sub]
  exact norm_sub_le _ _

lemma pe_eq {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (fstar : Fin n → ℝ) (β : Fin p → ℝ) :
    predictionError X fstar β = SubsetShrink.Events.l2 (fun i => fstar i - X.mulVec β i) ^ 2 := by
  unfold SubsetShrink.Events.l2 predictionError
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]

/-- `‖X(β - βhat)‖ ≤ ‖f* - Xβhat‖ + ‖f* - Xβ‖`. -/
lemma D_le {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (fstar : Fin n → ℝ) (βhat β : Fin p → ℝ) :
    SubsetShrink.Events.l2 (X.mulVec (β - βhat)) ≤
      SubsetShrink.Events.l2 (fun i => fstar i - X.mulVec βhat i) +
        SubsetShrink.Events.l2 (fun i => fstar i - X.mulVec β i) := by
  have : X.mulVec (β - βhat) = (fun i => fstar i - X.mulVec βhat i) -
      (fun i => fstar i - X.mulVec β i) := by
    funext i
    rw [Matrix.mulVec_sub]
    simp only [Pi.sub_apply]
    ring
  rw [this]
  exact l2_sub_le _ _

lemma l2sym {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (βhat β : Fin p → ℝ) :
    SubsetShrink.Events.l2 (X.mulVec (βhat - β)) =
      SubsetShrink.Events.l2 (X.mulVec (β - βhat)) := by
  unfold SubsetShrink.Events.l2
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.mulVec_sub, Matrix.mulVec_sub]
  simp only [Pi.sub_apply]
  ring

lemma l1_nonneg {m : ℕ} (v : Fin m → ℝ) : 0 ≤ SubsetShrink.Events.l1 v :=
  Finset.sum_nonneg (fun i _ => abs_nonneg _)

/-- Absorption: `a² ≤ b² + t D + R`, `D ≤ a + b`, `t ≥ 0` gives `a² ≤ 3b² + 2t² + 2R`. -/
lemma absorb (a b D t R : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 ≤ t)
    (h : a ^ 2 ≤ b ^ 2 + t * D + R) (hD : D ≤ a + b) :
    a ^ 2 ≤ 3 * b ^ 2 + 2 * t ^ 2 + 2 * R := by
  have h1 : t * D ≤ t * (a + b) := mul_le_mul_of_nonneg_left hD ht
  nlinarith [sq_nonneg (a - t), sq_nonneg (b - t)]

lemma l0_sub_le {p : ℕ} (v w : Fin p → ℝ) :
    SubsetShrink.Events.l0 (v - w) ≤ SubsetShrink.Events.l0 v + SubsetShrink.Events.l0 w := by
  unfold SubsetShrink.Events.l0
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply, Finset.mem_union] at hi ⊢
  by_contra hc
  push Not at hc
  exact hi (by rw [hc.1, hc.2]; ring)

lemma gam_mul_le {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (s : ℕ) (u : Fin p → ℝ)
    (hu : SubsetShrink.Events.l0 u ≤ s) :
    SubsetShrink.L2.gam X s * SubsetShrink.Events.l2 u ≤
      SubsetShrink.Events.l2 (X.mulVec u) := by
  by_cases h0 : u = 0
  · subst h0
    have : SubsetShrink.Events.l2 (0 : Fin p → ℝ) = 0 := by
      unfold SubsetShrink.Events.l2; simp
    rw [this, mul_zero]
    exact l2_nonneg _
  · have hpos : 0 < SubsetShrink.Events.l2 u := by
      rw [l2_eq_norm]
      apply norm_pos_iff.mpr
      intro h
      apply h0
      have := congrArg (WithLp.ofLp) h
      simpa using this
    have hle : SubsetShrink.L2.gam X s ≤
        SubsetShrink.Events.l2 (X.mulVec u) / SubsetShrink.Events.l2 u := by
      unfold SubsetShrink.L2.gam
      refine ciInf_le_of_le ⟨0, ?_⟩ ⟨u, h0, hu⟩ le_rfl
      rintro _ ⟨w, rfl⟩
      exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rw [le_div_iff₀ hpos] at hle
    exact hle

end L1Thm3Aux

open L1Thm3Aux in
theorem solution :
    ∃ CA CB : ℝ, 0 < CA ∧ 0 < CB ∧
      ∀ {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
        (fstar ε : Fin n → ℝ) (k : ℕ) (σ δ0 lam : ℝ)
        (βhat : Fin p → ℝ),
        SubsetShrink.Events.UnitCols X → 1 ≤ k → k ≤ p → 0 < σ → 0 < δ0 → δ0 ≤ 1 →
        IsL1BestSubset X (fun i => fstar i + ε i) k lam βhat →
        ∀ β : Fin p → ℝ, SubsetShrink.Events.l0 β ≤ k →
          (lam = 2 * σ * Real.sqrt (2 * Real.log (2 * (p : ℝ))) +
              2 * σ * Real.sqrt (2 * Real.log (1 / δ0)) →
            ε ∈ SubsetShrink.Events.H X σ δ0 →
              predictionError X fstar βhat ≤
                predictionError X fstar β + 2 * lam * SubsetShrink.Events.l1 β) ∧
          ((8 + 2 * Real.sqrt 2) * σ *
              Real.sqrt (Real.log (2 * (p : ℝ))) ≤ lam →
            ε ∈ SubsetShrink.Events.F X σ δ0 →
              predictionError X fstar βhat ≤
                CA * (predictionError X fstar β + lam * SubsetShrink.Events.l1 β +
                  σ ^ 2 * Real.log (1 / δ0))) ∧
          (0 ≤ lam → (0 < SubsetShrink.L2.gam X (2 * k) ∨ lam = 0) →
            ε ∈ SubsetShrink.Events.G X σ δ0 (2 * k) →
              predictionError X fstar βhat ≤
                CB * (predictionError X fstar β +
                  σ ^ 2 * (k : ℝ) * Real.log (Real.exp 1 * (p : ℝ) / k) +
                  lam ^ 2 * (k : ℝ) / (SubsetShrink.L2.gam X (2 * k)) ^ 2 +
                  σ ^ 2 * Real.log (1 / δ0))) := by
  refine ⟨240, 160, by norm_num, by norm_num, ?_⟩
  intro n p X fstar ε k σ δ0 lam βhat _hX hk hkp hσ hδ0 hδ1 hbest β hβ
  have hp : 1 ≤ p := le_trans hk hkp
  have h37 := eq_37 X fstar ε k lam βhat β hbest hβ
  have hL : 0 ≤ Real.log (1 / δ0) := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hlog2p : 0 ≤ Real.log (2 * (p : ℝ)) := Real.log_nonneg (by linarith)
  set a := SubsetShrink.Events.l2 (fun i => fstar i - X.mulVec βhat i) with ha_def
  set b := SubsetShrink.Events.l2 (fun i => fstar i - X.mulVec β i) with hb_def
  have hPEa : predictionError X fstar βhat = a ^ 2 := pe_eq X fstar βhat
  have hPEb : predictionError X fstar β = b ^ 2 := pe_eq X fstar β
  have ha0 : 0 ≤ a := l2_nonneg _
  have hb0 : 0 ≤ b := l2_nonneg _
  have hD := D_le X fstar βhat β
  rw [← ha_def, ← hb_def] at hD
  have hl1b := l1_nonneg β
  have hl1h := l1_nonneg βhat
  refine ⟨?_, ?_, ?_⟩
  · -- slow rate on H
    intro hlam hH
    have hd := h_display X ε βhat β σ δ0 lam hσ hδ0 hδ1 hp hlam
    have h1 := hd.1
    have h2 := hd.2 hH
    linarith
  · -- slow rate on F
    intro hlam hF
    have hlam0 : 0 ≤ lam := le_trans (by positivity) hlam
    have hfa := f_case_a X fstar ε k σ δ0 lam βhat β hσ hδ0 hδ1 hp hF hbest hβ hlam
    have hfin : predictionError X fstar βhat ≤
        3 * predictionError X fstar β + 2 * lam * SubsetShrink.Events.l1 β +
          240 * σ ^ 2 * Real.log (1 / δ0) := by
      rcases hfa.1 with hA | hB
      · have := hfa.2 hA
        nlinarith [sq_nonneg b, mul_nonneg (sq_nonneg σ) hL]
      · set c := (4 + Real.sqrt 2) with hc
        set t := 2 * c * σ * Real.sqrt (Real.log (1 / δ0)) with ht
        have hc0 : 0 ≤ c := by positivity
        have ht0 : 0 ≤ t := by positivity
        have hmain : a ^ 2 ≤ b ^ 2 + t * SubsetShrink.Events.l2 (X.mulVec (β - βhat)) +
            lam * SubsetShrink.Events.l1 β := by
          rw [← hPEa, ← hPEb]
          have : 0 ≤ lam * SubsetShrink.Events.l1 βhat := mul_nonneg hlam0 hl1h
          nlinarith
        have hab := absorb a b _ t _ ha0 hb0 ht0 hmain hD
        have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
          rw [Real.sqrt_le_left (by norm_num)]; norm_num
        have hs20 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
        have hc2 : c ^ 2 ≤ 30 := by rw [hc]; nlinarith
        have ht2 : t ^ 2 = 4 * c ^ 2 * σ ^ 2 * Real.log (1 / δ0) := by
          rw [ht, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hL]; ring
        have : 2 * t ^ 2 ≤ 240 * σ ^ 2 * Real.log (1 / δ0) := by
          rw [ht2]
          have := mul_le_mul_of_nonneg_right hc2 (mul_nonneg (sq_nonneg σ) hL)
          nlinarith
        rw [hPEa, hPEb]
        linarith
    have : 0 ≤ lam * SubsetShrink.Events.l1 β := mul_nonneg hlam0 hl1b
    have : 0 ≤ predictionError X fstar β := by rw [hPEb]; positivity
    nlinarith [mul_nonneg (sq_nonneg σ) hL]
  · -- fast rate on G_{2k}
    intro hlam0 hgam hG
    clear_value a b
    set g := SubsetShrink.L2.gam X (2 * k) with hg
    have hk1 := hbest.1
    have hu0 : SubsetShrink.Events.l0 (βhat - β) ≤ 2 * k := by
      have := l0_sub_le βhat β; omega
    have hu0' : SubsetShrink.Events.l0 (β - βhat) ≤ 2 * k := by
      have := l0_sub_le β βhat; omega
    set D := SubsetShrink.Events.l2 (X.mulVec (β - βhat)) with hD_def
    have hD0 : 0 ≤ D := l2_nonneg _
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hkpR : (k : ℝ) ≤ p := by exact_mod_cast hkp
    -- noise term
    set A := 5 * ((2 * k : ℕ) : ℝ) * Real.log (Real.exp 1 * p / ((2 * k : ℕ) : ℝ)) +
      Real.log (1 / δ0) with hA
    have he2 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    have hlogk : Real.log (Real.exp 1 * p / ((2 * k : ℕ) : ℝ)) ≤
        Real.log (Real.exp 1 * p / k) := by
      push_cast
      apply Real.log_le_log
      · positivity
      · apply div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    have hlogk0 : 0 ≤ Real.log (Real.exp 1 * p / ((2 * k : ℕ) : ℝ)) := by
      apply Real.log_nonneg
      push_cast
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have hA0 : 0 ≤ A := by
      rw [hA]; positivity
    have hGu := hG (βhat - β) hu0
    rw [l2sym, ← hD_def, ← hA] at hGu
    -- regularization term
    have hfast := fast_l1_step k lam βhat β hlam0 hβ (hbest.1)
    set s := lam * Real.sqrt (2 * (k : ℝ)) / g with hs
    have hreg : lam * SubsetShrink.Events.l1 β - lam * SubsetShrink.Events.l1 βhat ≤ s * D := by
      rcases hgam with hgpos | hl0
      · have hgm := gam_mul_le X (2 * k) (β - βhat) hu0'
        rw [← hg] at hgm
        have hl2u : SubsetShrink.Events.l2 (β - βhat) ≤ D / g := by
          rw [le_div_iff₀ hgpos]; linarith
        have : lam * Real.sqrt (2 * (k : ℝ)) * SubsetShrink.Events.l2 (β - βhat) ≤ s * D := by
          rw [hs, div_mul_eq_mul_div, mul_div_assoc]
          exact mul_le_mul_of_nonneg_left hl2u (by positivity)
        linarith [hfast.1, hfast.2]
      · rw [hs, hl0]; simp
    have hs0 : 0 ≤ s := by
      rcases hgam with hgpos | hl0
      · rw [hs]; positivity
      · rw [hs, hl0]; simp
    set t := 2 * σ * Real.sqrt A + s with ht
    have ht0 : 0 ≤ t := by positivity
    clear_value t s A D g
    have hmain : a ^ 2 ≤ b ^ 2 + t * D + 0 := by
      rw [← hPEa, ← hPEb]
      have hdot : 2 * SubsetShrink.Events.dot ε (X.mulVec (βhat - β)) ≤
          2 * σ * Real.sqrt A * D := by linarith
      have htD : t * D = 2 * σ * Real.sqrt A * D + s * D := by rw [ht]; ring
      linarith
    have hab := absorb a b D t 0 ha0 hb0 ht0 hmain hD
    have hsA : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA0
    have hs2 : s ^ 2 = 2 * (lam ^ 2 * (k : ℝ) / g ^ 2) := by
      rw [hs, div_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring
    have ht2 : t ^ 2 ≤ 8 * σ ^ 2 * A + 2 * s ^ 2 := by
      have hx : (2 * σ * Real.sqrt A) ^ 2 = 4 * σ ^ 2 * A := by
        rw [mul_pow, mul_pow, hsA]; ring
      have hsq := sq_nonneg (2 * σ * Real.sqrt A - s)
      rw [ht]
      calc (2 * σ * Real.sqrt A + s) ^ 2
          = 2 * (2 * σ * Real.sqrt A) ^ 2 + 2 * s ^ 2 - (2 * σ * Real.sqrt A - s) ^ 2 := by ring
        _ ≤ 2 * (2 * σ * Real.sqrt A) ^ 2 + 2 * s ^ 2 := by linarith
        _ = 8 * σ ^ 2 * A + 2 * s ^ 2 := by rw [hx]; ring
    have hAle : A ≤ 10 * (k : ℝ) * Real.log (Real.exp 1 * p / k) + Real.log (1 / δ0) := by
      rw [hA]; push_cast
      have : 5 * (2 * (k : ℝ)) * Real.log (Real.exp 1 * p / (2 * k)) ≤
          5 * (2 * (k : ℝ)) * Real.log (Real.exp 1 * p / k) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have := hlogk; push_cast at this; exact this
      linarith
    have hK0 : 0 ≤ lam ^ 2 * (k : ℝ) / g ^ 2 := by positivity
    have hlk0 : 0 ≤ Real.log (Real.exp 1 * p / k) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_right he2 (by positivity : (0:ℝ) ≤ p)
      linarith
    have hσ2 : 0 ≤ σ ^ 2 := sq_nonneg σ
    have hfin : a ^ 2 ≤ 3 * b ^ 2 + 160 * (σ ^ 2 * (k : ℝ) * Real.log (Real.exp 1 * p / k)) +
        8 * (lam ^ 2 * (k : ℝ) / g ^ 2) + 16 * (σ ^ 2 * Real.log (1 / δ0)) := by
      have h1 := mul_le_mul_of_nonneg_left hAle hσ2
      linarith
    rw [hPEa, hPEb]
    have : 0 ≤ σ ^ 2 * (k : ℝ) * Real.log (Real.exp 1 * p / k) := by positivity
    have : 0 ≤ σ ^ 2 * Real.log (1 / δ0) := by positivity
    linarith [sq_nonneg b]
