-- Prove2me | solution 1 for WeldedPath.theorem_4_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dmilosch
-- created : 2026-11-17T16:18:06.583355+00:00
-- url     : https://prove2.me/submissions/5832b379-16bf-42f6-b697-54e5e450c042
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeldedPath_verifier_comparison
import Theorems.Thm_WeldedPath_crossing_probability_bound
import Theorems.Thm_WeldedPath_Supplement_theorem_3_12
import Definitions.Def_WeldedPath_successProb
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false


open QAlgorithms

namespace WeldedPath.ProbabilityBounds

theorem xorOracle_star {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    [AddCommGroup κ] (f : ι → κ) : star (xorOracle f) = xorOracle (-f) := by
  ext ⟨i, y⟩ ⟨j, z⟩
  simp only [Matrix.star_apply, xorOracle, Matrix.of_apply, Pi.neg_apply]
  by_cases h : i = j
  · subst j
    have he : (z = y + f i) ↔ (y = z + -f i) := by
      constructor <;> intro h <;> subst_vars <;> simp
    simp [he]
  · simp [h, Ne.symm h]

theorem xorOracle_unitary {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [AddCommGroup κ] (f : ι → κ) :
    xorOracle f ∈ Matrix.unitaryGroup (ι × κ) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, xorOracle_star]
  exact xorOracle_mul_neg f

theorem kronecker_one_unitary {ι W : Type*} [Fintype ι] [Fintype W]
    [DecidableEq ι] [DecidableEq W] {O : Matrix ι ι ℂ}
    (hO : O ∈ Matrix.unitaryGroup ι ℂ) :
    Matrix.kronecker O (1 : Matrix W W ℂ) ∈ Matrix.unitaryGroup (ι × W) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hO ⊢
  simp only [Matrix.kronecker, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  rw [← Matrix.mul_kronecker_mul]
  simpa only [← Matrix.star_eq_conjTranspose, hO, one_mul, Matrix.one_kronecker_one]

theorem finalState_unit {ι κ W : Type*} [Fintype ι] [Fintype κ] [Fintype W]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq W] {q : ℕ}
    (A : QueryAlg ι κ W q) (O : Matrix (ι × κ) (ι × κ) ℂ)
    (hO : O ∈ Matrix.unitaryGroup (ι × κ) ℂ) : ‖A.finalState O‖ = 1 := by
  suffices h : ∀ i, ‖A.stateAt O i‖ = 1 from h _
  intro i
  induction i using Fin.induction with
  | zero =>
      change ‖act (A.U 0 : Matrix _ _ ℂ) A.start‖ = 1
      rw [act_norm_of_mem_unitaryGroup (A.U 0).property]
      exact A.start_unit
  | succ i ih =>
      change ‖act (A.U i.succ : Matrix _ _ ℂ)
        (act (Matrix.kronecker O (1 : Matrix W W ℂ)) (A.stateAt O i.castSucc))‖ = 1
      rw [act_norm_of_mem_unitaryGroup (A.U i.succ).property,
        act_norm_of_mem_unitaryGroup (kronecker_one_unitary hO)]
      exact ih

theorem probEvent_le_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (P : ι → Prop) [DecidablePred P] :
    probEvent ψ P ≤ 1 := by
  have hsum : ∑ z, prob ψ z = 1 := by
    simpa [prob, QAlgorithms.ket, EuclideanSpace.inner_single_left, hψ]
      using (EuclideanSpace.norm_sq_eq ψ).symm
  calc
    probEvent ψ P ≤ ∑ z, prob ψ z := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro i _ _
      exact sq_nonneg _
    _ = 1 := hsum

theorem avgOver_le_one {α : Type*} (S : Finset α) (f : α → ℝ)
    (hf : ∀ x ∈ S, f x ≤ 1) : avgOver S f ≤ 1 := by
  unfold avgOver
  by_cases hS : S.card = 0
  · simp [hS]
  · apply (div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hS)).2
    simpa using Finset.sum_le_sum hf

theorem successProb_le_one {n : ℕ} (l : ℕ) (G : WeldedInstance n)
    {W : Type*} [Fintype W] [DecidableEq W] {q : ℕ}
    (A : QueryAlg (Qubits (2 * n + 1) × Fin 3) (Qubits (2 * n + 1)) W q)
    (out : ((Qubits (2 * n + 1) × Fin 3) × Qubits (2 * n + 1)) × W →
      List (Fin 3 × Qubits (2 * n + 1))) :
    G.successProb l A out ≤ 1 := by
  classical
  unfold WeldedInstance.successProb WeldedInstance.probOver
  apply avgOver_le_one
  intro σ _
  exact probEvent_le_one _ (finalState_unit A _ (xorOracle_unitary _)) _

end WeldedPath.ProbabilityBounds


namespace WeldedPath

lemma assemble_bound (n q a b d s C₀ Cv Ct Cc : ℝ)
    (hn : 1 ≤ n) (hq : 1 ≤ q) (ha : 0 < a) (hb : 0 < b) (hd : 0 < d)
    (hC₀ : 0 < C₀) (hCv : 0 < Cv) (hCt : 0 < Ct) (hCc : 0 < Cc)
    (hs : s ≤ 1)
    (hsmall : 80 * (q + 1) ≤ a → C₀ * (q + 1) ≤ a →
      C₀ * ((q + 1) / b + (n + 1) * (q + 1) ^ 3 / d) ≤ 1 / 2 →
      s ≤ Cv * (Ct * (Cc * (q ^ 2 / b + n * q ^ 3 / d) + q / a) +
        n * q ^ 2 / d)) :
    s ≤ (Cv * (Ct * (Cc + 1) + 1) + 32 * C₀ + 160) *
      (q / a + q ^ 2 / b + n * q ^ 3 / d) := by
  let E := q / a + q ^ 2 / b + n * q ^ 3 / d
  let K := Cv * (Ct * (Cc + 1) + 1) + 32 * C₀ + 160
  have hn0 : 0 ≤ n := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hx : 0 ≤ q / a := by positivity
  have hy : 0 ≤ q ^ 2 / b := by positivity
  have hz : 0 ≤ n * q ^ 3 / d := by positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hxE : q / a ≤ E := by dsimp [E]; linarith
  have hyzE : q ^ 2 / b + n * q ^ 3 / d ≤ E := by dsimp [E]; linarith
  have hzE : n * q ^ 3 / d ≤ E := by dsimp [E]; linarith
  have hbase : 0 ≤ Cv * (Ct * (Cc + 1) + 1) := by positivity
  have hK160 : 160 ≤ K := by dsimp [K]; linarith
  have hK32 : 32 * C₀ ≤ K := by dsimp [K]; linarith
  have hK2 : 2 * C₀ ≤ K := by
    have : 0 ≤ Cv * (Ct * (Cc + 1) + 1) := by positivity
    dsimp [K]; linarith
  have hKbase : Cv * (Ct * (Cc + 1) + 1) ≤ K := by dsimp [K]; linarith
  change s ≤ K * E
  have hqplus : q + 1 ≤ 2 * q := by linarith
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have hq3 : q ^ 2 ≤ q ^ 3 := by
    have := mul_le_mul_of_nonneg_left hq2 hq0
    nlinarith
  have herr : (q + 1) / b + (n + 1) * (q + 1) ^ 3 / d ≤ 16 * E := by
    have hfirst : (q + 1) / b ≤ 2 * (q ^ 2 / b) := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (by linarith) hb.le
    have hpow : (q + 1) ^ 3 ≤ 8 * q ^ 3 := by
      calc
        (q + 1) ^ 3 ≤ (2 * q) ^ 3 := by gcongr
        _ = 8 * q ^ 3 := by ring
    have hsecond : (n + 1) * (q + 1) ^ 3 / d ≤ 16 * (n * q ^ 3 / d) := by
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ hd.le
      calc
        (n + 1) * (q + 1) ^ 3 ≤ (2 * n) * (8 * q ^ 3) := by gcongr <;> linarith
        _ = 16 * (n * q ^ 3) := by ring
    dsimp [E]
    linarith
  by_cases h80 : 80 * (q + 1) ≤ a
  · by_cases h0 : C₀ * (q + 1) ≤ a
    · by_cases he : C₀ * ((q + 1) / b + (n + 1) * (q + 1) ^ 3 / d) ≤ 1 / 2
      · have hmain := hsmall h80 h0 he
        have hthird : n * q ^ 2 / d ≤ E := by
          exact (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hq3 hn0) hd.le).trans hzE
        calc
          s ≤ Cv * (Ct * (Cc * (q ^ 2 / b + n * q ^ 3 / d) + q / a) +
            n * q ^ 2 / d) := hmain
          _ ≤ Cv * (Ct * (Cc * E + E) + E) := by gcongr
          _ = (Cv * (Ct * (Cc + 1) + 1)) * E := by ring
          _ ≤ K * E := mul_le_mul_of_nonneg_right hKbase hE
      · have hlarge : 1 ≤ (32 * C₀) * E := by
          have := mul_le_mul_of_nonneg_left herr hC₀.le
          push Not at he
          nlinarith
        exact hs.trans (hlarge.trans (mul_le_mul_of_nonneg_right hK32 hE))
    · have hlarge : 1 ≤ (2 * C₀) * E := by
        have hqa : a ≤ (2 * C₀) * q := by
          have := mul_le_mul_of_nonneg_left hqplus hC₀.le
          push Not at h0
          nlinarith
        have hdiv : 1 ≤ (2 * C₀) * (q / a) := by
          rw [← mul_div_assoc]
          exact (le_div_iff₀ ha).2 (by simpa using hqa)
        exact hdiv.trans (mul_le_mul_of_nonneg_left hxE (by positivity))
      exact hs.trans (hlarge.trans (mul_le_mul_of_nonneg_right hK2 hE))
  · have hlarge : 1 ≤ 160 * E := by
      have hqa : a ≤ 160 * q := by push Not at h80; linarith
      have hdiv : 1 ≤ 160 * (q / a) := by
        rw [← mul_div_assoc]
        exact (le_div_iff₀ ha).2 (by simpa using hqa)
      exact hdiv.trans (mul_le_mul_of_nonneg_left hxE (by norm_num))
    exact hs.trans (hlarge.trans (mul_le_mul_of_nonneg_right hK160 hE))

end WeldedPath


set_option autoImplicit false

namespace WeldedPath

theorem numeric_choice_range (n : ℕ) (hn : 16 ≤ n) :
    2 ≤ 2 * n / 3 ∧ 2 * n / 3 ≤ n - 4 := by omega

theorem numeric_bound_implies_lower_bound
    (C p : ℝ) (hC : 0 < C) (hp : 0 < p) (hp1 : p ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ n q : ℕ, 16 ≤ n →
      p ≤ C * ((q : ℝ) / 2 ^ (n - 2 * n / 3) +
        (q : ℝ) ^ 2 / 2 ^ (2 * n / 3) +
        (n : ℝ) * (q : ℝ) ^ 3 / 2 ^ n) →
      c * ((2 : ℝ) ^ n / ((n : ℝ) + 1)) ^ ((1 : ℝ) / 3) ≤ (q : ℝ) := by
  let c := p / (8 * (C + 1))
  have hc : 0 < c := div_pos hp (by positivity)
  have hc1 : c ≤ 1 := by
    dsimp [c]
    apply (div_le_iff₀ (by positivity : 0 < 8 * (C + 1))).2
    linarith
  have hcp : 8 * (C + 1) * c = p := by
    dsimp [c]
    field_simp
  refine ⟨c, hc, ?_⟩
  intro n q hn hbound
  let r : ℝ := ((2 : ℝ) ^ n / ((n : ℝ) + 1)) ^ ((1 : ℝ) / 3)
  let A : ℝ := 2 ^ (n - 2 * n / 3)
  let B : ℝ := 2 ^ (2 * n / 3)
  have hN : 0 < (2 : ℝ) ^ n := by positivity
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hn1 : 0 < (n : ℝ) + 1 := by positivity
  have hr : 0 ≤ r := Real.rpow_nonneg (by positivity) _
  have hA : 0 < A := by positivity
  have hB : 0 < B := by positivity
  have hr3 : r ^ 3 = (2 : ℝ) ^ n / ((n : ℝ) + 1) := by
    simpa [r, one_div] using
      Real.rpow_inv_natCast_pow (by positivity : 0 ≤ (2 : ℝ) ^ n / ((n : ℝ) + 1))
        (by decide : (3 : ℕ) ≠ 0)
  have hr3N : r ^ 3 ≤ (2 : ℝ) ^ n := by
    rw [hr3]
    apply (div_le_iff₀ hn1).2
    nlinarith only [hn0, hN]
  have hNA : (2 : ℝ) ^ n ≤ A ^ 3 := by
    dsimp [A]
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hrA : r ≤ A :=
    le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) hA.le (hr3N.trans hNA)
  have hNB : ((2 : ℝ) ^ n) ^ 2 ≤ 4 * B ^ 3 := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (show n * 2 ≤ (2 * n / 3) * 3 + 2 by omega)
    calc
      ((2 : ℝ) ^ n) ^ 2 ≤ (2 : ℝ) ^ ((2 * n / 3) * 3 + 2) := by
        simpa only [pow_mul] using h
      _ = 4 * B ^ 3 := by
        dsimp [B]
        rw [pow_add, pow_mul]
        ring
  have hrB : r ^ 2 ≤ 2 * B := by
    apply le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) (by positivity)
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ r ^ 3) hr3N 2
    have hB3 : 0 ≤ B ^ 3 := by positivity
    nlinarith only [hsq, hNB, hB3]
  by_contra hnot
  have hq : (q : ℝ) < c * r := lt_of_not_ge hnot
  have hq0 : 0 ≤ (q : ℝ) := by positivity
  have hqA : (q : ℝ) / A ≤ c := by
    apply (div_le_iff₀ hA).2
    exact hq.le.trans (mul_le_mul_of_nonneg_left hrA hc.le)
  have hqB : (q : ℝ) ^ 2 / B ≤ 2 * c ^ 2 := by
    apply (div_le_iff₀ hB).2
    have hs := pow_le_pow_left₀ hq0 hq.le 2
    have hm := mul_le_mul_of_nonneg_left hrB (sq_nonneg c)
    nlinarith only [hs, hm]
  have hqN : (n : ℝ) * (q : ℝ) ^ 3 / 2 ^ n ≤ c ^ 3 := by
    apply (div_le_iff₀ hN).2
    have hq3 := pow_le_pow_left₀ hq0 hq.le 3
    have hm := mul_le_mul_of_nonneg_left hq3 hn0
    have hr3eq : r ^ 3 * ((n : ℝ) + 1) = (2 : ℝ) ^ n := by
      rw [hr3]
      exact div_mul_cancel₀ _ (ne_of_gt hn1)
    have hc3 : 0 ≤ c ^ 3 := by positivity
    have hnr : (n : ℝ) * r ^ 3 ≤ (2 : ℝ) ^ n := by
      nlinarith only [hr3eq, pow_nonneg hr 3]
    have hmul := mul_le_mul_of_nonneg_left hnr hc3
    nlinarith only [hm, hmul]
  have hc2 : c ^ 2 ≤ c := by nlinarith only [hc, hc1]
  have hc3 : c ^ 3 ≤ c := by
    have h := mul_le_mul_of_nonneg_left hc2 hc.le
    nlinarith only [h, hc2]
  have hsum : (q : ℝ) / 2 ^ (n - 2 * n / 3) +
      (q : ℝ) ^ 2 / 2 ^ (2 * n / 3) +
      (n : ℝ) * (q : ℝ) ^ 3 / 2 ^ n ≤ 4 * c := by
    change (q : ℝ) / A + (q : ℝ) ^ 2 / B + _ ≤ _
    linarith
  have hfinal := mul_le_mul_of_nonneg_left hsum hC.le
  nlinarith only [hbound, hfinal, hcp, hC, hc]

end WeldedPath

open WeldedPath QAlgorithms

theorem solution :
    (∃ C : ℝ, 0 < C ∧
      ∀ n l : ℕ, Even n → 16 ≤ n → 2 ≤ l → l ≤ n - 4 →
      ∀ G : WeldedInstance n, G.IsValid →
      ∀ (W : Type) [Fintype W] [DecidableEq W] (q : ℕ), 1 ≤ q →
      ∀ (A : QueryAlg (Qubits (2 * n + 1) × Fin 3) (Qubits (2 * n + 1)) W q)
        (out : ((Qubits (2 * n + 1) × Fin 3) × Qubits (2 * n + 1)) × W →
          List (Fin 3 × Qubits (2 * n + 1))),
      G.successProb l A out ≤
        C * ((q : ℝ) / 2 ^ (n - l) + (q : ℝ) ^ 2 / 2 ^ l + (n : ℝ) * (q : ℝ) ^ 3 / 2 ^ n)) ∧
    (∃ L : ℕ → ℕ, (∀ n : ℕ, Even n → 16 ≤ n → 2 ≤ L n ∧ L n ≤ n - 4) ∧
      ∀ p : ℝ, 0 < p → p ≤ 1 → ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, Even n → 16 ≤ n →
      ∀ G : WeldedInstance n, G.IsValid →
      ∀ (W : Type) [Fintype W] [DecidableEq W] (q : ℕ), 1 ≤ q →
      ∀ (A : QueryAlg (Qubits (2 * n + 1) × Fin 3) (Qubits (2 * n + 1)) W q)
        (out : ((Qubits (2 * n + 1) × Fin 3) × Qubits (2 * n + 1)) × W →
          List (Fin 3 × Qubits (2 * n + 1))),
      p ≤ G.successProb (L n) A out →
        c * ((2 : ℝ) ^ n / ((n : ℝ) + 1)) ^ ((1 : ℝ) / 3) ≤ (q : ℝ)) := by

  rcases verifier_comparison with ⟨Cv, hCv, hv⟩
  rcases Supplement.theorem_3_12 with ⟨Ct, hCt, ht⟩
  rcases crossing_probability_bound with ⟨C₀, hC₀, Cc, hCc, hc⟩
  let C : ℝ := Cv * (Ct * (Cc + 1) + 1) + 32 * C₀ + 160
  have hC : 0 < C := by dsimp [C]; positivity
  have hbound : ∀ n l : ℕ, Even n → 16 ≤ n → 2 ≤ l → l ≤ n - 4 →
      ∀ G : WeldedInstance n, G.IsValid →
      ∀ (W : Type) [Fintype W] [DecidableEq W] (q : ℕ), 1 ≤ q →
      ∀ (A : QueryAlg (Qubits (2 * n + 1) × Fin 3) (Qubits (2 * n + 1)) W q)
        (out : ((Qubits (2 * n + 1) × Fin 3) × Qubits (2 * n + 1)) × W →
          List (Fin 3 × Qubits (2 * n + 1))),
      G.successProb l A out ≤
        C * ((q : ℝ) / 2 ^ (n - l) + (q : ℝ) ^ 2 / 2 ^ l + (n : ℝ) * (q : ℝ) ^ 3 / 2 ^ n) := by
    intro n l hn hn16 hl hlmax G hG W _ _ q hq A out
    apply assemble_bound (n : ℝ) (q : ℝ) (2 ^ (n - l)) (2 ^ l) (2 ^ n)
      (G.successProb l A out) C₀ Cv Ct Cc
      (by exact_mod_cast (show 1 ≤ n by omega)) (by exact_mod_cast hq)
      (by positivity) (by positivity) (by positivity) hC₀ hCv hCt hCc
      (ProbabilityBounds.successProb_le_one l G A out)
    intro h80 h0 he
    obtain ⟨out', hv'⟩ := hv n l hn hn16 hl hlmax G hG W q hq A out
    have ht' := ht n l hn hl hlmax G hG W q hq A out' h80
    have hc' := hc n l hn hn16 hl hlmax G hG W q hq A h0 he
    calc
      G.successProb l A out ≤ Cv * (Supplement.pWt l G A out' +
          (n : ℝ) * (q : ℝ) ^ 2 / 2 ^ n) := hv'
      _ ≤ Cv * (Ct * (Supplement.pCross l G A + (q : ℝ) / 2 ^ (n - l)) +
          (n : ℝ) * (q : ℝ) ^ 2 / 2 ^ n) := by gcongr
      _ ≤ Cv * (Ct * (Cc * ((q : ℝ) ^ 2 / 2 ^ l +
          (n : ℝ) * (q : ℝ) ^ 3 / 2 ^ n) + (q : ℝ) / 2 ^ (n - l)) +
          (n : ℝ) * (q : ℝ) ^ 2 / 2 ^ n) := by gcongr
  refine ⟨⟨C, hC, hbound⟩, ?_⟩
  refine ⟨fun n => 2 * n / 3, ?_, ?_⟩
  · intro n _ hn16
    exact numeric_choice_range n hn16
  · intro p hp hp1
    obtain ⟨c, hcpos, hnum⟩ := numeric_bound_implies_lower_bound C p hC hp hp1
    refine ⟨c, hcpos, ?_⟩
    intro n hn hn16 G hG W _ _ q hq A out hpSuc
    obtain ⟨hl, hlmax⟩ := numeric_choice_range n hn16
    exact hnum n q hn16 (hpSuc.trans
      (hbound n (2 * n / 3) hn hn16 hl hlmax G hG W q hq A out))
