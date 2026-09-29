-- Prove2me | solution 1 for ThreeOpSplitting.Convergence.descent_inequality
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T16:52:19.001982+00:00
-- url     : https://prove2.me/submissions/a394be8b-40be-4c8f-bcd5-2fdcd820065b

import Definitions.Def_ThreeOpSplitting_Convergence_Nonexpansive
import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_ThreeOperatorIteration

open InnerProductSpace

namespace ThreeOpSplitting.Convergence

theorem lemma_2_3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U T₁ V : H → H) (hU : IsFirmlyNonexpansive U) (hT₁ : IsFirmlyNonexpansive T₁) :
    let S : H → H := fun x => U x + T₁ (V x)
    let W : H → H := fun x => x - ((2 : ℝ) • U x + V x)
    ∀ z w : H,
      ‖S z - S w‖ ^ 2 ≤ ‖z - w‖ ^ 2 - ‖(z - S z) - (w - S w)‖ ^ 2
        - 2 * ⟪T₁ (V z) - T₁ (V w), W z - W w⟫_ℝ := by
  intro S W z w
  set a := U z - U w with ha
  set b := T₁ (V z) - T₁ (V w) with hb
  set d := z - w with hd
  set v := V z - V w with hv
  have e1 : S z - S w = a + b := by simp only [S, ha, hb]; abel
  have e2 : (z - S z) - (w - S w) = d - (a + b) := by simp only [S, ha, hb, hd]; abel
  have e3 : W z - W w = d - (2 : ℝ) • a - v := by simp only [W, ha, hd, hv]; module
  have hUa : ‖a‖ ^ 2 ≤ ⟪a, d⟫_ℝ := hU z w
  have hTb : ‖b‖ ^ 2 ≤ ⟪b, v⟫_ℝ := hT₁ (V z) (V w)
  rw [e1, e2, e3]
  clear_value a b d v
  rw [norm_sub_sq_real d (a + b), norm_add_sq_real a b, inner_add_right d a b,
    inner_sub_right b (d - (2:ℝ) • a) v, inner_sub_right b d ((2:ℝ) • a),
    real_inner_smul_right b a 2]
  have s1 : ⟪d, a⟫_ℝ = ⟪a, d⟫_ℝ := real_inner_comm _ _
  have s2 : ⟪d, b⟫_ℝ = ⟪b, d⟫_ℝ := real_inner_comm _ _
  have s3 : ⟪b, a⟫_ℝ = ⟪a, b⟫_ℝ := real_inner_comm _ _
  nlinarith

/-- `I - T` is firmly nonexpansive when `T` is. -/
lemma firm_compl {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (T : H → H)
    (hT : IsFirmlyNonexpansive T) : IsFirmlyNonexpansive (fun x => x - T x) := by
  intro x y
  have h := hT x y
  have e : (x - T x) - (y - T y) = (x - y) - (T x - T y) := by abel
  simp only
  rw [e, norm_sub_sq_real (x - y) (T x - T y), inner_sub_left (x - y) (T x - T y) (x - y),
    real_inner_self_eq_norm_sq]
  have := real_inner_comm (x - y) (T x - T y)
  linarith

/-- The key inequality for `T = threeOp γ T₁ T₂ C` with a Young parameter `ε > 0`. -/
lemma key_ineq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T₁ T₂ C : H → H) (β γ ε : ℝ)
    (hT₁ : IsFirmlyNonexpansive T₁) (hT₂ : IsFirmlyNonexpansive T₂)
    (hC : IsCocoercive β C) (hγ0 : 0 < γ) (hε : 0 < ε) (z w : H) :
    ‖threeOp γ T₁ T₂ C z - threeOp γ T₁ T₂ C w‖ ^ 2 ≤ ‖z - w‖ ^ 2
      - (1 - ε) * ‖(z - threeOp γ T₁ T₂ C z) - (w - threeOp γ T₁ T₂ C w)‖ ^ 2
      - γ * (2 * β - γ / ε) * ‖C (T₂ z) - C (T₂ w)‖ ^ 2 := by
  set T := threeOp γ T₁ T₂ C with hTdef
  set U : H → H := fun x => x - T₂ x with hUdef
  set V : H → H := fun x => (2 : ℝ) • T₂ x - x - γ • C (T₂ x) with hVdef
  have hS : ∀ x, U x + T₁ (V x) = T x := by
    intro x; simp only [hUdef, hVdef, hTdef, threeOp]; abel
  have hW : ∀ x, x - ((2 : ℝ) • U x + V x) = γ • C (T₂ x) := by
    intro x; simp only [hUdef, hVdef]; module
  have hT1V : ∀ x, T₁ (V x) = T x - x + T₂ x := by
    intro x; rw [← hS x]; simp only [hUdef]; abel
  have h23 := lemma_2_3 U T₁ V (firm_compl T₂ hT₂) hT₁ z w
  simp only [hS, hW] at h23
  rw [hT1V, hT1V] at h23
  set c := C (T₂ z) - C (T₂ w) with hc
  set p := T₂ z - T₂ w with hp
  set e := (T z - z) - (T w - w) with he
  have hsplit : (T z - z + T₂ z) - (T w - w + T₂ w) = e + p := by rw [he, hp]; abel
  have hWd : γ • C (T₂ z) - γ • C (T₂ w) = γ • c := by rw [hc, smul_sub]
  rw [hsplit, hWd, real_inner_smul_right, inner_add_left] at h23
  -- cocoercivity
  have hcoc : β * ‖c‖ ^ 2 ≤ ⟪c, p⟫_ℝ := hC (T₂ z) (T₂ w)
  have hcp : ⟪p, c⟫_ℝ = ⟪c, p⟫_ℝ := real_inner_comm _ _
  -- Young
  have hY0 : 0 ≤ ‖ε • e + γ • c‖ ^ 2 := sq_nonneg _
  rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hε, abs_of_pos hγ0] at hY0
  have hY : -2 * γ * ⟪e, c⟫_ℝ ≤ ε * ‖e‖ ^ 2 + γ ^ 2 / ε * ‖c‖ ^ 2 := by
    have h1 : 0 ≤ (ε * ‖e‖) ^ 2 + 2 * (ε * (γ * ⟪e, c⟫_ℝ)) + (γ * ‖c‖) ^ 2 := hY0
    have h2 : (ε * ‖e‖) ^ 2 + 2 * (ε * (γ * ⟪e, c⟫_ℝ)) + (γ * ‖c‖) ^ 2 =
        ε * (ε * ‖e‖ ^ 2 + 2 * γ * ⟪e, c⟫_ℝ + γ ^ 2 / ε * ‖c‖ ^ 2) := by
      field_simp
    rw [h2] at h1
    have h3 := (mul_nonneg_iff_of_pos_left hε).1 h1
    linarith
  have hnorm : ‖(z - T z) - (w - T w)‖ = ‖e‖ := by
    rw [he, ← norm_neg]; congr 1; abel
  rw [hnorm]
  rw [hnorm] at h23
  have hγc : γ * (2 * β - γ / ε) * ‖c‖ ^ 2 = 2 * γ * (β * ‖c‖ ^ 2) - γ ^ 2 / ε * ‖c‖ ^ 2 := by
    field_simp
  have hγcoc := mul_le_mul_of_nonneg_left hcoc (by linarith : (0:ℝ) ≤ 2 * γ)
  nlinarith

lemma resolvent_firm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (γ : ℝ) (A : H → Set H) (J : H → H) (hγ : 0 < γ) (hAm : IsMonotoneOp A)
    (hJ : IsResolvent γ A J) : IsFirmlyNonexpansive J := by
  intro x y
  have h := hAm (J x) (J y) _ _ (hJ x) (hJ y)
  rw [← smul_sub, real_inner_smul_right] at h
  have h2 : 0 ≤ ⟪J x - J y, x - J x - (y - J y)⟫_ℝ :=
    (mul_nonneg_iff_of_pos_left (inv_pos.2 hγ)).1 h
  have e : x - J x - (y - J y) = (x - y) - (J x - J y) := by abel
  rw [e, inner_sub_right, real_inner_self_eq_norm_sq] at h2
  linarith

lemma affine_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (p q : H) (l : ℝ) :
    ‖(1 - l) • p + l • q‖ ^ 2 = (1 - l) * ‖p‖ ^ 2 + l * ‖q‖ ^ 2 - l * (1 - l) * ‖q - p‖ ^ 2 := by
  rw [norm_add_sq_real, norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left,
    real_inner_smul_right, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs,
    real_inner_comm p q]
  ring

theorem descent_inequality {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (A B : H → Set H) (C : H → H) (β γ ε : ℝ) (JA JB : H → H) (lam : ℕ → ℝ) (z0 : H)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (hβ : 0 < β) (hC : IsCocoercive β C)
    (hJA : IsResolvent γ A JA) (hJB : IsResolvent γ B JB)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hγ0 : 0 < γ) (hγ : γ < 2 * β * ε)
    (hlam : ∀ j, 0 < lam j ∧ lam j < 1 / alpha ε)
    (zs : H) (hzs : zs ∈ Function.fixedPoints (threeOp γ JA JB C)) :
    let T := threeOp γ JA JB C
    let z := zSeq γ JA JB C lam z0
    let xB := xBSeq γ JA JB C lam z0
    (∀ k : ℕ,
        ‖z (k + 1) - zs‖ ^ 2 + tau ε (lam k) * ‖T (z k) - z k‖ ^ 2
          + γ * lam k * (2 * β - γ / ε) * ‖C (xB k) - C (JB zs)‖ ^ 2 ≤ ‖z k - zs‖ ^ 2) ∧
      ∀ c : ℝ, 0 < c → (∀ j, c ≤ lam j) → ∀ k : ℕ,
        Summable (fun i : ℕ => ‖C (xB (k + i)) - C (JB zs)‖ ^ 2) ∧
          ∑' i : ℕ, ‖C (xB (k + i)) - C (JB zs)‖ ^ 2
            ≤ ‖z k - zs‖ ^ 2 / (γ * c * (2 * β - γ / ε)) := by
  intro T z xB
  have hfA := resolvent_firm γ A JA hγ0 hA.1 hJA
  have hfB := resolvent_firm γ B JB hγ0 hB.1 hJB
  have hTzs : T zs = zs := hzs
  have hα : alpha ε = 1 / (2 - ε) := rfl
  have h2e : 0 < 2 - ε := by linarith
  have hcoefα : (1 - alpha ε) / alpha ε = 1 - ε := by
    rw [hα]; field_simp; ring
  have hκ : 0 < 2 * β - γ / ε := by
    rw [sub_pos, div_lt_iff₀ hε0]; linarith
  have hstep : ∀ k, z (k + 1) = (1 - lam k) • (z k - zs) + lam k • (T (z k) - zs) + zs := by
    intro k
    show zSeq γ JA JB C lam z0 (k + 1) = _
    simp only [zSeq, T, threeOp, z]
    module
  have h26 : ∀ k : ℕ,
      ‖z (k + 1) - zs‖ ^ 2 + tau ε (lam k) * ‖T (z k) - z k‖ ^ 2
        + γ * lam k * (2 * β - γ / ε) * ‖C (xB k) - C (JB zs)‖ ^ 2 ≤ ‖z k - zs‖ ^ 2 := by
    intro k
    have hkey : ‖T (z k) - T zs‖ ^ 2 ≤ ‖z k - zs‖ ^ 2
        - (1 - ε) * ‖(z k - T (z k)) - (zs - T zs)‖ ^ 2
        - γ * (2 * β - γ / ε) * ‖C (JB (z k)) - C (JB zs)‖ ^ 2 :=
      key_ineq JA JB C β γ ε hfA hfB hC hγ0 hε0 (z k) zs
    rw [hTzs, sub_self, sub_zero] at hkey
    have hn : ‖z k - T (z k)‖ = ‖T (z k) - z k‖ := norm_sub_rev _ _
    have hxB : xB k = JB (z k) := rfl
    rw [hn] at hkey
    rw [hxB]
    have hz : z (k + 1) - zs = (1 - lam k) • (z k - zs) + lam k • (T (z k) - zs) := by
      rw [hstep k]; abel
    have hq : T (z k) - zs - (z k - zs) = T (z k) - z k := by abel
    rw [hz, affine_sq, hq]
    have hl := (hlam k).1
    have hm := mul_le_mul_of_nonneg_left hkey hl.le
    have htau : tau ε (lam k) = lam k * (1 - lam k) + lam k * (1 - ε) := by
      unfold tau; rw [mul_div_assoc, hcoefα]
    rw [htau]
    nlinarith
  refine ⟨h26, fun c hc hcl k => ?_⟩
  set κ := γ * c * (2 * β - γ / ε) with hκdef
  have hκpos : 0 < κ := by positivity
  set f : ℕ → ℝ := fun i => ‖C (xB (k + i)) - C (JB zs)‖ ^ 2 with hf
  have hf0 : ∀ i, 0 ≤ f i := fun i => sq_nonneg _
  have hdesc : ∀ j, κ * ‖C (xB j) - C (JB zs)‖ ^ 2 ≤ ‖z j - zs‖ ^ 2 - ‖z (j + 1) - zs‖ ^ 2 := by
    intro j
    have h := h26 j
    have htau0 : 0 ≤ tau ε (lam j) := by
      unfold tau; rw [mul_div_assoc, hcoefα]
      have h1 := (hlam j).2
      rw [hα, one_div_one_div] at h1
      have := (hlam j).1
      nlinarith
    have hmono : κ * ‖C (xB j) - C (JB zs)‖ ^ 2 ≤
        γ * lam j * (2 * β - γ / ε) * ‖C (xB j) - C (JB zs)‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      rw [hκdef]
      have := hcl j
      have : 0 ≤ γ * (2 * β - γ / ε) := by positivity
      nlinarith
    nlinarith [mul_nonneg htau0 (sq_nonneg ‖T (z j) - z j‖)]
  have hpartial : ∀ n, ∑ i ∈ Finset.range n, f i ≤ ‖z k - zs‖ ^ 2 / κ := by
    intro n
    have htel : ∀ n, κ * ∑ i ∈ Finset.range n, f i ≤ ‖z k - zs‖ ^ 2 - ‖z (k + n) - zs‖ ^ 2 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, mul_add]
        have := hdesc (k + n)
        simp only [hf]
        rw [show k + (n + 1) = k + n + 1 by ring]
        linarith
    rw [le_div_iff₀ hκpos]
    have := htel n
    nlinarith [sq_nonneg ‖z (k + n) - zs‖]
  exact ⟨summable_of_sum_range_le hf0 hpartial, Real.tsum_le_of_sum_range_le hf0 hpartial⟩

end ThreeOpSplitting.Convergence

open ThreeOpSplitting.Convergence

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (A B : H → Set H) (C : H → H) (β γ ε : ℝ) (JA JB : H → H) (lam : ℕ → ℝ) (z0 : H)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (hβ : 0 < β) (hC : IsCocoercive β C)
    (hJA : IsResolvent γ A JA) (hJB : IsResolvent γ B JB)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hγ0 : 0 < γ) (hγ : γ < 2 * β * ε)
    (hlam : ∀ j, 0 < lam j ∧ lam j < 1 / alpha ε)
    (zs : H) (hzs : zs ∈ Function.fixedPoints (threeOp γ JA JB C)) :
    let T := threeOp γ JA JB C
    let z := zSeq γ JA JB C lam z0
    let xB := xBSeq γ JA JB C lam z0
    (∀ k : ℕ,
        ‖z (k + 1) - zs‖ ^ 2 + tau ε (lam k) * ‖T (z k) - z k‖ ^ 2
          + γ * lam k * (2 * β - γ / ε) * ‖C (xB k) - C (JB zs)‖ ^ 2 ≤ ‖z k - zs‖ ^ 2) ∧
      ∀ c : ℝ, 0 < c → (∀ j, c ≤ lam j) → ∀ k : ℕ,
        Summable (fun i : ℕ => ‖C (xB (k + i)) - C (JB zs)‖ ^ 2) ∧
          ∑' i : ℕ, ‖C (xB (k + i)) - C (JB zs)‖ ^ 2
            ≤ ‖z k - zs‖ ^ 2 / (γ * c * (2 * β - γ / ε)) := by
  exact descent_inequality A B C β γ ε JA JB lam z0 hA hB hβ hC hJA hJB hε0 hε1 hγ0 hγ hlam zs hzs
