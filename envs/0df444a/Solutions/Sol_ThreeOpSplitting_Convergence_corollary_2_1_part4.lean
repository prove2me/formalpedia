-- Prove2me | solution 1 for ThreeOpSplitting.Convergence.corollary_2_1_part4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T16:57:10.680796+00:00
-- url     : https://prove2.me/submissions/0c891c4b-41c4-480f-81af-af9abeb6a5de

import Definitions.Def_ThreeOpSplitting_Convergence_Nonexpansive
import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_ThreeOperatorIteration

open Filter Topology
open InnerProductSpace Filter Topology

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

/-- Averagedness from the strengthened inequality. -/
lemma nonexp_of_ineq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H → H) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (h : ∀ z w : H, ‖T z - T w‖ ^ 2 ≤ ‖z - w‖ ^ 2 - (1 - α) / α * ‖(z - T z) - (w - T w)‖ ^ 2)
    (z w : H) :
    ‖α⁻¹ • (T z - (1 - α) • z) - α⁻¹ • (T w - (1 - α) • w)‖ ≤ ‖z - w‖ := by
  have hzw := h z w
  set t := T z - T w with ht
  set d := z - w with hd
  have e1 : α⁻¹ • (T z - (1 - α) • z) - α⁻¹ • (T w - (1 - α) • w) =
      α⁻¹ • (t - (1 - α) • d) := by simp only [t, d]; module
  have e2 : (z - T z) - (w - T w) = d - t := by simp only [t, d]; abel
  rw [e2] at hzw
  rw [e1]
  clear_value t d
  rw [norm_sub_sq_real d t] at hzw
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hα0]
  have key : ‖t - (1 - α) • d‖ ^ 2 ≤ (α * ‖d‖) ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, real_inner_smul_right, Real.norm_eq_abs,
      abs_of_pos (by linarith : (0:ℝ) < 1 - α)]
    have hm : α * ‖t‖ ^ 2 ≤ α * ‖d‖ ^ 2 - (1 - α) * (‖d‖ ^ 2 - 2 * ⟪d, t⟫_ℝ + ‖t‖ ^ 2) := by
      have := mul_le_mul_of_nonneg_left hzw hα0.le
      have e3 : α * ((1 - α) / α * (‖d‖ ^ 2 - 2 * ⟪d, t⟫_ℝ + ‖t‖ ^ 2)) =
          (1 - α) * (‖d‖ ^ 2 - 2 * ⟪d, t⟫_ℝ + ‖t‖ ^ 2) := by field_simp
      nlinarith
    have hdt : ⟪t, d⟫_ℝ = ⟪d, t⟫_ℝ := real_inner_comm _ _
    nlinarith
  have hk : ‖t - (1 - α) • d‖ ≤ α * ‖d‖ :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 key
  rw [inv_mul_le_iff₀ hα0]; exact hk

/-- `n f(n) → 0` for antitone nonnegative summable sequences. -/
lemma little_o_of_antitone {f : ℕ → ℝ} (hf0 : ∀ n, 0 ≤ f n) (hfa : Antitone f)
    (hs : Summable f) : Tendsto (fun k : ℕ => ((k : ℝ) + 1) * f k) atTop (𝓝 0) := by
  set S := fun n => ∑ i ∈ Finset.range n, f i with hS
  have hSlim : Tendsto S atTop (𝓝 (∑' i, f i)) := hs.hasSum.tendsto_sum_nat
  have hdiv : Tendsto (fun k : ℕ => k / 2) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b; exact ⟨2 * b, fun a ha => by omega⟩
  have h1 : Tendsto (fun k : ℕ => S (k + 1)) atTop (𝓝 (∑' i, f i)) :=
    hSlim.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun k : ℕ => S (k / 2)) atTop (𝓝 (∑' i, f i)) := hSlim.comp hdiv
  have h3 : Tendsto (fun k : ℕ => 2 * (S (k + 1) - S (k / 2))) atTop (𝓝 (2 * (∑' i, f i - ∑' i, f i))) :=
    (h1.sub h2).const_mul 2
  rw [sub_self, mul_zero] at h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 (fun k => ?_) (fun k => ?_)
  · exact mul_nonneg (by positivity) (hf0 k)
  · have hle : k / 2 ≤ k + 1 := by omega
    have hsum : S (k + 1) - S (k / 2) = ∑ i ∈ Finset.Ico (k / 2) (k + 1), f i := by
      simp only [hS]; rw [Finset.sum_Ico_eq_sub _ hle]
    rw [hsum]
    have hcard := Finset.card_nsmul_le_sum (Finset.Ico (k / 2) (k + 1)) f (f k)
      (fun i hi => hfa (Finset.mem_Ico.1 hi).2.le |> fun h => by
        have := Finset.mem_Ico.1 hi; exact hfa (Nat.lt_succ_iff.1 this.2))
    rw [Nat.card_Ico, nsmul_eq_mul] at hcard
    have hc : ((k : ℝ) + 1) ≤ 2 * (((k + 1 - k / 2 : ℕ) : ℝ)) := by
      have : 2 * (k / 2) ≤ k := Nat.mul_div_le k 2
      have h' : (k + 1 - k / 2 : ℕ) = k + 1 - k / 2 := rfl
      rw [Nat.cast_sub hle]
      push_cast
      have : (2 : ℝ) * ((k / 2 : ℕ) : ℝ) ≤ k := by exact_mod_cast this
      linarith
    nlinarith [hf0 k]

theorem corollary_2_1_part4 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (A B : H → Set H) (C : H → H) (β γ ε : ℝ) (JA JB : H → H) (lam : ℕ → ℝ) (z0 : H)
    (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (hβ : 0 < β) (hC : IsCocoercive β C)
    (hJA : IsResolvent γ A JA) (hJB : IsResolvent γ B JB)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hγ0 : 0 < γ) (hγ : γ < 2 * β * ε)
    (hlam : ∀ j, 0 < lam j ∧ lam j < 1 / alpha ε)
    (hτ : Tendsto (fun n => ∑ i ∈ Finset.range n, tau ε (lam i)) atTop atTop)
    (hFix : (Function.fixedPoints (threeOp γ JA JB C)).Nonempty)
    (hτinf : 0 < ⨅ j, tau ε (lam j)) :
    let T := threeOp γ JA JB C
    let z := zSeq γ JA JB C lam z0
    (∀ zs ∈ Function.fixedPoints T, ∀ k : ℕ,
        ‖T (z k) - z k‖ ^ 2 ≤ ‖z0 - zs‖ ^ 2 / ((⨅ j, tau ε (lam j)) * ((k : ℝ) + 1))) ∧
      Tendsto (fun k : ℕ => ((k : ℝ) + 1) * ‖T (z k) - z k‖ ^ 2) atTop (𝓝 0) := by
  intro T z
  have hfA := resolvent_firm γ A JA hγ0 hA.1 hJA
  have hfB := resolvent_firm γ B JB hγ0 hB.1 hJB
  have h2e : 0 < 2 - ε := by linarith
  have hcoefα : (1 - alpha ε) / alpha ε = 1 - ε := by
    unfold alpha
    have : (2 - ε) ≠ 0 := by linarith
    field_simp; ring
  set α := alpha ε with hαdef
  have hα : α = 1 / (2 - ε) := rfl
  have hα0 : 0 < α := by rw [hα]; positivity
  have hα1 : α < 1 := by rw [hα, div_lt_one h2e]; linarith
  have hκ : 0 < 2 * β - γ / ε := by rw [sub_pos, div_lt_iff₀ hε0]; linarith
  -- averagedness inequality
  have hTin : ∀ u w : H, ‖T u - T w‖ ^ 2 ≤ ‖u - w‖ ^ 2 - (1 - α) / α * ‖(u - T u) - (w - T w)‖ ^ 2 := by
    intro u w
    have h := key_ineq JA JB C β γ ε hfA hfB hC hγ0 hε0 u w
    rw [hcoefα]
    have : 0 ≤ γ * (2 * β - γ / ε) * ‖C (JB u) - C (JB w)‖ ^ 2 := by positivity
    linarith
  set R : H → H := fun x => α⁻¹ • (T x - (1 - α) • x) with hR
  have hRne : ∀ u w, ‖R u - R w‖ ≤ ‖u - w‖ := fun u w => nonexp_of_ineq T α hα0 hα1 hTin u w
  have hRres : ∀ x, T x - x = α • (R x - x) := by
    intro x
    rw [smul_sub (α) (R x) x]
    simp only [hR]
    rw [smul_smul, mul_inv_cancel₀ hα0.ne', one_smul]
    module
  have hstep : ∀ k, z (k + 1) = z k + lam k • (T (z k) - z k) := by
    intro k
    show zSeq γ JA JB C lam z0 (k + 1) = _
    simp only [zSeq, T, threeOp, z]
    module
  -- residual antitone
  have hresmono : ∀ k, ‖T (z (k + 1)) - z (k + 1)‖ ≤ ‖T (z k) - z k‖ := by
    intro k
    set μ := lam k * α with hμ
    have hμ0 : 0 < μ := mul_pos (hlam k).1 hα0
    have hμ1 : μ ≤ 1 := by
      have := (hlam k).2
      rw [lt_div_iff₀ hα0] at this
      linarith
    have hz1 : z (k + 1) = z k + μ • (R (z k) - z k) := by
      rw [hstep k, hRres, smul_smul]
    have hdec : R (z (k + 1)) - z (k + 1) =
        (R (z (k + 1)) - R (z k)) + (1 - μ) • (R (z k) - z k) := by
      rw [hz1]; module
    have hb : ‖R (z (k + 1)) - z (k + 1)‖ ≤ ‖R (z k) - z k‖ := by
      rw [hdec]
      calc ‖(R (z (k + 1)) - R (z k)) + (1 - μ) • (R (z k) - z k)‖
          ≤ ‖R (z (k + 1)) - R (z k)‖ + ‖(1 - μ) • (R (z k) - z k)‖ := norm_add_le _ _
        _ ≤ ‖z (k + 1) - z k‖ + (1 - μ) * ‖R (z k) - z k‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
            linarith [hRne (z (k + 1)) (z k)]
        _ = ‖R (z k) - z k‖ := by
            rw [hz1, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hμ0]; ring
    rw [hRres, hRres, norm_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)
  have hresA : Antitone (fun k => ‖T (z k) - z k‖ ^ 2) := by
    apply antitone_nat_of_succ_le
    intro k
    exact pow_le_pow_left₀ (norm_nonneg _) (hresmono k) 2
  obtain ⟨zs0, hzs0⟩ := hFix
  have hdesc := fun zs (hzs : zs ∈ Function.fixedPoints T) =>
    (descent_inequality A B C β γ ε JA JB lam z0 hA hB hβ hC hJA hJB hε0 hε1 hγ0 hγ hlam zs hzs).1
  set τm := ⨅ j, tau ε (lam j) with hτm
  have htau0 : ∀ j, 0 ≤ tau ε (lam j) := by
    intro j
    unfold tau; rw [mul_div_assoc, hcoefα]
    have h1 := (hlam j).2
    rw [hα, one_div_one_div] at h1
    have := (hlam j).1
    nlinarith
  have hbdd : BddBelow (Set.range fun j => tau ε (lam j)) := ⟨0, by rintro _ ⟨j, rfl⟩; exact htau0 j⟩
  have hτle : ∀ j, τm ≤ tau ε (lam j) := fun j => ciInf_le hbdd j
  -- partial sums bound
  have hsums : ∀ zs ∈ Function.fixedPoints T, ∀ n : ℕ,
      τm * ∑ i ∈ Finset.range n, ‖T (z i) - z i‖ ^ 2 ≤ ‖z0 - zs‖ ^ 2 := by
    intro zs hzs n
    have htel : ∀ n, τm * ∑ i ∈ Finset.range n, ‖T (z i) - z i‖ ^ 2 ≤
        ‖z 0 - zs‖ ^ 2 - ‖z n - zs‖ ^ 2 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, mul_add]
        have h := hdesc zs hzs n
        have hc : 0 ≤ γ * lam n * (2 * β - γ / ε) *
            ‖C (xBSeq γ JA JB C lam z0 n) - C (JB zs)‖ ^ 2 := by
          have := (hlam n).1; positivity
        have hm := mul_le_mul_of_nonneg_right (hτle n) (sq_nonneg ‖T (z n) - z n‖)
        linarith
    have := htel n
    have hz0 : z 0 = z0 := rfl
    rw [hz0] at this
    nlinarith [sq_nonneg ‖z n - zs‖]
  refine ⟨fun zs hzs k => ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)]
    have h := hsums zs hzs (k + 1)
    have hmono : ((k : ℝ) + 1) * ‖T (z k) - z k‖ ^ 2 ≤
        ∑ i ∈ Finset.range (k + 1), ‖T (z i) - z i‖ ^ 2 := by
      have := Finset.card_nsmul_le_sum (Finset.range (k + 1))
        (fun i => ‖T (z i) - z i‖ ^ 2) (‖T (z k) - z k‖ ^ 2)
        (fun i hi => hresA (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)))
      rw [Finset.card_range, nsmul_eq_mul] at this
      push_cast at this
      linarith
    have := mul_le_mul_of_nonneg_left hmono hτinf.le
    nlinarith
  · apply little_o_of_antitone (fun n => sq_nonneg _) hresA
    apply summable_of_sum_range_le (c := ‖z0 - zs0‖ ^ 2 / τm) (fun n => sq_nonneg _)
    intro n
    rw [le_div_iff₀ hτinf]
    have := hsums zs0 hzs0 n
    linarith

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
    (hτ : Tendsto (fun n => ∑ i ∈ Finset.range n, tau ε (lam i)) atTop atTop)
    (hFix : (Function.fixedPoints (threeOp γ JA JB C)).Nonempty)
    (hτinf : 0 < ⨅ j, tau ε (lam j)) :
    let T := threeOp γ JA JB C
    let z := zSeq γ JA JB C lam z0
    (∀ zs ∈ Function.fixedPoints T, ∀ k : ℕ,
        ‖T (z k) - z k‖ ^ 2 ≤ ‖z0 - zs‖ ^ 2 / ((⨅ j, tau ε (lam j)) * ((k : ℝ) + 1))) ∧
      Tendsto (fun k : ℕ => ((k : ℝ) + 1) * ‖T (z k) - z k‖ ^ 2) atTop (𝓝 0) := by
  exact corollary_2_1_part4 A B C β γ ε JA JB lam z0 hA hB hβ hC hJA hJB hε0 hε1 hγ0 hγ hlam hτ hFix hτinf
