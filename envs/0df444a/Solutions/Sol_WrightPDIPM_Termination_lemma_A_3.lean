-- Prove2me | solution 1 for WrightPDIPM.Termination.lemma_A_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T15:17:04.490587+00:00
-- url     : https://prove2.me/submissions/ed3ae6d0-c5ff-4957-a4e8-ef53990b9917

import Mathlib
import Definitions.Def_WrightPDIPM_Termination_Setup

open WrightPDIPM.Termination

open Matrix
open WrightPDIPM.Termination

theorem g70wr_n2le {q : ℕ} (w : Fin q → ℝ) : norm2 w ≤ Real.sqrt q * ‖w‖ := by
  unfold norm2
  have h1 : ∑ i, w i ^ 2 ≤ ∑ _i : Fin q, ‖w‖ ^ 2 := Finset.sum_le_sum fun i _ => by
    have := norm_le_pi_norm w i
    rw [Real.norm_eq_abs] at this
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  calc Real.sqrt (∑ i, w i ^ 2) ≤ Real.sqrt (q * ‖w‖ ^ 2) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt q * ‖w‖ := by
      rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem g70wr_pairle {r p : ℕ} (g : Fin r → ℝ) (h : Fin p → ℝ) : ‖(g, h)‖ ≤ norm2Pair g h := by
  have hn : 0 ≤ norm2Pair g h := Real.sqrt_nonneg _
  have hg0 : 0 ≤ ∑ i, g i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hh0 : 0 ≤ ∑ i, h i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [Prod.norm_def, max_le_iff]
  constructor
  · rw [pi_norm_le_iff_of_nonneg hn]
    intro i
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    have := Finset.single_le_sum (f := fun i => g i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i)
    linarith
  · rw [pi_norm_le_iff_of_nonneg hn]
    intro i
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    have := Finset.single_le_sum (f := fun i => h i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i)
    linarith


open Matrix

/-- Lemma A.3 (Hoffman's lemma, p. 248): for matrices `G ∈ ℝ^{r×q}`, `H ∈ ℝ^{p×q}` there is a
constant `L ≥ 0`, depending only on `G` and `H`, such that for every `(g, h)` in the range of
`[G; H]` the system (A.18) `Gw ≤ g`, `Hw = h` has a solution with `‖w‖ ≤ L‖(g, h)‖`. -/
theorem solution {r p q : ℕ} (G : Matrix (Fin r) (Fin q) ℝ) (H : Matrix (Fin p) (Fin q) ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (g : Fin r → ℝ) (h : Fin p → ℝ),
      (∃ w₀ : Fin q → ℝ, G *ᵥ w₀ = g ∧ H *ᵥ w₀ = h) →
        ∃ w : Fin q → ℝ, (∀ i, (G *ᵥ w) i ≤ g i) ∧ H *ᵥ w = h ∧
          norm2 w ≤ L * norm2Pair g h := by
  let M : (Fin q → ℝ) →ₗ[ℝ] (Fin r → ℝ) × (Fin p → ℝ) :=
    LinearMap.prod (Matrix.mulVecLin G) (Matrix.mulVecLin H)
  obtain ⟨S, hS⟩ := M.rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict M)
  let Sc := LinearMap.toContinuousLinearMap S
  refine ⟨Real.sqrt q * ‖Sc‖, by positivity, fun g h ⟨w0, hg, hh⟩ => ?_⟩
  have hy : (g, h) ∈ LinearMap.range M := ⟨w0, by simp [M, hg, hh]⟩
  set w := S ⟨(g, h), hy⟩ with hw
  have hMw : M w = (g, h) := by
    have := congrArg Subtype.val (LinearMap.congr_fun hS ⟨(g, h), hy⟩)
    simpa [hw] using this
  have hGw : G *ᵥ w = g := by
    have := congrArg Prod.fst hMw; simpa [M] using this
  have hHw : H *ᵥ w = h := by
    have := congrArg Prod.snd hMw; simpa [M] using this
  refine ⟨w, fun i => by rw [hGw], hHw, ?_⟩
  have h1 : ‖w‖ ≤ ‖Sc‖ * ‖(⟨(g, h), hy⟩ : LinearMap.range M)‖ := Sc.le_opNorm _
  have h2 : ‖(⟨(g, h), hy⟩ : LinearMap.range M)‖ = ‖(g, h)‖ := rfl
  rw [h2] at h1
  have h3 := g70wr_pairle g h
  calc norm2 w ≤ Real.sqrt q * ‖w‖ := g70wr_n2le w
    _ ≤ Real.sqrt q * (‖Sc‖ * ‖(g, h)‖) := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt q * (‖Sc‖ * norm2Pair g h) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (ContinuousLinearMap.opNorm_nonneg Sc)) (Real.sqrt_nonneg _)
    _ = Real.sqrt q * ‖Sc‖ * norm2Pair g h := by ring


