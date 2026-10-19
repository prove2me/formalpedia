-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P05.minimalExpansionImpliesProperty1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:26:51.864401+00:00
-- url     : https://prove2.me/submissions/886bf3a3-c1fd-494f-93b2-1a7cb25468bd

import Mathlib
import Definitions.Def_QAlgorithms_Defs_NLTSPreparationCircuits
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P05_Model
set_option autoImplicit false

/-! Statements from Anshu--Breuckmann--Nirkhe, arXiv:2206.13228v4.
Theorem 5 and three construction-specific expansion claims are deferred in HARD.md.
All new definitions are specific to this paper. -/

noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Independent1 QAlgorithms.Papers.Independent.Independent1.P05
open PresentedCSS

/-- Section 3, PDF p.6: uniform expansion on constructed minimal-representative subsets
implies Property 1 uniformly in a family. Actual check-density factors are retained. -/
theorem gk_hn_add {n : ℕ} (x y : Fin n → ZMod 2) :
    hammingNorm (x + y) ≤ hammingNorm x + hammingNorm y := by
  unfold hammingNorm
  calc (Finset.univ.filter fun i => (x + y) i ≠ 0).card
      ≤ ((Finset.univ.filter fun i => x i ≠ 0) ∪ (Finset.univ.filter fun i => y i ≠ 0)).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
          Pi.add_apply] at hi ⊢
        by_contra h
        push_neg at h
        rw [h.1, h.2, add_zero] at hi
        exact hi rfl
    _ ≤ _ := Finset.card_union_le _ _

theorem gk_red_spec {n : ℕ} (S : Submodule (ZMod 2) (Fin n → ZMod 2)) (a : Fin n → ZMod 2) :
    ∃ s ∈ S, NLTS.reducedHammingWeight S a = hammingNorm (a + s) := by
  unfold NLTS.reducedHammingWeight
  obtain ⟨s, _, hs⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty_iff.mpr ⟨(0 : S)⟩)
    (fun s : S => hammingNorm (a + (s : Fin n → ZMod 2)))
  exact ⟨s, s.2, hs⟩

theorem gk_red_le {n : ℕ} (S : Submodule (ZMod 2) (Fin n → ZMod 2)) (a s : Fin n → ZMod 2)
    (hs : s ∈ S) : NLTS.reducedHammingWeight S a ≤ hammingNorm (a + s) := by
  unfold NLTS.reducedHammingWeight
  exact Finset.inf'_le (fun s : S => hammingNorm (a + (s : Fin n → ZMod 2)))
    (Finset.mem_univ (⟨s, hs⟩ : S))

theorem gk_dualZ {n mx mz : ℕ} (C : CheckPresentation n mx mz) (s : Fin n → ZMod 2)
    (hs : s ∈ codeDual C.Cx) : C.HZ.mulVec s = 0 := by
  ext i
  have hrow : C.HZ i ∈ C.Cx := by
    apply C.css
    intro c hc
    have : C.HZ.mulVec c = 0 := hc
    have := congrFun this i
    simp only [Matrix.mulVec, Pi.zero_apply] at this
    rw [dotProduct_comm]; exact this
  have := hs (C.HZ i) hrow
  simpa [Matrix.mulVec] using this

theorem gk_dualX {n mx mz : ℕ} (C : CheckPresentation n mx mz) (s : Fin n → ZMod 2)
    (hs : s ∈ codeDual C.Cz) : C.HX.mulVec s = 0 := by
  ext i
  have hrow : C.HX i ∈ C.Cz := by
    show C.HZ.mulVec (C.HX i) = 0
    ext j
    have := congrFun (congrFun C.orthogonal i) j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply] at this
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [← this]; apply Finset.sum_congr rfl; intro k _; ring
  have := hs (C.HX i) hrow
  simpa [Matrix.mulVec] using this

theorem gk_side {n m : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2))
    (S : Submodule (ZMod 2) (Fin n → ZMod 2)) (hS : ∀ s ∈ S, H.mulVec s = 0)
    (V : Set (Fin n → ZMod 2)) (alpha beta delta upper : ℝ) (hb : 0 < beta)
    (hm : (m : ℝ) ≤ upper * n) (hd : 0 ≤ delta)
    (hV : ∀ y, (hammingNorm (H.mulVec y) : ℝ) ≤ delta * m →
      (∀ s ∈ S, hammingNorm y ≤ hammingNorm (y + s)) → y ∈ V)
    (hexp : nltsExpanding H V alpha beta)
    (y : Fin n → ZMod 2) (hy : (hammingNorm (H.mulVec y) : ℝ) ≤ delta * m) :
    (NLTS.reducedHammingWeight S y : ℝ) ≤ upper / beta * delta * n ∨
      alpha * n ≤ (NLTS.reducedHammingWeight S y : ℝ) := by
  obtain ⟨s0, hs0, e⟩ := gk_red_spec S y
  have hHy : H.mulVec (y + s0) = H.mulVec y := by
    rw [Matrix.mulVec_add, hS s0 hs0, add_zero]
  have hmem : y + s0 ∈ V := by
    apply hV
    · rw [hHy]; exact hy
    · intro s hs
      rw [← e, add_assoc]
      exact gk_red_le S y _ (S.add_mem hs0 hs)
  rw [e]
  by_cases h : (hammingNorm (y + s0) : ℝ) ≤ alpha * n
  · left
    have h1 := hexp _ hmem h
    rw [hHy] at h1
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hb]
    have : delta * (m:ℝ) ≤ delta * (upper * n) := mul_le_mul_of_nonneg_left hm hd
    nlinarith
  · right; push_neg at h; exact h.le

theorem solution (F : NLTSCheckFamily)
    (alphaX betaX alphaZ betaZ deltaBar lower upper : ℝ)
    (haX : 0 < alphaX) (hbX : 0 < betaX) (haZ : 0 < alphaZ) (hbZ : 0 < betaZ)
    (hd : 0 < deltaBar) (hl : 0 < lower) (hu : 0 < upper) (n0 : ℕ) (hn0 : 1 ≤ n0)
    (hrows : ∀ n ≥ n0,
      lower*n ≤ (F.rowsX n : ℝ) ∧ lower*n ≤ (F.rowsZ n : ℝ) ∧
      (F.rowsX n : ℝ) ≤ upper*n ∧ (F.rowsZ n : ℝ) ≤ upper*n)
    (hexp : ∀ n ≥ n0, ∀ delta : ℝ, 0 ≤ delta → delta < deltaBar →
      nltsExpanding (F.checks n).HX (nltsMinimal (F.checks n) true delta) alphaX betaX ∧
      nltsExpanding (F.checks n).HZ (nltsMinimal (F.checks n) false delta) alphaZ betaZ) :
    ∃ c1 c2 delta0 : ℝ, 0 < c1 ∧ 0 < c2 ∧ 0 < delta0 ∧
      ∀ n ≥ n0, NLTS.ClustersApproximateCodewords (F.checks n) c1 c2 delta0 := by
  refine ⟨upper/betaX + upper/betaZ, min alphaX alphaZ, deltaBar, by positivity,
    lt_min haX haZ, hd, ?_⟩
  intro n hn
  obtain ⟨_, _, hux, huz⟩ := hrows n hn
  refine ⟨by positivity, lt_min haX haZ, hd, ?_⟩
  intro delta hd0 hdl y
  have hnn : (0:ℝ) ≤ n := by positivity
  have hX0 : 0 ≤ upper / betaX := by positivity
  have hZ0 : 0 ≤ upper / betaZ := by positivity
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · have := gk_side (F.checks n).HZ (codeDual (F.checks n).Cx) (gk_dualZ _)
      (nltsMinimal (F.checks n) false delta) alphaZ betaZ delta upper hbZ huz hd0
      (fun y h1 h2 => ⟨by simpa [nltsApprox] using h1, h2⟩) (hexp n hn delta hd0 hdl).2 y hy
    rcases this with h | h
    · left
      have : upper / betaZ * delta * n ≤ (upper/betaX + upper/betaZ) * delta * n := by
        have := mul_nonneg hd0 hnn
        nlinarith
      linarith
    · right
      have : min alphaX alphaZ * n ≤ alphaZ * n :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hnn
      linarith
  · have := gk_side (F.checks n).HX (codeDual (F.checks n).Cz) (gk_dualX _)
      (nltsMinimal (F.checks n) true delta) alphaX betaX delta upper hbX hux hd0
      (fun y h1 h2 => ⟨by simpa [nltsApprox] using h1, h2⟩) (hexp n hn delta hd0 hdl).1 y hy
    rcases this with h | h
    · left
      have : upper / betaX * delta * n ≤ (upper/betaX + upper/betaZ) * delta * n := by
        have := mul_nonneg hd0 hnn
        nlinarith
      linarith
    · right
      have : min alphaX alphaZ * n ≤ alphaX * n :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) hnn
      linarith

