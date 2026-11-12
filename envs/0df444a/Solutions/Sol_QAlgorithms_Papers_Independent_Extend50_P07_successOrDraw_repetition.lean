-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P07.successOrDraw_repetition
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T02:42:17.30081+00:00
-- url     : https://prove2.me/submissions/88133e11-af8a-4b16-a99d-02d36d4820b1

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P07

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P75 (Mat)

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P07 in
theorem solution (d D k : ℕ) (hd : 0 < d) (hD : d ≤ D)
    (A : General d D D D k) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hS : ∀ V : Isometry d D, ∀ X,
      A.run V (conjSuperop V.val X) = (p : ℂ) • conjSuperop (embedding d D) X)
    (hF : ∀ V : Isometry d D, ∀ X,
      A.draw V (conjSuperop V.val X) = ((1 - p : ℝ) : ℂ) • conjSuperop V.val X) :
    (∀ m : ℕ, (repeatProtocol A m).queryCount = m * k ∧
      ∀ V : Isometry d D, ∀ X,
      (repeatProtocol A m).success V (conjSuperop V.val X) =
        ((1 - (1 - p)^m : ℝ) : ℂ) • conjSuperop (embedding d D) X ∧
      (repeatProtocol A m).failure V (conjSuperop V.val X) =
        (((1 - p)^m : ℝ) : ℂ) • conjSuperop V.val X) ∧
    (0 < p → p < 1 → ∃ C : ℝ, 0 < C ∧ ∀ delta : ℝ,
      0 < delta → delta < 1 → ∃ m : ℕ,
        (1 - p)^m ≤ delta ∧
        ((repeatProtocol A m).queryCount : ℝ) ≤ (k : ℝ) + C * Real.log (1 / delta)) := by
  have hconj : ∀ {n o : ℕ} (W : Matrix (Fin o) (Fin n) ℂ) (c : ℂ) (Y : Matrix (Fin n) (Fin n) ℂ),
      conjSuperop W (c • Y) = c • conjSuperop W Y := by
    intro n o W c Y
    simp only [conjSuperop]
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have part1 : ∀ m : ℕ, (repeatProtocol A m).queryCount = m * k ∧
      ∀ V : Isometry d D, ∀ X,
      (repeatProtocol A m).success V (conjSuperop V.val X) =
        ((1 - (1 - p)^m : ℝ) : ℂ) • conjSuperop (embedding d D) X ∧
      (repeatProtocol A m).failure V (conjSuperop V.val X) =
        (((1 - p)^m : ℝ) : ℂ) • conjSuperop V.val X := by
    intro m
    induction m with
    | zero =>
      refine ⟨by simp [repeatProtocol, RoundTree.queryCount], fun V X => ⟨?_, ?_⟩⟩
      · simp [repeatProtocol, RoundTree.success]
      · simp [repeatProtocol, RoundTree.failure]
    | succ m ih =>
      obtain ⟨hq, hsf⟩ := ih
      refine ⟨?_, fun V X => ?_⟩
      · simp only [repeatProtocol, RoundTree.queryCount, hq]
        ring
      · have hdraw : A.draw V (conjSuperop V.val X) =
            conjSuperop V.val ((((1 - p : ℝ)) : ℂ) • X) := by
          rw [hF, hconj]
        obtain ⟨hs, hf⟩ := hsf V ((((1 - p : ℝ)) : ℂ) • X)
        constructor
        · show A.run V (conjSuperop V.val X) +
              (repeatProtocol A m).success V (A.draw V (conjSuperop V.val X)) = _
          rw [hS, hdraw, hs, hconj, smul_smul, ← add_smul]
          congr 1
          push_cast
          ring
        · show (repeatProtocol A m).failure V (A.draw V (conjSuperop V.val X)) = _
          rw [hdraw, hf, hconj, smul_smul]
          congr 1
          push_cast
          ring
  refine ⟨part1, ?_⟩
  intro hp hp1'
  have h1p : 0 < 1 - p := by linarith
  have hlog : Real.log (1 - p) < 0 := Real.log_neg h1p (by linarith)
  obtain ⟨c, hcdef⟩ : ∃ c, c = -Real.log (1 - p) := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hcdef]; linarith
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  refine ⟨k / c + 1, by positivity, ?_⟩
  intro delta hδ hδ1
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log (1 / delta) := ⟨_, rfl⟩
  have hL : 0 < L := by
    rw [hLdef]
    exact Real.log_pos (one_lt_one_div hδ hδ1)
  have hLδ : Real.log delta = -L := by
    rw [hLdef, one_div, Real.log_inv, neg_neg]
  refine ⟨⌈L / c⌉₊, ?_, ?_⟩
  · have hm : L / c ≤ (⌈L / c⌉₊ : ℝ) := Nat.le_ceil _
    have hmc : L ≤ (⌈L / c⌉₊ : ℝ) * c := by rwa [div_le_iff₀ hc] at hm
    have e1 : (1 - p) ^ ⌈L / c⌉₊ = Real.exp (⌈L / c⌉₊ * Real.log (1 - p)) := by
      rw [Real.exp_nat_mul, Real.exp_log h1p]
    have e2 : delta = Real.exp (Real.log delta) := (Real.exp_log hδ).symm
    rw [e1, e2]
    apply Real.exp_le_exp.mpr
    rw [hLδ, show Real.log (1 - p) = -c by rw [hcdef, neg_neg]]
    linarith
  · rw [(part1 _).1, ← hLdef]
    have hm2 : (⌈L / c⌉₊ : ℝ) < L / c + 1 := Nat.ceil_lt_add_one (div_nonneg hL.le hc.le)
    have h3 := mul_le_mul_of_nonneg_right hm2.le hk
    have h4 : 0 ≤ L := hL.le
    push_cast
    have h5 : (L / c + 1) * (k : ℝ) = k + k / c * L := by ring
    nlinarith

end
