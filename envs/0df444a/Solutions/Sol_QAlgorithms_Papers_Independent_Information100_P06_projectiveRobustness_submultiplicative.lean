-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P06.projectiveRobustness_submultiplicative
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T16:02:20.223323+00:00
-- url     : https://prove2.me/submissions/80310afd-f2e9-43c7-a976-b8b8a30c9c01

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P06

noncomputable section

open scoped Matrix ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P06

lemma x8_tc_psd {I1 O1 I2 O2 : Type} [Fintype I1] [Fintype O1] [Fintype I2] [Fintype O2]
    (X : Choi I1 O1) (Y : Choi I2 O2) (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    (tensorChoi X Y).PosSemidef := by
  have := (hX.kronecker hY).submatrix
    (fun p : (I1 × I2) × (O1 × O2) => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
  have e : tensorChoi X Y = (Matrix.kronecker X Y).submatrix
      (fun p : (I1 × I2) × (O1 × O2) => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
      (fun p : (I1 × I2) × (O1 × O2) => ((p.1.1, p.2.1), (p.1.2, p.2.2))) := by
    ext p q; rfl
  rw [e]
  exact this

lemma x8_tc_sub_left {I1 O1 I2 O2 : Type} (X X' : Choi I1 O1) (Y : Choi I2 O2) :
    tensorChoi (X - X') Y = tensorChoi X Y - tensorChoi X' Y := by
  ext p q; simp [tensorChoi, sub_mul]

lemma x8_tc_sub_right {I1 O1 I2 O2 : Type} (X : Choi I1 O1) (Y Y' : Choi I2 O2) :
    tensorChoi X (Y - Y') = tensorChoi X Y - tensorChoi X Y' := by
  ext p q; simp [tensorChoi, mul_sub]

lemma x8_tc_smul {I1 O1 I2 O2 : Type} (a b : ℂ) (X : Choi I1 O1) (Y : Choi I2 O2) :
    tensorChoi (a • X) (b • Y) = (a * b) • tensorChoi X Y := by
  ext p q; simp [tensorChoi]; ring

/-- `A ≤ B`, `C ≤ D`, with `A` and `D` PSD, gives `A ⊗ C ≤ B ⊗ D`. -/
lemma x8_below_tc {I1 O1 I2 O2 : Type} [Fintype I1] [Fintype O1] [Fintype I2] [Fintype O2]
    (A B : Choi I1 O1) (C D : Choi I2 O2) (hA : A.PosSemidef) (hD : D.PosSemidef)
    (h1 : Below A B) (h2 : Below C D) : Below (tensorChoi A C) (tensorChoi B D) := by
  unfold Below at *
  have : tensorChoi B D - tensorChoi A C = tensorChoi (B - A) D + tensorChoi A (D - C) := by
    rw [x8_tc_sub_left, x8_tc_sub_right]; abel
  rw [this]
  exact (x8_tc_psd _ _ h1 hD).add (x8_tc_psd _ _ hA h2)

lemma x8_psd_of_below {I : Type} [Fintype I] (X Y : Matrix I I ℂ) (hX : X.PosSemidef)
    (h : Below X Y) : Y.PosSemidef := by
  have := hX.add h
  simpa using this

lemma x8_below_trans {I : Type} [Fintype I] (X Y Z : Matrix I I ℂ)
    (h1 : Below X Y) (h2 : Below Y Z) : Below X Z := by
  unfold Below at *
  have := h1.add h2
  simpa using this

lemma x8_trace_one {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [Nonempty I]
    (X : Choi I O) (hX : IsChannelChoi X) : X.trace = 1 := by
  have h := hX.2
  have : X.trace = ∑ i, traceOutput X i i := by
    simp [Matrix.trace, traceOutput, Fintype.sum_prod_type]
  rw [this, h]
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card I : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

lemma x8_ge_one {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [Nonempty I]
    (F : FreeSet I O) (N : Choi I O) (hN : IsChannelChoi N) :
    1 ≤ projectiveRobustness F N := by
  unfold projectiveRobustness
  refine le_sInf ?_
  rintro g ⟨gamma, lam, rfl, M, hM, h1, h2⟩
  have h3 := x8_below_trans _ _ _ h1 h2
  unfold Below at h3
  have h4 := h3.trace_nonneg
  have e : ((gamma : ℂ) • N - N).trace = ((gamma : ℂ) - 1) := by
    rw [Matrix.trace_sub, Matrix.trace_smul, x8_trace_one N hN, smul_eq_mul, mul_one]
  rw [e] at h4
  have h5 : (1 : ℝ) ≤ (gamma : ℝ) := by
    have := (Complex.nonneg_iff.mp h4).1
    simpa using this
  have : (1 : NNReal) ≤ gamma := by exact_mod_cast h5
  exact_mod_cast this

lemma x8_main {I1 O1 I2 O2 : Type}
    [Fintype I1] [Fintype O1] [Fintype I2] [Fintype O2]
    [DecidableEq I1] [DecidableEq I2]
    [Nonempty I1] [Nonempty O1] [Nonempty I2] [Nonempty O2]
    (F : FreeSet I1 O1) (G : FreeSet I2 O2)
    (H : FreeSet (I1 × I2) (O1 × O2))
    (htensor : ∀ M ∈ F.carrier, ∀ L ∈ G.carrier, tensorChoi M L ∈ H.carrier)
    (N : Choi I1 O1) (L : Choi I2 O2)
    (hN : IsChannelChoi N) (hL : IsChannelChoi L) :
    projectiveRobustness H (tensorChoi N L) ≤
      projectiveRobustness F N * projectiveRobustness G L := by
  set SA := {g : ℝ≥0∞ | ∃ gamma lambda : NNReal, g = (gamma : ℝ≥0∞) ∧
    ∃ M ∈ F.carrier, Below N ((lambda : ℂ) • M) ∧
      Below ((lambda : ℂ) • M) ((gamma : ℂ) • N)} with hSA
  set SB := {g : ℝ≥0∞ | ∃ gamma lambda : NNReal, g = (gamma : ℝ≥0∞) ∧
    ∃ M ∈ G.carrier, Below L ((lambda : ℂ) • M) ∧
      Below ((lambda : ℂ) • M) ((gamma : ℂ) • L)} with hSB
  have hpa : projectiveRobustness F N = sInf SA := rfl
  have hpb : projectiveRobustness G L = sInf SB := rfl
  have key : ∀ a ∈ SA, ∀ b ∈ SB, projectiveRobustness H (tensorChoi N L) ≤ a * b := by
    rintro a ⟨g1, l1, rfl, M1, hM1, a1, a2⟩ b ⟨g2, l2, rfl, M2, hM2, b1, b2⟩
    unfold projectiveRobustness
    refine sInf_le ⟨g1 * g2, l1 * l2, by push_cast; rfl, tensorChoi M1 M2, htensor _ hM1 _ hM2,
      ?_, ?_⟩
    · have := x8_below_tc _ _ _ _ hN.1 (x8_psd_of_below _ _ hL.1 b1) a1 b1
      rw [x8_tc_smul] at this
      push_cast
      exact this
    · have hl1 := x8_psd_of_below _ _ hN.1 a1
      have hg2 := x8_psd_of_below _ _ (x8_psd_of_below _ _ hL.1 b1) b2
      have := x8_below_tc _ _ _ _ hl1 hg2 a2 b2
      rw [x8_tc_smul, x8_tc_smul] at this
      push_cast
      exact this
  rw [hpa, hpb]
  by_cases hA : SA.Nonempty
  · by_cases hB : SB.Nonempty
    · rw [sInf_eq_iInf', sInf_eq_iInf']
      obtain ⟨a, ha⟩ := hA
      obtain ⟨b, hb⟩ := hB
      have fin : ∀ S : Set ℝ≥0∞, (∀ x ∈ S, x ≠ ∞) → ∀ x ∈ S, ∃ i : S, (i : ℝ≥0∞) ≠ ∞ :=
        fun S hS x hx => ⟨⟨x, hx⟩, hS x hx⟩
      refine ENNReal.le_iInf_mul_iInf ?_ ?_ fun i j => key _ i.2 _ j.2
      · refine fin SA ?_ a ha
        rintro _ ⟨g, _, rfl, _⟩; exact ENNReal.coe_ne_top
      · refine fin SB ?_ b hb
        rintro _ ⟨g, _, rfl, _⟩; exact ENNReal.coe_ne_top
    · rw [Set.not_nonempty_iff_eq_empty.mp hB, sInf_empty]
      have : sInf SA ≠ 0 := by
        have := x8_ge_one F N hN
        rw [hpa] at this
        exact (lt_of_lt_of_le zero_lt_one this).ne'
      rw [ENNReal.mul_top this]
      exact le_top
  · rw [Set.not_nonempty_iff_eq_empty.mp hA, sInf_empty]
    have : sInf SB ≠ 0 := by
      have := x8_ge_one G L hL
      rw [hpb] at this
      exact (lt_of_lt_of_le zero_lt_one this).ne'
    rw [ENNReal.top_mul this]
    exact le_top

end QAlgorithms.Papers.Independent.Information100.P06

open QAlgorithms.Papers.Independent.Information100.P06 in
theorem solution
    {I1 O1 I2 O2 : Type}
    [Fintype I1] [Fintype O1] [Fintype I2] [Fintype O2]
    [DecidableEq I1] [DecidableEq I2]
    [Nonempty I1] [Nonempty O1] [Nonempty I2] [Nonempty O2]
    (F : FreeSet I1 O1) (G : FreeSet I2 O2)
    (H : FreeSet (I1 × I2) (O1 × O2))
    (htensor : ∀ M ∈ F.carrier, ∀ L ∈ G.carrier, tensorChoi M L ∈ H.carrier)
    (N : Choi I1 O1) (L : Choi I2 O2)
    (hN : IsChannelChoi N) (hL : IsChannelChoi L) :
    projectiveRobustness H (tensorChoi N L) ≤
      projectiveRobustness F N * projectiveRobustness G L :=
  x8_main F G H htensor N L hN hL
