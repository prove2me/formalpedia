-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P27.idealKD_perfect
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T08:30:37.992906+00:00
-- url     : https://prove2.me/submissions/d9fd58a4-5b3d-490b-b29d-5a5a58c918c4

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P27
noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P27

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Dependency50.P07
  (CQData ensembleMean ensembleInformation accessibleInformation)

open QAlgorithms.Papers.Independent.Dependency50.P24 (Key)

open QAlgorithms.Papers.Independent.Dependency50.P47 (cqMatrix)

attribute [local instance] Classical.decEq Classical.propDecidable

lemma S168_mullog (a b : ℝ) :
    (a * b) * Real.logb 2 (a * b) = b * (a * Real.logb 2 a) + a * (b * Real.logb 2 b) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  rw [Real.logb_mul ha hb]; ring

lemma S168_prod_info {X Y : Type} [Fintype X] [Fintype Y] (p : X → ℝ) (q : Y → ℝ)
    (hp : ∑ x, p x = 1) (hq : ∑ y, q y = 1) :
    QAlgorithms.Papers.Independent.Information100.P27.shannon p +
      QAlgorithms.Papers.Independent.Information100.P27.shannon (fun y => ∑ x, p x * q y) -
      QAlgorithms.Papers.Independent.Information100.P27.shannon
        (fun z : X × Y => p z.1 * q z.2) = 0 := by
  simp only [QAlgorithms.Papers.Independent.Information100.P27.shannon]
  have h1 : ∀ y, ∑ x, p x * q y = q y := fun y => by rw [← Finset.sum_mul, hp, one_mul]
  simp only [h1]
  rw [Fintype.sum_prod_type]
  simp only [S168_mullog, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hp, hq]
  ring

lemma S168_pair_sum (m : ℕ) : ∑ z : Key (2 ^ m), idealPairProb m z = 1 := by
  simp only [idealPairProb, Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp

end QAlgorithms.Papers.Independent.Support50.P27

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P27
open QAlgorithms.Papers.Independent.Dependency50.P07
  (CQData ensembleMean ensembleInformation accessibleInformation)
open QAlgorithms.Papers.Independent.Dependency50.P24 (Key)

attribute [local instance] Classical.decEq Classical.propDecidable

theorem solution {L : ℕ} {E : Type} [Fintype E] [Nonempty E]
    (D : KeyData L E) :
    equalityUniformityDefect D.lengthProb (idealBranch D) = 0 ∧
      (∑ m, D.lengthProb m * accessibleInformation (idealBranch D m)) = 0 := by
  refine ⟨by simp [equalityUniformityDefect, idealBranch], ?_⟩
  refine Finset.sum_eq_zero fun m _ => ?_
  suffices h : accessibleInformation (idealBranch D m) = 0 by rw [h, mul_zero]
  have htr : (actualEveMean D m).trace = 1 := by
    obtain ⟨_, hs, hd⟩ := D.branchValid m
    simp only [actualEveMean, ensembleMean,
      QAlgorithms.Papers.Independent.Information100.P27.average, Matrix.trace_sum,
      Matrix.trace_smul, (hd _).2, smul_eq_mul, mul_one]
    exact_mod_cast hs
  have hq : ∀ M : QAlgorithms.Papers.Independent.Information100.P04.Measurement E,
      ∑ y, effectProb (M.effect y) (actualEveMean D m) = 1 := by
    intro M
    have : ∑ y, effectProb (M.effect y) (actualEveMean D m) =
        ((∑ y, M.effect y) * actualEveMean D m).trace.re := by
      simp only [effectProb, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
    rw [this, M.valid.2, one_mul, htr, Complex.one_re]
  have hall : ∀ v ∈ {v | ∃ M : QAlgorithms.Papers.Independent.Information100.P04.Measurement E,
      let joint : Key (2 ^ m.val) × Fin M.outcomes → ℝ := fun z =>
        (idealBranch D m).prob z.1 * effectProb (M.effect z.2) ((idealBranch D m).state z.1)
      v = QAlgorithms.Papers.Independent.Information100.P27.shannon (idealBranch D m).prob +
        QAlgorithms.Papers.Independent.Information100.P27.shannon (fun y => ∑ x, joint (x,y)) -
        QAlgorithms.Papers.Independent.Information100.P27.shannon joint}, v = 0 := by
    rintro v ⟨M, hv⟩
    rw [hv]
    exact S168_prod_info (idealPairProb m.val) (fun y => effectProb (M.effect y) (actualEveMean D m))
      (S168_pair_sum m.val) (hq M)
  unfold accessibleInformation
  apply le_antisymm
  · exact Real.sSup_nonpos fun v hv => (hall v hv).le
  · exact Real.sSup_nonneg fun v hv => (hall v hv).ge

end
