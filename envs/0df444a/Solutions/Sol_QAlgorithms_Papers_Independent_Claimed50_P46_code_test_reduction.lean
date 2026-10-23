-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P46.code_test_reduction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T11:43:09.701242+00:00
-- url     : https://prove2.me/submissions/dccfd2de-6273-42e7-be50-3c41bb3ddf00

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P46

noncomputable section

open Filter

open scoped BigOperators ENNReal NNReal

attribute [local instance] Classical.propDecidable

universe u

namespace QAlgorithms.Papers.Independent.Claimed50.P46

theorem x8_typeI (P : Source.{u}) (k : ℕ) (T : SimpleHypothesisTest (sourceSystem P k)) :
    testingTypeI T = ∑' x, (P.p k x : ℝ≥0∞) * ENNReal.ofReal (1 - (T x).val) := rfl

theorem x8_typeII (P : Source.{u}) (k : ℕ) (T : SimpleHypothesisTest (sourceSystem P k)) :
    testingTypeII T = ∑' x, ENNReal.ofReal (T x).val := by
  show (∑' x, ((1 : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (T x).val) = _
  simp

theorem x8_acc_nonneg {X : Type u} (C : StochasticSourceCode X) (x : X) :
    0 ≤ codeAcceptance C x :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)

theorem x8_dec_le {X : Type u} (C : StochasticSourceCode X) (y : Fin C.size) (x : X) :
    C.decoder y x ≤ 1 := by
  have h : (C.decoder y x : ℝ≥0∞) ≤ 1 := by
    rw [← C.decoder_normalized y]; exact ENNReal.le_tsum x
  exact_mod_cast h

theorem x8_acc_ennreal {X : Type u} (C : StochasticSourceCode X) (x : X) :
    ENNReal.ofReal (codeAcceptance C x) = ∑ y, (C.encoder x y : ℝ≥0∞) * (C.decoder y x : ℝ≥0∞) := by
  unfold codeAcceptance
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ =>
    mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]

theorem x8_acc_le {X : Type u} (C : StochasticSourceCode X) (x : X) :
    codeAcceptance C x ≤ 1 := by
  have h : ENNReal.ofReal (codeAcceptance C x) ≤ 1 := by
    rw [x8_acc_ennreal]
    calc ∑ y, (C.encoder x y : ℝ≥0∞) * (C.decoder y x : ℝ≥0∞)
        ≤ ∑ y, (C.encoder x y : ℝ≥0∞) := Finset.sum_le_sum fun y _ => by
          have := x8_dec_le C y x
          calc (C.encoder x y : ℝ≥0∞) * (C.decoder y x : ℝ≥0∞) ≤ (C.encoder x y : ℝ≥0∞) * 1 := by
                gcongr; exact_mod_cast this
            _ = _ := mul_one _
      _ = 1 := by
          have := C.encoder_normalized x
          rw [← ENNReal.ofNNReal_finsetSum, this]; rfl
  exact (ENNReal.ofReal_le_one).1 h

theorem x8_one_sub (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    ENNReal.ofReal a + ENNReal.ofReal (1 - a) = 1 := by
  rw [← ENNReal.ofReal_add h0 (by linarith)]; simp

theorem x8_error (P : Source.{u}) (k : ℕ) (C : StochasticSourceCode (P.X k))
    (T : SimpleHypothesisTest (sourceSystem P k)) (hT : ∀ x, (T x).val = codeAcceptance C x) :
    sourceCodeError P k C = testingTypeI T := by
  rw [x8_typeI]
  unfold sourceCodeError sourceCodeSuccess
  have hsum : (∑' x, (P.p k x : ℝ≥0∞) * ENNReal.ofReal (codeAcceptance C x)) +
      (∑' x, (P.p k x : ℝ≥0∞) * ENNReal.ofReal (1 - (T x).val)) = 1 := by
    rw [← ENNReal.tsum_add, ← P.normalized k]
    refine tsum_congr fun x => ?_
    rw [← mul_add, hT, x8_one_sub _ (x8_acc_nonneg C x) (x8_acc_le C x), mul_one]
  have hfin : (∑' x, (P.p k x : ℝ≥0∞) * ENNReal.ofReal (codeAcceptance C x)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∑' x, (P.p k x : ℝ≥0∞)) (by rw [P.normalized k]; simp) ?_
    exact ENNReal.tsum_le_tsum fun x => by
      calc (P.p k x : ℝ≥0∞) * ENNReal.ofReal (codeAcceptance C x) ≤ (P.p k x : ℝ≥0∞) * 1 := by
            gcongr; exact ENNReal.ofReal_le_one.2 (x8_acc_le C x)
        _ = _ := mul_one _
  rw [← hsum, ENNReal.add_sub_cancel_left hfin]

theorem x8_typeII_le (P : Source.{u}) (k : ℕ) (C : StochasticSourceCode (P.X k))
    (T : SimpleHypothesisTest (sourceSystem P k)) (hT : ∀ x, (T x).val = codeAcceptance C x) :
    testingTypeII T ≤ (C.size : ℝ≥0∞) := by
  rw [x8_typeII]
  simp_rw [hT, x8_acc_ennreal]
  calc ∑' x, ∑ y, (C.encoder x y : ℝ≥0∞) * (C.decoder y x : ℝ≥0∞)
      ≤ ∑' x, ∑ y, (C.decoder y x : ℝ≥0∞) := ENNReal.tsum_le_tsum fun x =>
        Finset.sum_le_sum fun y _ => by
          have h : (C.encoder x y : ℝ≥0∞) ≤ 1 := by
            have := C.encoder_normalized x
            have h2 : C.encoder x y ≤ ∑ y', C.encoder x y' :=
              Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ y)
            exact_mod_cast this ▸ h2
          calc (C.encoder x y : ℝ≥0∞) * (C.decoder y x : ℝ≥0∞) ≤ 1 * (C.decoder y x : ℝ≥0∞) := by
                gcongr
            _ = _ := one_mul _
    _ = ∑ y, ∑' x, (C.decoder y x : ℝ≥0∞) := (Summable.tsum_finsetSum (fun _ _ => ENNReal.summable))
    _ = (C.size : ℝ≥0∞) := by simp [C.decoder_normalized]

theorem x8_main (P : Source.{u}) (k : ℕ) :
    (∀ C : StochasticSourceCode (P.X k), ∃ T : SimpleHypothesisTest (sourceSystem P k),
      (∀ x, (T x).val = codeAcceptance C x) ∧
      sourceCodeError P k C = testingTypeI T ∧ testingTypeII T ≤ (C.size : ℝ≥0∞)) ∧
    (∀ A : Finset (P.X k), A.Nonempty → ∃ C : StochasticSourceCode (P.X k),
      C.size = A.card ∧
      (∀ x, codeAcceptance C x = if x ∈ A then 1 else 0) ∧
      sourceCodeError P k C = testingTypeI (finiteAcceptanceTest P k A) ∧
      (C.size : ℝ≥0∞) = testingTypeII (finiteAcceptanceTest P k A) ∧
      testingTypeII (finiteAcceptanceTest P k A) = (A.card : ℝ≥0∞)) := by
  refine ⟨fun C => ?_, fun A hA => ?_⟩
  · let T : SimpleHypothesisTest (sourceSystem P k) :=
      fun x => ⟨codeAcceptance C x, x8_acc_nonneg C x, x8_acc_le C x⟩
    have hT : ∀ x, (T x).val = codeAcceptance C x := fun _ => rfl
    exact ⟨T, hT, x8_error P k C T hT, x8_typeII_le P k C T hT⟩
  · obtain ⟨a0, ha0⟩ := hA
    let e := A.equivFin
    let g : P.X k → Fin A.card := fun x => if h : x ∈ A then e ⟨x, h⟩ else e ⟨a0, ha0⟩
    have hpos : 0 < A.card := Finset.card_pos.2 ⟨a0, ha0⟩
    let C : StochasticSourceCode (P.X k) :=
      { size := A.card
        size_pos := hpos
        encoder := fun x y => if g x = y then 1 else 0
        decoder := fun y x => if x = (e.symm y).val then 1 else 0
        encoder_normalized := fun x => by simp
        decoder_normalized := fun y => by
          simp only [apply_ite ENNReal.ofNNReal, ENNReal.coe_one, ENNReal.coe_zero]
          exact tsum_ite_eq _ _ }
    have hacc : ∀ x, codeAcceptance C x = if x ∈ A then 1 else 0 := by
      intro x
      unfold codeAcceptance
      simp only [C, apply_ite NNReal.toReal, NNReal.coe_one, NNReal.coe_zero, ite_mul, one_mul,
        zero_mul]
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_univ, if_true]
      by_cases hx : x ∈ A
      · simp [g, hx, e]
      · have : x ≠ a0 := fun h => hx (h ▸ ha0)
        simp [g, hx, e, this]
    have hT : ∀ x, (finiteAcceptanceTest P k A x).val = codeAcceptance C x := by
      intro x; rw [hacc]; unfold finiteAcceptanceTest; split_ifs <;> rfl
    have hII : testingTypeII (finiteAcceptanceTest P k A) = (A.card : ℝ≥0∞) := by
      rw [x8_typeII]
      have : ∀ x, ENNReal.ofReal (finiteAcceptanceTest P k A x).val =
          if x ∈ A then 1 else 0 := by
        intro x; unfold finiteAcceptanceTest; split_ifs <;> simp
      simp_rw [this]
      rw [tsum_eq_sum (s := A) (fun x hx => if_neg hx)]
      simp
    exact ⟨C, rfl, hacc, x8_error P k C _ hT, hII.symm ▸ rfl, hII⟩

end QAlgorithms.Papers.Independent.Claimed50.P46

open QAlgorithms.Papers.Independent.Claimed50.P46 in
theorem solution (P : Source.{u}) (k : ℕ) :
    (∀ C : StochasticSourceCode (P.X k), ∃ T : SimpleHypothesisTest (sourceSystem P k),
      (∀ x, (T x).val = codeAcceptance C x) ∧
      sourceCodeError P k C = testingTypeI T ∧ testingTypeII T ≤ (C.size : ℝ≥0∞)) ∧
    (∀ A : Finset (P.X k), A.Nonempty → ∃ C : StochasticSourceCode (P.X k),
      C.size = A.card ∧
      (∀ x, codeAcceptance C x = if x ∈ A then 1 else 0) ∧
      sourceCodeError P k C = testingTypeI (finiteAcceptanceTest P k A) ∧
      (C.size : ℝ≥0∞) = testingTypeII (finiteAcceptanceTest P k A) ∧
      testingTypeII (finiteAcceptanceTest P k A) = (A.card : ℝ≥0∞)) :=
  x8_main P k
