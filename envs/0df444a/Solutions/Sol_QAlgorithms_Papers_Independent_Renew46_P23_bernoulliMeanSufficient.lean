-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P23.bernoulliMeanSufficient
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T00:38:59.469991+00:00
-- url     : https://prove2.me/submissions/31e3c07b-1b3e-41de-9485-03e23725a5ca

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P23
noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal NNReal ComplexOrder MatrixOrder Matrix.Norms.L2Operator

open QAlgorithms.Papers.Independent.Renew46.P23

open QAlgorithms.Papers.Independent.Next46.P43
  (SufficientSigmaAlgebra MinimalSufficientSigmaAlgebra IsCStarCoarseGraining)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Dependency50.P28 (relativeEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

local instance : MeasurableSpace Bool := ⊤
lemma g64m_comb {X : Type*} [Fintype X] [DecidableEq X] {Y : Type*} [DecidableEq Y]
    (S : X → Y) (w : X → ℝ≥0∞) (hw : ∀ x y, S x = S y → w x = w y)
    (A B : Set X) [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (hB : ∀ x y, S x = S y → (x ∈ B ↔ y ∈ B)) :
    ∑ x, (if x ∈ B then ((Finset.univ.filter (fun y => y ∈ A ∧ S y = S x)).card : ℝ≥0∞) /
        (Finset.univ.filter (fun y => S y = S x)).card else 0) * w x =
      ∑ x, (if x ∈ A ∧ x ∈ B then w x else 0) := by
  set L : X → ℝ≥0∞ := fun x => ((Finset.univ.filter (fun y => S y = S x)).card : ℝ≥0∞) with hL
  have hLx : ∀ x y, S x = S y → L x = L y := by
    intro x y h; simp only [hL, h]
  have hLpos : ∀ x, L x ≠ 0 := by
    intro x
    simp only [hL, ne_eq, Nat.cast_eq_zero, Finset.card_eq_zero]
    exact Finset.nonempty_iff_ne_empty.mp ⟨x, by simp⟩
  have hLtop : ∀ x, L x ≠ ⊤ := fun x => by simp [hL]
  have step1 : ∀ x, (if x ∈ B then ((Finset.univ.filter (fun y => y ∈ A ∧ S y = S x)).card : ℝ≥0∞) /
        (Finset.univ.filter (fun y => S y = S x)).card else 0) * w x =
      ∑ y, (if y ∈ A ∧ S y = S x ∧ x ∈ B then w x / L x else 0) := by
    intro x
    by_cases hx : x ∈ B
    · simp only [hx, if_true, and_true]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, ENNReal.div_eq_inv_mul,
        ENNReal.div_eq_inv_mul]
      ring
    · simp [hx]
  simp only [step1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  have step2 : ∀ x, (if y ∈ A ∧ S y = S x ∧ x ∈ B then w x / L x else 0) =
      (if S x = S y then (if y ∈ A ∧ y ∈ B then w y / L y else 0) else 0) := by
    intro x
    by_cases hs : S x = S y
    · rw [if_pos hs, hw x y hs, hLx x y hs]
      have hb := hB x y hs
      by_cases hyB : y ∈ B <;> by_cases hyA : y ∈ A <;> simp [hs, hb, hyB, hyA]
    · rw [if_neg hs]
      simp [Ne.symm hs]
  simp only [step2]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  by_cases hy : y ∈ A ∧ y ∈ B
  · simp only [hy, and_self, if_true]
    have : ((Finset.univ.filter (fun x => S x = S y)).card : ℝ≥0∞) = L y := by
      rfl
    rw [this, ENNReal.mul_div_cancel (hLpos y) (hLtop y)]
  · simp [hy]

lemma g64m_suff {X Θ : Type*} [Fintype X] [DecidableEq X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (P : Θ → Measure X) (S : X → ℝ)
    (hw : ∀ θ x y, S x = S y → P θ {x} = P θ {y}) :
    SufficientSigmaAlgebra P (MeasurableSpace.comap S (borel ℝ)) := by
  classical
  refine ⟨fun s _ => (Set.toFinite s).measurableSet, ?_⟩
  intro A _
  set f : X → ℝ≥0∞ := fun x => ((Finset.univ.filter (fun y => y ∈ A ∧ S y = S x)).card : ℝ≥0∞) /
        (Finset.univ.filter (fun y => S y = S x)).card with hf
  have fconst : ∀ x y, S x = S y → f x = f y := by
    intro x y h; simp only [hf, h]
  refine ⟨f, ?_, fun θ => ⟨Filter.Eventually.of_forall (fun x => ?_), ?_⟩⟩
  · intro U _
    refine ⟨S '' (f ⁻¹' U), ?_, ?_⟩
    · have : (S '' (f ⁻¹' U)).Finite := (Set.toFinite _).image _
      have h2 := this.measurableSet (α := ℝ)
      have h3 : (borel ℝ) = Real.measurableSpace := (BorelSpace.measurable_eq (α := ℝ)).symm
      rw [h3]; exact h2
    · ext x
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · rintro ⟨y, hy, hxy⟩
        rwa [fconst x y hxy.symm]
      · intro hx; exact ⟨x, hx, rfl⟩
  · simp only [hf]
    apply ENNReal.div_le_of_le_mul
    rw [one_mul]
    exact_mod_cast Finset.card_le_card (fun y hy => by simp at hy ⊢; exact hy.2)
  · intro B hB
    obtain ⟨C, _, rfl⟩ := hB
    have hBm : MeasurableSet (S ⁻¹' C) := (Set.toFinite _).measurableSet
    rw [← lintegral_indicator hBm, lintegral_fintype, ← lintegral_indicator_one
      ((Set.toFinite _).measurableSet), lintegral_fintype]
    have := g64m_comb S (fun x => P θ {x}) (hw θ) A (S ⁻¹' C) (fun x y h => by simp [h])
    convert this using 2 with x
    · simp only [Set.indicator, hf]
    · simp only [Set.indicator, Set.mem_inter_iff, Pi.one_apply]
      split_ifs <;> simp

lemma g64m_prod_bool {n : ℕ} (g : Bool → ℝ≥0∞) (x : Fin n → Bool) :
    ∏ i, g (x i) = g true ^ (Finset.univ.filter (fun i => x i = true)).card *
      g false ^ (Finset.univ.filter (fun i => ¬ x i = true)).card := by
  have : ∀ i, g (x i) = if x i = true then g true else g false := by
    intro i; cases x i <;> simp
  simp only [this]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]

theorem solution (n : ℕ) (hn : 1 ≤ n) :
    SufficientSigmaAlgebra (bernoulliSampleLaw n)
      (MeasurableSpace.comap
        (fun x : Fin n → Bool => (∑ i, if x i then (1 : ℝ) else 0) / (n : ℝ))
        (borel ℝ)) := by
  apply g64m_suff
  intro p x y hxy
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hc : (Finset.univ.filter (fun i => x i = true)).card =
      (Finset.univ.filter (fun i => y i = true)).card := by
    have h1 := (div_left_inj' hn').mp hxy
    simp only [Finset.sum_boole] at h1
    exact_mod_cast h1
  have hc' : (Finset.univ.filter (fun i => ¬ x i = true)).card =
      (Finset.univ.filter (fun i => ¬ y i = true)).card := by
    have a1 := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => x i = true)
    have a2 := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => y i = true)
    omega
  simp only [bernoulliSampleLaw, Measure.pi_singleton]
  rw [g64m_prod_bool (fun b => ProbabilityTheory.bernoulliMeasure true false p {b}) x,
    g64m_prod_bool (fun b => ProbabilityTheory.bernoulliMeasure true false p {b}) y, hc, hc']
