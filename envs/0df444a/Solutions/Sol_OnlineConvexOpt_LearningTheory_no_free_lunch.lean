-- Prove2me | solution 1 for OnlineConvexOpt.LearningTheory.no_free_lunch
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T09:49:00.304183+00:00
-- url     : https://prove2.me/submissions/be659128-1c2d-4a25-9e59-4dafcd96ff5c

import Mathlib
import Definitions.Def_OnlineConvexOpt_LearningTheory_GeneralizationError

set_option autoImplicit false

open MeasureTheory

namespace NFLAuxDbbda360

open Finset

/-- Flipping the concept at an unseen point: exactly half the concepts are misclassified there. -/
theorem half_count {X : Type*} [Fintype X] [DecidableEq X] (m : ℕ)
    (A : (Fin m → X × Bool) → X → Bool) (s : Fin m → X) (x : X) (hx : ∀ i, s i ≠ x) :
    2 * (univ.filter fun C : X → Bool => A (fun i => (s i, C (s i))) x ≠ C x).card
      = 2 ^ Fintype.card X := by
  classical
  let σ : (X → Bool) ≃ (X → Bool) :=
    { toFun := fun C => Function.update C x (!C x)
      invFun := fun C => Function.update C x (!C x)
      left_inv := fun C => by
        funext y
        by_cases hy : y = x
        · subst hy; simp
        · simp [Function.update_of_ne hy]
      right_inv := fun C => by
        funext y
        by_cases hy : y = x
        · subst hy; simp
        · simp [Function.update_of_ne hy] }
  have hlab : ∀ C : X → Bool, (fun i => (s i, σ C (s i))) = (fun i => (s i, C (s i))) := by
    intro C; funext i
    simp [σ, Function.update_of_ne (hx i)]
  have hσx : ∀ C : X → Bool, σ C x = !C x := by intro C; simp [σ]
  let P : (X → Bool) → Prop := fun C => A (fun i => (s i, C (s i))) x ≠ C x
  have hflip : ∀ C, P (σ C) ↔ ¬ P C := by
    intro C
    simp only [P, hlab C, hσx C]
    cases A (fun i => (s i, C (s i))) x <;> cases C x <;> simp
  have hcard : (univ.filter P).card = (univ.filter fun C => ¬ P C).card := by
    rw [card_filter, card_filter]
    rw [← Equiv.sum_comp σ (fun C => if ¬ P C then 1 else 0)]
    apply sum_congr rfl
    intro C _
    simp only [hflip, not_not, P]
  have htot := card_filter_add_card_filter_not (s := (univ : Finset (X → Bool))) P
  rw [card_univ, Fintype.card_fun, Fintype.card_bool] at htot
  show 2 * (univ.filter P).card = 2 ^ Fintype.card X
  omega

/-- Number of points where the hypothesis produced from sample `s` disagrees with `C`. -/
def bad {X : Type*} [Fintype X] [DecidableEq X] {m : ℕ}
    (A : (Fin m → X × Bool) → X → Bool) (C : X → Bool) (s : Fin m → X) : ℕ :=
  (univ.filter fun x => A (fun i => (s i, C (s i))) x ≠ C x).card

theorem sum_bad_ge {X : Type*} [Fintype X] [DecidableEq X] (m : ℕ)
    (hm : Fintype.card X = 2 * m) (A : (Fin m → X × Bool) → X → Bool) (s : Fin m → X) :
    m * 2 ^ Fintype.card X ≤ 2 * ∑ C : X → Bool, bad A C s := by
  classical
  let U : Finset X := univ.filter fun x => ∀ i, s i ≠ x
  have hU : m ≤ U.card := by
    have h1 := card_filter_add_card_filter_not (s := (univ : Finset X))
      (fun x => ∀ i, s i ≠ x)
    have h2 : (univ.filter fun x => ¬ ∀ i, s i ≠ x) ⊆ univ.image s := by
      intro y hy
      simp only [mem_filter, mem_univ, true_and, not_forall, not_not] at hy
      obtain ⟨i, hi⟩ := hy
      exact mem_image.mpr ⟨i, mem_univ _, hi⟩
    have h3 := card_le_card h2
    have h4 : (univ.image s).card ≤ m := by
      calc (univ.image s).card ≤ (univ : Finset (Fin m)).card := card_image_le
        _ = m := by simp
    rw [card_univ, hm] at h1
    show m ≤ (univ.filter fun x => ∀ i, s i ≠ x).card
    omega
  have hswap : ∑ C : X → Bool, bad A C s
      = ∑ x : X, (univ.filter fun C : X → Bool =>
          A (fun i => (s i, C (s i))) x ≠ C x).card := by
    simp only [bad, card_filter]
    exact sum_comm
  rw [hswap, mul_sum]
  calc m * 2 ^ Fintype.card X ≤ ∑ x ∈ U, 2 ^ Fintype.card X := by
        rw [sum_const, smul_eq_mul]
        exact Nat.mul_le_mul_right _ hU
    _ = ∑ x ∈ U, 2 * (univ.filter fun C : X → Bool =>
          A (fun i => (s i, C (s i))) x ≠ C x).card := by
        apply sum_congr rfl
        intro x hx
        simp only [U, mem_filter, mem_univ, true_and] at hx
        rw [half_count m A s x hx]
    _ ≤ ∑ x : X, 2 * (univ.filter fun C : X → Bool =>
          A (fun i => (s i, C (s i))) x ≠ C x).card :=
        sum_le_sum_of_subset (subset_univ _)

theorem exists_good {X : Type*} [Fintype X] [DecidableEq X] (m : ℕ)
    (hm : Fintype.card X = 2 * m) (hm0 : 0 < m) (A : (Fin m → X × Bool) → X → Bool) :
    ∃ C : X → Bool, Fintype.card (Fin m → X) ≤
      10 * (univ.filter fun s : Fin m → X => 2 * m ≤ 10 * bad A C s).card := by
  classical
  set N := Fintype.card (Fin m → X) with hN
  -- averaging over concepts
  have htot : ∑ _C : X → Bool, N * m ≤ ∑ C : X → Bool, 2 * ∑ s : Fin m → X, bad A C s := by
    rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, smul_eq_mul]
    calc 2 ^ Fintype.card X * (N * m) = ∑ _s : Fin m → X, m * 2 ^ Fintype.card X := by
          rw [sum_const, card_univ, smul_eq_mul]; ring
      _ ≤ ∑ s : Fin m → X, 2 * ∑ C : X → Bool, bad A C s :=
          sum_le_sum fun s _ => sum_bad_ge m hm A s
      _ = ∑ C : X → Bool, 2 * ∑ s : Fin m → X, bad A C s := by
          rw [← mul_sum, ← mul_sum, sum_comm]
  obtain ⟨C, -, hC⟩ := exists_le_of_sum_le univ_nonempty htot
  refine ⟨C, ?_⟩
  set G := (univ.filter fun s : Fin m → X => 2 * m ≤ 10 * bad A C s).card with hG
  have hbad_le : ∀ s, bad A C s ≤ 2 * m := by
    intro s
    rw [← hm]
    exact card_le_univ _
  have hpt : ∀ s : Fin m → X,
      10 * bad A C s ≤ 2 * m + 20 * m * (if 2 * m ≤ 10 * bad A C s then 1 else 0) := by
    intro s
    have := hbad_le s
    split_ifs with h <;> omega
  have hsum : 10 * ∑ s : Fin m → X, bad A C s ≤ 2 * m * N + 20 * m * G := by
    rw [mul_sum]
    calc ∑ s : Fin m → X, 10 * bad A C s
        ≤ ∑ s : Fin m → X, (2 * m + 20 * m * (if 2 * m ≤ 10 * bad A C s then 1 else 0)) :=
          sum_le_sum fun s _ => hpt s
      _ = 2 * m * N + 20 * m * G := by
          rw [sum_add_distrib, sum_const, card_univ, smul_eq_mul, ← mul_sum, hG, card_filter]
          ring
  have key : 3 * N * m ≤ 20 * G * m := by nlinarith
  have key2 : 3 * N ≤ 20 * G := Nat.le_of_mul_le_mul_right key hm0
  omega


open OnlineConvexOpt.LearningTheory in
theorem main_dbbda360
    {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (m : ℕ) (hm : Fintype.card X = 2 * m) (hm4 : 4 < 2 * m)
    (A : (Fin m → X × Bool) → X → Bool) :
    ∃ (C : X → Bool) (D : Measure X), IsProbabilityMeasure D ∧
      GeneralizationErrorZeroOne (D.map fun x => (x, C x)) C = 0 ∧
      (1 / 10 : ℝ) ≤
        (Measure.pi (fun _ : Fin m => D)
          {S : Fin m → X | (1 / 10 : ℝ) ≤
            GeneralizationErrorZeroOne (D.map fun x => (x, C x))
              (A (fun i => (S i, C (S i))))}).toReal := by
  classical
  have hm0 : 0 < m := by omega
  have : Nonempty X := by
    apply Fintype.card_pos_iff.mp; omega
  obtain ⟨C, hC⟩ := exists_good m hm hm0 A
  let D : Measure X := ProbabilityTheory.uniformOn Set.univ
  have hDsing : ∀ x : X, D {x} = ((2 * m : ℕ) : ENNReal)⁻¹ := by
    intro x
    simp only [D, ProbabilityTheory.uniformOn_univ, Measure.count_singleton, hm]
    rw [ENNReal.div_eq_inv_mul, mul_one]
  have hDfin : ∀ T : Finset X, D ↑T = (T.card : ENNReal) * ((2 * m : ℕ) : ENNReal)⁻¹ := by
    intro T
    rw [← sum_measure_singleton]
    simp [hDsing]
  -- error of hypothesis h
  have herr : ∀ h : X → Bool, GeneralizationErrorZeroOne (D.map fun x => (x, C x)) h
      = ((univ.filter fun x => h x ≠ C x).card : ℝ) / (2 * m : ℝ) := by
    intro h
    unfold GeneralizationErrorZeroOne
    rw [Measure.map_apply (Measurable.of_discrete) (MeasurableSet.of_discrete)]
    have : ((fun x => (x, C x)) ⁻¹' {p : X × Bool | h p.1 ≠ p.2})
        = ↑(univ.filter fun x => h x ≠ C x) := by
      ext x; simp
    rw [this, hDfin, ENNReal.toReal_mul, ENNReal.toReal_inv]
    simp [div_eq_mul_inv]
  refine ⟨C, D, inferInstance, ?_, ?_⟩
  · rw [herr]; simp
  · set T : Finset (Fin m → X) :=
      univ.filter fun s : Fin m → X => 2 * m ≤ 10 * bad A C s with hT
    have hset : {S : Fin m → X | (1 / 10 : ℝ) ≤
        GeneralizationErrorZeroOne (D.map fun x => (x, C x))
          (A (fun i => (S i, C (S i))))} = ↑T := by
      ext S
      simp only [Set.mem_ofPred_eq, hT, coe_filter, mem_univ, true_and, herr]
      have hpos : (0 : ℝ) < 2 * m := by positivity
      rw [le_div_iff₀ hpos]
      unfold bad
      constructor
      · intro h
        have : ((2 * m : ℕ) : ℝ) ≤ ((10 * (univ.filter fun x =>
            A (fun i => (S i, C (S i))) x ≠ C x).card : ℕ) : ℝ) := by
          push_cast; linarith
        exact_mod_cast this
      · intro h
        have : ((2 * m : ℕ) : ℝ) ≤ ((10 * (univ.filter fun x =>
            A (fun i => (S i, C (S i))) x ≠ C x).card : ℕ) : ℝ) := by exact_mod_cast h
        push_cast at this; linarith
    rw [hset, ← sum_measure_singleton]
    simp only [Measure.pi_singleton, hDsing, prod_const, card_univ, Fintype.card_fin,
      sum_const, nsmul_eq_mul]
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv]
    simp only [ENNReal.toReal_natCast]
    have hN : Fintype.card (Fin m → X) = (2 * m) ^ m := by
      simp [Fintype.card_fun, hm]
    rw [hN] at hC
    have hC' : ((2 * m : ℕ) : ℝ) ^ m ≤ 10 * (T.card : ℝ) := by exact_mod_cast hC
    have hpos : (0 : ℝ) < ((2 * m : ℕ) : ℝ) ^ m := by positivity
    rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ hpos]
    linarith

end NFLAuxDbbda360

open MeasureTheory OnlineConvexOpt.LearningTheory in
theorem solution
    {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (m : ℕ) (hm : Fintype.card X = 2 * m) (hm4 : 4 < 2 * m)
    (A : (Fin m → X × Bool) → X → Bool) :
    ∃ (C : X → Bool) (D : Measure X), IsProbabilityMeasure D ∧
      GeneralizationErrorZeroOne (D.map fun x => (x, C x)) C = 0 ∧
      (1 / 10 : ℝ) ≤
        (Measure.pi (fun _ : Fin m => D)
          {S : Fin m → X | (1 / 10 : ℝ) ≤
            GeneralizationErrorZeroOne (D.map fun x => (x, C x))
              (A (fun i => (S i, C (S i))))}).toReal := by
  exact NFLAuxDbbda360.main_dbbda360 m hm hm4 A
