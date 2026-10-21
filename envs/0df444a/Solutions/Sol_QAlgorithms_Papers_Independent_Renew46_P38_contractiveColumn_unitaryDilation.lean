-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P38.contractiveColumn_unitaryDilation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T23:38:23.225188+00:00
-- url     : https://prove2.me/submissions/770b7838-b48f-40f9-bcc0-d4bd3e465ed0

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P38
noncomputable section

section
variable {A : Type*} [Ring A] [StarRing A] {n : ℕ}

def g64e_W (a : Fin n → A) (g : A) (i j : Fin n) : A :=
  (if i = j then 1 else 0) - a i * g * star (a j)

def g64e_U (a : Fin n → A) (g d : A) : Matrix (Option (Fin n)) (Option (Fin n)) A
  | some i, some j => g64e_W a g i j
  | some i, none => a i
  | none, some j => -star (a j)
  | none, none => d

theorem g64e_sumS (a : Fin n → A) (x y : A) :
    ∑ k, x * star (a k) * (a k * y) = x * (∑ k, star (a k) * a k) * y := by
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [mul_assoc]

theorem g64e_U_unitary (a : Fin n → A) (g d : A) (hg : star g = g) (hd : star d = d)
    (h1 : (∑ k, star (a k) * a k) + d * d = 1)
    (h2 : (∑ k, star (a k) * a k) * g = 1 - d)
    (h3 : g * (∑ k, star (a k) * a k) = 1 - d)
    (h4 : (1 + d) * g = 1) :
    star (g64e_U a g d) * g64e_U a g d = 1 ∧ g64e_U a g d * star (g64e_U a g d) = 1 := by
  have hWs : ∀ i k, star (g64e_W a g i k) = g64e_W a g k i := by
    intro i k
    unfold g64e_W
    rw [star_sub, star_mul, star_mul, star_star, hg, ← mul_assoc]
    congr 1
    by_cases h : i = k
    · subst h; simp
    · simp [h, Ne.symm h]
  have LW : ∀ i j, (∑ k, g64e_W a g i k * g64e_W a g k j) + a i * star (a j) =
      if i = j then 1 else 0 := by
    intro i j
    have : ∀ k, g64e_W a g i k * g64e_W a g k j =
        ((if i = k then 1 else 0) * (if k = j then 1 else 0)) - (if i = k then a k * g * star (a j) else 0)
        - (if k = j then a i * g * star (a k) else 0) + (a i * g) * star (a k) * (a k * (g * star (a j))) := by
      intro k
      unfold g64e_W
      split_ifs <;> subst_vars <;> noncomm_ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, g64e_sumS, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hgSg : g * (∑ k, star (a k) * a k) * g = g + g - 1 := by
      rw [h3]
      have : d * g = 1 - g := by rw [← h4]; noncomm_ring
      calc (1 - d) * g = g - d * g := by noncomm_ring
        _ = g + g - 1 := by rw [this]; noncomm_ring
    have e : a i * g * (∑ k, star (a k) * a k) * (g * star (a j)) =
        a i * (g * (∑ k, star (a k) * a k) * g) * star (a j) := by noncomm_ring
    rw [e, hgSg]
    split_ifs with h
    · subst h; noncomm_ring
    · noncomm_ring
  have Lw1 : ∀ i, ∑ k, g64e_W a g i k * a k = a i * d := by
    intro i
    simp only [g64e_W, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    have : ∑ k, a i * g * star (a k) * a k = a i * g * (∑ k, star (a k) * a k) := by
      rw [Finset.mul_sum]; simp only [mul_assoc]
    rw [this, mul_assoc, h3]; noncomm_ring
  have Lw2 : ∀ j, ∑ k, star (a k) * g64e_W a g k j = d * star (a j) := by
    intro j
    simp only [g64e_W, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    have : ∑ k, star (a k) * (a k * g * star (a j)) = (∑ k, star (a k) * a k) * g * star (a j) := by
      rw [Finset.sum_mul, Finset.sum_mul]; simp only [mul_assoc]
    rw [this, h2]; noncomm_ring
  constructor
  · ext x y
    rw [Matrix.mul_apply, Fintype.sum_option]
    simp only [Matrix.star_apply]
    rcases x with _ | i <;> rcases y with _ | j
    · simp only [g64e_U, hd, Matrix.one_apply_eq]
      rw [add_comm]; exact h1
    · simp only [g64e_U, hd, Matrix.one_apply, reduceCtorEq, if_false]
      rw [Lw2, mul_neg, neg_add_cancel]
    · simp only [g64e_U, hWs, star_neg, star_star, Matrix.one_apply, reduceCtorEq, if_false]
      rw [Lw1, neg_mul, neg_add_cancel]
    · simp only [g64e_U, hWs, star_neg, star_star, neg_mul_neg, Matrix.one_apply, Option.some.injEq]
      rw [add_comm, LW]
  · ext x y
    rw [Matrix.mul_apply, Fintype.sum_option]
    simp only [Matrix.star_apply]
    rcases x with _ | i <;> rcases y with _ | j
    · simp only [g64e_U, hd, Matrix.one_apply_eq, star_neg, star_star, neg_mul_neg]
      rw [add_comm]; exact h1
    · simp only [g64e_U, hWs, star_neg, star_star, neg_mul, Matrix.one_apply, reduceCtorEq,
        if_false, Finset.sum_neg_distrib]
      rw [Lw2, add_neg_cancel]
    · simp only [g64e_U, hd, star_neg, star_star, mul_neg, Matrix.one_apply, reduceCtorEq,
        if_false, Finset.sum_neg_distrib]
      rw [Lw1, add_neg_cancel]
    · simp only [g64e_U, hWs, Matrix.one_apply, Option.some.injEq]
      rw [add_comm, LW]
end


section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem g64e_cfc_facts (y : A) (hy : 0 ≤ y) :
    star (cfc Real.sqrt y) = cfc Real.sqrt y ∧
    star (cfc (fun t => (1 + Real.sqrt t)⁻¹) y) = cfc (fun t => (1 + Real.sqrt t)⁻¹) y ∧
    cfc Real.sqrt y * cfc Real.sqrt y = y ∧
    (1 - y) * cfc (fun t => (1 + Real.sqrt t)⁻¹) y = 1 - cfc Real.sqrt y ∧
    cfc (fun t => (1 + Real.sqrt t)⁻¹) y * (1 - y) = 1 - cfc Real.sqrt y ∧
    (1 + cfc Real.sqrt y) * cfc (fun t => (1 + Real.sqrt t)⁻¹) y = 1 ∧
    cfc (fun t => (1 + Real.sqrt t)⁻¹) y * (1 + cfc Real.sqrt y) = 1 := by
  have hsa : IsSelfAdjoint y := IsSelfAdjoint.of_nonneg hy
  have hspec : ∀ t ∈ spectrum ℝ y, 0 ≤ t := fun t ht => spectrum_nonneg_of_nonneg hy ht
  have hgc : Continuous (fun t : ℝ => (1 + Real.sqrt t)⁻¹) :=
    Continuous.inv₀ (by fun_prop) (fun t => by positivity)
  have hgc' : ContinuousOn (fun t : ℝ => (1 + Real.sqrt t)⁻¹) (spectrum ℝ y) := hgc.continuousOn
  have hsc : ContinuousOn Real.sqrt (spectrum ℝ y) := Real.continuous_sqrt.continuousOn
  have h1y : (1 : A) - y = cfc (fun t : ℝ => 1 - t) y := by
    have := cfc_sub (a := y) (f := fun _ : ℝ => (1:ℝ)) (g := fun t : ℝ => t)
    rw [this, cfc_const_one ℝ y, cfc_id' ℝ y]
  have h1d : (1 : A) - cfc Real.sqrt y = cfc (fun t : ℝ => 1 - Real.sqrt t) y := by
    have := cfc_sub (a := y) (f := fun _ : ℝ => (1:ℝ)) (g := Real.sqrt) (hg := hsc)
    rw [this, cfc_const_one ℝ y]
  have hpd : (1 : A) + cfc Real.sqrt y = cfc (fun t : ℝ => 1 + Real.sqrt t) y := by
    have := cfc_add (a := y) (fun _ : ℝ => (1:ℝ)) Real.sqrt (hg := hsc)
    rw [this, cfc_const_one ℝ y]
  have sd : IsSelfAdjoint (cfc Real.sqrt y) := cfc_predicate _ _
  have sg : IsSelfAdjoint (cfc (fun t => (1 + Real.sqrt t)⁻¹) y) := cfc_predicate _ _
  refine ⟨sd.star_eq, sg.star_eq, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← cfc_mul Real.sqrt Real.sqrt y hsc hsc]
    conv_rhs => rw [← cfc_id' ℝ y]
    exact cfc_congr fun t ht => Real.mul_self_sqrt (hspec t ht)
  · rw [h1y, ← cfc_mul (fun t : ℝ => 1 - t) (fun t : ℝ => (1 + Real.sqrt t)⁻¹) y (hg := hgc'), h1d]
    refine cfc_congr fun t ht => ?_
    have h0 := hspec t ht
    have hs := Real.mul_self_sqrt h0
    have : 0 < 1 + Real.sqrt t := by positivity
    field_simp; nlinarith
  · rw [h1y, ← cfc_mul (fun t : ℝ => (1 + Real.sqrt t)⁻¹) (fun t : ℝ => 1 - t) y (hf := hgc'), h1d]
    refine cfc_congr fun t ht => ?_
    have h0 := hspec t ht
    have hs := Real.mul_self_sqrt h0
    have : 0 < 1 + Real.sqrt t := by positivity
    field_simp; nlinarith
  · rw [hpd, ← cfc_mul (fun t : ℝ => 1 + Real.sqrt t) (fun t : ℝ => (1 + Real.sqrt t)⁻¹) y (hg := hgc'),
      ← cfc_const_one ℝ y]
    refine cfc_congr fun t ht => ?_
    have : 0 < 1 + Real.sqrt t := by positivity
    field_simp
  · rw [hpd, ← cfc_mul (fun t : ℝ => (1 + Real.sqrt t)⁻¹) (fun t : ℝ => 1 + Real.sqrt t) y (hf := hgc'),
      ← cfc_const_one ℝ y]
    refine cfc_congr fun t ht => ?_
    have : 0 < 1 + Real.sqrt t := by positivity
    field_simp
end



open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal

open QAlgorithms.Papers.Independent.Renew46.P38

universe u

/-- Hansen--Pedersen, §3, PDF p. 5, unitary dilation of a contractive column.
The last entry is computed by the positive square root, not supplied as extra data. -/
theorem solution (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (n : ℕ) (hn : 1 ≤ n)
    (a : Fin n → Operators H) (ha : columnSquares a ≤ 1) :
    IsUnitaryColumn (dilatedColumn a) ∧
      (columnSquares a = 1 → dilatedColumn a none = 0) := by
  have hy : (0 : Operators H) ≤ 1 - columnSquares a := sub_nonneg.mpr ha
  obtain ⟨hd, hg, hdd, h2, h3, h4, -⟩ := g64e_cfc_facts _ hy
  have hS1 : (1 : Operators H) - (1 - columnSquares a) = ∑ k, star (a k) * a k := by
    rw [sub_sub_cancel]; rfl
  rw [hS1] at h2 h3
  have h1 : (∑ k, star (a k) * a k) + cfc Real.sqrt (1 - columnSquares a) *
      cfc Real.sqrt (1 - columnSquares a) = 1 := by
    rw [hdd, ← hS1]; abel
  have hU := g64e_U_unitary a _ _ hg hd h1 h2 h3 h4
  refine ⟨⟨g64e_U a (cfc (fun t => (1 + Real.sqrt t)⁻¹) (1 - columnSquares a))
    (cfc Real.sqrt (1 - columnSquares a)), ⟨hU.1, hU.2⟩, none, fun i => ?_⟩, fun h => ?_⟩
  · rcases i with _ | i <;> rfl
  · simp [dilatedColumn, h, cfc_apply_zero]


end
