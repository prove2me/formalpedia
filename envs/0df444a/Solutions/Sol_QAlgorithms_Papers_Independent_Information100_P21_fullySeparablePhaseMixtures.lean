-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P21.fullySeparablePhaseMixtures
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T03:54:37.561005+00:00
-- url     : https://prove2.me/submissions/8141a440-0d25-4a92-aebe-489f8e904854

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

abbrev x8ω (t : ZMod 6) : ℂ := (ZMod.stdAddChar t : ℂ)

lemma x8ω_conj (x : ZMod 6) : conj (x8ω x) = x8ω (-x) := by
  simp only [x8ω]
  rw [AddChar.map_neg_eq_inv, ZMod.stdAddChar_apply, ← Circle.coe_inv_eq_conj, Circle.coe_inv]

lemma x8ω_norm (x : ZMod 6) : ‖x8ω x‖ = 1 := by
  simp only [x8ω, ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

lemma x8ω_esum (c : ZMod 6) :
    ∑ x : ZMod 6, x8ω (x * c) = if c = 0 then (6 : ℂ) else 0 := by
  rw [AddChar.sum_mulShift c (ZMod.isPrimitive_stdAddChar 6), ZMod.card]
  split_ifs <;> simp

lemma x8ω_three : x8ω 3 = -1 := by
  have h : ((3 : ℕ) : ZMod 6) = 3 := rfl
  rw [x8ω, ← h, ZMod.stdAddChar_apply, ZMod.toCircle_natCast]
  have : (2 * (Real.pi : ℂ) * Complex.I * ((3 : ℕ) : ℂ) / ((6 : ℕ) : ℂ)) =
      Real.pi * Complex.I := by push_cast; ring
  rw [this]
  exact Complex.exp_pi_mul_I

lemma x8ω_add (a b : ZMod 6) : x8ω (a + b) = x8ω a * x8ω b := AddChar.map_add_eq_mul _ _ _

lemma x8ω_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 6) :
    x8ω (∑ i ∈ s, f i) = ∏ i ∈ s, x8ω (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [x8ω]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, x8ω,
      AddChar.map_add_eq_mul, ← ih]

/-- one-qubit phase ket `(|0⟩ + ω^a |1⟩)/√2`. -/
def x8ψ (a : ZMod 6) : Vec (Fin 2) :=
  WithLp.toLp 2 fun b => x8ω (a * ((b.val : ℕ) : ZMod 6)) / (Real.sqrt 2 : ℂ)

lemma x8ψ_norm (a : ZMod 6) : ‖x8ψ a‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp only [x8ψ, Fin.sum_univ_two, norm_div, x8ω_norm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 2)]
  rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

lemma x8ψ_pair (a : ZMod 6) (b c : Fin 2) :
    x8ψ a b * conj (x8ψ a c) =
      x8ω (a * (((b.val : ℕ) : ZMod 6) - ((c.val : ℕ) : ZMod 6))) / 2 := by
  simp only [x8ψ, map_div₀, x8ω_conj, Complex.conj_ofReal]
  rw [div_mul_div_comm, ← AddChar.map_add_eq_mul, mul_sub, sub_eq_add_neg]
  congr 1
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

lemma x8_entry {n : ℕ} (φ : Fin n → ZMod 6) (x y : Fin n → Fin 2) :
    proj (productKet (d := fun _ : Fin n => 2) (fun j => x8ψ (φ j))) x y =
      x8ω (∑ j, φ j * (((x j).val : ℕ) - ((y j).val : ℕ) : ZMod 6)) / 2 ^ n := by
  simp only [proj, QAlgorithms.pureDensity, Matrix.of_apply, productKet, map_prod]
  rw [← Finset.prod_mul_distrib]
  simp only [x8ψ_pair]
  rw [Finset.prod_div_distrib, x8ω_sum]
  simp

end QAlgorithms.Papers.Independent.Information100.P21
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

def x8φ {n : ℕ} (j0 : Fin n) (s : ZMod 6) (k : Fin n → ZMod 6) (j : Fin n) : ZMod 6 :=
  k j - if j = j0 then (∑ i, k i - s) else 0

lemma x8_avg {n : ℕ} (j0 : Fin n) (s : ZMod 6) (m : Fin n → ZMod 6) :
    ∑ k : Fin n → ZMod 6, x8ω (∑ j, x8φ j0 s k j * m j) =
      if ∀ j, m j = m j0 then 6 ^ n * x8ω (s * m j0) else 0 := by
  have e : ∀ k : Fin n → ZMod 6, ∑ j, x8φ j0 s k j * m j =
      ∑ j, k j * (m j - m j0) + s * m j0 := by
    intro k
    simp only [x8φ, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, mul_sub, Finset.sum_mul]
    ring
  simp_rw [e, x8ω_add, x8ω_sum]
  rw [← Finset.sum_mul]
  have hsw := Finset.sum_prod_piFinset (Finset.univ : Finset (ZMod 6))
    (fun j t => x8ω (t * (m j - m j0)))
  simp only [Fintype.piFinset_univ] at hsw
  rw [hsw]
  simp only [x8ω_esum, sub_eq_zero]
  split_ifs with h
  · rw [Finset.prod_eq_pow_card (b := (6 : ℂ)) (fun j _ => if_pos (h j))]
    simp
  · push Not at h
    obtain ⟨j, hj⟩ := h
    rw [Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj), zero_mul]

end QAlgorithms.Papers.Independent.Information100.P21
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

lemma x8_ghzC {n : ℕ} (x y : Fin n → Fin 2) :
    ghzC n x y = (if x = (fun _ => 0) ∧ y = (fun _ => 1) then 1 else 0) +
      (if x = (fun _ => 1) ∧ y = (fun _ => 0) then 1 else 0) := by
  simp only [ghzC, constantKet, QAlgorithms.ket, PiLp.single_apply, Bool.false_eq_true,
    if_false, if_true]
  split_ifs <;> simp_all

lemma x8_fin (a b c d : Fin 2)
    (h : ((a.val : ℕ) : ZMod 6) - ((b.val : ℕ) : ZMod 6) = ((c.val : ℕ) : ZMod 6) - ((d.val : ℕ) : ZMod 6)) :
    (a = b ↔ c = d) ∧ (a ≠ b → a = c ∧ b = d) := by
  revert a b c d; decide

lemma x8_comb {n : ℕ} (j0 : Fin n) (s : ZMod 6) (sg : ℂ) (hs1 : x8ω s = sg)
    (hs2 : x8ω (-s) = sg) (x y : Fin n → Fin 2) :
    (if ∀ j, ((x j).val : ZMod 6) - ((y j).val : ℕ) = ((x j0).val : ZMod 6) - ((y j0).val : ℕ)
      then x8ω (s * (((x j0).val : ZMod 6) - ((y j0).val : ℕ))) else 0) =
      (if x = y then 1 else 0) + sg * ghzC n x y := by
  have h01 : (fun _ : Fin n => (0 : Fin 2)) ≠ (fun _ => 1) := by
    intro h; have := congrFun h j0; simp at this
  rw [x8_ghzC]
  by_cases hxy : x = y
  · subst hxy
    have A : ¬ (x = (fun _ => 0) ∧ x = (fun _ => 1)) := fun h => h01 (h.1.symm.trans h.2)
    have B : ¬ (x = (fun _ => 1) ∧ x = (fun _ => 0)) := fun h => h01 (h.2.symm.trans h.1)
    rw [if_pos (fun j => by simp), if_pos rfl, if_neg A, if_neg B]
    simp [x8ω]
  rw [if_neg hxy, zero_add]
  by_cases h1 : x = (fun _ => 0) ∧ y = (fun _ => 1)
  · obtain ⟨rfl, rfl⟩ := h1
    rw [if_pos (fun j => rfl), if_pos ⟨rfl, rfl⟩, if_neg (fun h => h01 h.2.symm)]
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, zero_sub,
      mul_neg, mul_one, hs2]
    ring
  by_cases h2 : x = (fun _ => 1) ∧ y = (fun _ => 0)
  · obtain ⟨rfl, rfl⟩ := h2
    rw [if_pos (fun j => rfl), if_neg h1, if_pos ⟨rfl, rfl⟩]
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, sub_zero,
      mul_one, hs1]
    ring
  rw [if_neg h1, if_neg h2, add_zero, mul_zero, if_neg]
  intro hall
  obtain ⟨j1, hj1⟩ := Function.ne_iff.mp hxy
  have hne : x j0 ≠ y j0 := fun h => hj1 (((x8_fin _ _ _ _ (hall j1)).1).mpr h)
  have hc : ∀ j, x j = x j0 ∧ y j = y j0 := fun j => by
    have := x8_fin _ _ _ _ (hall j)
    exact this.2 (fun h => hne (this.1.mp h))
  have hx : x = fun _ => x j0 := funext fun j => (hc j).1
  have hy : y = fun _ => y j0 := funext fun j => (hc j).2
  have key : (x j0 = 0 ∧ y j0 = 1) ∨ (x j0 = 1 ∧ y j0 = 0) := by
    revert hne; generalize x j0 = a; generalize y j0 = b; revert a b; decide
  rcases key with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact h1 ⟨by rw [hx, ha], by rw [hy, hb]⟩
  · exact h2 ⟨by rw [hx, ha], by rw [hy, hb]⟩

theorem x8_repr {n : ℕ} (j0 : Fin n) (plus : Bool) :
    phaseMixture n plus = ∑ k : Fin n → ZMod 6, ((6 : ℝ) ^ n)⁻¹ •
      proj (productKet (d := fun _ : Fin n => 2)
        (fun j => x8ψ (x8φ j0 (if plus then 0 else 3) k j))) := by
  have hs1 : x8ω (if plus then 0 else 3) = (if plus then 1 else (-1 : ℂ)) := by
    cases plus
    · simpa using x8ω_three
    · simp [x8ω]
  have hs2 : x8ω (-(if plus then 0 else 3)) = (if plus then 1 else (-1 : ℂ)) := by
    cases plus
    · simp only [Bool.false_eq_true, if_false]
      rw [show -(3 : ZMod 6) = 3 by decide]; exact x8ω_three
    · simp [x8ω]
  ext x y
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, x8_entry, Complex.real_smul]
  rw [← Finset.mul_sum, ← Finset.sum_div, x8_avg]
  have hc := x8_comb j0 _ _ hs1 hs2 x y
  simp only [phaseMixture, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Matrix.one_apply]
  rw [← hc]
  split_ifs <;> push_cast <;> field_simp <;> simp

end QAlgorithms.Papers.Independent.Information100.P21
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

theorem x8_mem {n : ℕ} (hn : 2 ≤ n) (plus : Bool) :
    phaseMixture n plus ∈ fs (fun _ : Fin n => 2) := by
  rw [x8_repr (⟨0, by omega⟩ : Fin n) plus]
  refine (convex_convexHull ℝ _).sum_mem (fun _ _ => by positivity) ?_ ?_
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast
    field_simp
  · intro k _
    exact subset_convexHull ℝ _ ⟨_, fun j => x8ψ_norm _, rfl⟩

end QAlgorithms.Papers.Independent.Information100.P21

open QAlgorithms.Papers.Independent.Information100.P21 in
attribute [local instance] Classical.propDecidable Classical.decEq in
theorem solution (n : ℕ) (hn : 2≤n) :
  phaseMixture n true ∈ fs (fun _ : Fin n => 2) ∧
    phaseMixture n false ∈ fs (fun _ : Fin n => 2) :=
  ⟨QAlgorithms.Papers.Independent.Information100.P21.x8_mem hn true,
    QAlgorithms.Papers.Independent.Information100.P21.x8_mem hn false⟩
