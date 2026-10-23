-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P37.classicalRelativeEntropy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T11:36:10.575313+00:00
-- url     : https://prove2.me/submissions/e09dfd19-64bb-4ba3-a59e-51fd9533fb70

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P37

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace X7P37ClassKL

open QAlgorithms.Papers.Independent.Renew46.P37
open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)
open QAlgorithms.Papers.Independent.Claimed50.P33 (singleParties allParties)

variable {n : ℕ}

/-- Marginalisation: summing a function of one coordinate against the joint law. -/
lemma marg_sum (p : CData n) (i : Fin n) (f : Fin (p.dims i) → ℝ) :
    ∑ x, p.prob x * f (x i) = ∑ a, localLaw p i a * f a := by
  simp only [localLaw, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_eq_single (x i)]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

lemma localLaw_sum (p : CData n) (hp : IsValidClassicalData p) (i : Fin n) :
    ∑ a, localLaw p i a = 1 := by
  have := marg_sum p i (fun _ => 1)
  simp only [mul_one] at this
  rw [← this]; exact hp.2.2

lemma localLaw_nonneg (p : CData n) (hp : IsValidClassicalData p) (i : Fin n) (a) :
    0 ≤ localLaw p i a :=
  Finset.sum_nonneg (fun x _ => by split_ifs <;> [exact hp.2.1 x; exact le_rfl])

lemma le_localLaw (p : CData n) (hp : IsValidClassicalData p) (x) (i : Fin n) :
    p.prob x ≤ localLaw p i (x i) := by
  unfold localLaw
  have := Finset.single_le_sum (f := fun y => if y i = x i then p.prob y else 0)
    (fun y _ => by dsimp only; split_ifs <;> [exact hp.2.1 y; exact le_rfl]) (Finset.mem_univ x)
  simpa using this

/-- The finite KL sum against a product law, when no support failure occurs. -/
lemma kl_sum (p : CData n) (hp : IsValidClassicalData p) (q : (i : Fin n) → Fin (p.dims i) → ℝ)
    (hq : ∀ x, 0 < p.prob x → ∀ i, q i (x i) ≠ 0) :
    (∑ x, if p.prob x = 0 then 0 else p.prob x * Real.logb 2 (p.prob x / productLaw q x)) =
      ∑ x, p.prob x * Real.logb 2 (p.prob x) -
        ∑ i, ∑ a, localLaw p i a * Real.logb 2 (q i a) := by
  have h1 : ∀ i, ∑ a, localLaw p i a * Real.logb 2 (q i a) =
      ∑ x, p.prob x * Real.logb 2 (q i (x i)) := fun i =>
    (marg_sum p i (fun a => Real.logb 2 (q i a))).symm
  simp only [h1]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← Finset.mul_sum, ← mul_sub]
  split_ifs with h0
  · simp [h0]
  · have hpos : 0 < p.prob x := lt_of_le_of_ne (hp.2.1 x) (Ne.symm h0)
    have hQ : productLaw q x ≠ 0 := Finset.prod_ne_zero_iff.2 (fun i _ => hq x hpos i)
    congr 1
    rw [Real.logb_div h0 hQ]
    congr 1
    simp only [productLaw, Real.logb]
    rw [Real.log_prod (fun i _ => hq x hpos i), Finset.sum_div]

/-- Gibbs' inequality for one party. -/
lemma gibbs {m : ℕ} (P q : Fin m → ℝ) (hP : ∀ a, 0 ≤ P a) (hq : ∀ a, 0 ≤ q a)
    (hsP : ∑ a, P a = 1) (hsq : ∑ a, q a = 1) (hsupp : ∀ a, 0 < P a → q a ≠ 0) :
    ∑ a, P a * Real.logb 2 (q a) ≤ ∑ a, P a * Real.logb 2 (P a) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have key : ∀ a, P a - q a ≤ P a * Real.log (P a) - P a * Real.log (q a) := by
    intro a
    rcases eq_or_lt_of_le (hP a) with h | h
    · rw [← h]; simp [hq a]
    · have hqa : 0 < q a := lt_of_le_of_ne (hq a) (Ne.symm (hsupp a h))
      have := Real.log_le_sub_one_of_pos (div_pos hqa h)
      rw [Real.log_div hqa.ne' h.ne'] at this
      have h2 := mul_le_mul_of_nonneg_left this h.le
      have e : P a * (q a / P a - 1) = q a - P a := by field_simp
      rw [e] at h2
      nlinarith
  have hs := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => key a)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hsP, hsq, sub_self] at hs
  simp only [Real.logb, mul_div_assoc']
  rw [← Finset.sum_div, ← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ hl2.le
  linarith

lemma shannon_eq_of_bij {X Y : Type} [Fintype X] [Fintype Y] (f : X → ℝ) (g : Y → ℝ) (φ : X → Y)
    (hφ : Function.Bijective φ) (h : ∀ x, f x = g (φ x)) : shannon f = shannon g := by
  unfold shannon
  congr 1
  rw [← hφ.sum_comp (fun y => g y * Real.logb 2 (g y))]
  exact Finset.sum_congr rfl (fun x _ => by rw [h])

lemma cH_single (p : CData n) (i : Fin n) : cH p {i} = shannon (localLaw p i) := by
  unfold cH
  refine shannon_eq_of_bij _ _ (fun g => g ⟨i, Finset.mem_singleton_self i⟩) ⟨?_, ?_⟩ ?_
  · intro g g' h
    funext j
    obtain ⟨j, hj⟩ := j
    rw [Finset.mem_singleton] at hj
    subst hj
    exact h
  · intro a
    refine ⟨fun j => Fin.cast (congrArg p.dims (Finset.mem_singleton.1 j.2)).symm a, ?_⟩
    rfl
  · intro g
    unfold lawMarginal localLaw
    refine Finset.sum_congr rfl (fun x _ => ?_)
    have : (∀ j : {j // j ∈ ({i} : Finset (Fin n))}, x j.val = g j) ↔
        x i = g ⟨i, Finset.mem_singleton_self i⟩ := by
      constructor
      · intro h; exact h ⟨i, Finset.mem_singleton_self i⟩
      · intro h j
        obtain ⟨j, hj⟩ := j
        rw [Finset.mem_singleton] at hj
        subst hj
        exact h
    simp only [this]

lemma cH_univ (p : CData n) : cH p Finset.univ = shannon p.prob := by
  unfold cH
  refine shannon_eq_of_bij _ _ (fun g i => g ⟨i, Finset.mem_univ i⟩) ⟨?_, ?_⟩ ?_
  · intro g g' h
    funext j
    exact congrFun h j.val
  · intro x
    exact ⟨fun j => x j.val, rfl⟩
  · intro g
    unfold lawMarginal
    rw [Finset.sum_eq_single (fun i => g ⟨i, Finset.mem_univ i⟩)]
    · simp
    · intro y _ hy
      rw [if_neg]
      intro h
      apply hy
      funext i
      exact h ⟨i, Finset.mem_univ i⟩
    · simp

lemma total_eq (p : CData n) :
    cValue .total p = ∑ i, shannon (localLaw p i) - shannon p.prob := by
  unfold cValue cInfo
  have : allParties (singleParties n) = Finset.univ := by
    ext i; simp [allParties, singleParties]
  rw [this, cH_univ]
  simp only [singleParties, cH_single]

lemma total_formula (p : CData n) :
    cValue .total p = ∑ x, p.prob x * Real.logb 2 (p.prob x) -
      ∑ i, ∑ a, localLaw p i a * Real.logb 2 (localLaw p i a) := by
  rw [total_eq]
  simp only [shannon, Finset.sum_neg_distrib]
  ring

end X7P37ClassKL


open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)
open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

open QAlgorithms.Papers.Independent.Renew46.P37 X7P37ClassKL in
theorem solution {n : ℕ} (hn : 2 ≤ n) (p : CData n) (hp : IsValidClassicalData p) :
    classicalKL p.prob (productLaw (localLaw p)) = ENNReal.ofReal (cValue .total p) ∧
    ∀ q : (i : Fin n) → Fin (p.dims i) → ℝ,
      (∀ i, IsLaw (q i)) →
      ENNReal.ofReal (cValue .total p) ≤ classicalKL p.prob (productLaw q) := by
  constructor
  · have hsupp : ∀ x, 0 < p.prob x → ∀ i, localLaw p i (x i) ≠ 0 := fun x hx i =>
      (lt_of_lt_of_le hx (le_localLaw p hp x i)).ne'
    unfold classicalKL
    rw [if_neg]
    · rw [kl_sum p hp _ hsupp, total_formula]
    · rintro ⟨x, hx, h0⟩
      exact Finset.prod_ne_zero_iff.2 (fun i _ => hsupp x hx i) h0
  · intro q hq
    unfold classicalKL
    split_ifs with h
    · exact le_top
    · push Not at h
      have hsupp : ∀ x, 0 < p.prob x → ∀ i, q i (x i) ≠ 0 := fun x hx i =>
        (Finset.prod_ne_zero_iff.1 (h x hx)) i (Finset.mem_univ i)
      rw [kl_sum p hp q hsupp, total_formula]
      apply ENNReal.ofReal_le_ofReal
      have hg : ∀ i, ∑ a, localLaw p i a * Real.logb 2 (q i a) ≤
          ∑ a, localLaw p i a * Real.logb 2 (localLaw p i a) := by
        intro i
        refine gibbs _ _ (localLaw_nonneg p hp i) (hq i).1 (localLaw_sum p hp i) (hq i).2 ?_
        intro a ha
        unfold localLaw at ha
        by_contra hcon
        have hz : (∑ x, if x i = a then p.prob x else 0) = 0 := by
          refine Finset.sum_eq_zero (fun x _ => ?_)
          split_ifs with hxi
          · by_contra hne
            have hpos : 0 < p.prob x := lt_of_le_of_ne (hp.2.1 x) (Ne.symm hne)
            exact (hxi ▸ hsupp x hpos i) hcon
          · rfl
        linarith
      have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hg i)
      linarith
