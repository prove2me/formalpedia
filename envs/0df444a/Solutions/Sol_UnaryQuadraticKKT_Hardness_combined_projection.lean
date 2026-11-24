-- Prove2me | solution 1 for UnaryQuadraticKKT.Hardness.combined_projection
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T18:19:46.758828+00:00
-- url     : https://prove2.me/submissions/43611135-983c-4f99-adc7-356a1b44121e

import Mathlib
import Definitions.Def_UnaryQuadraticKKT_Hardness_Combined
import Theorems.Thm_UnaryQuadraticKKT_Hardness_chain_unique
import Theorems.Thm_UnaryQuadraticKKT_Hardness_normalization_dyadic

set_option autoImplicit false

namespace UQKKTProjectionAux
open Finset UnaryQuadraticKKT.Hardness NetworkEquilibriumCLS.LinearNash

/-! ### List sums -/

theorem list_sum_map_filter {α : Type*} (l : List α) (q : α → Bool) (g : α → ℝ) :
    ((l.filter q).map g).sum = (l.map fun a => if q a then g a else 0).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : q a
    · simp [List.filter_cons, h, ih]
    · simp [List.filter_cons, h, ih]

theorem list_sum_finRange {m : ℕ} (f : Fin m → ℝ) :
    ((List.finRange m).map f).sum = ∑ i, f i := (Fin.sum_univ_def f).symm

theorem sum_map_flatMap {α β : Type*} (l : List α) (f : α → List β) (F : β → ℝ) :
    ((l.flatMap f).map F).sum = (l.map fun a => ((f a).map F).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

/-! ### The monomial slots and the source gradient -/

theorem slots_sum {n : ℕ} (F : Monomial n → ℝ) :
    ((slots n).map F).sum =
      ∑ a : Fin n, ∑ b : Fin n, (if a ≤ b then F (.quadratic a b) else 0) +
        ∑ a : Fin n, F (.linear a) := by
  unfold slots
  rw [List.map_append, List.sum_append, sum_map_flatMap, list_sum_finRange, List.map_map,
    list_sum_finRange]
  congr 1
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [List.map_map, list_sum_map_filter, list_sum_finRange]
  simp [Function.comp]

/-- The partial derivative in `x_i` of the monomial of slot `t`. -/
noncomputable def slotGrad {n : ℕ} (x : Fin n → ℝ) (i : Fin n) (t : Monomial n) : ℝ :=
  (if (factors t).1 = some i then factorValue (factors t).2 x else 0) +
    (if (factors t).2 = some i then factorValue (factors t).1 x else 0)

theorem slots_gradient {n : ℕ} (q : Quadratic n) (x : Fin n → ℝ) (i : Fin n) :
    ((slots n).map fun t => (coefficient q t : ℝ) * slotGrad x i t).sum =
      sourceGradient q x i := by
  rw [slots_sum]
  have hlin : ∑ a : Fin n, (coefficient q (.linear a) : ℝ) * slotGrad x i (.linear a)
      = (q.c i : ℝ) := by
    simp [coefficient, slotGrad, factors, factorValue]
  set c : Fin n → Fin n → ℝ := fun a b => (coefficient q (.quadratic a b) : ℝ) with hc
  have hterm : ∀ a b : Fin n,
      (if a ≤ b then (coefficient q (.quadratic a b) : ℝ) * slotGrad x i (.quadratic a b) else 0)
        = (if a = i then (if i ≤ b then c i b * x b else 0) else 0) +
          (if b = i then (if a ≤ i then c a i * x a else 0) else 0) := by
    intro a b
    by_cases h1 : a = i <;> by_cases h2 : b = i
    · subst h1; subst h2; simp [slotGrad, factors, factorValue, hc]; try ring
    · subst h1; simp [slotGrad, factors, factorValue, hc, h2]
    · subst h2; simp [slotGrad, factors, factorValue, hc, h1]
    · simp [slotGrad, factors, factorValue, hc, h1, h2]
  have hq : ∑ a : Fin n, ∑ b : Fin n,
      (if a ≤ b then (coefficient q (.quadratic a b) : ℝ) * slotGrad x i (.quadratic a b) else 0)
      = ∑ b : Fin n, (if i ≤ b then c i b * x b else 0) +
        ∑ a : Fin n, (if a ≤ i then c a i * x a else 0) := by
    simp only [hterm, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_comm]; simp
    · simp
  rw [hq, hlin, sourceGradient, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rcases lt_trichotomy i j with h | rfl | h
  · simp [hc, coefficient, h.le, not_le.2 h, h.ne]
  · simp [hc, coefficient]; ring
  · simp [hc, coefficient, h.le, not_le.2 h, h.ne, q.symmetric i j]

/-! ### Dyadic terms -/

/-- The partial derivative in `x_i` of the monomial `s 2^{-k} X Y` of a dyadic term. -/
noncomputable def termGrad {n : ℕ} (x : Fin n → ℝ) (i : Fin n) (d : DyadicTerm n) : ℝ :=
  (d.sign : ℝ) * (2 : ℝ) ^ (-(d.exponent : ℤ)) *
    ((if d.left = some i then factorValue d.right x else 0) +
      (if d.right = some i then factorValue d.left x else 0))

theorem dyadic_gradient {n : ℕ} (hn : 0 < n) (p : Quadratic n) (x : Fin n → ℝ) (i : Fin n) :
    ∑ r : TermIndex p, termGrad x i (termAt p r) = sourceGradient (normalized p) x i := by
  rw [← slots_gradient (normalized p) x i]
  have h1 : ∑ r : TermIndex p, termGrad x i (termAt p r) =
      ((dyadicTerms p).map (termGrad x i)).sum :=
    Fin.sum_univ_fun_getElem (dyadicTerms p) (termGrad x i)
  rw [h1]
  unfold dyadicTerms
  rw [sum_map_flatMap]
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [List.map_map, list_sum_map_filter, list_sum_finRange]
  rw [(normalization_dyadic hn p).2 t ht |>.2, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  cases hb : coefficientBit p t j
  · simp
  · simp [termGrad, slotGrad, Function.comp]
    try ring

/-! ### Chains -/

theorem factor_hasDerivAt {n : ℕ} (a : Option (Fin n)) (x : Fin n → ℝ) (i : Fin n) :
    HasDerivAt (fun t => factorValue a (Function.update x i t))
      (if a = some i then 1 else 0) (x i) := by
  cases a with
  | none => simpa [factorValue] using hasDerivAt_const (x i) (1 : ℝ)
  | some b =>
    by_cases h : b = i
    · subst h
      simpa [factorValue] using hasDerivAt_id' (x b)
    · have : (fun t => factorValue (some b) (Function.update x i t)) = fun _ => x b := by
        funext t; simp [factorValue, Function.update_of_ne h]
      rw [this]
      simpa [h] using hasDerivAt_const (x i) (x b)

theorem chain_hasDerivAt (k : ℕ) (s : ℤ) (u : Fin (k + 2) → ℝ) (X Y : ℝ → ℝ) (dX dY t0 : ℝ)
    (hX : HasDerivAt X dX t0) (hY : HasDerivAt Y dY t0) :
    HasDerivAt (fun t => chainValue k s (X t) (Y t) u)
      ((-6 * u ⟨0, by omega⟩ + 2 * X t0) * dX +
        (6 * (s : ℝ) * u ⟨k + 1, by omega⟩ + 2 * Y t0) * dY) t0 := by
  set C : ℝ := 3 * ∑ i : Fin (k + 1),
    (2 * u ⟨i.val, by omega⟩ - u ⟨i.val + 1, by omega⟩) ^ 2 + 9 * (u ⟨k + 1, by omega⟩) ^ 2 with hC
  have e : (fun t => chainValue k s (X t) (Y t) u) = fun t =>
      C + ((-6 * u ⟨0, by omega⟩) * X t + (6 * (s : ℝ) * u ⟨k + 1, by omega⟩) * Y t +
        X t ^ 2 + Y t ^ 2) := by
    funext t; simp only [chainValue, hC]; ring
  rw [e]
  have h := ((((hX.const_mul (-6 * u ⟨0, by omega⟩)).add
    (hY.const_mul (6 * (s : ℝ) * u ⟨k + 1, by omega⟩))).add (hX.pow 2)).add (hY.pow 2)).const_add C
  refine h.congr_deriv ?_
  simp only [show (2 : ℕ) - 1 = 1 from rfl, pow_one, Nat.cast_ofNat]
  ring

theorem minimizer_partials (k : ℕ) (s : ℤ) (hs : s = -1 ∨ s = 1) (X Y : ℝ) :
    -6 * chainMinimizer k s X Y ⟨0, by omega⟩ + 2 * X =
        (s : ℝ) * (2 : ℝ) ^ (-(k : ℤ)) * Y ∧
      6 * (s : ℝ) * chainMinimizer k s X Y ⟨k + 1, by omega⟩ + 2 * Y =
        (s : ℝ) * (2 : ℝ) ^ (-(k : ℤ)) * X := by
  have h0 : chainMinimizer k s X Y ⟨0, by omega⟩ =
      ((2 : ℝ) ^ (-((0 : ℕ) : ℤ)) * X -
        (s : ℝ) * (2 : ℝ) ^ (((0 : ℕ) : ℤ) + 1 - ((k : ℤ) + 2)) * Y) / 3 := rfl
  have h1 : chainMinimizer k s X Y ⟨k + 1, by omega⟩ =
      ((2 : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) * X -
        (s : ℝ) * (2 : ℝ) ^ (((k + 1 : ℕ) : ℤ) + 1 - ((k : ℤ) + 2)) * Y) / 3 := rfl
  have e0 : (((0 : ℕ) : ℤ) + 1 - ((k : ℤ) + 2)) = -(k : ℤ) - 1 := by push_cast; ring
  have e1 : (-((k + 1 : ℕ) : ℤ)) = -(k : ℤ) - 1 := by push_cast; ring
  have e2 : (((k + 1 : ℕ) : ℤ) + 1 - ((k : ℤ) + 2)) = 0 := by push_cast; ring
  have hw : (2 : ℝ) ^ (-(k : ℤ) - 1) = (2 : ℝ) ^ (-(k : ℤ)) / 2 :=
    zpow_sub_one₀ (by norm_num) _
  rw [h0, h1, e0, e1, e2, hw, zpow_zero]
  simp only [Nat.cast_zero, neg_zero, zpow_zero]
  rcases hs with rfl | rfl <;> constructor <;> push_cast <;> ring

theorem coefficientSign_cases {n : ℕ} (p : Quadratic n) (t : Monomial n) :
    coefficientSign p t = -1 ∨ coefficientSign p t = 1 := by
  unfold coefficientSign; split_ifs <;> simp

theorem termAt_facts {n : ℕ} (p : Quadratic n) (r : TermIndex p) :
    ((termAt p r).sign = -1 ∨ (termAt p r).sign = 1) ∧ 1 ≤ (termAt p r).exponent := by
  have hmem : termAt p r ∈ dyadicTerms p := List.getElem_mem r.isLt
  unfold dyadicTerms at hmem
  obtain ⟨t, -, ht⟩ := List.mem_flatMap.1 hmem
  obtain ⟨j, -, hj⟩ := List.mem_map.1 ht
  rw [← hj]
  exact ⟨coefficientSign_cases p t, by simp⟩

theorem factorValue_mem {n : ℕ} (a : Option (Fin n)) (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) : 0 ≤ factorValue a x ∧ factorValue a x ≤ 1 := by
  cases a with
  | none => simp [factorValue]
  | some b => simpa [factorValue] using hx b

end UQKKTProjectionAux

open Finset NetworkEquilibriumCLS.LinearNash UnaryQuadraticKKT.Hardness UQKKTProjectionAux

theorem solution {n : ℕ} (hn : 0 < n) (p : Quadratic n)
    (z : CombinedIndex p → ℝ)
    (hz : IntervalKKT (mixedLower p) (fun _ => 1) (combinedValue p) z) :
    QuadraticKKT (normalized p) (fun i => z (.inl i)) := by
  classical
  set x : Fin n → ℝ := fun i => z (.inl i) with hxdef
  have hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1 := fun i => by
    simpa [mixedLower, hxdef] using hz.1 (.inl i)
  -- Step 1: every auxiliary block is the chain minimizer
  have hmin : ∀ r : TermIndex p, (fun j => z (.inr ⟨r, j⟩)) =
      chainMinimizer (termAt p r).exponent (termAt p r).sign (factorValue (termAt p r).left x) (factorValue (termAt p r).right x) := by
    intro r
    obtain ⟨hs, hk⟩ := termAt_facts p r
    set u : Fin ((termAt p r).exponent + 2) → ℝ := fun j => z (.inr ⟨r, j⟩) with hu
    have hpart : ∀ j, coordinatePartial (combinedValue p) z (.inr ⟨r, j⟩) =
        coordinatePartial (chainValue (termAt p r).exponent (termAt p r).sign (factorValue (termAt p r).left x) (factorValue (termAt p r).right x)) u j := by
      intro j
      set C : ℝ := ∑ r' ∈ univ.erase r,
        chainValue (termAt p r').exponent (termAt p r').sign
          (factorValue (termAt p r').left x) (factorValue (termAt p r').right x)
          (fun j' => z (.inr ⟨r', j'⟩)) with hC
      have hfun : (fun t => combinedValue p (Function.update z (.inr ⟨r, j⟩) t)) =
          fun t => chainValue (termAt p r).exponent (termAt p r).sign (factorValue (termAt p r).left x) (factorValue (termAt p r).right x)
            (Function.update u j t) + C := by
        funext t
        have hxu : (fun i => Function.update z (.inr ⟨r, j⟩) t (.inl i)) = x := by
          funext i; simp [Function.update_apply, hxdef]
        unfold combinedValue
        rw [hxu, ← Finset.add_sum_erase _ _ (Finset.mem_univ r)]
        congr 1
        · congr 1
          funext j'
          by_cases h : j' = j
          · subst h; simp [hu]
          · simp [Function.update_apply, h, hu]
        · refine Finset.sum_congr rfl (fun r' hr' => ?_)
          have hne : r' ≠ r := Finset.ne_of_mem_erase hr'
          congr 1
          funext j'
          simp [Function.update_apply, hne]
      unfold coordinatePartial
      rw [hfun, deriv_add_const]
    have hkkt : IntervalKKT (fun _ => -1) (fun _ => 1)
        (chainValue (termAt p r).exponent (termAt p r).sign (factorValue (termAt p r).left x) (factorValue (termAt p r).right x)) u := by
      refine ⟨fun j => ?_, fun j => ?_⟩
      · simpa [mixedLower, hu] using hz.1 (.inr ⟨r, j⟩)
      · have := hz.2 (.inr ⟨r, j⟩)
        rw [hpart j] at this
        simpa [mixedLower, hu] using this
    exact (chain_unique _ hk _ hs (factorValue (termAt p r).left x) (factorValue (termAt p r).right x) (factorValue_mem _ x hx)
      (factorValue_mem _ x hx)).2.2.2 u hkkt
  -- Step 2: the partial derivative in an original coordinate
  have hgrad : ∀ i, coordinatePartial (combinedValue p) z (.inl i) =
      sourceGradient (normalized p) x i := by
    intro i
    rw [← dyadic_gradient hn p x i]
    have hfun : (fun t => combinedValue p (Function.update z (.inl i) t)) = fun t =>
        ∑ r : TermIndex p, chainValue (termAt p r).exponent (termAt p r).sign
          (factorValue (termAt p r).left (Function.update x i t))
          (factorValue (termAt p r).right (Function.update x i t))
          (fun j => z (.inr ⟨r, j⟩)) := by
      funext t
      unfold combinedValue
      refine Finset.sum_congr rfl (fun r _ => ?_)
      have hxu : (fun i' => Function.update z (.inl i) t (.inl i')) = Function.update x i t := by
        funext i'; by_cases h : i' = i
        · subst h; simp
        · simp [Function.update_apply, h, hxdef]
      have huu : (fun j => Function.update z (.inl i) t (.inr ⟨r, j⟩)) =
          fun j => z (.inr ⟨r, j⟩) := by
        funext j; simp [Function.update_apply]
      rw [hxu, huu]
    have hder := HasDerivAt.fun_sum (u := (univ : Finset (TermIndex p))) (x := x i)
      (fun r _ => chain_hasDerivAt (termAt p r).exponent (termAt p r).sign
        (fun j => z (.inr ⟨r, j⟩)) _ _ _ _ (x i)
        (factor_hasDerivAt (termAt p r).left x i) (factor_hasDerivAt (termAt p r).right x i))
    unfold coordinatePartial
    rw [hfun]
    have hd := hder.deriv
    beta_reduce at hd
    refine hd.trans ?_
    refine Finset.sum_congr rfl (fun r _ => ?_)
    obtain ⟨hs, -⟩ := termAt_facts p r
    have hm := hmin r
    have hu0 : z (.inr ⟨r, ⟨0, by omega⟩⟩) = chainMinimizer (termAt p r).exponent
        (termAt p r).sign (factorValue (termAt p r).left x) (factorValue (termAt p r).right x) ⟨0, by omega⟩ := congrFun hm _
    have hu1 : z (.inr ⟨r, ⟨(termAt p r).exponent + 1, by omega⟩⟩) =
        chainMinimizer (termAt p r).exponent (termAt p r).sign (factorValue (termAt p r).left x) (factorValue (termAt p r).right x)
          ⟨(termAt p r).exponent + 1, by omega⟩ := congrFun hm _
    obtain ⟨e0, e1⟩ := minimizer_partials (termAt p r).exponent (termAt p r).sign hs (factorValue (termAt p r).left x) (factorValue (termAt p r).right x)
    simp only [Function.update_eq_self]
    rw [hu0, hu1]
    rw [e0, e1]
    unfold termGrad
    split_ifs <;> ring
  unfold QuadraticKKT BoxSigns
  refine ⟨fun i => hx i, fun i => ?_⟩
  have := hz.2 (.inl i)
  rw [hgrad i] at this
  simpa [mixedLower, hxdef] using this
