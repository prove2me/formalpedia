-- Prove2me | solution 1 for SchedComplexity.Tardiness.knapsack_iff_split
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T12:34:37.030893+00:00
-- url     : https://prove2.me/submissions/7941b455-282a-477d-b319-21de6284b03d

import Mathlib
import Definitions.Def_SchedComplexity_Tardiness_Construction
import Definitions.Def_SchedComplexity_Tardiness_Knapsack



namespace SchedComplexity.Tardiness

open Finset

lemma tard_posCompletion_succ {n : ℕ} (p : Fin n → ℕ) (π : Equiv.Perm (Fin n)) (i : Fin n) :
    posCompletion p π (i.val + 1) = posCompletion p π i.val + p (π i) := by
  unfold posCompletion
  have : Finset.univ.filter (fun j : Fin n => j.val < i.val + 1) =
      insert i (Finset.univ.filter (fun j : Fin n => j.val < i.val)) := by
    ext j; simp [Fin.ext_iff]; omega
  rw [this, Finset.sum_insert (by simp)]; ring

lemma tard_posCompletion_mono {n : ℕ} (p : Fin n → ℕ) (π : Equiv.Perm (Fin n)) {k l : ℕ}
    (h : k ≤ l) : posCompletion p π k ≤ posCompletion p π l := by
  unfold posCompletion
  apply Finset.sum_le_sum_of_subset
  intro i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega

lemma tard_posCompletion_zero {n : ℕ} (p : Fin n → ℕ) (π : Equiv.Perm (Fin n)) :
    posCompletion p π 0 = 0 := by
  unfold posCompletion; simp

lemma tard_noIdle_feasible {n : ℕ} (p : Fin n → ℕ) (π : Equiv.Perm (Fin n)) :
    IsFeasible p (noIdleStart p π) := by
  intro i j hij
  have key : ∀ i j : Fin n, (π.symm i).val < (π.symm j).val →
      noIdleStart p π i + p i ≤ noIdleStart p π j := by
    intro i j h
    unfold noIdleStart
    have := tard_posCompletion_succ p π (π.symm i)
    simp only [Equiv.apply_symm_apply] at this
    rw [← this]
    exact tard_posCompletion_mono p π (by omega)
  have : (π.symm i).val ≠ (π.symm j).val := by
    intro h; apply hij; have := Fin.ext h; simpa using this
  rcases lt_or_gt_of_ne this with h | h
  · exact Or.inl (key i j h)
  · exact Or.inr (key j i h)

theorem idle_time_removal_core {n : ℕ} (p w d : Fin n → ℕ) :
    (∀ π : Equiv.Perm (Fin n), IsFeasible p (noIdleStart p π)) ∧
    ∀ S : Fin n → ℕ, IsFeasible p S →
      ∃ π : Equiv.Perm (Fin n), orderTWT p w d π ≤ totalWeightedTardiness p w d S := by
  refine ⟨tard_noIdle_feasible p, ?_⟩
  intro S hS
  let key : Fin n → ℕ ×ₗ ℕ := fun j => toLex (S j, p j)
  refine ⟨Tuple.sort key, ?_⟩
  set π := Tuple.sort key with hπ
  have hmono : Monotone (key ∘ π) := Tuple.monotone_sort key
  have step : ∀ k : ℕ, (hk : k < n) → posCompletion p π k ≤ S (π ⟨k, hk⟩) := by
    intro k
    induction k with
    | zero => intro hk; rw [tard_posCompletion_zero]; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := tard_posCompletion_succ p π ⟨k, by omega⟩
      simp only at h2
      rw [h2]
      have hle : key (π ⟨k, by omega⟩) ≤ key (π ⟨k+1, hk⟩) :=
        hmono (show (⟨k, by omega⟩ : Fin n) ≤ ⟨k+1, hk⟩ from by simp [Fin.le_def])
      have hne : π ⟨k, by omega⟩ ≠ π ⟨k+1, hk⟩ := by
        intro h; have := π.injective h; simp [Fin.ext_iff] at this
      have hf := hS _ _ hne
      simp only [key, Function.comp, Prod.Lex.le_iff, ofLex_toLex] at hle
      omega
  unfold orderTWT totalWeightedTardiness
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  unfold tardiness completion
  apply max_le_max le_rfl
  have := step (π.symm j).val (π.symm j).isLt
  simp only [Fin.eta, Equiv.apply_symm_apply] at this
  unfold noIdleStart
  have : posCompletion p π (π.symm j).val ≤ S j := this
  omega


lemma tard_S2 {m : ℕ} (T : Finset (Fin m)) (f : Fin m → ℤ) :
    2 * ∑ j ∈ T, ∑ k ∈ T.filter (· ≤ j), f j * f k
      = (∑ j ∈ T, f j) ^ 2 + ∑ j ∈ T, (f j) ^ 2 := by
  induction T using Finset.induction_on_max with
  | empty => simp
  | insert μ s hlt ih =>
    have hμ : μ ∉ s := fun h => lt_irrefl _ (hlt μ h)
    rw [sum_insert hμ, sum_insert hμ, sum_insert hμ]
    have e1 : ∑ j ∈ s, ∑ k ∈ (insert μ s).filter (· ≤ j), f j * f k
        = ∑ j ∈ s, ∑ k ∈ s.filter (· ≤ j), f j * f k := by
      apply sum_congr rfl; intro j hj
      apply sum_congr _ (fun _ _ => rfl)
      ext k; simp only [mem_filter, mem_insert]; constructor
      · rintro ⟨h1 | h1, h2⟩
        · exfalso; subst h1; exact absurd (hlt j hj) (not_lt.mpr h2)
        · exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨Or.inr h1, h2⟩
    have e2 : ∑ k ∈ (insert μ s).filter (· ≤ μ), f μ * f k
        = f μ * (∑ k ∈ s, f k) + f μ * f μ := by
      have : (insert μ s).filter (· ≤ μ) = insert μ s := by
        ext k; simp only [mem_filter, mem_insert]; constructor
        · exact fun h => h.1
        · intro h; refine ⟨h, ?_⟩
          rcases h with h | h
          · exact h ▸ le_rfl
          · exact (hlt k h).le
      rw [this, sum_insert hμ, ← mul_sum]; ring
    rw [e2, e1]
    linear_combination ih

lemma tard_swap {m : ℕ} (T : Finset (Fin m)) (G : Fin m → Fin m → ℤ) :
    ∑ j ∈ T, ∑ k ∈ T.filter (j ≤ ·), G j k = ∑ k ∈ T, ∑ j ∈ T.filter (· ≤ k), G j k := by
  apply Finset.sum_comm'
  intro x y; simp only [mem_filter]; tauto

lemma tard_cheb {m : ℕ} (g : Fin m → ℕ) (hmono : Monotone g) (r : ℕ)
    (hr : (univ.filter (fun k => g k ≠ 0)).card ≤ r) :
    2 * ∑ j : Fin m, ∑ k ∈ univ.filter (· ≤ j), (g k : ℤ) ≤ (r + 1) * ∑ k, (g k : ℤ) := by
  set s := univ.filter (fun k => g k ≠ 0) with hs
  set c := s.card with hc
  let w : Fin m → ℤ := fun k => ((univ.filter (k ≤ ·)).card : ℤ)
  have hX : ∑ j : Fin m, ∑ k ∈ univ.filter (· ≤ j), (g k : ℤ) = ∑ k, (g k : ℤ) * w k := by
    rw [Finset.sum_comm' (s := univ) (t := fun j => univ.filter (· ≤ j)) (t' := univ)
      (s' := fun k => univ.filter (k ≤ ·)) (by intro x y; simp)]
    apply sum_congr rfl; intro k _
    simp [w, mul_comm]
  have hXs : ∑ k, (g k : ℤ) * w k = ∑ k ∈ s, (g k : ℤ) * w k := by
    rw [hs, Finset.sum_filter]
    apply sum_congr rfl; intro k _
    by_cases h : g k = 0 <;> simp [h]
  have hQs : ∑ k, (g k : ℤ) = ∑ k ∈ s, (g k : ℤ) := by
    rw [hs, Finset.sum_filter]
    apply sum_congr rfl; intro k _
    by_cases h : g k = 0 <;> simp [h]
  have hwA : Antitone w := by
    intro x y hxy
    simp only [w]
    exact_mod_cast Finset.card_le_card (fun z hz => by
      simp only [mem_filter, mem_univ, true_and] at hz ⊢; exact le_trans hxy hz)
  have hch := (Monotone.antivary (f := fun k => (g k : ℤ)) (g := w)
      (fun x y h => Nat.cast_le.mpr (hmono h)) hwA).antivaryOn (s : Set (Fin m))
  have hch2 := hch.card_smul_sum_le_sum_smul_sum
  simp only [smul_eq_mul, nsmul_eq_mul] at hch2
  -- weights on s
  have hws : ∀ k ∈ s, w k = ((s.filter (k ≤ ·)).card : ℤ) := by
    intro k hk
    simp only [w]
    congr 1
    congr 1
    ext z; simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro hz
      refine ⟨?_, hz⟩
      have hk' : g k ≠ 0 := (mem_filter.mp hk).2
      have := hmono hz
      simp only [hs, mem_filter, mem_univ, true_and]
      omega
    · exact fun h => h.2
  have hsw : 2 * ∑ k ∈ s, w k = (c : ℤ) ^ 2 + c := by
    have h1 := tard_S2 s (fun _ => (1:ℤ))
    have h3 := tard_swap s (fun _ _ => (1:ℤ))
    have h2 : ∑ k ∈ s, w k = ∑ j ∈ s, ∑ k ∈ s.filter (j ≤ ·), (1:ℤ) := by
      rw [sum_congr rfl hws]; simp
    rw [h2, h3]
    simpa [hc] using h1
  rw [hX, hXs, hQs]
  have hQ0 : (0:ℤ) ≤ ∑ k ∈ s, (g k : ℤ) := sum_nonneg (fun _ _ => by positivity)
  by_cases hc0 : c = 0
  · have : s = ∅ := Finset.card_eq_zero.mp hc0
    rw [this]; simp
  · have hcpos : (0:ℤ) < c := by exact_mod_cast Nat.pos_of_ne_zero hc0
    have hrr : (c:ℤ) ≤ r := by exact_mod_cast hr
    have : (c:ℤ) * (2 * ∑ k ∈ s, (g k : ℤ) * w k) ≤ (c:ℤ) * ((r + 1) * ∑ k ∈ s, (g k : ℤ)) := by
      rw [← hc] at hch2
      generalize ∑ k ∈ s, (g k : ℤ) * w k = X at *
      generalize ∑ k ∈ s, (g k : ℤ) = Q at *
      generalize ∑ k ∈ s, w k = W at *
      have h5 : 0 ≤ ((r:ℤ) - c) * c * Q := mul_nonneg (mul_nonneg (by linarith) hcpos.le) hQ0
      nlinarith [hch2, hsw, h5]
    exact le_of_mul_le_mul_left this hcpos


lemma tard_pos_split {t m : ℕ} (p : Fin (t+m) → ℕ) (π : Equiv.Perm (Fin (t+m))) (k : ℕ) :
    posCompletion p π k = ∑ i : Fin t, (if i.val < k then p (π (Fin.castAdd m i)) else 0)
      + ∑ j : Fin m, (if t + j.val < k then p (π (Fin.natAdd t j)) else 0) := by
  unfold posCompletion
  rw [Finset.sum_filter, Fin.sum_univ_add]
  simp

lemma tard_pos_head {t m : ℕ} (p : Fin (t+m) → ℕ) (π : Equiv.Perm (Fin (t+m))) :
    posCompletion p π t = ∑ i : Fin t, p (π (Fin.castAdd m i)) := by
  rw [tard_pos_split]
  simp

lemma tard_tail_split {t m : ℕ} (p v : Fin (t+m) → ℕ) (π : Equiv.Perm (Fin (t+m))) :
    tailWeighted p v π t = ∑ j : Fin m, (v (π (Fin.natAdd t j)) : ℤ) *
      ∑ k ∈ univ.filter (· ≤ j), (p (π (Fin.natAdd t k)) : ℤ) := by
  unfold tailWeighted
  rw [Finset.sum_filter, Fin.sum_univ_add]
  have h0 : ∀ i : Fin t, ¬ (t ≤ (Fin.castAdd m i).val) := by intro i; simp
  simp only [h0, if_false, sum_const_zero, zero_add]
  apply sum_congr rfl; intro j _
  have : t ≤ (Fin.natAdd t j).val := by simp
  rw [if_pos this]
  congr 1
  rw [tard_pos_split p π ((Fin.natAdd t j).val+1), tard_pos_head]
  simp
  have e1 : ∀ x : Fin t, (x.val ≤ t + j.val) := fun x => by have := x.isLt; omega
  simp only [e1, if_true]
  rw [Finset.sum_filter]; ring


lemma tard_pair_split {t m : ℕ} (F : Fin (t+m) → Fin (t+m) → ℤ) :
    ∑ i ∈ univ.filter (fun i : Fin (t+m) => t ≤ i.val), ∑ k ∈ univ.filter (fun k : Fin (t+m) => i ≤ k), F i k
      = ∑ j : Fin m, ∑ k ∈ univ.filter (j ≤ ·), F (Fin.natAdd t j) (Fin.natAdd t k) := by
  rw [Finset.sum_filter, Fin.sum_univ_add]
  have h0 : ∀ i : Fin t, ¬ (t ≤ (Fin.castAdd m i).val) := by intro i; simp
  simp only [h0, if_false, sum_const_zero, zero_add]
  apply sum_congr rfl; intro j _
  have : t ≤ (Fin.natAdd t j).val := by simp
  rw [if_pos this, Finset.sum_filter, Fin.sum_univ_add]
  have h1 : ∀ k : Fin t, ¬ (Fin.natAdd t j ≤ Fin.castAdd m k) := by
    intro k; simp only [Fin.le_def, Fin.val_natAdd, Fin.val_castAdd]; have := k.isLt; omega
  simp only [h1, if_false, sum_const_zero, zero_add]
  rw [Finset.sum_filter]
  apply sum_congr rfl; intro k _
  have e : (Fin.natAdd t j ≤ Fin.natAdd t k) ↔ j ≤ k := by
    simp only [Fin.le_def, Fin.val_natAdd]; omega
  simp only [e]

lemma tard_sum_aE {t : ℕ} (a : Fin t → ℕ) (b : ℕ) :
    ∑ j : Fin (t + tPrime a b), aExt a b j = bigA a := by
  rw [Fin.sum_univ_add]
  unfold bigA
  have h1 : ∀ i : Fin t, aExt a b (Fin.castAdd (tPrime a b) i) = a i := by
    intro i; simp [aExt]
  have h2 : ∀ j : Fin (tPrime a b), aExt a b (Fin.natAdd t j) = 0 := by
    intro j; simp [aExt]
  simp [h1, h2]

lemma tard_aExt_le {t : ℕ} (a : Fin t → ℕ) (b : ℕ) (j : Fin (t + tPrime a b)) :
    aExt a b j ≤ aStar a := by
  unfold aExt aStar
  split_ifs with h
  · exact Finset.le_sup (f := a) (Finset.mem_univ _)
  · exact Nat.zero_le _

lemma tard_count_nonzero {t : ℕ} (a : Fin t → ℕ) (b : ℕ) (π : Equiv.Perm (Fin (t + tPrime a b))) :
    (univ.filter (fun k : Fin (tPrime a b) => aExt a b (π (Fin.natAdd t k)) ≠ 0)).card ≤ t := by
  have := Finset.card_le_card_of_injOn (s := univ.filter (fun k : Fin (tPrime a b) => aExt a b (π (Fin.natAdd t k)) ≠ 0))
    (t := Finset.range t) (fun k => (π (Fin.natAdd t k)).val) ?_ ?_
  · simpa using this
  · intro k hk
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hk
    simp only [coe_range, Set.mem_Iio]
    by_contra hlt
    apply hk
    simp [aExt]
    intro h; omega
  · intro k _ k' _ h
    have := π.injective (Fin.ext h)
    simpa using this

lemma tard_cPi_eq {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ) (π : Equiv.Perm (Fin (t + tPrime a b))) :
    cPi a b τ π = (∑ i : Fin t, (aExt a b (π (Fin.castAdd (tPrime a b) i)) : ℤ)) - b := by
  unfold cPi
  rw [tard_pos_head]
  push_cast
  simp only [wtP, Nat.cast_add, sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

lemma tard_head_tail {t : ℕ} (a : Fin t → ℕ) (b : ℕ) (π : Equiv.Perm (Fin (t + tPrime a b))) :
    (∑ i : Fin t, (aExt a b (π (Fin.castAdd (tPrime a b) i)) : ℤ)) +
      ∑ j : Fin (tPrime a b), (aExt a b (π (Fin.natAdd t j)) : ℤ) = bigA a := by
  have h := tard_sum_aE a b
  have h2 : ∑ j : Fin (t + tPrime a b), (aExt a b (π j) : ℤ) = bigA a := by
    rw [Equiv.sum_comp π (fun j => (aExt a b j : ℤ))]
    exact_mod_cast h
  rw [← h2, Fin.sum_univ_add]

lemma tard_g_bounds {m : ℕ} (g : Fin m → ℕ) (B t : ℕ) (hle : ∀ j, g j ≤ B)
    (hc : (univ.filter (fun k => g k ≠ 0)).card ≤ t) :
    ((∑ j, (g j : ℤ)) ^ 2 + ∑ j, (g j : ℤ) ^ 2) ≤ (t : ℤ) * (t + 1) * (B : ℤ) ^ 2 := by
  set s := univ.filter (fun k => g k ≠ 0) with hs
  have e1 : ∑ j, (g j : ℤ) = ∑ j ∈ s, (g j : ℤ) := by
    rw [hs, Finset.sum_filter]; apply sum_congr rfl; intro k _
    by_cases h : g k = 0 <;> simp [h]
  have e2 : ∑ j, (g j : ℤ) ^ 2 = ∑ j ∈ s, (g j : ℤ) ^ 2 := by
    rw [hs, Finset.sum_filter]; apply sum_congr rfl; intro k _
    by_cases h : g k = 0 <;> simp [h]
  have b1 : ∑ j ∈ s, (g j : ℤ) ≤ s.card * B := by
    calc ∑ j ∈ s, (g j : ℤ) ≤ ∑ j ∈ s, (B : ℤ) := sum_le_sum (fun j _ => by exact_mod_cast hle j)
      _ = s.card * B := by simp
  have b2 : ∑ j ∈ s, (g j : ℤ) ^ 2 ≤ s.card * (B : ℤ) ^ 2 := by
    calc ∑ j ∈ s, (g j : ℤ) ^ 2 ≤ ∑ j ∈ s, (B : ℤ) ^ 2 :=
          sum_le_sum (fun j _ => pow_le_pow_left₀ (by positivity) (by exact_mod_cast hle j) 2)
      _ = s.card * (B : ℤ) ^ 2 := by simp
  have q0 : (0:ℤ) ≤ ∑ j ∈ s, (g j : ℤ) := sum_nonneg (fun _ _ => by positivity)
  have hct : (s.card : ℤ) ≤ t := by exact_mod_cast hc
  rw [e1, e2]
  have h3 : (∑ j ∈ s, (g j : ℤ)) ^ 2 ≤ ((s.card : ℤ) * B) ^ 2 := pow_le_pow_left₀ q0 b1 2
  have hB : (0:ℤ) ≤ (B:ℤ)^2 := by positivity
  have hc0 : (0:ℤ) ≤ s.card := by positivity
  nlinarith [mul_nonneg hB (mul_nonneg hc0 (sub_nonneg.mpr hct)), mul_nonneg hB (sub_nonneg.mpr hct)]

lemma tard_S2' {m : ℕ} (T : Finset (Fin m)) (f : Fin m → ℤ) :
    2 * ∑ j ∈ T, ∑ k ∈ T.filter (j ≤ ·), f j * f k
      = (∑ j ∈ T, f j) ^ 2 + ∑ j ∈ T, (f j) ^ 2 := by
  rw [tard_swap T (fun j k => f j * f k), ← tard_S2 T f]
  congr 1
  apply sum_congr rfl; intro j _; apply sum_congr rfl; intro k _; ring

/-- tail values of the job indices -/
def tailG {t : ℕ} (a : Fin t → ℕ) (b : ℕ) (π : Equiv.Perm (Fin (t + tPrime a b))) :
    Fin (tPrime a b) → ℕ := fun j => aExt a b (π (Fin.natAdd t j))

lemma tard_wtP_tail {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ) (π : Equiv.Perm (Fin (t + tPrime a b)))
    (j : Fin (tPrime a b)) :
    ((wtP a b τ (π (Fin.natAdd t j)) : ℕ) : ℤ) = τ + (tailG a b π j : ℤ) := by
  simp [wtP, tailG]

lemma tard_aPS {t : ℕ} (a : Fin t → ℕ) (b : ℕ) (π : Equiv.Perm (Fin (t + tPrime a b))) :
    2 * aPairSum a b π = (∑ j, (tailG a b π j : ℤ)) ^ 2 + ∑ j, (tailG a b π j : ℤ) ^ 2 := by
  have hAP : aPairSum a b π = ∑ j : Fin (tPrime a b), ∑ k ∈ univ.filter (j ≤ ·),
      (tailG a b π j : ℤ) * tailG a b π k := by
    unfold aPairSum
    exact tard_pair_split (fun i k => (aExt a b (π i) : ℤ) * aExt a b (π k))
  rw [hAP]
  exact tard_S2' univ (fun j => (tailG a b π j : ℤ))

lemma tard_tailpp {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ) (π : Equiv.Perm (Fin (t + tPrime a b))) :
    2 * tailWeighted (wtP a b τ) (wtP a b τ) π t =
      (tPrime a b : ℤ) * (tPrime a b + 1) * τ ^ 2 +
      2 * (tPrime a b + 1) * τ * (∑ j, (tailG a b π j : ℤ)) + 2 * aPairSum a b π := by
  have e : tailWeighted (wtP a b τ) (wtP a b τ) π t = ∑ j : Fin (tPrime a b),
      ∑ k ∈ univ.filter (· ≤ j), ((τ : ℤ) + tailG a b π j) * ((τ : ℤ) + tailG a b π k) := by
    rw [tard_tail_split]
    simp only [tard_wtP_tail, mul_sum]
  rw [e, tard_aPS]
  have hf := tard_S2 univ (fun j => (τ : ℤ) + (tailG a b π j : ℤ))
  beta_reduce at hf
  rw [hf]
  have s1 : ∑ j : Fin (tPrime a b), ((τ : ℤ) + (tailG a b π j : ℤ)) =
      tPrime a b * τ + ∑ j, (tailG a b π j : ℤ) := by
    rw [sum_add_distrib]; simp
  have s2 : ∑ j : Fin (tPrime a b), ((τ : ℤ) + (tailG a b π j : ℤ)) ^ 2 =
      tPrime a b * τ ^ 2 + 2 * τ * ∑ j, (tailG a b π j : ℤ) + ∑ j, (tailG a b π j : ℤ) ^ 2 := by
    have : ∀ j, ((τ : ℤ) + (tailG a b π j : ℤ)) ^ 2
        = τ ^ 2 + 2 * τ * (tailG a b π j : ℤ) + (tailG a b π j : ℤ) ^ 2 := fun j => by ring
    simp only [this, sum_add_distrib, ← mul_sum]
    simp
  rw [s1, s2]; ring

lemma tard_tail1 {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ) (π : Equiv.Perm (Fin (t + tPrime a b))) :
    ∃ N Y : ℤ, 2 * N = (tPrime a b : ℤ) ^ 2 + tPrime a b ∧
      Y = ∑ j : Fin (tPrime a b), ∑ k ∈ univ.filter (· ≤ j), (tailG a b π k : ℤ) ∧
      tailWeighted (wtP a b τ) (fun _ => 1) π t = τ * N + Y := by
  refine ⟨∑ j : Fin (tPrime a b), ∑ k ∈ univ.filter (· ≤ j), (1 : ℤ),
    ∑ j : Fin (tPrime a b), ∑ k ∈ univ.filter (· ≤ j), (tailG a b π k : ℤ), ?_, rfl, ?_⟩
  · have := tard_S2 (Finset.univ : Finset (Fin (tPrime a b))) (fun _ => (1 : ℤ))
    simpa using this
  · rw [tard_tail_split]
    simp only [tard_wtP_tail, Nat.cast_one, one_mul, mul_sum, sum_add_distrib, sum_const]
    congr 1
    apply sum_congr rfl; intro x _; simp [mul_comm]

lemma tard_Q {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ) (π : Equiv.Perm (Fin (t + tPrime a b))) :
    ∑ j, (tailG a b π j : ℤ) = (bigA a : ℤ) - b - cPi a b τ π := by
  have h := tard_head_tail a b π
  rw [tard_cPi_eq]
  unfold tailG
  linarith

lemma tard_yThr2 {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ) (hbA : b < bigA a) :
    2 * (yThr a b τ : ℤ) = (tPrime a b : ℤ) * (tPrime a b + 1) * τ * (τ + 1)
      + 2 * (tPrime a b + 1) * τ * ((bigA a : ℤ) - b) + 2 * tPrime a b := by
  unfold yThr
  have hd : 2 ∣ tPrime a b * (tPrime a b + 1) * τ * (τ + 1) := by
    obtain ⟨k, hk⟩ := Nat.even_mul_succ_self (tPrime a b)
    exact ⟨k * τ * (τ + 1), by rw [hk]; ring⟩
  obtain ⟨k, hk⟩ := hd
  rw [hk, Nat.mul_div_cancel_left _ (by norm_num)]
  have h1 : (((bigA a - b : ℕ)) : ℤ) = (bigA a : ℤ) - b := by
    rw [Nat.cast_sub hbA.le]
  have hk' : (tPrime a b : ℤ) * (tPrime a b + 1) * τ * (τ + 1) = 2 * k := by exact_mod_cast hk
  push_cast
  rw [h1]
  linear_combination (-1 : ℤ) * hk'

lemma tard_tPrime_ge {t : ℕ} (a : Fin t → ℕ) (b : ℕ) (hbA : b < bigA a) :
    ((t : ℤ) + 1) * ((bigA a : ℤ) - b) + t * (t + 1) * (aStar a : ℤ) ^ 2 ≤ 2 * tPrime a b := by
  unfold tPrime
  have h1 : (((bigA a - b : ℕ)) : ℤ) = (bigA a : ℤ) - b := by
    rw [Nat.cast_sub hbA.le]
  rw [← h1]
  have : (((t + 1) * (bigA a - b) + t * (t + 1) * aStar a ^ 2 + 1) / 2 : ℕ) * 2 + 1 ≥
      (t + 1) * (bigA a - b) + t * (t + 1) * aStar a ^ 2 + 1 := by omega
  have h2 : (((t + 1) * (bigA a - b) + t * (t + 1) * aStar a ^ 2 : ℕ) : ℤ) ≤
      2 * ((((t + 1) * (bigA a - b) + t * (t + 1) * aStar a ^ 2 + 1) / 2 : ℕ) : ℤ) := by
    have : (t + 1) * (bigA a - b) + t * (t + 1) * aStar a ^ 2 ≤
      2 * (((t + 1) * (bigA a - b) + t * (t + 1) * aStar a ^ 2 + 1) / 2) := by omega
    exact_mod_cast this
  push_cast at h2
  exact h2


lemma tard_tail_wtW {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ) (π : Equiv.Perm (Fin (t + tPrime a b))) :
    tailWeighted (wtP a b τ) (wtW a b τ) π t =
      tailWeighted (wtP a b τ) (wtP a b τ) π t + tailWeighted (wtP a b τ) (fun _ => 1) π t := by
  rw [tard_tail_split, tard_tail_split, tard_tail_split, ← sum_add_distrib]
  apply sum_congr rfl; intro j _
  have : ((wtW a b τ (π (Fin.natAdd t j)) : ℕ) : ℤ) =
      ((wtP a b τ (π (Fin.natAdd t j)) : ℕ) : ℤ) + 1 := by simp [wtW, wtP]
  rw [this]; push_cast; ring

lemma tard_aPS_nonneg {t : ℕ} (a : Fin t → ℕ) (b : ℕ) (π : Equiv.Perm (Fin (t + tPrime a b))) :
    0 ≤ aPairSum a b π := by
  have h := tard_aPS a b π
  have h2 : (0:ℤ) ≤ ∑ j, (tailG a b π j : ℤ) ^ 2 := sum_nonneg (fun j _ => sq_nonneg _)
  nlinarith [sq_nonneg (∑ j, (tailG a b π j : ℤ))]

lemma tard_aPS_le {t : ℕ} (a : Fin t → ℕ) (b : ℕ) (π : Equiv.Perm (Fin (t + tPrime a b))) :
    2 * aPairSum a b π ≤ (t : ℤ) * (t + 1) * (aStar a : ℤ) ^ 2 := by
  rw [tard_aPS]
  exact tard_g_bounds (tailG a b π) (aStar a) t (fun j => tard_aExt_le a b _)
    (tard_count_nonzero a b π)

lemma tard_Y_nonneg {t : ℕ} (a : Fin t → ℕ) (b : ℕ) (π : Equiv.Perm (Fin (t + tPrime a b))) :
    0 ≤ ∑ j : Fin (tPrime a b), ∑ k ∈ univ.filter (· ≤ j), (tailG a b π k : ℤ) :=
  sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => by positivity))

lemma tard_ineq6 {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ) (hbA : b < bigA a)
    (π : Equiv.Perm (Fin (t + tPrime a b))) :
    (yThr a b τ : ℤ) - (tPrime a b + 1) * τ * cPi a b τ π - tPrime a b ≤
      tailWeighted (wtP a b τ) (wtW a b τ) π t := by
  rw [tard_tail_wtW]
  have h1 := tard_tailpp a b τ π
  obtain ⟨N, Y, hN, hY, hT⟩ := tard_tail1 a b τ π
  have hy := tard_yThr2 a b τ hbA
  have hQ := tard_Q a b τ π
  have hY0 : 0 ≤ Y := by rw [hY]; exact tard_Y_nonneg a b π
  have hP := tard_aPS_nonneg a b π
  rw [hT]
  rw [hQ] at h1
  have hτN : 2 * ((τ : ℤ) * N) = τ * ((tPrime a b : ℤ) ^ 2 + tPrime a b) := by
    linear_combination (τ : ℤ) * hN
  nlinarith [h1, hy, hτN, hY0, hP]

lemma tard_sorted_exists {t : ℕ} (a : Fin t → ℕ) (b : ℕ) (π : Equiv.Perm (Fin (t + tPrime a b))) :
    ∃ π' : Equiv.Perm (Fin (t + tPrime a b)),
      (∀ i : Fin (t + tPrime a b), i.val < t → π' i = π i) ∧ Monotone (tailG a b π') := by
  let τ' := Tuple.sort (tailG a b π)
  have hmono : Monotone (tailG a b π ∘ τ') := Tuple.monotone_sort (tailG a b π)
  let σ : Equiv.Perm (Fin (t + tPrime a b)) :=
    finSumFinEquiv.symm.trans ((Equiv.sumCongr (Equiv.refl (Fin t)) τ').trans finSumFinEquiv)
  have hσc : ∀ i : Fin t, σ (Fin.castAdd (tPrime a b) i) = Fin.castAdd (tPrime a b) i := by
    intro i; simp [σ]
  have hσn : ∀ j : Fin (tPrime a b), σ (Fin.natAdd t j) = Fin.natAdd t (τ' j) := by
    intro j; simp [σ]
  refine ⟨σ.trans π, ?_, ?_⟩
  · intro i hi
    obtain ⟨x, rfl⟩ : ∃ x : Fin t, i = Fin.castAdd (tPrime a b) x := ⟨⟨i.val, hi⟩, by ext; simp⟩
    show π (σ _) = π _
    rw [hσc]
  · intro x y hxy
    have := hmono hxy
    simpa [tailG, hσn] using this

lemma tard_cPi_congr {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ) (π π' : Equiv.Perm (Fin (t + tPrime a b)))
    (h : ∀ i : Fin (t + tPrime a b), i.val < t → π' i = π i) :
    cPi a b τ π' = cPi a b τ π := by
  rw [tard_cPi_eq, tard_cPi_eq]
  congr 1
  apply sum_congr rfl; intro i _
  rw [h]; simp


lemma tard_ineq5 {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ)
    (π : Equiv.Perm (Fin (t + tPrime a b))) :
    ∃ π' : Equiv.Perm (Fin (t + tPrime a b)),
      (∀ i : Fin (t + tPrime a b), i.val < t → π' i = π i) ∧
      2 * tailWeighted (wtP a b τ) (fun _ => 1) π' t ≤
        (tPrime a b : ℤ) * (tPrime a b + 1) * τ
          + ((t : ℤ) + 1) * ((bigA a : ℤ) - b - cPi a b τ π) := by
  obtain ⟨π', hsame, hmono⟩ := tard_sorted_exists a b π
  refine ⟨π', hsame, ?_⟩
  obtain ⟨N, Y, hN, hY, hT⟩ := tard_tail1 a b τ π'
  have hc := tard_cheb (tailG a b π') hmono t (tard_count_nonzero a b π')
  have hQ := tard_Q a b τ π'
  rw [tard_cPi_congr a b τ π π' hsame] at hQ
  rw [hQ] at hc
  rw [← hY] at hc
  have hτN : 2 * ((τ : ℤ) * N) = τ * ((tPrime a b : ℤ) ^ 2 + tPrime a b) := by
    linear_combination (τ : ℤ) * hN
  rw [hT]
  nlinarith [hc, hτN]

lemma tard_ineq7 {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ) (hbA : b < bigA a)
    (π : Equiv.Perm (Fin (t + tPrime a b))) :
    ∃ π' : Equiv.Perm (Fin (t + tPrime a b)),
      (∀ i : Fin (t + tPrime a b), i.val < t → π' i = π i) ∧
      2 * tailWeighted (wtP a b τ) (wtW a b τ) π' t ≤
        2 * (yThr a b τ : ℤ) - 2 * (tPrime a b + 1) * τ * cPi a b τ π
          - ((t : ℤ) + 1) * cPi a b τ π := by
  obtain ⟨π', hsame, h5⟩ := tard_ineq5 a b τ π
  refine ⟨π', hsame, ?_⟩
  rw [tard_tail_wtW]
  have h1 := tard_tailpp a b τ π'
  have hQ := tard_Q a b τ π'
  rw [tard_cPi_congr a b τ π π' hsame] at hQ
  rw [hQ] at h1
  have h3 := tard_aPS_le a b π'
  have hy := tard_yThr2 a b τ hbA
  have hp := tard_tPrime_ge a b hbA
  nlinarith [h1, h5, h3, hy, hp]

theorem ineq_2_3_core {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ)
    (ha : ∀ j, 0 < a j) (hb : 0 < b) (hbA : b < bigA a)
    (hτ : 2 * tPrime a b + bigA a < τ)
    (π : Equiv.Perm (Fin (t + tPrime a b))) :
    tailWeighted (wtP a b τ) (wtP a b τ) π t =
        ∑ i ∈ Finset.univ.filter (fun i : Fin (t + tPrime a b) => t ≤ i.val),
          ∑ k ∈ Finset.univ.filter (fun k : Fin (t + tPrime a b) => i ≤ k),
            (wtP a b τ (π i) : ℤ) * wtP a b τ (π k) ∧
    (tailWeighted (wtP a b τ) (wtP a b τ) π t : ℝ) =
        (1 / 2 : ℝ) * tPrime a b * (tPrime a b + 1) * (τ : ℝ) ^ 2
          + (tPrime a b + 1) * (τ : ℝ) * ((bigA a : ℝ) - b - cPi a b τ π)
          + aPairSum a b π ∧
    0 ≤ aPairSum a b π ∧
    (aPairSum a b π : ℝ) ≤ (1 / 2 : ℝ) * t * (t + 1) * (aStar a : ℝ) ^ 2 := by
  refine ⟨?_, ?_, tard_aPS_nonneg a b π, ?_⟩
  · rw [tard_pair_split (fun i k => (wtP a b τ (π i) : ℤ) * wtP a b τ (π k))]
    have e : tailWeighted (wtP a b τ) (wtP a b τ) π t = ∑ j : Fin (tPrime a b),
        ∑ k ∈ univ.filter (· ≤ j), ((τ : ℤ) + tailG a b π j) * ((τ : ℤ) + tailG a b π k) := by
      rw [tard_tail_split]
      simp only [tard_wtP_tail, mul_sum]
    rw [e]
    simp only [tard_wtP_tail]
    rw [tard_swap univ (fun j k => ((τ : ℤ) + tailG a b π j) * ((τ : ℤ) + tailG a b π k))]
    apply sum_congr rfl; intro j _
    apply sum_congr rfl; intro k _
    ring
  · have h1 := tard_tailpp a b τ π
    rw [tard_Q a b τ π] at h1
    have h1r : ((2 * tailWeighted (wtP a b τ) (wtP a b τ) π t : ℤ) : ℝ) =
        (((tPrime a b : ℤ) * (tPrime a b + 1) * τ ^ 2 +
        2 * (tPrime a b + 1) * τ * ((bigA a : ℤ) - b - cPi a b τ π) + 2 * aPairSum a b π : ℤ) : ℝ) := by
      rw [h1]
    push_cast at h1r
    linarith
  · have h3 := tard_aPS_le a b π
    have h3r : ((2 * aPairSum a b π : ℤ) : ℝ) ≤ (((t : ℤ) * (t + 1) * (aStar a : ℤ) ^ 2 : ℤ) : ℝ) := by
      exact_mod_cast h3
    push_cast at h3r
    linarith

theorem ineq_4_core {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ)
    (ha : ∀ j, 0 < a j) (hb : 0 < b) (hbA : b < bigA a)
    (hτ : 2 * tPrime a b + bigA a < τ)
    (π : Equiv.Perm (Fin (t + tPrime a b))) :
    (1 / 2 : ℝ) * tPrime a b * (tPrime a b + 1) * τ ≤
      (tailWeighted (wtP a b τ) (fun _ => 1) π t : ℝ) := by
  obtain ⟨N, Y, hN, hY, hT⟩ := tard_tail1 a b τ π
  have hY0 : 0 ≤ Y := by rw [hY]; exact tard_Y_nonneg a b π
  have h2N : (2 : ℝ) * N = (tPrime a b : ℝ) ^ 2 + tPrime a b := by exact_mod_cast hN
  have hTr : (tailWeighted (wtP a b τ) (fun _ => 1) π t : ℝ) = τ * N + Y := by
    rw [hT]; push_cast; ring
  have hY0r : (0 : ℝ) ≤ Y := by exact_mod_cast hY0
  rw [hTr]
  have key : (1 / 2 : ℝ) * tPrime a b * (tPrime a b + 1) * τ = τ * N := by
    linear_combination (-(τ : ℝ) / 2) * h2N
  linarith

theorem ineq_5_core {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ)
    (ha : ∀ j, 0 < a j) (hb : 0 < b) (hbA : b < bigA a)
    (hτ : 2 * tPrime a b + bigA a < τ)
    (π : Equiv.Perm (Fin (t + tPrime a b))) :
    ∃ π' : Equiv.Perm (Fin (t + tPrime a b)),
      (∀ i : Fin (t + tPrime a b), i.val < t → π' i = π i) ∧
      (tailWeighted (wtP a b τ) (fun _ => 1) π' t : ℝ) ≤
        (1 / 2 : ℝ) * tPrime a b * (tPrime a b + 1) * τ
          + (1 / 2 : ℝ) * (t + 1) * ((bigA a : ℝ) - b - cPi a b τ π) := by
  obtain ⟨π', hs, h⟩ := tard_ineq5 a b τ π
  refine ⟨π', hs, ?_⟩
  have hr : ((2 * tailWeighted (wtP a b τ) (fun _ => 1) π' t : ℤ) : ℝ) ≤
      (((tPrime a b : ℤ) * (tPrime a b + 1) * τ
          + ((t : ℤ) + 1) * ((bigA a : ℤ) - b - cPi a b τ π) : ℤ) : ℝ) := by
    exact_mod_cast h
  push_cast at hr
  linarith

theorem ineq_6_core {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ)
    (ha : ∀ j, 0 < a j) (hb : 0 < b) (hbA : b < bigA a)
    (hτ : 2 * tPrime a b + bigA a < τ)
    (π : Equiv.Perm (Fin (t + tPrime a b))) :
    (yThr a b τ : ℝ) - (tPrime a b + 1) * (τ : ℝ) * cPi a b τ π - tPrime a b ≤
      (tailWeighted (wtP a b τ) (wtW a b τ) π t : ℝ) := by
  have h := tard_ineq6 a b τ hbA π
  have hr : (((yThr a b τ : ℤ) - (tPrime a b + 1) * τ * cPi a b τ π - tPrime a b : ℤ) : ℝ) ≤
      ((tailWeighted (wtP a b τ) (wtW a b τ) π t : ℤ) : ℝ) := by exact_mod_cast h
  push_cast at hr
  exact hr

theorem ineq_7_core {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ)
    (ha : ∀ j, 0 < a j) (hb : 0 < b) (hbA : b < bigA a)
    (hτ : 2 * tPrime a b + bigA a < τ)
    (π : Equiv.Perm (Fin (t + tPrime a b))) :
    ∃ π' : Equiv.Perm (Fin (t + tPrime a b)),
      (∀ i : Fin (t + tPrime a b), i.val < t → π' i = π i) ∧
      (tailWeighted (wtP a b τ) (wtW a b τ) π' t : ℝ) ≤
        (yThr a b τ : ℝ) - (tPrime a b + 1) * (τ : ℝ) * cPi a b τ π
          - (1 / 2 : ℝ) * (t + 1) * cPi a b τ π := by
  obtain ⟨π', hs, h⟩ := tard_ineq7 a b τ hbA π
  refine ⟨π', hs, ?_⟩
  have hr : ((2 * tailWeighted (wtP a b τ) (wtW a b τ) π' t : ℤ) : ℝ) ≤
      ((2 * (yThr a b τ : ℤ) - 2 * (tPrime a b + 1) * τ * cPi a b τ π
          - ((t : ℤ) + 1) * cPi a b τ π : ℤ) : ℝ) := by
    exact_mod_cast h
  push_cast at hr
  linarith


lemma tard_order_pos {n : ℕ} (p w d : Fin n → ℕ) (π : Equiv.Perm (Fin n)) :
    orderTWT p w d π = ∑ i : Fin n, (w (π i) : ℤ) *
      max 0 ((posCompletion p π (i.val + 1) : ℤ) - d (π i)) := by
  unfold orderTWT totalWeightedTardiness
  rw [← Equiv.sum_comp π]
  apply sum_congr rfl; intro i _
  unfold tardiness completion noIdleStart
  simp only [Equiv.symm_apply_apply]
  rw [tard_posCompletion_succ]

lemma tard_pos_tail {t m : ℕ} (p : Fin (t+m) → ℕ) (π : Equiv.Perm (Fin (t+m))) (j : Fin m) :
    posCompletion p π (t + j.val + 1) = posCompletion p π t +
      ∑ k ∈ univ.filter (· ≤ j), p (π (Fin.natAdd t k)) := by
  rw [tard_pos_split p π (t + j.val + 1), tard_pos_head]
  have e1 : ∀ x : Fin t, x.val < t + j.val + 1 := fun x => by have := x.isLt; omega
  simp only [e1, if_true]
  rw [Finset.sum_filter]
  congr 1
  apply sum_congr rfl; intro k _
  have : (t + k.val < t + j.val + 1) ↔ k ≤ j := by simp only [Fin.le_def]; omega
  simp only [this]

lemma tard_order_split {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ) (π : Equiv.Perm (Fin (t + tPrime a b))) :
    orderTWT (wtP a b τ) (wtW a b τ) (wtD a b τ) π =
      ∑ i : Fin t, (wtW a b τ (π (Fin.castAdd (tPrime a b) i)) : ℤ) *
        max 0 ((posCompletion (wtP a b τ) π (i.val + 1) : ℤ) - ((t * τ + b : ℕ) : ℤ)) +
      ∑ j : Fin (tPrime a b), (wtW a b τ (π (Fin.natAdd t j)) : ℤ) *
        max 0 (cPi a b τ π + ∑ k ∈ univ.filter (· ≤ j), (wtP a b τ (π (Fin.natAdd t k)) : ℤ)) := by
  rw [tard_order_pos, Fin.sum_univ_add]
  congr 1
  apply sum_congr rfl; intro j _
  congr 2
  have := tard_pos_tail (wtP a b τ) π j
  simp only [Fin.val_natAdd]
  rw [this]
  unfold cPi
  push_cast
  simp [wtD]
  ring

lemma tard_w_ge {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ) (j : Fin (t + tPrime a b)) :
    (τ : ℤ) + 1 ≤ (wtW a b τ j : ℤ) := by
  simp only [wtW]; push_cast; have := Int.natCast_nonneg (aExt a b j); linarith

lemma tard_sum_w {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ) (π : Equiv.Perm (Fin (t + tPrime a b))) :
    ∑ j : Fin (tPrime a b), (wtW a b τ (π (Fin.natAdd t j)) : ℤ) =
      (tPrime a b : ℤ) * (τ + 1) + ∑ j, (tailG a b π j : ℤ) := by
  have : ∀ j : Fin (tPrime a b), (wtW a b τ (π (Fin.natAdd t j)) : ℤ) =
      ((τ : ℤ) + 1) + (tailG a b π j : ℤ) := by
    intro j; simp [wtW, tailG]; ring
  simp only [this, sum_add_distrib]
  simp
  ring

lemma tard_tail_wS {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ) (π : Equiv.Perm (Fin (t + tPrime a b))) :
    tailWeighted (wtP a b τ) (wtW a b τ) π t = ∑ j : Fin (tPrime a b),
      (wtW a b τ (π (Fin.natAdd t j)) : ℤ) *
        ∑ k ∈ univ.filter (· ≤ j), (wtP a b τ (π (Fin.natAdd t k)) : ℤ) :=
  tard_tail_split _ _ π

lemma tard_S_nonneg {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ) (π : Equiv.Perm (Fin (t + tPrime a b)))
    (j : Fin (tPrime a b)) :
    0 ≤ ∑ k ∈ univ.filter (· ≤ j), (wtP a b τ (π (Fin.natAdd t k)) : ℤ) :=
  sum_nonneg (fun _ _ => by positivity)

theorem claim_A_core {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ)
    (ha : ∀ j, 0 < a j) (hb : 0 < b) (hbA : b < bigA a)
    (hτ : 2 * tPrime a b + bigA a < τ)
    (π : Equiv.Perm (Fin (t + tPrime a b))) (hc : cPi a b τ π = 0) :
    ∃ π' : Equiv.Perm (Fin (t + tPrime a b)), cPi a b τ π' = 0 ∧
      orderTWT (wtP a b τ) (wtW a b τ) (wtD a b τ) π' ≤ (yThr a b τ : ℤ) := by
  obtain ⟨π', hs, h7⟩ := tard_ineq7 a b τ hbA π
  have hc' : cPi a b τ π' = 0 := by rw [tard_cPi_congr a b τ π π' hs]; exact hc
  refine ⟨π', hc', ?_⟩
  rw [tard_order_split, hc']
  have hhead : ∑ i : Fin t, (wtW a b τ (π' (Fin.castAdd (tPrime a b) i)) : ℤ) *
        max 0 ((posCompletion (wtP a b τ) π' (i.val + 1) : ℤ) - ((t * τ + b : ℕ) : ℤ)) = 0 := by
    apply sum_eq_zero; intro i _
    have h1 : (posCompletion (wtP a b τ) π' (i.val + 1) : ℤ) ≤ posCompletion (wtP a b τ) π' t := by
      exact_mod_cast tard_posCompletion_mono _ _ (by have := i.isLt; omega)
    have h2 : (posCompletion (wtP a b τ) π' t : ℤ) = ((t * τ + b : ℕ) : ℤ) := by
      unfold cPi at hc'; linarith
    have : max 0 ((posCompletion (wtP a b τ) π' (i.val + 1) : ℤ) - ((t * τ + b : ℕ) : ℤ)) = 0 :=
      max_eq_left (by linarith)
    rw [this]; ring
  have htail : ∑ j : Fin (tPrime a b), (wtW a b τ (π' (Fin.natAdd t j)) : ℤ) *
        max 0 ((0:ℤ) + ∑ k ∈ univ.filter (· ≤ j), (wtP a b τ (π' (Fin.natAdd t k)) : ℤ)) =
      tailWeighted (wtP a b τ) (wtW a b τ) π' t := by
    rw [tard_tail_wS]
    apply sum_congr rfl; intro j _
    rw [max_eq_right (by have := tard_S_nonneg a b τ π' j; linarith)]
    ring
  rw [hhead, htail, zero_add]
  have hc2 : cPi a b τ π = 0 := hc
  rw [hc2] at h7
  linarith

theorem claim_B_core {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ)
    (ha : ∀ j, 0 < a j) (hb : 0 < b) (hbA : b < bigA a)
    (hτ : 2 * tPrime a b + bigA a < τ)
    (π : Equiv.Perm (Fin (t + tPrime a b))) (hc : 0 < cPi a b τ π) :
    (yThr a b τ : ℤ) < orderTWT (wtP a b τ) (wtW a b τ) (wtD a b τ) π := by
  rw [tard_order_split]
  have h6 := tard_ineq6 a b τ hbA π
  have ht : 0 < t := by
    by_contra h0
    have : t = 0 := by omega
    subst this
    have : cPi a b τ π = -(b : ℤ) := by
      rw [tard_cPi_eq]; simp
    omega
  -- head term
  have hhead : ((τ : ℤ) + 1) * cPi a b τ π ≤
      ∑ i : Fin t, (wtW a b τ (π (Fin.castAdd (tPrime a b) i)) : ℤ) *
        max 0 ((posCompletion (wtP a b τ) π (i.val + 1) : ℤ) - ((t * τ + b : ℕ) : ℤ)) := by
    have hi : t - 1 < t := by omega
    have hsingle := Finset.single_le_sum (f := fun i : Fin t => (wtW a b τ (π (Fin.castAdd (tPrime a b) i)) : ℤ) *
        max 0 ((posCompletion (wtP a b τ) π (i.val + 1) : ℤ) - ((t * τ + b : ℕ) : ℤ)))
      (fun i _ => mul_nonneg (by positivity) (le_max_left _ _)) (Finset.mem_univ (⟨t - 1, hi⟩ : Fin t))
    refine le_trans ?_ hsingle
    simp only
    have e : (t - 1) + 1 = t := by omega
    rw [e]
    have hm : max 0 ((posCompletion (wtP a b τ) π t : ℤ) - ((t * τ + b : ℕ) : ℤ)) = cPi a b τ π := by
      unfold cPi; unfold cPi at hc; exact max_eq_right hc.le
    rw [hm]
    exact mul_le_mul_of_nonneg_right (tard_w_ge a b τ _) hc.le
  have htail : ∑ j : Fin (tPrime a b), (wtW a b τ (π (Fin.natAdd t j)) : ℤ) *
        max 0 (cPi a b τ π + ∑ k ∈ univ.filter (· ≤ j), (wtP a b τ (π (Fin.natAdd t k)) : ℤ)) =
      cPi a b τ π * ∑ j : Fin (tPrime a b), (wtW a b τ (π (Fin.natAdd t j)) : ℤ) +
        tailWeighted (wtP a b τ) (wtW a b τ) π t := by
    rw [tard_tail_wS, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl; intro j _
    rw [max_eq_right (by have := tard_S_nonneg a b τ π j; linarith)]
    ring
  have hsw : (tPrime a b : ℤ) * (τ + 1) ≤ ∑ j : Fin (tPrime a b), (wtW a b τ (π (Fin.natAdd t j)) : ℤ) := by
    calc (tPrime a b : ℤ) * (τ + 1) = ∑ j : Fin (tPrime a b), ((τ : ℤ) + 1) := by simp
      _ ≤ _ := sum_le_sum (fun j _ => tard_w_ge a b τ _)
  rw [htail] at *
  have hprod : cPi a b τ π * ((tPrime a b : ℤ) * (τ + 1)) ≤
      cPi a b τ π * ∑ j : Fin (tPrime a b), (wtW a b τ (π (Fin.natAdd t j)) : ℤ) :=
    mul_le_mul_of_nonneg_left hsw hc.le
  have hc1 : (1 : ℤ) ≤ cPi a b τ π := hc
  have hm0 : (0 : ℤ) ≤ tPrime a b := by positivity
  nlinarith [hhead, hprod, h6, mul_le_mul_of_nonneg_left hc1 hm0]

theorem claim_C_core {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ)
    (ha : ∀ j, 0 < a j) (hb : 0 < b) (hbA : b < bigA a)
    (hτ : 2 * tPrime a b + bigA a < τ)
    (π : Equiv.Perm (Fin (t + tPrime a b))) (hc : cPi a b τ π < 0) :
    (yThr a b τ : ℤ) < orderTWT (wtP a b τ) (wtW a b τ) (wtD a b τ) π := by
  rw [tard_order_split]
  have h6 := tard_ineq6 a b τ hbA π
  have hhead : (0 : ℤ) ≤ ∑ i : Fin t, (wtW a b τ (π (Fin.castAdd (tPrime a b) i)) : ℤ) *
        max 0 ((posCompletion (wtP a b τ) π (i.val + 1) : ℤ) - ((t * τ + b : ℕ) : ℤ)) :=
    sum_nonneg (fun i _ => mul_nonneg (by positivity) (le_max_left _ _))
  have htail : cPi a b τ π * ∑ j : Fin (tPrime a b), (wtW a b τ (π (Fin.natAdd t j)) : ℤ) +
        tailWeighted (wtP a b τ) (wtW a b τ) π t ≤
      ∑ j : Fin (tPrime a b), (wtW a b τ (π (Fin.natAdd t j)) : ℤ) *
        max 0 (cPi a b τ π + ∑ k ∈ univ.filter (· ≤ j), (wtP a b τ (π (Fin.natAdd t k)) : ℤ)) := by
    rw [tard_tail_wS, mul_sum, ← sum_add_distrib]
    apply sum_le_sum; intro j _
    have hw : (0 : ℤ) ≤ (wtW a b τ (π (Fin.natAdd t j)) : ℤ) := by positivity
    have := le_max_right 0 (cPi a b τ π + ∑ k ∈ univ.filter (· ≤ j), (wtP a b τ (π (Fin.natAdd t k)) : ℤ))
    calc cPi a b τ π * (wtW a b τ (π (Fin.natAdd t j)) : ℤ) +
          (wtW a b τ (π (Fin.natAdd t j)) : ℤ) * ∑ k ∈ univ.filter (· ≤ j), (wtP a b τ (π (Fin.natAdd t k)) : ℤ)
        = (wtW a b τ (π (Fin.natAdd t j)) : ℤ) *
          (cPi a b τ π + ∑ k ∈ univ.filter (· ≤ j), (wtP a b τ (π (Fin.natAdd t k)) : ℤ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this hw
  have hsw := tard_sum_w a b τ π
  have hQ := tard_Q a b τ π
  have hQA : ∑ j, (tailG a b π j : ℤ) ≤ bigA a := by
    have := tard_head_tail a b π
    have h0 : (0 : ℤ) ≤ ∑ i : Fin t, (aExt a b (π (Fin.castAdd (tPrime a b) i)) : ℤ) :=
      sum_nonneg (fun _ _ => by positivity)
    unfold tailG; linarith
  have hτ' : (2 * (tPrime a b : ℤ) + bigA a + 1 ≤ τ) := by exact_mod_cast hτ
  have hm0 : (0 : ℤ) ≤ tPrime a b := by positivity
  -- c * Σw ≥ c * (m(τ+1) + A)
  have hprod : cPi a b τ π * ((tPrime a b : ℤ) * (τ + 1) + bigA a) ≤
      cPi a b τ π * ∑ j : Fin (tPrime a b), (wtW a b τ (π (Fin.natAdd t j)) : ℤ) := by
    rw [hsw]
    exact mul_le_mul_of_nonpos_left (by linarith) hc.le
  have hc1 : cPi a b τ π ≤ -1 := by omega
  have hbig : (0 : ℤ) ≤ (τ : ℤ) - tPrime a b - bigA a - tPrime a b - 1 := by linarith
  have h7 : (tPrime a b : ℤ) + 1 ≤ -(cPi a b τ π) * ((τ : ℤ) - tPrime a b - bigA a) := by
    nlinarith [mul_nonneg hbig (show (0:ℤ) ≤ -(cPi a b τ π) - 1 by linarith)]
  nlinarith [hhead, htail, hprod, h6, h7]


lemma tard_perm_of_card {t m : ℕ} (U : Finset (Fin (t + m))) (hU : U.card = t) :
    ∃ π : Equiv.Perm (Fin (t + m)),
      (∀ i, π (Fin.castAdd m i) ∈ U) ∧ ∀ j, π (Fin.natAdd t j) ∉ U := by
  classical
  have c1 : Fintype.card {x // x ∈ U} = Fintype.card (Fin t) := by simp [hU]
  have c2 : Fintype.card {x // x ∉ U} = Fintype.card (Fin m) := by
    rw [Fintype.card_subtype_compl]; simp [hU]
  let f1 : Fin t ≃ {x // x ∈ U} := (Fintype.equivOfCardEq c1).symm
  let f2 : Fin m ≃ {x // x ∉ U} := (Fintype.equivOfCardEq c2).symm
  refine ⟨finSumFinEquiv.symm.trans ((Equiv.sumCongr f1 f2).trans (Equiv.sumCompl (· ∈ U))), ?_, ?_⟩
  · intro i; simp
  · intro j; simp; exact (f2 j).2

lemma tard_head_sum_eq {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ) (π : Equiv.Perm (Fin (t + tPrime a b))) :
    posCompletion (wtP a b τ) π t = t * τ + b ↔
      ∑ i : Fin t, aExt a b (π (Fin.castAdd (tPrime a b) i)) = b := by
  rw [tard_pos_head]
  simp only [wtP, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  exact Nat.add_left_cancel_iff

lemma tard_t_le {t : ℕ} (a : Fin t → ℕ) (b : ℕ) (ha : ∀ j, 0 < a j) (hbA : b < bigA a) :
    t ≤ tPrime a b := by
  have ht : 0 < t := by
    by_contra h0
    have : t = 0 := by omega
    subst this
    simp [bigA] at hbA
  have h := tard_tPrime_ge a b hbA
  have hs : 1 ≤ aStar a := by
    have := Finset.le_sup (f := a) (Finset.mem_univ (⟨0, ht⟩ : Fin t))
    have := ha ⟨0, ht⟩
    unfold aStar; omega
  have hAb : (1 : ℤ) ≤ (bigA a : ℤ) - b := by omega
  have hs' : (1 : ℤ) ≤ (aStar a : ℤ) := by exact_mod_cast hs
  have ht' : (1 : ℤ) ≤ t := by exact_mod_cast ht
  have h2 : (t : ℤ) ≤ tPrime a b := by
    nlinarith [mul_nonneg (show (0:ℤ) ≤ t by linarith) (show (0:ℤ) ≤ (t:ℤ) + 1 by linarith),
      mul_le_mul hs' hs' (by norm_num) (by linarith), mul_nonneg (show (0:ℤ) ≤ (t:ℤ) + 1 by linarith) (show (0:ℤ) ≤ (bigA a : ℤ) - b - 1 by linarith)]
  exact_mod_cast h2

lemma tard_knap_fwd {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ) (ha : ∀ j, 0 < a j) (hbA : b < bigA a)
    (S : Finset (Fin t)) (hS : ∑ j ∈ S, a j = b) :
    ∃ π : Equiv.Perm (Fin (t + tPrime a b)),
      ∑ i : Fin t, aExt a b (π (Fin.castAdd (tPrime a b) i)) = b := by
  have hm := tard_t_le a b ha hbA
  have hSc : S.card ≤ t := by simpa using Finset.card_le_univ S
  obtain ⟨D, -, hD⟩ := Finset.exists_subset_card_eq (s := (univ : Finset (Fin (tPrime a b))))
    (n := t - S.card) (by simp; omega)
  have hdisj : Disjoint (S.map (Fin.castAddEmb (tPrime a b))) (D.map (Fin.natAddEmb t)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [mem_map, Fin.castAddEmb_apply, Fin.natAddEmb_apply] at hx hx'
    obtain ⟨i, _, rfl⟩ := hx
    obtain ⟨j, _, hj⟩ := hx'
    have := congrArg Fin.val hj
    simp at this
    have := i.isLt; omega
  set U := S.map (Fin.castAddEmb (tPrime a b)) ∪ D.map (Fin.natAddEmb t) with hU
  have hUc : U.card = t := by
    rw [hU, Finset.card_union_of_disjoint hdisj]; simp [hD]; omega
  obtain ⟨π, h1, h2⟩ := tard_perm_of_card U hUc
  refine ⟨π, ?_⟩
  let V := (univ : Finset (Fin t)).image (fun i => π (Fin.castAdd (tPrime a b) i))
  have hinj : Function.Injective (fun i : Fin t => π (Fin.castAdd (tPrime a b) i)) := by
    intro x y h
    have := π.injective h
    exact Fin.castAdd_injective _ _ this
  have hVsub : V ⊆ U := by
    intro x hx
    simp only [V, mem_image, mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    exact h1 i
  have hVc : V.card = t := by simp [V, Finset.card_image_of_injective _ hinj]
  have hVU : V = U := Finset.eq_of_subset_of_card_le hVsub (by omega)
  have : ∑ i : Fin t, aExt a b (π (Fin.castAdd (tPrime a b) i)) = ∑ x ∈ V, aExt a b x :=
    (Finset.sum_image (fun x _ y _ h => hinj h)).symm
  rw [this, hVU, hU, Finset.sum_union hdisj]
  simp only [sum_map, Fin.castAddEmb_apply, Fin.natAddEmb_apply]
  have h3 : ∀ i : Fin t, aExt a b (Fin.castAdd (tPrime a b) i) = a i := by intro i; simp [aExt]
  have h4 : ∀ j : Fin (tPrime a b), aExt a b (Fin.natAdd t j) = 0 := by intro j; simp [aExt]
  simp [h3, h4, hS]

lemma tard_knap_bwd {t : ℕ} (a : Fin t → ℕ) (b : ℕ) (π : Equiv.Perm (Fin (t + tPrime a b)))
    (h : ∑ i : Fin t, aExt a b (π (Fin.castAdd (tPrime a b) i)) = b) :
    ∃ S : Finset (Fin t), ∑ j ∈ S, a j = b := by
  classical
  let V := (univ : Finset (Fin t)).image (fun i => π (Fin.castAdd (tPrime a b) i))
  have hinj : Function.Injective (fun i : Fin t => π (Fin.castAdd (tPrime a b) i)) := by
    intro x y h
    have := π.injective h
    exact Fin.castAdd_injective _ _ this
  refine ⟨univ.filter (fun j : Fin t => Fin.castAdd (tPrime a b) j ∈ V), ?_⟩
  have e1 : ∑ i : Fin t, aExt a b (π (Fin.castAdd (tPrime a b) i)) = ∑ x ∈ V, aExt a b x :=
    (Finset.sum_image (fun x _ y _ h => hinj h)).symm
  have e2 : ∑ x ∈ V, aExt a b x = ∑ x : Fin (t + tPrime a b), if x ∈ V then aExt a b x else 0 := by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have h3 : ∀ i : Fin t, aExt a b (Fin.castAdd (tPrime a b) i) = a i := by intro i; simp [aExt]
  have h4 : ∀ j : Fin (tPrime a b), aExt a b (Fin.natAdd t j) = 0 := by intro j; simp [aExt]
  have key : ∑ j ∈ univ.filter (fun j : Fin t => Fin.castAdd (tPrime a b) j ∈ V), a j =
      ∑ i : Fin t, aExt a b (π (Fin.castAdd (tPrime a b) i)) := by
    rw [e1, e2, Fin.sum_univ_add, Finset.sum_filter]
    simp [h3, h4]
  rw [key]; exact h

theorem knapsack_iff_split_core {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ)
    (ha : ∀ j, 0 < a j) (hb : 0 < b) (hbA : b < bigA a)
    (hτ : 2 * tPrime a b + bigA a < τ) :
    (KnapsackYes a b ↔
      ∃ π : Equiv.Perm (Fin (t + tPrime a b)), posCompletion (wtP a b τ) π t = t * τ + b) ∧
    ∀ π : Equiv.Perm (Fin (t + tPrime a b)),
      -(b : ℤ) ≤ cPi a b τ π ∧ cPi a b τ π ≤ (bigA a : ℤ) - b := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨S, hS⟩
    obtain ⟨π, hπ⟩ := tard_knap_fwd a b τ ha hbA S hS
    exact ⟨π, (tard_head_sum_eq a b τ π).2 hπ⟩
  · rintro ⟨π, hπ⟩
    exact tard_knap_bwd a b π ((tard_head_sum_eq a b τ π).1 hπ)
  · intro π
    have h := tard_head_tail a b π
    have h0 : (0 : ℤ) ≤ ∑ i : Fin t, (aExt a b (π (Fin.castAdd (tPrime a b) i)) : ℤ) :=
      sum_nonneg (fun _ _ => by positivity)
    have h1 : (0 : ℤ) ≤ ∑ j : Fin (tPrime a b), (aExt a b (π (Fin.natAdd t j)) : ℤ) :=
      sum_nonneg (fun _ _ => by positivity)
    rw [tard_cPi_eq]
    constructor <;> linarith


theorem theorem_4d_equivalence_core {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ)
    (ha : ∀ j, 0 < a j) (hb : 0 < b) (hbA : b < bigA a)
    (hτ : 2 * tPrime a b + bigA a < τ) :
    KnapsackYes a b ↔ HasScheduleLE (wtP a b τ) (wtW a b τ) (wtD a b τ) (yThr a b τ) := by
  have hsplit := (knapsack_iff_split_core a b τ ha hb hbA hτ).1
  constructor
  · intro hK
    obtain ⟨π, hπ⟩ := hsplit.1 hK
    have hc : cPi a b τ π = 0 := by
      unfold cPi; rw [hπ]; simp
    obtain ⟨π', -, hπ'⟩ := claim_A_core a b τ ha hb hbA hτ π hc
    exact ⟨noIdleStart (wtP a b τ) π', tard_noIdle_feasible _ π', hπ'⟩
  · rintro ⟨S, hfeas, hle⟩
    obtain ⟨-, hid⟩ := idle_time_removal_core (wtP a b τ) (wtW a b τ) (wtD a b τ)
    obtain ⟨π, hπ⟩ := hid S hfeas
    have hπy : orderTWT (wtP a b τ) (wtW a b τ) (wtD a b τ) π ≤ (yThr a b τ : ℤ) := le_trans hπ hle
    apply hsplit.2
    refine ⟨π, ?_⟩
    rcases lt_trichotomy (cPi a b τ π) 0 with h | h | h
    · exact absurd (claim_C_core a b τ ha hb hbA hτ π h) (not_lt.mpr hπy)
    · unfold cPi at h
      have : ((posCompletion (wtP a b τ) π t : ℕ) : ℤ) = ((t * τ + b : ℕ) : ℤ) := by linarith
      exact_mod_cast this
    · exact absurd (claim_B_core a b τ ha hb hbA hτ π h) (not_lt.mpr hπy)


end SchedComplexity.Tardiness

open SchedComplexity.Tardiness


theorem solution {t : ℕ} (a : Fin t → ℕ) (b τ : ℕ)
    (ha : ∀ j, 0 < a j) (hb : 0 < b) (hbA : b < bigA a)
    (hτ : 2 * tPrime a b + bigA a < τ) :
    (KnapsackYes a b ↔
      ∃ π : Equiv.Perm (Fin (t + tPrime a b)), posCompletion (wtP a b τ) π t = t * τ + b) ∧
    ∀ π : Equiv.Perm (Fin (t + tPrime a b)),
      -(b : ℤ) ≤ cPi a b τ π ∧ cPi a b τ π ≤ (bigA a : ℤ) - b := by
  exact knapsack_iff_split_core a b τ ha hb hbA hτ
