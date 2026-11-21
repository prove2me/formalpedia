-- Prove2me | solution 1 for TranspositionIID.Main.proposition_3_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T18:13:41.867629+00:00
-- url     : https://prove2.me/submissions/d255299c-33bd-43f5-a4bf-2b822d0f7250

import Mathlib
import Definitions.Def_TranspositionIID_Main_Stationary
import Definitions.Def_TranspositionIID_Main_Auxiliary
import Definitions.Def_TranspositionIID_Main_Exclusion
import Definitions.Def_TranspositionIID_Main_Entropy
import Theorems.Thm_TranspositionIID_Main_lemma_3_2
section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.Rev
open TranspositionIID.Main

variable {n : ℕ}

def pr (a : Equiv.Perm (Fin n)) (i : Fin n) : Fin n :=
  ⟨(a i).val - 1, by have := (a i).isLt; omega⟩

lemma T_pos {a : Equiv.Perm (Fin n)} {i : Fin n} (h : 0 < (a i).val) :
    transposeRequest a i = a.trans (Equiv.swap (a i) (pr a i)) := by
  unfold transposeRequest; rw [dif_pos h]; rfl

lemma T_zero {a : Equiv.Perm (Fin n)} {i : Fin n} (h : ¬ 0 < (a i).val) :
    transposeRequest a i = a := by
  unfold transposeRequest; rw [dif_neg h]

lemma pow_markov {S : Type*} [Fintype S] [DecidableEq S] (P : Matrix S S ℝ)
    (hP : ActuarialValuation.isFiniteMarkovKernel P) (t : ℕ) :
    (∀ a b, 0 ≤ (P ^ t) a b) ∧ ∀ a, ∑ b, (P ^ t) a b = 1 := by
  induction t with
  | zero =>
    refine ⟨fun a b => ?_, fun a => ?_⟩
    · simp [Matrix.one_apply]; split_ifs <;> simp
    · simp [Matrix.one_apply]
  | succ t ih =>
    refine ⟨fun a b => ?_, fun a => ?_⟩
    · rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun c _ => mul_nonneg (ih.1 a c) (hP.1 c b)
    · rw [pow_succ]
      simp only [Matrix.mul_apply]
      rw [Finset.sum_comm]
      calc ∑ c, ∑ b, (P ^ t) a c * P c b = ∑ c, (P ^ t) a c := by
            apply Finset.sum_congr rfl; intro c _
            rw [← Finset.mul_sum, hP.2 c, mul_one]
        _ = 1 := ih.2 a

lemma weight_swap (q : Fin n → ℝ) (a : Equiv.Perm (Fin n)) (i : Fin n) (h : 0 < (a i).val) :
    stationaryWeight q (a.trans (Equiv.swap (a i) (pr a i))) * q (a.symm (pr a i)) =
      stationaryWeight q a * q i := by
  set j := a.symm (pr a i) with hj
  have haj : a j = pr a i := by simp [hj]
  have hji : j ≠ i := by
    intro e; rw [e] at haj
    have := congrArg Fin.val haj
    simp [pr] at this; omega
  set z := a.trans (Equiv.swap (a i) (pr a i)) with hz
  have hzi : z i = pr a i := by simp [hz]
  have hzj : z j = a i := by simp [hz, haj]
  have hzk : ∀ k, k ≠ i → k ≠ j → z k = a k := by
    intro k hki hkj
    simp only [hz, Equiv.trans_apply]
    apply Equiv.swap_apply_of_ne_of_ne
    · intro e; exact hki (a.injective e)
    · intro e; apply hkj; rw [← haj] at e; exact a.injective e
  have hprv : (pr a i).val = (a i).val - 1 := rfl
  have hlt := (a i).isLt
  unfold stationaryWeight
  have hmem_i : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
  have hmem_j : j ∈ (Finset.univ : Finset (Fin n)).erase i := by simp [hji]
  rw [← Finset.mul_prod_erase _ _ hmem_i, ← Finset.mul_prod_erase _ _ hmem_i,
    ← Finset.mul_prod_erase _ _ hmem_j, ← Finset.mul_prod_erase _ _ hmem_j]
  have hrest : ∏ k ∈ ((Finset.univ : Finset (Fin n)).erase i).erase j, q k ^ (n - 1 - (z k).val) =
      ∏ k ∈ ((Finset.univ : Finset (Fin n)).erase i).erase j, q k ^ (n - 1 - (a k).val) := by
    apply Finset.prod_congr rfl
    intro k hk
    simp only [Finset.mem_erase] at hk
    rw [hzk k hk.2.1 hk.1]
  rw [hrest, hzi, hzj, haj]
  have e1 : n - 1 - (pr a i).val = (n - 1 - (a i).val) + 1 := by rw [hprv]; omega
  have e2 : n - 1 - (a i).val + 1 = n - 1 - (pr a i).val := e1.symm
  rw [e1, pow_succ]
  ring

lemma weight_pos (q : Fin n → ℝ) (hpos : ∀ i, 0 < q i) (a : Equiv.Perm (Fin n)) :
    0 < stationaryWeight q a :=
  Finset.prod_pos fun i _ => pow_pos (hpos i) _

lemma partition_pos (q : Fin n → ℝ) (hpos : ∀ i, 0 < q i) : 0 < partitionFunction q :=
  Finset.sum_pos (fun a _ => weight_pos q hpos a) Finset.univ_nonempty

lemma law_pos (q : Fin n → ℝ) (hpos : ∀ i, 0 < q i) (a : Equiv.Perm (Fin n)) :
    0 < stationaryLaw q a :=
  div_pos (weight_pos q hpos a) (partition_pos q hpos)

end TranspositionIID.Main.Dev.Rev
end

section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.C1
open TranspositionIID.Main TranspositionIID.Main.Dev

variable {n : ℕ}

def nonint (p : Fin n → ℝ) (x θ : ℝ) (k : Fin n) : Prop :=
  Real.log (p k) ≤ x ∨ x + θ < Real.log (p k)

lemma mem_pairs (p : Fin n → ℝ) (x θ : ℝ) (σ : ListState n) (k l : Fin n) :
    (k, l) ∈ auxiliaryPairs p x θ σ ↔
      nonint p x θ k ∧ nonint p x θ l ∧ σ k < σ l ∧
        ∀ m, σ k < σ m → σ m < σ l → ¬ nonint p x θ m := by
  unfold auxiliaryPairs nonint
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, fun m hm1 hm2 hm => ?_⟩
    have := h4 m hm1 hm2
    rcases hm with h | h <;> linarith [this.1, this.2]
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, fun m hm1 hm2 => ?_⟩
    have := h4 m hm1 hm2
    simp only [not_or, not_le, not_lt] at this
    exact this

lemma swap_nonint (p : Fin n → ℝ) (x θ : ℝ) (i j : Fin n) (hi : nonint p x θ i)
    (hj : nonint p x θ j) (m : Fin n) :
    nonint p x θ (Equiv.swap i j m) ↔ nonint p x θ m := by
  by_cases h1 : m = i
  · subst h1; simp [hj, hi]
  · by_cases h2 : m = j
    · subst h2; simp [hi, hj]
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]

lemma pairs_comp (p : Fin n → ℝ) (x θ : ℝ) (σ : ListState n) (τ : Equiv.Perm (Fin n))
    (hτ : ∀ m, nonint p x θ (τ m) ↔ nonint p x θ m) (k l : Fin n) :
    (k, l) ∈ auxiliaryPairs p x θ (τ.trans σ) ↔ (τ k, τ l) ∈ auxiliaryPairs p x θ σ := by
  rw [mem_pairs, mem_pairs]
  simp only [Equiv.trans_apply, hτ]
  apply and_congr Iff.rfl; apply and_congr Iff.rfl; apply and_congr Iff.rfl
  constructor
  · intro h m' h1 h2
    have := h (τ.symm m') (by simpa using h1) (by simpa using h2)
    intro hm; apply this
    exact (hτ (τ.symm m')).1 (by simpa using hm)
  · intro h m h1 h2
    have := h (τ m) h1 h2
    exact fun hm => this ((hτ m).2 hm)

lemma trans_swap_eq (σ : ListState n) (i j : Fin n) :
    σ.trans (Equiv.swap (σ i) (σ j)) = (Equiv.swap i j).trans σ := by
  ext m
  simp only [Equiv.trans_apply]
  by_cases h1 : m = i
  · subst h1; simp
  · by_cases h2 : m = j
    · subst h2; simp
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2,
        Equiv.swap_apply_of_ne_of_ne (fun h => h1 (σ.injective h)) (fun h => h2 (σ.injective h))]

lemma weight_swap_gen (q : Fin n → ℝ) (σ : ListState n) (i j : Fin n) (hij : σ i < σ j) :
    stationaryWeight q ((Equiv.swap i j).trans σ) * q i ^ ((σ j).val - (σ i).val) =
      stationaryWeight q σ * q j ^ ((σ j).val - (σ i).val) := by
  have hne : i ≠ j := fun h => by subst h; exact lt_irrefl _ hij
  set η := (Equiv.swap i j).trans σ with hη
  have hηi : η i = σ j := by simp [hη]
  have hηj : η j = σ i := by simp [hη]
  have hηk : ∀ k, k ≠ i → k ≠ j → η k = σ k := fun k h1 h2 => by
    simp [hη, Equiv.swap_apply_of_ne_of_ne h1 h2]
  have hlt : (σ i).val < (σ j).val := hij
  have hi' := (σ i).isLt
  have hj' := (σ j).isLt
  unfold stationaryWeight
  have hmem_i : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
  have hmem_j : j ∈ (Finset.univ : Finset (Fin n)).erase i := by simp [hne.symm]
  rw [← Finset.mul_prod_erase _ _ hmem_i, ← Finset.mul_prod_erase _ _ hmem_i,
    ← Finset.mul_prod_erase _ _ hmem_j, ← Finset.mul_prod_erase _ _ hmem_j]
  have hrest : ∏ k ∈ ((Finset.univ : Finset (Fin n)).erase i).erase j, q k ^ (n - 1 - (η k).val) =
      ∏ k ∈ ((Finset.univ : Finset (Fin n)).erase i).erase j, q k ^ (n - 1 - (σ k).val) := by
    apply Finset.prod_congr rfl
    intro k hk
    simp only [Finset.mem_erase] at hk
    rw [hηk k hk.2.1 hk.1]
  rw [hrest, hηi, hηj]
  set d := (σ j).val - (σ i).val with hd
  have e1 : n - 1 - (σ i).val = (n - 1 - (σ j).val) + d := by omega
  rw [e1]
  rw [pow_add, pow_add]
  ring

end TranspositionIID.Main.Dev.C1
end

section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.C1
open TranspositionIID.Main TranspositionIID.Main.Dev

variable {n : ℕ}

lemma a_bounds (p : Fin n → ℝ) (hpos : ∀ i, 0 < p i) (i j : Fin n) (d : ℕ) :
    0 ≤ p j ^ d / (p j ^ d + p i ^ d) ∧ p j ^ d / (p j ^ d + p i ^ d) ≤ 1 := by
  have h1 := pow_pos (hpos i) d
  have h2 := pow_pos (hpos j) d
  constructor
  · positivity
  · rw [div_le_one (by positivity)]; linarith

lemma kappa_nonneg (p : Fin n → ℝ) (hpos : ∀ i, 0 < p i) (x : ℝ) (σ η : ListState n)
    (ij : Fin n × Fin n) : 0 ≤ auxiliaryPairKernel p x σ η ij := by
  unfold auxiliaryPairKernel
  have hb := a_bounds p hpos ij.1 ij.2 ((σ ij.2).val - (σ ij.1).val)
  by_cases h : (Real.log (p ij.1) ≤ x ↔ Real.log (p ij.2) ≤ x)
  · simp only [h, if_true]; split_ifs <;> norm_num
  · simp only [h, if_false]
    apply add_nonneg
    · split_ifs <;> linarith [hb.1]
    · split_ifs <;> linarith [hb.2]

lemma kappa_sum (p : Fin n → ℝ) (hpos : ∀ i, 0 < p i) (x : ℝ) (σ : ListState n)
    (ij : Fin n × Fin n) : ∑ η, auxiliaryPairKernel p x σ η ij = 1 := by
  unfold auxiliaryPairKernel
  by_cases h : (Real.log (p ij.1) ≤ x ↔ Real.log (p ij.2) ≤ x)
  · simp [h]
  · simp only [h, if_false, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring

lemma aux_markov (p : Fin n → ℝ) (hpos : ∀ i, 0 < p i) (x θ : ℝ) :
    ActuarialValuation.isFiniteMarkovKernel (auxiliaryKernel p x θ) := by
  constructor
  · intro σ η
    unfold auxiliaryKernel
    simp only
    split_ifs
    · norm_num
    · norm_num
    · exact div_nonneg (Finset.sum_nonneg fun ij _ => kappa_nonneg p hpos x σ η ij) (Nat.cast_nonneg _)
  · intro σ
    unfold auxiliaryKernel
    simp only
    by_cases hc : (auxiliaryPairs p x θ σ).card = 0
    · simp [hc]
    · simp only [hc, if_false]
      rw [← Finset.sum_div, Finset.sum_comm]
      simp_rw [kappa_sum p hpos x σ]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact div_self (by exact_mod_cast hc)

end TranspositionIID.Main.Dev.C1
end

section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.C1
open TranspositionIID.Main TranspositionIID.Main.Dev
open Classical

variable {n : ℕ}

noncomputable def S1 (p : Fin n → ℝ) (x θ : ℝ) (σ η : ListState n) : ℝ :=
  ∑ ij ∈ auxiliaryPairs p x θ σ, auxiliaryPairKernel p x σ η ij

def Opp (p : Fin n → ℝ) (x : ℝ) (ij : Fin n × Fin n) : Prop :=
  ¬ (Real.log (p ij.1) ≤ x ↔ Real.log (p ij.2) ≤ x)

noncomputable def aa (p : Fin n → ℝ) (σ : ListState n) (ij : Fin n × Fin n) : ℝ :=
  p ij.2 ^ ((σ ij.2).val - (σ ij.1).val) /
    (p ij.2 ^ ((σ ij.2).val - (σ ij.1).val) + p ij.1 ^ ((σ ij.2).val - (σ ij.1).val))

lemma B_eq (p : Fin n → ℝ) (x θ : ℝ) (σ η : ListState n) (h : σ ≠ η) :
    auxiliaryKernel p x θ σ η = S1 p x θ σ η / (auxiliaryPairs p x θ σ).card := by
  unfold auxiliaryKernel S1
  simp only
  by_cases hc : (auxiliaryPairs p x θ σ).card = 0
  · simp [hc, h]
  · simp [hc]

lemma kappa_ne (p : Fin n → ℝ) (x : ℝ) (σ η : ListState n) (h : σ ≠ η) (ij : Fin n × Fin n) :
    auxiliaryPairKernel p x σ η ij =
      if Opp p x ij ∧ σ.trans (Equiv.swap (σ ij.1) (σ ij.2)) = η then aa p σ ij else 0 := by
  unfold auxiliaryPairKernel Opp aa
  by_cases hc : (Real.log (p ij.1) ≤ x ↔ Real.log (p ij.2) ≤ x)
  · simp [hc, h]
  · simp [hc, h]

lemma trans_swap_twice (σ : ListState n) (u v : Fin n) :
    (σ.trans (Equiv.swap u v)).trans (Equiv.swap u v) = σ := by
  ext m; simp

lemma step (p : Fin n → ℝ) (x θ : ℝ) (σ η : ListState n) (ij : Fin n × Fin n)
    (h1 : ij ∈ auxiliaryPairs p x θ σ) (h2 : Opp p x ij)
    (h3 : σ.trans (Equiv.swap (σ ij.1) (σ ij.2)) = η) :
    (ij.2, ij.1) ∈ auxiliaryPairs p x θ η ∧ Opp p x (ij.2, ij.1) ∧
      η.trans (Equiv.swap (η ij.2) (η ij.1)) = σ := by
  obtain ⟨i, j⟩ := ij
  simp only at *
  have hm := (mem_pairs p x θ σ i j).1 h1
  have hη : η = (Equiv.swap i j).trans σ := by rw [← h3]; exact trans_swap_eq σ i j
  have hτ := swap_nonint p x θ i j hm.1 hm.2.1
  refine ⟨?_, fun h => h2 h.symm, ?_⟩
  · rw [hη, pairs_comp p x θ σ (Equiv.swap i j) hτ]
    simpa using h1
  · have e1 : η j = σ i := by rw [← h3]; simp
    have e2 : η i = σ j := by rw [← h3]; simp
    rw [e1, e2, ← h3]
    exact trans_swap_twice σ (σ i) (σ j)

lemma claimA (p : Fin n → ℝ) (hpos : ∀ i, 0 < p i) (x θ : ℝ) (σ η : ListState n) (h : σ ≠ η) :
    stationaryWeight p σ * S1 p x θ σ η = stationaryWeight p η * S1 p x θ η σ := by
  unfold S1
  simp only [kappa_ne p x σ η h, kappa_ne p x η σ h.symm]
  rw [← Finset.sum_filter, ← Finset.sum_filter, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_bij' (fun ij _ => (ij.2, ij.1)) (fun ij _ => (ij.2, ij.1)) ?_ ?_ ?_ ?_ ?_
  · intro ij hij
    simp only [Finset.mem_filter] at hij ⊢
    have := step p x θ σ η ij hij.1 hij.2.1 hij.2.2
    exact ⟨this.1, this.2.1, this.2.2⟩
  · intro ij hij
    simp only [Finset.mem_filter] at hij ⊢
    have := step p x θ η σ ij hij.1 hij.2.1 hij.2.2
    exact ⟨this.1, this.2.1, this.2.2⟩
  · intro ij _; rfl
  · intro ij _; rfl
  · intro ij hij
    simp only [Finset.mem_filter] at hij
    obtain ⟨i, j⟩ := ij
    simp only at *
    have hm := (mem_pairs p x θ σ i j).1 hij.1
    have hη : η = (Equiv.swap i j).trans σ := by rw [← hij.2.2]; exact trans_swap_eq σ i j
    have hw := weight_swap_gen p σ i j hm.2.2.1
    rw [← hη] at hw
    have e1 : η j = σ i := by rw [← hij.2.2]; simp
    have e2 : η i = σ j := by rw [← hij.2.2]; simp
    unfold aa
    simp only [e1, e2]
    set d := (σ j).val - (σ i).val
    have h1 := pow_pos (hpos i) d
    have h2 := pow_pos (hpos j) d
    rw [mul_div_assoc', mul_div_assoc', add_comm (p i ^ d)]
    congr 1
    linarith

end TranspositionIID.Main.Dev.C1
end

section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.C1
open TranspositionIID.Main TranspositionIID.Main.Dev
open Classical

variable {n : ℕ}

lemma card_swap (p : Fin n → ℝ) (x θ : ℝ) (σ : ListState n) (i j : Fin n)
    (hi : nonint p x θ i) (hj : nonint p x θ j) :
    (auxiliaryPairs p x θ ((Equiv.swap i j).trans σ)).card = (auxiliaryPairs p x θ σ).card := by
  have hτ := swap_nonint p x θ i j hi hj
  refine Finset.card_bij' (fun kl _ => (Equiv.swap i j kl.1, Equiv.swap i j kl.2))
    (fun kl _ => (Equiv.swap i j kl.1, Equiv.swap i j kl.2)) ?_ ?_ ?_ ?_
  · intro kl hkl
    obtain ⟨k, l⟩ := kl
    exact (pairs_comp p x θ σ _ hτ k l).1 hkl
  · intro kl hkl
    obtain ⟨k, l⟩ := kl
    exact (pairs_comp p x θ σ _ hτ _ _).2 (by simpa using hkl)
  · intro kl _; simp
  · intro kl _; simp

lemma claimB (p : Fin n → ℝ) (x θ : ℝ) (σ η : ListState n) (h : σ ≠ η)
    (hS : S1 p x θ σ η ≠ 0) :
    (auxiliaryPairs p x θ σ).card = (auxiliaryPairs p x θ η).card := by
  unfold S1 at hS
  obtain ⟨ij, hij, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
  rw [kappa_ne p x σ η h] at hne
  have hc : Opp p x ij ∧ σ.trans (Equiv.swap (σ ij.1) (σ ij.2)) = η := by
    by_contra hh; exact hne (if_neg hh)
  obtain ⟨i, j⟩ := ij
  simp only at hc hij
  have hm := (mem_pairs p x θ σ i j).1 hij
  have hη : η = (Equiv.swap i j).trans σ := by rw [← hc.2]; exact trans_swap_eq σ i j
  rw [hη, card_swap p x θ σ i j hm.1 hm.2.1]

lemma aux_db (p : Fin n → ℝ) (hpos : ∀ i, 0 < p i) (x θ : ℝ) (σ η : ListState n) :
    stationaryLaw p σ * auxiliaryKernel p x θ σ η =
      stationaryLaw p η * auxiliaryKernel p x θ η σ := by
  by_cases h : σ = η
  · subst h; rfl
  · rw [B_eq p x θ σ η h, B_eq p x θ η σ (Ne.symm h)]
    unfold stationaryLaw
    have hA := claimA p hpos x θ σ η h
    have hZ := Rev.partition_pos p hpos
    by_cases hS : S1 p x θ σ η = 0
    · have : S1 p x θ η σ = 0 := by
        have hw := Rev.weight_pos p hpos η
        rw [hS, mul_zero] at hA
        rcases mul_eq_zero.1 hA.symm with h0 | h0
        · exact absurd h0 hw.ne'
        · exact h0
      rw [hS, this]; simp
    · rw [claimB p x θ σ η h hS]
      rw [div_mul_div_comm, div_mul_div_comm, hA]

end TranspositionIID.Main.Dev.C1
end

section
set_option autoImplicit false

/-!
Blueprint for Lemma 3.2 (biased exclusion inversion count), elementary route.

Instead of Levin–Peres, the mixing step uses:
* the grand coupling (same edge, same bit) is monotone for the prefix-H-count order `wle`;
* with `ρ = exp (-θ)`, the functions `ρ ^ pre z j` evolve linearly under the kernel (`kernel_rho`);
* a weighted sum with weights `exp(θ j/2) j (N-j)` contracts by `1 - 4/(N^2 (N-1))` per step.
-/

namespace TranspositionIID.Main.Dev.L32
open TranspositionIID.Main

variable {N : ℕ}

/-- Number of `true` (H) letters among positions `< j`. -/
def pre (w : BinaryWord N) (j : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin N => i.val < j ∧ w i = true)).card

/-- Number of H letters. -/
def hcount (w : BinaryWord N) : ℕ := (Finset.univ.filter (fun i : Fin N => w i = true)).card

/-- The prefix order: `w` is everywhere less sorted than `z`. -/
def wle (w z : BinaryWord N) : Prop := ∀ j, pre w j ≤ pre z j

/-- Monotone (increasing in the prefix order) observable. -/
def MonoW (f : BinaryWord N → ℝ) : Prop := ∀ w z, wle w z → f w ≤ f z

/-- H-first probability. -/
noncomputable def qH (θ : ℝ) : ℝ := 1 / (1 + Real.exp (-θ))

/-! ### Part A: kernel basics, monotonicity, linear identity -/

/-! ### Part D: the stationary law -/

/-! ### Part E: the stationary inversion count -/

/-! ### Part F: inversion count in prefix counts; the bottom word -/

/-! ### Part G: comparison of expectations under stochastic domination -/

/-! ### Part H: contraction of the linear recursion -/

/-! ### Assembly -/

end TranspositionIID.Main.Dev.L32
end

section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.L32.PartA
open TranspositionIID.Main TranspositionIID.Main.Dev.L32

variable {N : ℕ}

/-! ### Basic facts on `pre` -/

lemma pre_eq_sum (w : BinaryWord N) (j : ℕ) :
    pre w j = ∑ i : Fin N, if i.val < j ∧ w i = true then 1 else 0 := by
  unfold pre; rw [Finset.card_filter]

lemma pre_succ' (w : BinaryWord N) (j : ℕ) :
    pre w (j + 1) = pre w j + (if h : j < N then (if w ⟨j, h⟩ = true then 1 else 0) else 0) := by
  rw [pre_eq_sum, pre_eq_sum]
  have key : ∀ i : Fin N, (if i.val < j + 1 ∧ w i = true then 1 else 0) =
      (if i.val < j ∧ w i = true then 1 else 0) + (if i.val = j ∧ w i = true then 1 else 0) := by
    intro i
    by_cases h1 : i.val < j <;> by_cases h2 : i.val = j <;> by_cases h3 : w i = true <;>
      simp [h1, h2, h3] <;> omega
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib]
  congr 1
  by_cases h : j < N
  · rw [dif_pos h, Finset.sum_eq_single ⟨j, h⟩]
    · simp
    · intro b _ hb
      have : b.val ≠ j := fun e => hb (Fin.ext e)
      simp [this]
    · simp
  · rw [dif_neg h]
    apply Finset.sum_eq_zero
    intro i _
    have := i.isLt
    have : i.val ≠ j := by omega
    simp [this]

lemma pre_congr (u w : BinaryWord N) (j : ℕ) (h : ∀ i : Fin N, i.val < j → u i = w i) :
    pre u j = pre w j := by
  unfold pre
  congr 1
  apply Finset.filter_congr
  intro i _
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, (h i h1) ▸ h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, (h i h1).symm ▸ h2⟩

lemma hcount_eq_pre (w : BinaryWord N) : hcount w = pre w N := by
  unfold hcount pre
  congr 1
  apply Finset.filter_congr
  intro i _
  have := i.isLt
  constructor
  · intro h; exact ⟨this, h⟩
  · rintro ⟨_, h⟩; exact h

lemma pre_add_le (w : BinaryWord N) (j m : ℕ) : pre w (j + m) ≤ pre w j + m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← add_assoc, pre_succ']
    split_ifs <;> omega

lemma pre_mono (w : BinaryWord N) (j m : ℕ) : pre w j ≤ pre w (j + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← add_assoc, pre_succ']
    omega

/-! ### Part F -/

/-! ### Inversions as double sums -/

/-- indicator of an L letter -/
noncomputable def ell (w : BinaryWord N) (i : Fin N) : ℝ := if w i = false then 1 else 0

lemma inv_sum (w : BinaryWord N) : binaryInversions w =
    ∑ i : Fin N, ∑ j : Fin N, if i < j ∧ w i = false ∧ w j = true then (1 : ℝ) else 0 := by
  unfold binaryInversions
  rw [Finset.card_filter]
  push_cast
  rw [Fintype.sum_prod_type]

lemma pre_sum (w : BinaryWord N) : ∑ j ∈ Finset.range N, (pre w j : ℝ) =
    ∑ i : Fin N, ∑ j : Fin N, if i < j ∧ w i = true then (1 : ℝ) else 0 := by
  rw [← Fin.sum_univ_eq_sum_range (fun j => (pre w j : ℝ))]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [pre_eq_sum]
  push_cast
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact if_congr Iff.rfl rfl rfl

noncomputable def dd (w : BinaryWord N) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N, if i < j then ell w i * ell w j else 0

lemma partition (w : BinaryWord N) :
    binaryInversions w + ∑ j ∈ Finset.range N, (pre w j : ℝ) + dd w =
      ∑ i : Fin N, ∑ j : Fin N, if i < j then (1 : ℝ) else 0 := by
  rw [inv_sum, pre_sum, dd, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h : i < j <;> cases hi : w i <;> cases hj : w j <;> simp [h, hi, hj, ell]

lemma ell_sum (w : BinaryWord N) : ∑ i, ell w i = (N : ℝ) - hcount w := by
  have : ∀ i, ell w i = 1 - (if w i = true then (1 : ℝ) else 0) := by
    intro i; cases hi : w i <;> simp [ell, hi]
  rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_sub_distrib]
  unfold hcount
  rw [Finset.card_filter]
  push_cast
  simp

lemma dd_eq (w : BinaryWord N) : 2 * dd w = (∑ i, ell w i) ^ 2 - ∑ i, ell w i := by
  have hsq : (∑ i, ell w i) ^ 2 = ∑ i : Fin N, ∑ j : Fin N, ell w i * ell w j := by
    rw [sq, Finset.sum_mul_sum]
  have hpt : ∀ i j : Fin N, ell w i * ell w j =
      (if i < j then ell w i * ell w j else 0) + (if j < i then ell w j * ell w i else 0) +
        (if i = j then ell w i else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · have : ell w i * ell w i = ell w i := by unfold ell; split_ifs <;> simp
      simp [this]
    · simp [h, h.ne', not_lt.mpr h.le, mul_comm]
  have h2 : ∑ i : Fin N, ∑ j : Fin N, (if j < i then ell w j * ell w i else 0) = dd w := by
    rw [dd, Finset.sum_comm]
  rw [hsq, Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hpt i j))]
  simp only [Finset.sum_add_distrib]
  rw [h2]
  simp [Finset.sum_ite_eq, dd]
  ring

theorem inversions_diff (w z : BinaryWord N) (h : hcount w = hcount z) :
    binaryInversions w - binaryInversions z =
      ∑ j ∈ Finset.range N, ((pre z j : ℝ) - pre w j) := by
  have hw := partition w
  have hz := partition z
  have hd : dd w = dd z := by
    have a := dd_eq w
    have b := dd_eq z
    rw [ell_sum] at a b
    rw [h] at a
    linarith
  rw [Finset.sum_sub_distrib]
  linarith

/-! ### Part A -/

lemma update_of_eq (w : BinaryWord N) (k : Fin (N - 1)) (b : Bool)
    (h : w ⟨k.val, by omega⟩ = w ⟨k.val + 1, by omega⟩) : exclusionUpdate w k b = w := by
  simp [exclusionUpdate, h]

lemma update_of_ne (w : BinaryWord N) (k : Fin (N - 1)) (b : Bool)
    (h : w ⟨k.val, by omega⟩ ≠ w ⟨k.val + 1, by omega⟩) (i : Fin N) :
    exclusionUpdate w k b i =
      if i.val = k.val then b else if i.val = k.val + 1 then !b else w i := by
  simp only [exclusionUpdate, h, if_false]
  simp [Fin.ext_iff]

theorem pre_update (w : BinaryWord N) (k : Fin (N - 1)) (b : Bool) (j : ℕ) :
    pre (exclusionUpdate w k b) j =
      if j = k.val + 1 then
        (if b then min (pre w k.val + 1) (pre w (k.val + 2))
         else max (pre w k.val) (pre w (k.val + 2) - 1))
      else pre w j := by
  have hk := k.isLt
  have p1 : pre w (k.val + 1) = pre w k.val +
      (if w ⟨k.val, by omega⟩ = true then 1 else 0) := by
    rw [pre_succ', dif_pos (by omega)]
  have p2 : pre w (k.val + 2) = pre w (k.val + 1) +
      (if w ⟨k.val + 1, by omega⟩ = true then 1 else 0) := by
    rw [pre_succ', dif_pos (by omega)]
  by_cases hac : w ⟨k.val, by omega⟩ = w ⟨k.val + 1, by omega⟩
  · rw [update_of_eq w k b hac]
    split_ifs with hj hb
    · subst hj
      rw [p2, p1]; rw [← hac]
      cases w ⟨k.val, by omega⟩ <;> simp
    · subst hj
      rw [p2, p1]; rw [← hac]
      cases w ⟨k.val, by omega⟩ <;> simp
    · rfl
  · have hu := update_of_ne w k b hac
    set u := exclusionUpdate w k b with hu_def
    have hlow : pre u k.val = pre w k.val := by
      apply pre_congr; intro i hi
      rw [hu]; simp [show i.val ≠ k.val by omega, show i.val ≠ k.val + 1 by omega]
    have hlow' : ∀ j, j ≤ k.val → pre u j = pre w j := by
      intro j hj; apply pre_congr; intro i hi
      rw [hu]; simp [show i.val ≠ k.val by omega, show i.val ≠ k.val + 1 by omega]
    have q1 : pre u (k.val + 1) = pre w k.val + (if b then 1 else 0) := by
      rw [pre_succ', dif_pos (by omega), hlow, hu]
      simp
    have q2 : pre u (k.val + 2) = pre u (k.val + 1) + (if !b then 1 else 0) := by
      rw [pre_succ', dif_pos (by omega), hu]
      simp
    have q2' : pre u (k.val + 2) = pre w (k.val + 2) := by
      rw [q2, q1, p2, p1]
      revert hac
      cases w ⟨k.val, by omega⟩ <;> cases w ⟨k.val + 1, by omega⟩ <;> cases b <;> simp
    have hhigh : ∀ m, pre u (k.val + 2 + m) = pre w (k.val + 2 + m) := by
      intro m
      induction m with
      | zero => simpa using q2'
      | succ m ih =>
        rw [← add_assoc, pre_succ', pre_succ', ih]
        congr 1
        by_cases hm : k.val + 2 + m < N
        · rw [dif_pos hm, dif_pos hm, hu]
          simp [show k.val + 2 + m ≠ k.val by omega, show k.val + 2 + m ≠ k.val + 1 by omega]
        · rw [dif_neg hm, dif_neg hm]
    split_ifs with hj hb
    · subst hj; subst hb
      rw [q1, p2, p1]
      revert hac
      cases w ⟨k.val, by omega⟩ <;> cases w ⟨k.val + 1, by omega⟩ <;> simp
    · subst hj
      rw [q1, p2, p1]
      simp only [Bool.not_eq_true] at hb
      subst hb
      revert hac
      cases w ⟨k.val, by omega⟩ <;> cases w ⟨k.val + 1, by omega⟩ <;> simp
    · by_cases hjk : j ≤ k.val
      · exact hlow' j hjk
      · obtain ⟨m, rfl⟩ : ∃ m, j = k.val + 2 + m := ⟨j - (k.val + 2), by omega⟩
        exact hhigh m

theorem update_mono (w z : BinaryWord N) (k : Fin (N - 1)) (b : Bool) (h : wle w z) :
    wle (exclusionUpdate w k b) (exclusionUpdate z k b) := by
  intro j
  rw [pre_update, pre_update]
  have h0 := h k.val
  have h2 := h (k.val + 2)
  split_ifs
  · omega
  · omega
  · exact h j

lemma qH_pos (θ : ℝ) : 0 < qH θ := by
  unfold qH; positivity

lemma qH_le_one (θ : ℝ) : qH θ ≤ 1 := by
  unfold qH
  rw [div_le_one (by positivity)]
  linarith [Real.exp_pos (-θ)]

theorem kernel_apply (θ : ℝ) (w : BinaryWord N) (f : BinaryWord N → ℝ) :
    ∑ z, exclusionKernel N θ w z * f z =
      ∑ k : Fin (N - 1), (qH θ * f (exclusionUpdate w k true) +
        (1 - qH θ) * f (exclusionUpdate w k false)) / ((N - 1 : ℕ) : ℝ) := by
  unfold exclusionKernel
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hpt : ∀ z, ((if exclusionUpdate w k true = z then 1 / (1 + Real.exp (-θ)) else 0) +
      (if exclusionUpdate w k false = z then 1 - 1 / (1 + Real.exp (-θ)) else 0)) /
        ((N - 1 : ℕ) : ℝ) * f z =
      (if exclusionUpdate w k true = z then
          qH θ * f (exclusionUpdate w k true) / ((N - 1 : ℕ) : ℝ) else 0) +
      (if exclusionUpdate w k false = z then
          (1 - qH θ) * f (exclusionUpdate w k false) / ((N - 1 : ℕ) : ℝ) else 0) := by
    intro z
    unfold qH
    by_cases h1 : exclusionUpdate w k true = z <;> by_cases h2 : exclusionUpdate w k false = z <;>
      simp only [h1, h2, if_true, if_false] <;> ring
  rw [Finset.sum_congr rfl (fun z _ => hpt z), Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

lemma kernel_row (hN : 2 ≤ N) (θ : ℝ) (w : BinaryWord N) :
    ∑ z, exclusionKernel N θ w z = 1 := by
  have := kernel_apply θ w (fun _ => 1)
  simp only [mul_one] at this
  rw [this]
  have hN1 : ((N - 1 : ℕ) : ℝ) ≠ 0 := by
    have : 1 ≤ N - 1 := by omega
    exact_mod_cast (by omega : N - 1 ≠ 0)
  simp only [add_sub_cancel, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem kernel_pow_row (hN : 2 ≤ N) (θ : ℝ) (t : ℕ) (w : BinaryWord N) :
    ∑ z, (exclusionKernel N θ ^ t) w z = 1 := by
  induction t with
  | zero =>
    simp [Matrix.one_apply]
  | succ t ih =>
    rw [pow_succ]
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, kernel_row hN, mul_one]
    exact ih

lemma kernel_ne_zero (θ : ℝ) (w z : BinaryWord N) (h : exclusionKernel N θ w z ≠ 0) :
    ∃ k b, exclusionUpdate w k b = z := by
  by_contra hc
  push Not at hc
  apply h
  unfold exclusionKernel
  apply Finset.sum_eq_zero
  intro k _
  simp [hc k true, hc k false]

lemma hcount_update (w : BinaryWord N) (k : Fin (N - 1)) (b : Bool) :
    hcount (exclusionUpdate w k b) = hcount w := by
  have := k.isLt
  rw [hcount_eq_pre, hcount_eq_pre, pre_update, if_neg (by omega)]

theorem kernel_pow_class (θ : ℝ) (t : ℕ) (w z : BinaryWord N)
    (h : (exclusionKernel N θ ^ t) w z ≠ 0) : hcount z = hcount w := by
  induction t generalizing z with
  | zero =>
    rw [pow_zero, Matrix.one_apply] at h
    split_ifs at h with hwz
    · rw [hwz]
    · exact absurd rfl h
  | succ t ih =>
    rw [pow_succ, Matrix.mul_apply] at h
    obtain ⟨y, _, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have hy1 : (exclusionKernel N θ ^ t) w y ≠ 0 := left_ne_zero_of_mul hy
    have hy2 : exclusionKernel N θ y z ≠ 0 := right_ne_zero_of_mul hy
    obtain ⟨k, b, rfl⟩ := kernel_ne_zero θ y _ hy2
    rw [hcount_update]
    exact ih y hy1

lemma expectedAfter_succ (P : Matrix (BinaryWord N) (BinaryWord N) ℝ) (w : BinaryWord N)
    (t : ℕ) (f : BinaryWord N → ℝ) :
    expectedAfter P w (t + 1) f = ∑ y, P w y * expectedAfter P y t f := by
  unfold expectedAfter
  rw [pow_succ']
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem expectedAfter_mono (θ : ℝ) (t : ℕ) (f : BinaryWord N → ℝ) (hf : MonoW f) :
    MonoW (fun w => expectedAfter (exclusionKernel N θ) w t f) := by
  induction t with
  | zero =>
    intro w z h
    simp only [expectedAfter, pow_zero, Matrix.one_apply]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact hf w z h
  | succ t ih =>
    intro w z h
    simp only [expectedAfter_succ]
    rw [kernel_apply θ w (fun y => expectedAfter (exclusionKernel N θ) y t f),
      kernel_apply θ z (fun y => expectedAfter (exclusionKernel N θ) y t f)]
    apply Finset.sum_le_sum
    intro k _
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have h1 := qH_pos θ
    have h2 := qH_le_one θ
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left (ih _ _ (update_mono w z k true h)) h1.le
    · exact mul_le_mul_of_nonneg_left (ih _ _ (update_mono w z k false h)) (by linarith)

end TranspositionIID.Main.Dev.L32.PartA
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.P33
open TranspositionIID.Main
variable {n : ℕ}
/-!
Blueprint for Proposition 3.4 (3.3): canonical paths comparing the auxiliary kernel with the
transposition kernel.

For an "up" exchange (i low, j high, adjacent among non-intermediate labels, i in front of j at
positions a < b, m = b - a - 1 intermediate labels between them), the path calls j (m+1) times
(j walks to position a, pushing i to a+1), then calls the original intermediates
g_1, ..., g_m (originally at positions a+1, ..., b-1) in order, each jumping over i.
It ends at `σ.trans (swap (σ i) (σ j))` after `2m+1` steps; every step strictly increases the
stationary weight and calls a label of probability ≥ exp x.  The data
(state, called label, original position of j) determines (σ, i, j, step).
-/
/-- An up exchange of the auxiliary chain: `i` low, `j` high, adjacent among non-intermediates. -/
def UpPair (p : Fin n → ℝ) (x θ : ℝ) (σ : ListState n) (i j : Fin n) : Prop :=
  (i, j) ∈ auxiliaryPairs p x θ σ ∧ Real.log (p i) ≤ x ∧ x + θ < Real.log (p j)

/-- Number of steps of the canonical path. -/
def pathLen (σ : ListState n) (i j : Fin n) : ℕ := 2 * ((σ j).val - (σ i).val - 1) + 1

/-- The label at position `k` of `σ` (junk `j` out of range). -/
def labelAt (σ : ListState n) (j : Fin n) (k : ℕ) : Fin n :=
  if h : k < n then σ.symm ⟨k, h⟩ else j

/-- The label called at step `s`. -/
def pathCall (σ : ListState n) (i j : Fin n) (s : ℕ) : Fin n :=
  if s ≤ (σ j).val - (σ i).val - 1 then j
  else labelAt σ j ((σ i).val + 1 + (s - ((σ j).val - (σ i).val)))

/-- The state after `s` steps. -/
def pathState (σ : ListState n) (i j : Fin n) : ℕ → ListState n
  | 0 => σ
  | s + 1 => transposeRequest (pathState σ i j s) (pathCall σ i j s)

end TranspositionIID.Main.Dev.P33
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.P33.PartC
/-! Arithmetic of positions along the canonical paths of Proposition 3.4 (Part C helpers). -/
/-- Phase 1 position map: label at `b` moved to `b - s`, positions `b-s..b-1` shifted back. -/
def F1 (b s q : ℕ) : ℕ :=
  if q = b then b - s else if b - s ≤ q ∧ q < b then q + 1 else q

/-- Phase 2 position map after `k` intermediates have jumped over the low label. -/
def F2 (a b k q : ℕ) : ℕ :=
  if q = b then a else if q = a then a + 1 + k else if a < q ∧ q ≤ a + k then q
  else if a + k < q ∧ q < b then q + 1 else q

/-- Position (in the state after `s` steps) of the label originally at position `q`. -/
def F (a b s q : ℕ) : ℕ :=
  if s ≤ b - a then F1 b s q else F2 a b (s - (b - a)) q

/-- Original position of the label called at step `s`. -/
def callPos (a b s : ℕ) : ℕ :=
  if s ≤ b - a - 1 then b else a + 1 + (s - (b - a))

/-- Transposition of positions `P` and `P - 1`. -/
def swapN (P q : ℕ) : ℕ :=
  if q = P then P - 1 else if q = P - 1 then P else q

end TranspositionIID.Main.Dev.P33.PartC
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.P33.PartC
open TranspositionIID.Main TranspositionIID.Main.Dev.P33
variable {n : ℕ}
/-! Part C of Proposition 3.4 (3.3): combinatorics of the canonical paths. -/
lemma tr_val (τ : ListState n) (c ℓ : Fin n) (h : 0 < (τ c).val) :
    (transposeRequest τ c ℓ).val = swapN (τ c).val (τ ℓ).val := by
  rw [Rev.T_pos h]
  simp only [Equiv.trans_apply, Equiv.swap_apply_def, swapN, Rev.pr]
  by_cases h1 : τ ℓ = τ c
  · rw [if_pos h1, if_pos (congrArg Fin.val h1)]
  · rw [if_neg h1, if_neg (fun e => h1 (Fin.ext e))]
    by_cases h2 : (τ ℓ).val = (τ c).val - 1
    · rw [if_pos (Fin.ext h2), if_pos h2]
    · rw [if_neg (fun e => h2 (congrArg Fin.val e)), if_neg h2]

lemma up_facts {p : Fin n → ℝ} {x θ : ℝ} {σ : ListState n} {i j : Fin n}
    (h : UpPair p x θ σ i j) :
    (σ i).val < (σ j).val ∧ Real.log (p i) ≤ x ∧ x + θ < Real.log (p j) ∧
      ∀ k, (σ i).val < (σ k).val → (σ k).val < (σ j).val →
        x < Real.log (p k) ∧ Real.log (p k) ≤ x + θ := by
  obtain ⟨hm, hi, hj⟩ := h
  unfold auxiliaryPairs at hm
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
  exact ⟨hm.2.2.1, hi, hj, fun k h1 h2 => hm.2.2.2 k h1 h2⟩

lemma call_val (σ : ListState n) (i j : Fin n) (s : ℕ) (hs : s < pathLen σ i j) :
    (σ (pathCall σ i j s)).val = callPos (σ i).val (σ j).val s := by
  unfold pathCall callPos
  split_ifs with h
  · rfl
  · unfold labelAt
    unfold pathLen at hs
    have hlt : (σ i).val + 1 + (s - ((σ j).val - (σ i).val)) < n := by
      have := (σ j).isLt; omega
    rw [dif_pos hlt]; simp

lemma call_ph1 (σ : ListState n) (i j : Fin n) (s : ℕ) (h : s ≤ (σ j).val - (σ i).val - 1) :
    pathCall σ i j s = j := by
  unfold pathCall; rw [if_pos h]

end TranspositionIID.Main.Dev.P33.PartC
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.P33.PartC
lemma F_zero (a b q : ℕ) : F a b 0 q = q := by
  unfold F F1; split_ifs <;> omega

lemma F_call (a b s : ℕ) (hab : a < b) (hs : s < 2 * (b - a - 1) + 1) :
    F a b s (callPos a b s) =
      if s ≤ b - a - 1 then b - s else a + 2 + (s - (b - a)) := by
  unfold F F1 F2 callPos; split_ifs <;> omega

lemma F_call_pos (a b s : ℕ) (hab : a < b) (hs : s < 2 * (b - a - 1) + 1) :
    0 < F a b s (callPos a b s) := by
  rw [F_call a b s hab hs]; split_ifs <;> omega

lemma F_step (a b s q : ℕ) (hab : a < b) (hs : s < 2 * (b - a - 1) + 1) :
    F a b (s + 1) q = swapN (F a b s (callPos a b s)) (F a b s q) := by
  rw [F_call a b s hab hs]
  by_cases h1 : s ≤ b - a - 1
  · rw [if_pos h1]
    have e1 : F a b (s + 1) q = F1 b (s + 1) q := by unfold F; rw [if_pos (by omega)]
    have e2 : F a b s q = F1 b s q := by unfold F; rw [if_pos (by omega)]
    rw [e1, e2]; unfold F1 swapN; split_ifs <;> omega
  · rw [if_neg h1]
    have e1 : F a b (s + 1) q = F2 a b (s + 1 - (b - a)) q := by
      unfold F F1 F2; split_ifs <;> omega
    have e2 : F a b s q = F2 a b (s - (b - a)) q := by
      unfold F F1 F2; split_ifs <;> omega
    rw [e1, e2]; unfold F2 swapN; split_ifs <;> omega

end TranspositionIID.Main.Dev.P33.PartC
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.P33.PartC
open TranspositionIID.Main TranspositionIID.Main.Dev.P33
variable {n : ℕ}
lemma state_val (σ : ListState n) (i j : Fin n) (hab : (σ i).val < (σ j).val) :
    ∀ s, s ≤ pathLen σ i j → ∀ ℓ,
      (pathState σ i j s ℓ).val = F (σ i).val (σ j).val s (σ ℓ).val := by
  intro s
  induction s with
  | zero => intro _ ℓ; simp [pathState, F_zero]
  | succ s ih =>
    intro hs ℓ
    have hs' : s < pathLen σ i j := by omega
    have hlen : s < 2 * ((σ j).val - (σ i).val - 1) + 1 := hs'
    have hc : (pathState σ i j s (pathCall σ i j s)).val =
        F (σ i).val (σ j).val s (callPos (σ i).val (σ j).val s) := by
      rw [ih hs'.le, call_val σ i j s hs']
    have hpos : 0 < (pathState σ i j s (pathCall σ i j s)).val := by
      rw [hc]; exact F_call_pos _ _ _ hab hlen
    show (transposeRequest (pathState σ i j s) (pathCall σ i j s) ℓ).val = _
    rw [tr_val _ _ _ hpos, hc, ih hs'.le, F_step _ _ _ _ hab hlen]

end TranspositionIID.Main.Dev.P33.PartC
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.P33.PartC
lemma F_end (a b q : ℕ) (hab : a < b) :
    F a b (2 * (b - a - 1) + 1) q = if q = a then b else if q = b then a else q := by
  unfold F F1 F2; split_ifs <;> omega

end TranspositionIID.Main.Dev.P33.PartC
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.P33.PartC
open TranspositionIID.Main TranspositionIID.Main.Dev.P33
variable {n : ℕ}
theorem path_end (p : Fin n → ℝ) (x θ : ℝ) (hθ : 0 < θ) (σ : ListState n) (i j : Fin n)
    (h : UpPair p x θ σ i j) :
    pathState σ i j (pathLen σ i j) = σ.trans (Equiv.swap (σ i) (σ j)) := by
  obtain ⟨hab, -, -, -⟩ := up_facts h
  apply Equiv.ext; intro ℓ; apply Fin.ext
  rw [state_val σ i j hab _ le_rfl ℓ]
  unfold pathLen; rw [F_end _ _ _ hab]
  simp only [Equiv.trans_apply, Equiv.swap_apply_def]
  by_cases h1 : σ ℓ = σ i
  · rw [if_pos (congrArg Fin.val h1), if_pos h1]
  · rw [if_neg (fun e => h1 (Fin.ext e)), if_neg h1]
    by_cases h2 : σ ℓ = σ j
    · rw [if_pos (congrArg Fin.val h2), if_pos h2]
    · rw [if_neg (fun e => h2 (Fin.ext e)), if_neg h2]

end TranspositionIID.Main.Dev.P33.PartC
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.P33
open TranspositionIID.Main
variable {n : ℕ}
/-! ### Part C (combinatorics of the paths) -/
alias path_end := TranspositionIID.Main.Dev.P33.PartC.path_end

end TranspositionIID.Main.Dev.P33
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.P33.PartC
lemma F_inj (a b s q1 q2 : ℕ) (hab : a < b) (hs : s ≤ 2 * (b - a - 1) + 1)
    (h : F a b s q1 = F a b s q2) : q1 = q2 := by
  unfold F F1 F2 at h; split_ifs at h <;> omega

/-- The label just in front of the called one. -/
lemma F_pred (a b s q : ℕ) (hab : a < b) (hs : s < 2 * (b - a - 1) + 1)
    (h : F a b s q = F a b s (callPos a b s) - 1) :
    q = a ∨ (s ≤ b - a - 1 ∧ a < q ∧ q < b) := by
  rw [F_call a b s hab hs] at h
  unfold F F1 F2 at h; split_ifs at h <;> omega

end TranspositionIID.Main.Dev.P33.PartC
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.P33.PartC
open TranspositionIID.Main TranspositionIID.Main.Dev.P33
variable {n : ℕ}
theorem path_step (p : Fin n → ℝ) (hpos : ∀ k, 0 < p k) (x θ : ℝ) (hθ : 0 < θ)
    (σ : ListState n) (i j : Fin n) (h : UpPair p x θ σ i j) (s : ℕ) (hs : s < pathLen σ i j) :
    Real.exp x ≤ p (pathCall σ i j s) ∧
      stationaryWeight p (pathState σ i j s) < stationaryWeight p (pathState σ i j (s + 1)) := by
  obtain ⟨hab, hi, hj, hmid⟩ := up_facts h
  have hlen : s < 2 * ((σ j).val - (σ i).val - 1) + 1 := hs
  have hcv := call_val σ i j s hs
  have hxc : x < Real.log (p (pathCall σ i j s)) := by
    by_cases h1 : s ≤ (σ j).val - (σ i).val - 1
    · rw [call_ph1 σ i j s h1]; linarith
    · rw [callPos, if_neg h1] at hcv
      exact (hmid _ (by omega) (by omega)).1
  refine ⟨((Real.lt_log_iff_exp_lt (hpos _)).1 hxc).le, ?_⟩
  have hτc : (pathState σ i j s (pathCall σ i j s)).val =
      F (σ i).val (σ j).val s (callPos (σ i).val (σ j).val s) := by
    rw [state_val σ i j hab s hs.le, hcv]
  have hcpos : 0 < (pathState σ i j s (pathCall σ i j s)).val := by
    rw [hτc]; exact F_call_pos _ _ _ hab hlen
  have hτd : (pathState σ i j s ((pathState σ i j s).symm
      (Rev.pr (pathState σ i j s) (pathCall σ i j s)))).val =
      (pathState σ i j s (pathCall σ i j s)).val - 1 := by
    simp [Rev.pr]
  have hFd := hτd
  rw [state_val σ i j hab s hs.le, hτc] at hFd
  have hdc : p ((pathState σ i j s).symm (Rev.pr (pathState σ i j s) (pathCall σ i j s))) <
      p (pathCall σ i j s) := by
    rcases F_pred _ _ _ _ hab hlen hFd with e | ⟨h1, h2, h3⟩
    · have hdi := σ.injective (Fin.ext e)
      rw [hdi, ← Real.log_lt_log_iff (hpos i) (hpos _)]; linarith
    · have := hmid _ h2 h3
      have e : Real.log (p (pathCall σ i j s)) = Real.log (p j) := by rw [call_ph1 σ i j s h1]
      rw [← Real.log_lt_log_iff (hpos _) (hpos _)]; linarith
  have hw := Rev.weight_swap p (pathState σ i j s) (pathCall σ i j s) hcpos
  have hstep : pathState σ i j (s + 1) = (pathState σ i j s).trans
      (Equiv.swap (pathState σ i j s (pathCall σ i j s))
        (Rev.pr (pathState σ i j s) (pathCall σ i j s))) := Rev.T_pos hcpos
  rw [hstep]
  have hW : 0 < stationaryWeight p (pathState σ i j s) :=
    Finset.prod_pos fun k _ => pow_pos (hpos k) _
  have h1 := mul_lt_mul_of_pos_left hdc hW
  rw [← hw] at h1
  exact lt_of_mul_lt_mul_right h1 (hpos _).le

end TranspositionIID.Main.Dev.P33.PartC
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.P33
open TranspositionIID.Main
variable {n : ℕ}
alias path_step := TranspositionIID.Main.Dev.P33.PartC.path_step

end TranspositionIID.Main.Dev.P33
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.P33.PartC
lemma F_ph1 (a b s q : ℕ) (hs : s ≤ b - a - 1) : F a b s q = F1 b s q := by
  unfold F; rw [if_pos (by omega)]

lemma F_ph2_b (a b s : ℕ) (hab : a < b) (hs1 : b - a - 1 < s) (hs : s < 2 * (b - a - 1) + 1) :
    F a b s b = a := by
  unfold F F1 F2; split_ifs <;> omega

lemma F_ph2_a (a b s : ℕ) (hab : a < b) (hs1 : b - a - 1 < s) :
    F a b s a = a + 1 + (s - (b - a)) := by
  unfold F F1 F2; split_ifs <;> omega

lemma F_ph2_mid (a b s q r : ℕ) (hab : a < b)
    (hs : s < 2 * (b - a - 1) + 1) (h : F a b s q = r) (hr1 : a < r)
    (hr2 : r < a + 1 + (s - (b - a))) : a < q ∧ q < b := by
  subst h; unfold F F1 F2 at *; split_ifs at * <;> omega

end TranspositionIID.Main.Dev.P33.PartC
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.P33.PartC
open TranspositionIID.Main TranspositionIID.Main.Dev.P33
variable {n : ℕ}
theorem path_inj (p : Fin n → ℝ) (x θ : ℝ) (hθ : 0 < θ)
    (σ σ' : ListState n) (i j i' j' : Fin n) (s s' : ℕ)
    (h : UpPair p x θ σ i j) (h' : UpPair p x θ σ' i' j')
    (hs : s < pathLen σ i j) (hs' : s' < pathLen σ' i' j')
    (hst : pathState σ i j s = pathState σ' i' j' s')
    (hc : pathCall σ i j s = pathCall σ' i' j' s')
    (hw : σ j = σ' j') :
    σ = σ' ∧ i = i' ∧ j = j' ∧ s = s' := by
  obtain ⟨hab, hi, hj, hmid⟩ := up_facts h
  obtain ⟨hab', hi', hj', hmid'⟩ := up_facts h'
  have hb : (σ' j').val = (σ j).val := by rw [hw]
  have hlen : s < 2 * ((σ j).val - (σ i).val - 1) + 1 := hs
  have hlen' : s' < 2 * ((σ' j').val - (σ' i').val - 1) + 1 := hs'
  have hcv := call_val σ i j s hs
  have hcv' := call_val σ' i' j' s' hs'
  have hsv := state_val σ i j hab s hs.le
  have hsv' := state_val σ' i' j' hab' s' hs'.le
  rw [hst] at hsv
  rw [hc] at hcv
  rw [hb] at hlen' hcv' hsv' hab' hmid'
  -- common data
  set c := pathCall σ' i' j' s' with hcdef
  set τ := pathState σ' i' j' s' with hτ
  by_cases h1 : s ≤ (σ j).val - (σ i).val - 1 <;>
    by_cases h1' : s' ≤ (σ j).val - (σ' i').val - 1
  · -- both in phase 1
    have hcj : c = j := by rw [← hc]; exact call_ph1 σ i j s h1
    have hcj' : c = j' := call_ph1 σ' i' j' s' (by rw [hb]; exact h1')
    have hjj : j = j' := hcj.symm.trans hcj'
    subst hjj
    have e1 := hsv j
    have e2 := hsv' j
    rw [F_ph1 _ _ _ _ h1] at e1
    rw [F_ph1 _ _ _ _ h1', ← hb] at e2
    simp only [F1, if_true] at e1 e2
    have hss : s = s' := by omega
    subst hss
    have hσ : σ = σ' := by
      apply Equiv.ext; intro ℓ; apply Fin.ext
      have e3 := hsv ℓ
      have e4 := hsv' ℓ
      rw [F_ph1 _ _ _ _ h1'] at e4
      rw [← F_ph1 (σ i).val _ _ _ h1] at e4
      exact F_inj _ _ _ _ _ hab hlen.le (e3.symm.trans e4)
    subst hσ
    refine ⟨rfl, ?_, rfl, rfl⟩
    rcases lt_trichotomy (σ i).val (σ i').val with e | e | e
    · have := (hmid i' e (by omega)).1; linarith
    · exact σ.injective (Fin.ext e)
    · have := (hmid' i e (by omega)).1; linarith
  · -- c = j high, but c intermediate for σ'
    exfalso
    have hcj : c = j := by rw [← hc]; exact call_ph1 σ i j s h1
    rw [callPos, if_neg h1'] at hcv'
    have := (hmid' c (by omega) (by omega)).2
    rw [hcj] at this; linarith
  · exfalso
    have hcj' : c = j' := call_ph1 σ' i' j' s' (by rw [hb]; exact h1')
    rw [callPos, if_neg h1] at hcv
    have := (hmid c (by omega) (by omega)).2
    rw [hcj'] at this; linarith
  · -- both in phase 2
    have ec := hsv c
    have ec' := hsv' c
    rw [hcv, F_call _ _ _ hab hlen, if_neg h1] at ec
    rw [hcv', F_call _ _ _ hab' hlen', if_neg h1'] at ec'
    have ei := hsv i
    have ei' := hsv' i'
    rw [F_ph2_a _ _ _ hab (by omega)] at ei
    rw [F_ph2_a _ _ _ hab' (by omega)] at ei'
    have hii : i = i' := τ.injective (Fin.ext (by omega))
    subst hii
    have ej := hsv j
    have ej' := hsv' j'
    rw [F_ph2_b _ _ _ hab (by omega) hlen] at ej
    rw [hb, F_ph2_b _ _ _ hab' (by omega) hlen'] at ej'
    have haa : (σ i).val = (σ' i).val := by
      rcases lt_trichotomy (σ i).val (σ' i).val with e | e | e
      · exfalso
        have ej2 := hsv j'
        rw [ej'] at ej2
        have := F_ph2_mid _ _ _ _ _ hab hlen ej2.symm e (by omega)
        have := (hmid j' this.1 this.2).2
        linarith
      · exact e
      · exfalso
        have ej2 := hsv' j
        rw [ej] at ej2
        have := F_ph2_mid _ _ _ _ _ hab' hlen' ej2.symm e (by omega)
        have := (hmid' j this.1 this.2).2
        linarith
    have hjj : j = j' := τ.injective (Fin.ext (by omega))
    subst hjj
    have hss : s = s' := by omega
    subst hss
    have hσ : σ = σ' := by
      apply Equiv.ext; intro ℓ; apply Fin.ext
      have e3 := hsv ℓ
      have e4 := hsv' ℓ
      rw [← haa] at e4
      exact F_inj _ _ _ _ _ hab hlen.le (e3.symm.trans e4)
    exact ⟨hσ, rfl, rfl, rfl⟩

end TranspositionIID.Main.Dev.P33.PartC
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.P33
open TranspositionIID.Main
variable {n : ℕ}
alias path_inj := TranspositionIID.Main.Dev.P33.PartC.path_inj

end TranspositionIID.Main.Dev.P33
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.P33.PartS
open TranspositionIID.Main TranspositionIID.Main.Dev TranspositionIID.Main.Dev.P33
open Classical
variable {n : ℕ}
/-! Part S, step A: the auxiliary Dirichlet form is bounded by the sum over up exchanges. -/
/-- The state after exchanging the labels of the pair `ij`. -/
def swp (σ : ListState n) (ij : Fin n × Fin n) : ListState n :=
  σ.trans (Equiv.swap (σ ij.1) (σ ij.2))

/-- The up exchanges of `σ`. -/
noncomputable def upSet (p : Fin n → ℝ) (x θ : ℝ) (σ : ListState n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun ij => UpPair p x θ σ ij.1 ij.2)

/-- `η` is reached from `σ` by an up exchange. -/
def UpType (p : Fin n → ℝ) (x θ : ℝ) (σ η : ListState n) : Prop :=
  ∃ ij ∈ upSet p x θ σ, swp σ ij = η

/-- The summand of the auxiliary Dirichlet form. -/
noncomputable def fB (p : Fin n → ℝ) (x θ : ℝ) (v : ListState n → ℝ) (σ η : ListState n) : ℝ :=
  stationaryLaw p σ * auxiliaryKernel p x θ σ η * (v σ - v η) * (v σ - v η)

lemma fB_nonneg (p : Fin n → ℝ) (hpos : ∀ i, 0 < p i) (x θ : ℝ) (v : ListState n → ℝ)
    (σ η : ListState n) : 0 ≤ fB p x θ v σ η := by
  have hM := C1.aux_markov p hpos x θ
  have h1 := (Rev.law_pos p hpos σ).le
  have h2 := hM.1 σ η
  unfold fB
  rw [mul_assoc]
  exact mul_nonneg (mul_nonneg h1 h2) (mul_self_nonneg _)

lemma fB_symm (p : Fin n → ℝ) (hpos : ∀ i, 0 < p i) (x θ : ℝ) (v : ListState n → ℝ)
    (σ η : ListState n) : fB p x θ v σ η = fB p x θ v η σ := by
  unfold fB
  rw [C1.aux_db p hpos x θ σ η]
  ring

lemma fB_le (p : Fin n → ℝ) (hpos : ∀ i, 0 < p i) (x θ : ℝ) (v : ListState n → ℝ)
    (σ η : ListState n) :
    fB p x θ v σ η ≤ (if UpType p x θ σ η then fB p x θ v σ η else 0) +
      (if UpType p x θ η σ then fB p x θ v η σ else 0) := by
  have hn1 := fB_nonneg p hpos x θ v σ η
  have hn2 := fB_nonneg p hpos x θ v η σ
  by_cases hu : UpType p x θ σ η
  · rw [if_pos hu]
    split_ifs <;> linarith
  rw [if_neg hu, zero_add]
  by_cases hσ : σ = η
  · subst hσ
    have : fB p x θ v σ σ = 0 := by simp [fB]
    rw [this]; split_ifs <;> linarith
  by_cases hB : auxiliaryKernel p x θ σ η = 0
  · have : fB p x θ v σ η = 0 := by simp [fB, hB]
    rw [this]; split_ifs <;> linarith
  rw [C1.B_eq p x θ σ η hσ] at hB
  have hS : C1.S1 p x θ σ η ≠ 0 := fun h => hB (by rw [h, zero_div])
  unfold C1.S1 at hS
  obtain ⟨ij, hij, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
  rw [C1.kappa_ne p x σ η hσ] at hne
  split_ifs at hne with hc
  swap
  · exact absurd rfl hne
  obtain ⟨hO, hsw⟩ := hc
  have hst := C1.step p x θ σ η ij hij hO hsw
  have hm := (C1.mem_pairs p x θ σ ij.1 ij.2).1 hij
  have hnot : ¬ UpPair p x θ σ ij.1 ij.2 := by
    intro hup
    exact hu ⟨ij, by simp [upSet, hup], hsw⟩
  have hup' : UpPair p x θ η ij.2 ij.1 := by
    refine ⟨hst.1, ?_, ?_⟩
    · by_contra h
      have h1 : Real.log (p ij.1) ≤ x := by
        by_contra h'
        exact hO ⟨fun a => absurd a h', fun a => absurd a h⟩
      rcases hm.2.1 with h2 | h2
      · exact h h2
      · exact hnot ⟨hij, h1, h2⟩
    · rcases hm.1 with h1 | h1
      · exfalso
        rcases hm.2.1 with h2 | h2
        · exact hO ⟨fun _ => h2, fun _ => h1⟩
        · exact hnot ⟨hij, h1, h2⟩
      · exact h1
  have hU : UpType p x θ η σ := ⟨(ij.2, ij.1), by simp [upSet, hup'], hst.2.2⟩
  rw [if_pos hU, fB_symm p hpos x θ v σ η]

lemma EB_le (p : Fin n → ℝ) (hpos : ∀ i, 0 < p i) (x θ : ℝ) (v : ListState n → ℝ) :
    GibbsCongestion.dirichletForm (auxiliaryKernel p x θ) (stationaryLaw p) v v ≤
      ∑ σ, ∑ η, (if UpType p x θ σ η then fB p x θ v σ η else 0) := by
  have h : GibbsCongestion.dirichletForm (auxiliaryKernel p x θ) (stationaryLaw p) v v =
      (1 / 2) * ∑ σ, ∑ η, fB p x θ v σ η := rfl
  rw [h]
  have h2 : ∑ σ, ∑ η, fB p x θ v σ η ≤
      ∑ σ, ∑ η, ((if UpType p x θ σ η then fB p x θ v σ η else 0) +
        (if UpType p x θ η σ then fB p x θ v η σ else 0)) :=
    Finset.sum_le_sum fun σ _ => Finset.sum_le_sum fun η _ => fB_le p hpos x θ v σ η
  simp only [Finset.sum_add_distrib] at h2
  rw [Finset.sum_comm (f := fun σ η => if UpType p x θ η σ then fB p x θ v η σ else 0)] at h2
  linarith

lemma kernel_le_one (p : Fin n → ℝ) (hpos : ∀ i, 0 < p i) (x θ : ℝ) (σ η : ListState n) :
    auxiliaryKernel p x θ σ η ≤ 1 := by
  have hM := C1.aux_markov p hpos x θ
  rw [← hM.2 σ]
  exact Finset.single_le_sum (fun η _ => hM.1 σ η) (Finset.mem_univ η)

lemma row_le (p : Fin n → ℝ) (hpos : ∀ i, 0 < p i) (x θ : ℝ) (v : ListState n → ℝ)
    (σ : ListState n) :
    ∑ η, (if UpType p x θ σ η then fB p x θ v σ η else 0) ≤
      ∑ ij ∈ upSet p x θ σ, stationaryLaw p σ * (v σ - v (swp σ ij)) ^ 2 := by
  rw [← Finset.sum_filter]
  have hf : Finset.univ.filter (UpType p x θ σ) = (upSet p x θ σ).image (swp σ) := by
    ext η; simp [UpType, Finset.mem_image]
  rw [hf]
  refine (Finset.sum_image_le_of_nonneg fun η _ => fB_nonneg p hpos x θ v σ η).trans ?_
  refine Finset.sum_le_sum fun ij _ => ?_
  have h1 := (Rev.law_pos p hpos σ).le
  have h2 := kernel_le_one p hpos x θ σ (swp σ ij)
  have h3 := (C1.aux_markov p hpos x θ).1 σ (swp σ ij)
  unfold fB
  rw [mul_assoc, sq]
  have h4 := mul_self_nonneg (v σ - v (swp σ ij))
  calc stationaryLaw p σ * auxiliaryKernel p x θ σ (swp σ ij) *
        ((v σ - v (swp σ ij)) * (v σ - v (swp σ ij)))
      ≤ stationaryLaw p σ * 1 * ((v σ - v (swp σ ij)) * (v σ - v (swp σ ij))) := by gcongr
    _ = _ := by ring

lemma EB_le_up (p : Fin n → ℝ) (hpos : ∀ i, 0 < p i) (x θ : ℝ) (v : ListState n → ℝ) :
    GibbsCongestion.dirichletForm (auxiliaryKernel p x θ) (stationaryLaw p) v v ≤
      ∑ σ, ∑ ij ∈ upSet p x θ σ, stationaryLaw p σ * (v σ - v (swp σ ij)) ^ 2 :=
  (EB_le p hpos x θ v).trans (Finset.sum_le_sum fun σ _ => row_le p hpos x θ v σ)

/-! Part S, step D: the weight-increasing moves carry at most the transposition Dirichlet form. -/
/-- The contribution of the move "call `c` in state `η`". -/
noncomputable def F (p : Fin n → ℝ) (v : ListState n → ℝ) (η : ListState n) (c : Fin n) : ℝ :=
  stationaryLaw p η * p c * (v (transposeRequest η c) - v η) ^ 2

/-- The strictly weight-increasing moves. -/
noncomputable def Tset (p : Fin n → ℝ) : Finset (ListState n × Fin n) :=
  Finset.univ.filter (fun ηc =>
    stationaryWeight p ηc.1 < stationaryWeight p (transposeRequest ηc.1 ηc.2))

lemma F_nonneg (p : Fin n → ℝ) (hpos : ∀ i, 0 < p i) (v : ListState n → ℝ) (η : ListState n)
    (c : Fin n) : 0 ≤ F p v η c := by
  have h1 := (Rev.law_pos p hpos η).le
  have h2 := (hpos c).le
  unfold F; positivity

lemma EP_eq (p : Fin n → ℝ) (v : ListState n → ℝ) :
    GibbsCongestion.dirichletForm (transpositionKernel p) (stationaryLaw p) v v =
      (1 / 2) * ∑ η, ∑ c, F p v η c := by
  unfold GibbsCongestion.dirichletForm
  congr 1
  refine Finset.sum_congr rfl fun η _ => ?_
  unfold transpositionKernel
  simp only [Finset.mul_sum, Finset.sum_mul, mul_ite, ite_mul, mul_zero, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true, F]
  ring

/-- The reverse move. -/
def rev (ηc : ListState n × Fin n) : ListState n × Fin n :=
  (transposeRequest ηc.1 ηc.2, ηc.1.symm (Rev.pr ηc.1 ηc.2))

lemma rev_facts (η : ListState n) (c : Fin n) (h : 0 < (η c).val) :
    0 < (transposeRequest η c (η.symm (Rev.pr η c))).val ∧
    transposeRequest (transposeRequest η c) (η.symm (Rev.pr η c)) = η ∧
    (transposeRequest η c).symm (Rev.pr (transposeRequest η c) (η.symm (Rev.pr η c))) = c := by
  set d := η.symm (Rev.pr η c) with hd
  have hT := Rev.T_pos (a := η) (i := c) h
  have h1 : transposeRequest η c d = η c := by rw [hT]; simp [hd]
  have h2 : Rev.pr (transposeRequest η c) d = Rev.pr η c := by
    ext; simp [Rev.pr, h1]
  have h3 : 0 < (transposeRequest η c d).val := by rw [h1]; exact h
  refine ⟨h3, ?_, ?_⟩
  · rw [Rev.T_pos h3, h1, h2, hT]
    ext m; simp
  · rw [h2, Equiv.symm_apply_eq, hT]; simp

lemma mem_T_pos (p : Fin n → ℝ) (ηc : ListState n × Fin n) (h : ηc ∈ Tset p) :
    0 < (ηc.1 ηc.2).val := by
  by_contra h'
  simp only [Tset, Finset.mem_filter, Finset.mem_univ, true_and] at h
  rw [Rev.T_zero h'] at h
  exact lt_irrefl _ h

lemma F_rev (p : Fin n → ℝ) (hpos : ∀ i, 0 < p i) (v : ListState n → ℝ) (η : ListState n)
    (c : Fin n) (h : 0 < (η c).val) :
    F p v (rev (η, c)).1 (rev (η, c)).2 = F p v η c := by
  obtain ⟨_, h2, _⟩ := rev_facts η c h
  have hw := Rev.weight_swap p η c h
  rw [← Rev.T_pos h] at hw
  simp only [rev, F]
  rw [h2]
  have hZ := Rev.partition_pos p hpos
  unfold stationaryLaw
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, hw]
  congr 1; ring

lemma sum_T_le (p : Fin n → ℝ) (hpos : ∀ i, 0 < p i) (v : ListState n → ℝ) :
    ∑ ηc ∈ Tset p, F p v ηc.1 ηc.2 ≤
      GibbsCongestion.dirichletForm (transpositionKernel p) (stationaryLaw p) v v := by
  rw [EP_eq]
  have hall : ∑ η, ∑ c, F p v η c = ∑ ηc ∈ Tset p, F p v ηc.1 ηc.2 +
      ∑ ηc ∈ Finset.univ.filter (fun ηc : ListState n × Fin n =>
        ¬ stationaryWeight p ηc.1 < stationaryWeight p (transposeRequest ηc.1 ηc.2)),
        F p v ηc.1 ηc.2 := by
    rw [Tset, Finset.sum_filter_add_sum_filter_not, Fintype.sum_prod_type]
  have hinj : Set.InjOn rev (Tset p : Set (ListState n × Fin n)) := by
    intro a ha b hb hab
    have ha' := mem_T_pos p a ha
    have hb' := mem_T_pos p b hb
    obtain ⟨_, a2, a3⟩ := rev_facts a.1 a.2 ha'
    obtain ⟨_, b2, b3⟩ := rev_facts b.1 b.2 hb'
    simp only [rev, Prod.mk.injEq] at hab
    obtain ⟨e1, e2⟩ := hab
    have : a.1 = b.1 := by rw [← a2, ← b2, e1, e2]
    refine Prod.ext this ?_
    rw [← a3, ← b3, e1, e2]
  have himg : ∑ ηc ∈ Tset p, F p v ηc.1 ηc.2 =
      ∑ ηc ∈ (Tset p).image rev, F p v ηc.1 ηc.2 := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun ηc h => ?_
    rw [F_rev p hpos v ηc.1 ηc.2 (mem_T_pos p ηc h)]
  have hsub : (Tset p).image rev ⊆ Finset.univ.filter (fun ηc : ListState n × Fin n =>
        ¬ stationaryWeight p ηc.1 < stationaryWeight p (transposeRequest ηc.1 ηc.2)) := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hb
    have ha' := mem_T_pos p a ha
    obtain ⟨_, a2, _⟩ := rev_facts a.1 a.2 ha'
    simp only [Tset, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, rev]
    rw [a2]
    exact not_lt.2 ha.le
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun ηc _ _ => F_nonneg p hpos v ηc.1 ηc.2)
  linarith

/-! Part S, step B: Cauchy–Schwarz along one canonical path. -/
lemma pathState_succ (σ : ListState n) (i j : Fin n) (s : ℕ) :
    pathState σ i j (s + 1) = transposeRequest (pathState σ i j s) (pathCall σ i j s) := rfl

lemma weight_mono (p : Fin n → ℝ) (hpos : ∀ k, 0 < p k) (x θ : ℝ) (hθ : 0 < θ)
    (σ : ListState n) (i j : Fin n) (h : UpPair p x θ σ i j) :
    ∀ s, s ≤ pathLen σ i j → stationaryWeight p σ ≤ stationaryWeight p (pathState σ i j s) := by
  intro s
  induction s with
  | zero => intro _; exact le_refl _
  | succ s ih =>
    intro hs
    have := (TranspositionIID.Main.Dev.P33.path_step p hpos x θ hθ σ i j h s (by omega)).2
    exact (ih (by omega)).trans this.le

lemma pathLen_le (σ : ListState n) (i j : Fin n) : pathLen σ i j ≤ 2 * n := by
  unfold pathLen
  have := (σ j).isLt
  omega

lemma pair_bound (p : Fin n → ℝ) (hpos : ∀ k, 0 < p k) (x θ : ℝ) (hθ : 0 < θ)
    (v : ListState n → ℝ) (σ : ListState n) (i j : Fin n) (h : UpPair p x θ σ i j) :
    stationaryLaw p σ * (v σ - v (swp σ (i, j))) ^ 2 ≤
      2 * n * Real.exp (-x) * ∑ s ∈ Finset.range (pathLen σ i j),
        F p v (pathState σ i j s) (pathCall σ i j s) := by
  set L := pathLen σ i j with hL
  have hend : swp σ (i, j) = pathState σ i j L :=
    (TranspositionIID.Main.Dev.P33.path_end p x θ hθ σ i j h).symm
  have htel := Finset.sum_range_sub (fun s => v (pathState σ i j s)) L
  have hsq : (v σ - v (swp σ (i, j))) ^ 2 =
      (∑ s ∈ Finset.range L, (v (pathState σ i j (s + 1)) - v (pathState σ i j s))) ^ 2 := by
    rw [htel, hend]; simp only [pathState]; ring
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range L)
    (f := fun s => v (pathState σ i j (s + 1)) - v (pathState σ i j s))
  rw [Finset.card_range] at hcs
  have hμ := (Rev.law_pos p hpos σ).le
  have hZ := Rev.partition_pos p hpos
  have hterm : ∀ s ∈ Finset.range L,
      stationaryLaw p σ * (v (pathState σ i j (s + 1)) - v (pathState σ i j s)) ^ 2 ≤
        Real.exp (-x) * F p v (pathState σ i j s) (pathCall σ i j s) := by
    intro s hs
    rw [Finset.mem_range] at hs
    have hstep := TranspositionIID.Main.Dev.P33.path_step p hpos x θ hθ σ i j h s hs
    have hw := weight_mono p hpos x θ hθ σ i j h s hs.le
    have hlaw : stationaryLaw p σ ≤ stationaryLaw p (pathState σ i j s) := by
      unfold stationaryLaw; gcongr
    have hlaw0 := (Rev.law_pos p hpos (pathState σ i j s)).le
    have he : 1 ≤ Real.exp (-x) * p (pathCall σ i j s) := by
      have := mul_le_mul_of_nonneg_left hstep.1 (Real.exp_pos (-x)).le
      rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at this
    have hc : stationaryLaw p σ ≤ Real.exp (-x) * (stationaryLaw p (pathState σ i j s) *
        p (pathCall σ i j s)) := by
      calc stationaryLaw p σ ≤ stationaryLaw p (pathState σ i j s) * 1 := by rw [mul_one]; exact hlaw
        _ ≤ stationaryLaw p (pathState σ i j s) * (Real.exp (-x) * p (pathCall σ i j s)) := by
          gcongr
        _ = _ := by ring
    unfold F
    rw [← pathState_succ]
    have hsq0 := sq_nonneg (v (pathState σ i j (s + 1)) - v (pathState σ i j s))
    calc stationaryLaw p σ * (v (pathState σ i j (s + 1)) - v (pathState σ i j s)) ^ 2
        ≤ Real.exp (-x) * (stationaryLaw p (pathState σ i j s) * p (pathCall σ i j s)) *
          (v (pathState σ i j (s + 1)) - v (pathState σ i j s)) ^ 2 := by gcongr
      _ = _ := by ring
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hLn : (L : ℝ) ≤ 2 * n := by exact_mod_cast pathLen_le σ i j
  have hS0 : 0 ≤ ∑ s ∈ Finset.range L,
      (v (pathState σ i j (s + 1)) - v (pathState σ i j s)) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hF0 : 0 ≤ Real.exp (-x) * ∑ s ∈ Finset.range L,
      F p v (pathState σ i j s) (pathCall σ i j s) :=
    mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun _ _ => F_nonneg p hpos v _ _)
  rw [hsq]
  calc stationaryLaw p σ * (∑ s ∈ Finset.range L,
        (v (pathState σ i j (s + 1)) - v (pathState σ i j s))) ^ 2
      ≤ stationaryLaw p σ * ((L : ℝ) * ∑ s ∈ Finset.range L,
        (v (pathState σ i j (s + 1)) - v (pathState σ i j s)) ^ 2) := by gcongr
    _ = (L : ℝ) * (stationaryLaw p σ * ∑ s ∈ Finset.range L,
        (v (pathState σ i j (s + 1)) - v (pathState σ i j s)) ^ 2) := by ring
    _ ≤ (L : ℝ) * (Real.exp (-x) * ∑ s ∈ Finset.range L,
        F p v (pathState σ i j s) (pathCall σ i j s)) := by gcongr
    _ ≤ 2 * n * (Real.exp (-x) * ∑ s ∈ Finset.range L,
        F p v (pathState σ i j s) (pathCall σ i j s)) := by gcongr
    _ = _ := by ring

/-! Part S, step C: the canonical paths load each weight-increasing move at most `n` times. -/
/-- The index set of (start, up pair, step). -/
noncomputable def Iset (p : Fin n → ℝ) (x θ : ℝ) : Finset (ListState n × (Fin n × Fin n) × ℕ) :=
  (Finset.univ ×ˢ Finset.univ ×ˢ Finset.range (2 * n)).filter (fun t =>
    UpPair p x θ t.1 t.2.1.1 t.2.1.2 ∧ t.2.2 < pathLen t.1 t.2.1.1 t.2.1.2)

/-- The summand attached to an index. -/
noncomputable def G (p : Fin n → ℝ) (v : ListState n → ℝ)
    (t : ListState n × (Fin n × Fin n) × ℕ) : ℝ :=
  F p v (pathState t.1 t.2.1.1 t.2.1.2 t.2.2) (pathCall t.1 t.2.1.1 t.2.1.2 t.2.2)

lemma sum_eq_Iset (p : Fin n → ℝ) (x θ : ℝ) (v : ListState n → ℝ) :
    ∑ σ, ∑ ij ∈ upSet p x θ σ, ∑ s ∈ Finset.range (pathLen σ ij.1 ij.2),
        F p v (pathState σ ij.1 ij.2 s) (pathCall σ ij.1 ij.2 s) =
      ∑ t ∈ Iset p x θ, G p v t := by
  rw [Iset, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_product, upSet, Finset.sum_filter]
  refine Finset.sum_congr rfl fun ij _ => ?_
  by_cases hu : UpPair p x θ σ ij.1 ij.2
  · simp only [hu, true_and, if_true]
    rw [← Finset.sum_filter]
    have : (Finset.range (2 * n)).filter (fun s => s < pathLen σ ij.1 ij.2) =
        Finset.range (pathLen σ ij.1 ij.2) := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_range]
      have := pathLen_le σ ij.1 ij.2
      omega
    rw [this]; rfl
  · simp [hu]

lemma Iset_le (p : Fin n → ℝ) (hpos : ∀ k, 0 < p k) (x θ : ℝ) (hθ : 0 < θ)
    (v : ListState n → ℝ) :
    ∑ t ∈ Iset p x θ, G p v t ≤ n * ∑ ηc ∈ Tset p, F p v ηc.1 ηc.2 := by
  let φ : ListState n × (Fin n × Fin n) × ℕ → (ListState n × Fin n) × Fin n := fun t =>
    ((pathState t.1 t.2.1.1 t.2.1.2 t.2.2, pathCall t.1 t.2.1.1 t.2.1.2 t.2.2), t.1 t.2.1.2)
  have hinj : Set.InjOn φ (Iset p x θ : Set _) := by
    rintro ⟨σ, ⟨i, j⟩, s⟩ ha ⟨σ', ⟨i', j'⟩, s'⟩ hb hab
    simp only [Iset, Finset.coe_filter, Set.mem_ofPred_eq] at ha hb
    simp only [φ, Prod.mk.injEq] at hab
    obtain ⟨⟨e1, e2⟩, e3⟩ := hab
    obtain ⟨r1, r2, r3, r4⟩ := TranspositionIID.Main.Dev.P33.path_inj p x θ hθ σ σ' i j i' j' s s'
      ha.2.1 hb.2.1 ha.2.2 hb.2.2 e1 e2 e3
    subst r1 r2 r3 r4; rfl
  have himg : ∑ t ∈ Iset p x θ, G p v t =
      ∑ u ∈ (Iset p x θ).image φ, F p v u.1.1 u.1.2 := by
    rw [Finset.sum_image hinj]; rfl
  have hsub : (Iset p x θ).image φ ⊆ Tset p ×ˢ Finset.univ := by
    intro u hu
    obtain ⟨⟨σ, ⟨i, j⟩, s⟩, ht, rfl⟩ := Finset.mem_image.1 hu
    simp only [Iset, Finset.mem_filter] at ht
    have hst := (TranspositionIID.Main.Dev.P33.path_step p hpos x θ hθ σ i j ht.2.1 s ht.2.2).2
    simp only [Finset.mem_product, Finset.mem_univ, and_true, Tset, Finset.mem_filter,
      true_and, φ]
    exact hst
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun u _ _ => F_nonneg p hpos v u.1.1 u.1.2)
  rw [himg]
  refine hle.trans (le_of_eq ?_)
  rw [Finset.sum_product, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ηc _ => ?_
  simp

end TranspositionIID.Main.Dev.P33.PartS
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.P33.PartS
open TranspositionIID.Main TranspositionIID.Main.Dev TranspositionIID.Main.Dev.P33
/-! Part S: the Dirichlet-form comparison (Proposition 3.4, (3.3)) from the canonical paths. -/
theorem dirichlet_comparison {n : ℕ} (hn : 1024 ≤ n) (p : Fin n → ℝ)
    (hp : ActuarialValuation.isFiniteStateDistribution p)
    (hsort : Decreasing p) (hpos : ∀ i, 0 < p i)
    (x θ : ℝ) (hθ : 0 < θ) (hθcap : θ ≤ 1 / 2) (v : ListState n → ℝ) :
    GibbsCongestion.dirichletForm (auxiliaryKernel p x θ) (stationaryLaw p) v v ≤
      2 * (n : ℝ) ^ 2 * Real.exp (-x) *
        GibbsCongestion.dirichletForm (transpositionKernel p) (stationaryLaw p) v v := by
  have h1 := EB_le_up p hpos x θ v
  have h2 : ∑ σ, ∑ ij ∈ upSet p x θ σ, stationaryLaw p σ * (v σ - v (swp σ ij)) ^ 2 ≤
      2 * n * Real.exp (-x) * ∑ σ, ∑ ij ∈ upSet p x θ σ,
        ∑ s ∈ Finset.range (pathLen σ ij.1 ij.2),
          F p v (pathState σ ij.1 ij.2 s) (pathCall σ ij.1 ij.2 s) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun σ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun ij hij => ?_
    have hu : UpPair p x θ σ ij.1 ij.2 := by
      classical
      simpa [upSet] using hij
    exact pair_bound p hpos x θ hθ v σ ij.1 ij.2 hu
  rw [sum_eq_Iset] at h2
  have h3 := Iset_le p hpos x θ hθ v
  have h4 := sum_T_le p hpos v
  have he := (Real.exp_pos (-x)).le
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h5 : 2 * n * Real.exp (-x) * ∑ t ∈ Iset p x θ, G p v t ≤
      2 * n * Real.exp (-x) * (n * GibbsCongestion.dirichletForm (transpositionKernel p)
        (stationaryLaw p) v v) := by
    gcongr
    exact h3.trans (by gcongr)
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ _ := h5
    _ = _ := by ring

end TranspositionIID.Main.Dev.P33.PartS
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.P33
open TranspositionIID.Main
variable {n : ℕ}
/-! ### Part S (the analytic comparison, from Part C) -/
alias dirichlet_comparison := TranspositionIID.Main.Dev.P33.PartS.dirichlet_comparison

end TranspositionIID.Main.Dev.P33
end

section
set_option autoImplicit false
noncomputable section
namespace TranspositionIID.Main.Dev.P34.PartM
open TranspositionIID.Main TranspositionIID.Main.Dev TranspositionIID.Main.Dev.L32
variable {n : ℕ}
/-! Projection of a list onto the binary word of its non-intermediate labels (H = high). -/
/-- High label indicator. -/
def hiB (p : Fin n → ℝ) (x θ : ℝ) (k : Fin n) : Bool := decide (x + θ < Real.log (p k))

/-- The non-intermediate labels. -/
def niSet (p : Fin n → ℝ) (x θ : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun k => Real.log (p k) ≤ x ∨ x + θ < Real.log (p k))

/-- Positions of the non-intermediate labels. -/
def posSet (p : Fin n → ℝ) (x θ : ℝ) (σ : ListState n) : Finset (Fin n) :=
  Finset.univ.filter (fun q => Real.log (p (σ.symm q)) ≤ x ∨ x + θ < Real.log (p (σ.symm q)))

lemma mem_niSet (p : Fin n → ℝ) (x θ : ℝ) (k : Fin n) :
    k ∈ niSet p x θ ↔ C1.nonint p x θ k := by
  simp [niSet, C1.nonint]

lemma mem_posSet (p : Fin n → ℝ) (x θ : ℝ) (σ : ListState n) (q : Fin n) :
    q ∈ posSet p x θ σ ↔ C1.nonint p x θ (σ.symm q) := by
  simp [posSet, C1.nonint]

lemma card_posSet (p : Fin n → ℝ) (x θ : ℝ) (σ : ListState n) :
    (posSet p x θ σ).card = (niSet p x θ).card := by
  have : posSet p x θ σ = (niSet p x θ).map σ.toEmbedding := by
    ext q
    rw [Finset.mem_map_equiv, mem_posSet, mem_niSet]
  rw [this, Finset.card_map]

/-- Increasing enumeration of the positions of non-intermediate labels. -/
def emb (p : Fin n → ℝ) (x θ : ℝ) (σ : ListState n) : Fin (niSet p x θ).card ↪o Fin n :=
  (posSet p x θ σ).orderEmbOfFin (card_posSet p x θ σ)

/-- The projected binary word. -/
def proj (p : Fin n → ℝ) (x θ : ℝ) (σ : ListState n) : BinaryWord (niSet p x θ).card :=
  fun m => hiB p x θ (σ.symm (emb p x θ σ m))

end TranspositionIID.Main.Dev.P34.PartM
end
end

section
set_option autoImplicit false
noncomputable section
namespace TranspositionIID.Main.Dev.P34.PartM
open TranspositionIID.Main TranspositionIID.Main.Dev TranspositionIID.Main.Dev.L32
variable {n : ℕ}
variable {p : Fin n → ℝ} {x θ : ℝ}
lemma proj_apply (σ : ListState n) (m : Fin (niSet p x θ).card) :
    proj p x θ σ m = hiB p x θ (σ.symm (emb p x θ σ m)) := rfl

lemma emb_mem (σ : ListState n) (m : Fin (niSet p x θ).card) :
    emb p x θ σ m ∈ posSet p x θ σ :=
  Finset.orderEmbOfFin_mem _ _ _

lemma emb_ni (σ : ListState n) (m : Fin (niSet p x θ).card) :
    C1.nonint p x θ (σ.symm (emb p x θ σ m)) :=
  (mem_posSet p x θ σ _).1 (emb_mem σ m)

lemma exists_emb (σ : ListState n) {q : Fin n} (hq : q ∈ posSet p x θ σ) :
    ∃ m, emb p x θ σ m = q := by
  have : q ∈ Set.range (emb p x θ σ) := by
    unfold emb; rw [Finset.range_orderEmbOfFin]; exact hq
  exact this

lemma exists_emb_label (σ : ListState n) {k : Fin n} (hk : C1.nonint p x θ k) :
    ∃ m, emb p x θ σ m = σ k :=
  exists_emb σ ((mem_posSet p x θ σ _).2 (by simpa using hk))

lemma low_iff (hθ : 0 < θ) {k : Fin n} (hk : C1.nonint p x θ k) :
    Real.log (p k) ≤ x ↔ hiB p x θ k = false := by
  unfold hiB
  unfold C1.nonint at hk
  simp only [decide_eq_false_iff_not, not_lt]
  constructor
  · intro h; linarith
  · intro h
    rcases hk with h' | h'
    · exact h'
    · linarith

lemma hiB_true_iff (k : Fin n) : hiB p x θ k = true ↔ x + θ < Real.log (p k) := by
  simp [hiB]

theorem sep_eq (hθ : 0 < θ) (σ : ListState n) :
    separatedInversions p x θ σ = binaryInversions (proj p x θ σ) := by
  unfold separatedInversions binaryInversions
  congr 1
  symm
  apply Finset.card_bij
    (fun ab _ => (σ.symm (emb p x θ σ ab.2), σ.symm (emb p x θ σ ab.1)))
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hab ⊢
    rw [proj_apply, proj_apply] at hab
    obtain ⟨h1, h2, h3⟩ := hab
    refine ⟨(low_iff hθ (emb_ni σ a)).2 h2, (hiB_true_iff _).1 h3, ?_⟩
    simpa using h1
  · rintro ⟨a, b⟩ _ ⟨a', b'⟩ _ h
    simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
    obtain ⟨h1, h2⟩ := h
    rw [h1, h2]
  · rintro ⟨i, j⟩ hij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hij
    obtain ⟨h1, h2, h3⟩ := hij
    obtain ⟨b, hb⟩ := exists_emb_label σ (k := i) (Or.inr h2)
    obtain ⟨a, ha⟩ := exists_emb_label σ (k := j) (Or.inl h1)
    refine ⟨(a, b), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [proj_apply, proj_apply, ha, hb, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      refine ⟨?_, ?_, ?_⟩
      · rw [← (emb p x θ σ).lt_iff_lt, ha, hb]; exact h3
      · simp only [hiB, decide_eq_false_iff_not, not_lt]; linarith
      · simp [hiB, h2]
    · simp [ha, hb]

theorem hcount_proj (σ : ListState n) :
    hcount (proj p x θ σ) = (Finset.univ.filter (fun k => x + θ < Real.log (p k))).card := by
  unfold hcount
  apply Finset.card_bij (fun m _ => σ.symm (emb p x θ σ m))
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
    rw [proj_apply] at hm
    exact (hiB_true_iff _).1 hm
  · intro a _ b _ h
    simpa using h
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    obtain ⟨m, hm⟩ := exists_emb_label σ (k := k) (Or.inr hk)
    refine ⟨m, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [proj_apply, hm, Equiv.symm_apply_apply]
      exact (hiB_true_iff _).2 hk
    · simp [hm]

/-! ### Adjacent pairs -/
/-- Left index of the k-th adjacent pair. -/
def lo {N : ℕ} (k : Fin (N - 1)) : Fin N := ⟨k.val, by omega⟩

/-- Right index of the k-th adjacent pair. -/
def hi {N : ℕ} (k : Fin (N - 1)) : Fin N := ⟨k.val + 1, by omega⟩

/-- The k-th adjacent pair of non-intermediate labels. -/
def pairOf (p : Fin n → ℝ) (x θ : ℝ) (σ : ListState n) (k : Fin ((niSet p x θ).card - 1)) :
    Fin n × Fin n :=
  (σ.symm (emb p x θ σ (lo k)), σ.symm (emb p x θ σ (hi k)))

lemma pairOf_inj (σ : ListState n) : Function.Injective (pairOf p x θ σ) := by
  intro k k' h
  simp only [pairOf, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
  have := congrArg Fin.val h.1
  simp only [lo] at this
  exact Fin.ext this

theorem pairs_eq (σ : ListState n) :
    auxiliaryPairs p x θ σ = Finset.univ.image (pairOf p x θ σ) := by
  ext ⟨i, j⟩
  rw [C1.mem_pairs, Finset.mem_image]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hi', hj', hlt, hbetw⟩
    obtain ⟨a, ha⟩ := exists_emb_label σ hi'
    obtain ⟨b, hb⟩ := exists_emb_label σ hj'
    have hab : a < b := by rw [← (emb p x θ σ).lt_iff_lt, ha, hb]; exact hlt
    have hab' : a.val < b.val := hab
    have hb' : b.val = a.val + 1 := by
      by_contra hne
      have hc : a.val + 1 < (niSet p x θ).card := by omega
      apply hbetw (σ.symm (emb p x θ σ ⟨a.val + 1, hc⟩))
      · rw [Equiv.apply_symm_apply, ← ha, (emb p x θ σ).lt_iff_lt, Fin.lt_def]
        simp
      · rw [Equiv.apply_symm_apply, ← hb, (emb p x θ σ).lt_iff_lt, Fin.lt_def]
        simp only; omega
      · exact emb_ni σ _
    refine ⟨⟨a.val, by omega⟩, ?_⟩
    simp only [pairOf, Prod.mk.injEq]
    constructor
    · have : (lo ⟨a.val, by omega⟩ : Fin (niSet p x θ).card) = a := Fin.ext rfl
      rw [this, ha]; simp
    · have : (hi ⟨a.val, by omega⟩ : Fin (niSet p x θ).card) = b := Fin.ext (by simp [hi]; omega)
      rw [this, hb]; simp
  · rintro ⟨k, hk⟩
    simp only [pairOf, Prod.mk.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    refine ⟨emb_ni σ _, emb_ni σ _, ?_, ?_⟩
    · rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, (emb p x θ σ).lt_iff_lt,
        Fin.lt_def]
      simp [lo, hi]
    · intro m h1 h2 hm
      obtain ⟨c, hc⟩ := exists_emb_label σ hm
      rw [Equiv.apply_symm_apply, ← hc, (emb p x θ σ).lt_iff_lt, Fin.lt_def] at h1 h2
      simp only [lo, hi] at h1 h2
      omega

theorem card_pairs (σ : ListState n) :
    (auxiliaryPairs p x θ σ).card = (niSet p x θ).card - 1 := by
  rw [pairs_eq, Finset.card_image_of_injective _ (pairOf_inj σ)]
  simp

/-! ### Swapping an adjacent pair -/
lemma posSet_swap (σ : ListState n) (u v : Fin n) (hu : u ∈ posSet p x θ σ)
    (hv : v ∈ posSet p x θ σ) :
    posSet p x θ (σ.trans (Equiv.swap u v)) = posSet p x θ σ := by
  ext q
  rw [mem_posSet, Equiv.symm_trans_apply, Equiv.symm_swap, ← mem_posSet]
  by_cases h1 : q = u
  · subst h1; rw [Equiv.swap_apply_left]; exact ⟨fun _ => hu, fun _ => hv⟩
  · by_cases h2 : q = v
    · subst h2; rw [Equiv.swap_apply_right]; exact ⟨fun _ => hv, fun _ => hu⟩
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]

lemma emb_swap (σ : ListState n) (u v : Fin n) (hu : u ∈ posSet p x θ σ)
    (hv : v ∈ posSet p x θ σ) :
    emb p x θ (σ.trans (Equiv.swap u v)) = emb p x θ σ := by
  apply Finset.orderEmbOfFin_unique' (card_posSet p x θ σ)
  intro m
  rw [← posSet_swap σ u v hu hv]
  exact emb_mem _ m

theorem proj_swap (σ : ListState n) (k : Fin ((niSet p x θ).card - 1)) :
    proj p x θ (σ.trans (Equiv.swap (emb p x θ σ (lo k)) (emb p x θ σ (hi k)))) =
      fun m => if m = lo k then proj p x θ σ (hi k)
        else if m = hi k then proj p x θ σ (lo k) else proj p x θ σ m := by
  funext m
  have hsw := emb_swap σ (emb p x θ σ (lo k)) (emb p x θ σ (hi k)) (emb_mem σ _) (emb_mem σ _)
  simp only [proj]
  rw [hsw, Equiv.symm_trans_apply, Equiv.symm_swap]
  split_ifs with h1 h2
  · subst h1; rw [Equiv.swap_apply_left]
  · subst h2; rw [Equiv.swap_apply_right]
  · rw [Equiv.swap_apply_of_ne_of_ne (fun h => h1 ((emb p x θ σ).injective h))
      (fun h => h2 ((emb p x θ σ).injective h))]

end TranspositionIID.Main.Dev.P34.PartM
end
end

section
set_option autoImplicit false
noncomputable section
namespace TranspositionIID.Main.Dev.P34.PartM
open TranspositionIID.Main TranspositionIID.Main.Dev TranspositionIID.Main.Dev.L32
variable {n : ℕ}
/-! One-step comparison of the auxiliary chain (projected) with the exclusion chain. -/
lemma kappa_apply (p : Fin n → ℝ) (x : ℝ) (σ : ListState n) (ij : Fin n × Fin n)
    (G : ListState n → ℝ) :
    ∑ η, auxiliaryPairKernel p x σ η ij * G η =
      if (Real.log (p ij.1) ≤ x ↔ Real.log (p ij.2) ≤ x) then G σ
      else p ij.2 ^ ((σ ij.2).val - (σ ij.1).val) /
          (p ij.2 ^ ((σ ij.2).val - (σ ij.1).val) + p ij.1 ^ ((σ ij.2).val - (σ ij.1).val)) *
            G (σ.trans (Equiv.swap (σ ij.1) (σ ij.2))) +
        (1 - p ij.2 ^ ((σ ij.2).val - (σ ij.1).val) /
          (p ij.2 ^ ((σ ij.2).val - (σ ij.1).val) + p ij.1 ^ ((σ ij.2).val - (σ ij.1).val))) *
            G σ := by
  unfold auxiliaryPairKernel
  split_ifs with h
  · simp [ite_mul]
  · simp [ite_mul, add_mul, Finset.sum_add_distrib]

lemma prob_bound {p : Fin n → ℝ} (hpos : ∀ i, 0 < p i) {x θ : ℝ} (hθ : 0 < θ) (l h : Fin n)
    (hl : Real.log (p l) ≤ x) (hh : x + θ < Real.log (p h)) (d : ℕ) (hd : 1 ≤ d) :
    qH θ ≤ p h ^ d / (p h ^ d + p l ^ d) := by
  have hpl := hpos l
  have hph := hpos h
  set r := p l / p h with hr_def
  have hr0 : 0 < r := div_pos hpl hph
  have hr : r ≤ Real.exp (-θ) := by
    have : r = Real.exp (Real.log (p l) - Real.log (p h)) := by
      rw [Real.exp_sub, Real.exp_log hpl, Real.exp_log hph]
    rw [this]
    apply Real.exp_le_exp.2
    linarith
  have hr1 : r ≤ 1 := hr.trans (by rw [Real.exp_le_one_iff]; linarith)
  have hrd : r ^ d ≤ r := pow_le_of_le_one hr0.le hr1 (by omega)
  have hpd : 0 < p h ^ d := pow_pos hph d
  have heq : p h ^ d / (p h ^ d + p l ^ d) = 1 / (1 + r ^ d) := by
    have : p l ^ d = r ^ d * p h ^ d := by
      rw [hr_def, div_pow]; field_simp
    rw [this]
    field_simp
  rw [heq]
  unfold qH
  apply one_div_le_one_div_of_le (by positivity)
  linarith

lemma prob_compl {p : Fin n → ℝ} (hpos : ∀ i, 0 < p i) (l h : Fin n) (d : ℕ) :
    p l ^ d / (p l ^ d + p h ^ d) = 1 - p h ^ d / (p h ^ d + p l ^ d) := by
  have h1 := pow_pos (hpos l) d
  have h2 := pow_pos (hpos h) d
  field_simp
  ring

lemma wle_upd {N : ℕ} (w : BinaryWord N) (k : Fin (N - 1)) :
    wle (exclusionUpdate w k false) (exclusionUpdate w k true) := by
  intro j
  rw [PartA.pre_update, PartA.pre_update]
  have h1 := PartA.pre_add_le w k.val 2
  have h2 := PartA.pre_mono w k.val 2
  by_cases hj : j = k.val + 1
  · simp only [hj, if_true, Bool.false_eq_true, if_false]
    omega
  · simp only [hj, if_false]
    exact le_rfl

lemma upd_self {N : ℕ} (w : BinaryWord N) (k : Fin (N - 1)) (b : Bool)
    (hb : w (lo k) = b) (hne : w (lo k) ≠ w (hi k)) : exclusionUpdate w k b = w := by
  funext i
  rw [PartA.update_of_ne w k b hne]
  split_ifs with h1 h2
  · rw [← hb]; congr 1; exact Fin.ext h1.symm
  · have : w (hi k) = !b := by
      rw [← hb]; revert hne; cases w (lo k) <;> cases w (hi k) <;> simp
    rw [← this]; congr 1; exact Fin.ext h2.symm
  · rfl

lemma upd_swap {N : ℕ} (w : BinaryWord N) (k : Fin (N - 1)) (b : Bool)
    (hb : w (lo k) = !b) (hne : w (lo k) ≠ w (hi k)) :
    exclusionUpdate w k b =
      fun m => if m = lo k then w (hi k) else if m = hi k then w (lo k) else w m := by
  funext i
  rw [PartA.update_of_ne w k b hne]
  have hhb : w (hi k) = b := by
    revert hne hb; cases w (lo k) <;> cases w (hi k) <;> cases b <;> simp
  by_cases h1 : i.val = k.val
  · have : i = lo k := Fin.ext h1
    subst this
    simp [lo, hhb]
  · by_cases h2 : i.val = k.val + 1
    · have : i = hi k := Fin.ext h2
      subst this
      simp [hi, lo, Fin.ext_iff]
      rw [show (⟨k.val, by omega⟩ : Fin N) = lo k from rfl, hb]
      simp
    · have e1 : i ≠ lo k := fun h => h1 (by rw [h]; rfl)
      have e2 : i ≠ hi k := fun h => h2 (by rw [h]; rfl)
      simp [h1, h2, e1, e2]

end TranspositionIID.Main.Dev.P34.PartM
end
end

section
set_option autoImplicit false
noncomputable section
namespace TranspositionIID.Main.Dev.P34.PartM
open TranspositionIID.Main TranspositionIID.Main.Dev TranspositionIID.Main.Dev.L32
variable {n : ℕ}
variable {p : Fin n → ℝ} {x θ : ℝ}
theorem compare_k (hθ : 0 < θ) (hpos : ∀ i, 0 < p i)
    (F : BinaryWord (niSet p x θ).card → ℝ) (hF : MonoW (fun w => -F w))
    (σ : ListState n) (k : Fin ((niSet p x θ).card - 1)) :
    ∑ η, auxiliaryPairKernel p x σ η (pairOf p x θ σ k) * F (proj p x θ η) ≤
      qH θ * F (exclusionUpdate (proj p x θ σ) k true) +
        (1 - qH θ) * F (exclusionUpdate (proj p x θ σ) k false) := by
  rw [kappa_apply]
  set w := proj p x θ σ with hw
  have hlo := emb_ni (p := p) (x := x) (θ := θ) σ (lo k)
  have hhi := emb_ni (p := p) (x := x) (θ := θ) σ (hi k)
  have hwlo : w (lo k) = hiB p x θ (σ.symm (emb p x θ σ (lo k))) := rfl
  have hwhi : w (hi k) = hiB p x θ (σ.symm (emb p x θ σ (hi k))) := rfl
  have hmono : F (exclusionUpdate w k true) ≤ F (exclusionUpdate w k false) := by
    have := hF _ _ (wle_upd w k); simp only at this; linarith
  have hq0 := PartA.qH_pos θ
  have hq1 := PartA.qH_le_one θ
  simp only [pairOf, Equiv.apply_symm_apply]
  have hlt : (emb p x θ σ (lo k)) < (emb p x θ σ (hi k)) := by
    rw [(emb p x θ σ).lt_iff_lt, Fin.lt_def]; simp [lo, hi]
  have hd : 1 ≤ (emb p x θ σ (hi k)).val - (emb p x θ σ (lo k)).val := by
    rw [Fin.lt_def] at hlt; omega
  by_cases hsame : (Real.log (p (σ.symm (emb p x θ σ (lo k)))) ≤ x ↔
      Real.log (p (σ.symm (emb p x θ σ (hi k)))) ≤ x)
  · rw [if_pos hsame]
    rw [low_iff hθ hlo, low_iff hθ hhi, ← hwlo, ← hwhi] at hsame
    have heq : w (lo k) = w (hi k) := by
      revert hsame; cases w (lo k) <;> cases w (hi k) <;> simp
    rw [PartA.update_of_eq w k true heq, PartA.update_of_eq w k false heq]
    linarith
  · rw [if_neg hsame]
    rw [low_iff hθ hlo, low_iff hθ hhi, ← hwlo, ← hwhi] at hsame
    have hne : w (lo k) ≠ w (hi k) := by
      intro h; apply hsame; rw [h]
    have hsw := proj_swap (p := p) (x := x) (θ := θ) σ k
    rw [← hw] at hsw
    rw [hsw]
    set d := (emb p x θ σ (hi k)).val - (emb p x θ σ (lo k)).val
    set i := σ.symm (emb p x θ σ (lo k))
    set j := σ.symm (emb p x θ σ (hi k))
    rcases Bool.eq_false_or_eq_true (w (lo k)) with hc | hc
    · -- high first: w = update true, swapped = update false
      have hwhi' : w (hi k) = false := by rw [hc] at hne; revert hne; cases w (hi k) <;> simp
      rw [upd_self w k true hc hne, upd_swap w k false (by simp [hc]) hne]
      rw [upd_self w k true hc hne, upd_swap w k false (by simp [hc]) hne] at hmono
      have hihi : x + θ < Real.log (p i) := (hiB_true_iff _).1 (hwlo ▸ hc)
      have hjlo : Real.log (p j) ≤ x := (low_iff hθ hhi).2 (hwhi ▸ hwhi')
      have ha := prob_bound hpos hθ j i hjlo hihi d hd
      rw [prob_compl hpos j i d]
      nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hmono)]
    · -- low first: w = update false, swapped = update true
      have hwhi' : w (hi k) = true := by rw [hc] at hne; revert hne; cases w (hi k) <;> simp
      rw [upd_self w k false hc hne, upd_swap w k true (by simp [hc]) hne]
      rw [upd_self w k false hc hne, upd_swap w k true (by simp [hc]) hne] at hmono
      have hjhi : x + θ < Real.log (p j) := (hiB_true_iff _).1 (hwhi ▸ hwhi')
      have hilo : Real.log (p i) ≤ x := (low_iff hθ hlo).2 (hwlo ▸ hc)
      have ha := prob_bound hpos hθ i j hilo hjhi d hd
      nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hmono)]

end TranspositionIID.Main.Dev.P34.PartM
end
end

section
set_option autoImplicit false
noncomputable section
namespace TranspositionIID.Main.Dev.P34.PartM
open TranspositionIID.Main TranspositionIID.Main.Dev TranspositionIID.Main.Dev.L32
variable {n : ℕ}
/-! Monotone comparison: the projected auxiliary chain is dominated by the exclusion chain. -/
lemma expectedAfter_succ' {S : Type*} [Fintype S] [DecidableEq S] (P : Matrix S S ℝ) (s : S)
    (t : ℕ) (f : S → ℝ) :
    expectedAfter P s (t + 1) f = ∑ y, P s y * expectedAfter P y t f := by
  unfold expectedAfter
  rw [pow_succ']
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

end TranspositionIID.Main.Dev.P34.PartM
end
end

section
set_option autoImplicit false
noncomputable section
namespace TranspositionIID.Main.Dev.P34.PartM
open TranspositionIID.Main TranspositionIID.Main.Dev TranspositionIID.Main.Dev.L32
variable {n : ℕ}
variable {p : Fin n → ℝ} {x θ : ℝ}
theorem one_step (hθ : 0 < θ) (hpos : ∀ i, 0 < p i) (hN : 2 ≤ (niSet p x θ).card)
    (F : BinaryWord (niSet p x θ).card → ℝ) (hF : MonoW (fun w => -F w)) (σ : ListState n) :
    ∑ η, auxiliaryKernel p x θ σ η * F (proj p x θ η) ≤
      ∑ z, exclusionKernel (niSet p x θ).card θ (proj p x θ σ) z * F z := by
  rw [PartA.kernel_apply]
  have hcard := card_pairs (p := p) (x := x) (θ := θ) σ
  have hne : (auxiliaryPairs p x θ σ).card ≠ 0 := by omega
  have hB : ∀ η, auxiliaryKernel p x θ σ η =
      (∑ ij ∈ auxiliaryPairs p x θ σ, auxiliaryPairKernel p x σ η ij) /
        (((niSet p x θ).card - 1 : ℕ) : ℝ) := by
    intro η
    unfold auxiliaryKernel
    simp only
    rw [if_neg hne, hcard]
  simp_rw [hB, div_mul_eq_mul_div, Finset.sum_mul, Finset.sum_div]
  rw [Finset.sum_comm, pairs_eq, Finset.sum_image (fun a _ b _ h => pairOf_inj σ h)]
  apply Finset.sum_le_sum
  intro k _
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right (compare_k hθ hpos F hF σ k) (Nat.cast_nonneg _)

theorem compare (hθ : 0 < θ) (hpos : ∀ i, 0 < p i) (hN : 2 ≤ (niSet p x θ).card) (t : ℕ) :
    ∀ (F : BinaryWord (niSet p x θ).card → ℝ), MonoW (fun w => -F w) → ∀ σ : ListState n,
      expectedAfter (auxiliaryKernel p x θ) σ t (fun η => F (proj p x θ η)) ≤
        expectedAfter (exclusionKernel (niSet p x θ).card θ) (proj p x θ σ) t F := by
  induction t with
  | zero =>
    intro F _ σ
    simp only [expectedAfter, pow_zero, Matrix.one_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact le_rfl
  | succ t ih =>
    intro F hF σ
    rw [expectedAfter_succ', expectedAfter_succ']
    set G : BinaryWord (niSet p x θ).card → ℝ :=
      fun w => expectedAfter (exclusionKernel (niSet p x θ).card θ) w t F with hG
    have hGm : MonoW (fun w => -G w) := by
      have h := PartA.expectedAfter_mono θ t (fun w => -F w) hF
      intro a b hab
      have := h a b hab
      simp only [expectedAfter, mul_neg, Finset.sum_neg_distrib] at this
      simpa [hG, expectedAfter] using this
    calc ∑ η, auxiliaryKernel p x θ σ η *
          expectedAfter (auxiliaryKernel p x θ) η t (fun η => F (proj p x θ η))
        ≤ ∑ η, auxiliaryKernel p x θ σ η * G (proj p x θ η) := by
          apply Finset.sum_le_sum
          intro η _
          exact mul_le_mul_of_nonneg_left (ih F hF η) ((C1.aux_markov p hpos x θ).1 σ η)
      _ ≤ _ := one_step hθ hpos hN G hGm σ

end TranspositionIID.Main.Dev.P34.PartM
end
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.P34.PartM
open TranspositionIID.Main TranspositionIID.Main.Dev TranspositionIID.Main.Dev.L32
/-! Proposition 3.4, bound (3.2): comparison with the exclusion chain and Lemma 3.2. -/
theorem part32 {n : ℕ} (hn : 1024 ≤ n) (p : Fin n → ℝ)
    (hp : ActuarialValuation.isFiniteStateDistribution p)
    (hsort : Decreasing p) (hpos : ∀ i, 0 < p i)
    (x θ : ℝ) (hθ : 0 < θ) (hθcap : θ ≤ 1 / 2) (σ : ListState n) :
    expectedAfter (auxiliaryKernel p x θ) σ (n ^ 4) (separatedInversions p x θ) ≤
      1 / 4 + Real.pi ^ 2 / (6 * θ ^ 2) := by
  have hRHS : 0 ≤ 1 / 4 + Real.pi ^ 2 / (6 * θ ^ 2) := by positivity
  by_cases hboth : (∃ l, Real.log (p l) ≤ x) ∧ (∃ h, x + θ < Real.log (p h))
  swap
  · have hzero : ∀ η, separatedInversions p x θ η = 0 := by
      intro η
      unfold separatedInversions
      rw [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro ⟨i, j⟩ _ ⟨h1, h2, _⟩
      exact hboth ⟨⟨j, h1⟩, ⟨i, h2⟩⟩
    simp only [expectedAfter, hzero, mul_zero, Finset.sum_const_zero]
    exact hRHS
  obtain ⟨⟨l, hl⟩, ⟨h, hh⟩⟩ := hboth
  set N := (niSet p x θ).card with hNdef
  have hN : 2 ≤ N := by
    have hlm : l ∈ niSet p x θ := (mem_niSet p x θ l).2 (Or.inl hl)
    have hhm : h ∈ niSet p x θ := (mem_niSet p x θ h).2 (Or.inr hh)
    have hne : l ≠ h := by intro e; subst e; linarith
    have := Finset.one_lt_card.2 ⟨l, hlm, h, hhm, hne⟩
    omega
  have hNn : N ≤ n := by
    have := Finset.card_le_univ (niSet p x θ); simpa using this
  set w₀ := proj p x θ σ with hw₀
  have hL : ∃ i, w₀ i = false := by
    obtain ⟨m, hm⟩ := exists_emb_label (p := p) (x := x) (θ := θ) σ (k := l) (Or.inl hl)
    refine ⟨m, ?_⟩
    rw [hw₀, proj_apply, hm, Equiv.symm_apply_apply]
    exact (low_iff hθ (Or.inl hl)).1 hl
  have hH : ∃ i, w₀ i = true := by
    obtain ⟨m, hm⟩ := exists_emb_label (p := p) (x := x) (θ := θ) σ (k := h) (Or.inr hh)
    refine ⟨m, ?_⟩
    rw [hw₀, proj_apply, hm, Equiv.symm_apply_apply]
    exact (hiB_true_iff _).2 hh
  have key := TranspositionIID.Main.lemma_3_2 n N hn hN hNn θ hθ hθcap w₀ hL hH
  refine le_trans ?_ key
  set T := n ^ 4 with hT
  set Fs : BinaryWord N → ℝ := fun z => -∑ j ∈ Finset.range N, (pre z j : ℝ) with hFs
  have hF : MonoW (fun z => -Fs z) := by
    intro a b hab
    simp only [hFs, neg_neg]
    apply Finset.sum_le_sum; intro j _; exact_mod_cast hab j
  set c := binaryInversions w₀ + ∑ j ∈ Finset.range N, (pre w₀ j : ℝ) with hc
  have hclass : ∀ z : BinaryWord N, hcount z = hcount w₀ → binaryInversions z = c + Fs z := by
    intro z hz
    have := PartA.inversions_diff z w₀ hz
    rw [Finset.sum_sub_distrib] at this
    simp only [hc, hFs]; linarith
  have hB : ∀ η, separatedInversions p x θ η = c + Fs (proj p x θ η) := by
    intro η
    rw [sep_eq hθ]
    apply hclass
    rw [hw₀, hcount_proj, hcount_proj]
  have hP : ∀ z, (exclusionKernel N θ ^ T) w₀ z * binaryInversions z =
      (exclusionKernel N θ ^ T) w₀ z * (c + Fs z) := by
    intro z
    by_cases hz : (exclusionKernel N θ ^ T) w₀ z = 0
    · rw [hz, zero_mul, zero_mul]
    · rw [hclass z (PartA.kernel_pow_class θ T w₀ z hz)]
  have hrowB := (Rev.pow_markov _ (C1.aux_markov p hpos x θ) T).2 σ
  have hrowP := PartA.kernel_pow_row hN θ T w₀
  have hcmp := compare hθ hpos hN T Fs hF σ
  unfold expectedAfter at hcmp ⊢
  simp_rw [hB, hP, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hrowB, hrowP]
  linarith

end TranspositionIID.Main.Dev.P34.PartM
end

section
set_option autoImplicit false
namespace TranspositionIID.Main.Dev.P34
open TranspositionIID.Main
/-! Blueprint for Proposition 3.4: (3.2) by monotone comparison with the exclusion chain and
`TranspositionIID.Main.lemma_3_2` (imported); (3.3) is `P33.dirichlet_comparison`. -/
alias part32 := TranspositionIID.Main.Dev.P34.PartM.part32

theorem proposition_3_4_dev {n : ℕ} (hn : 1024 ≤ n) (p : Fin n → ℝ)
    (hp : ActuarialValuation.isFiniteStateDistribution p)
    (hsort : Decreasing p) (hpos : ∀ i, 0 < p i)
    (x θ : ℝ) (hθ : 0 < θ) (hθcap : θ ≤ 1 / 2) :
    (∀ σ : ListState n,
      expectedAfter (auxiliaryKernel p x θ) σ (n ^ 4) (separatedInversions p x θ) ≤
        1 / 4 + Real.pi ^ 2 / (6 * θ ^ 2)) ∧
    (∀ v : ListState n → ℝ,
      GibbsCongestion.dirichletForm (auxiliaryKernel p x θ) (stationaryLaw p) v v ≤
        2 * (n : ℝ) ^ 2 * Real.exp (-x) *
          GibbsCongestion.dirichletForm (transpositionKernel p) (stationaryLaw p) v v) :=
  ⟨fun σ => part32 hn p hp hsort hpos x θ hθ hθcap σ,
   fun v => P33.dirichlet_comparison hn p hp hsort hpos x θ hθ hθcap v⟩

end TranspositionIID.Main.Dev.P34
end

section
set_option autoImplicit false
open TranspositionIID
open TranspositionIID.Main
open TranspositionIID.Main.Dev
open TranspositionIID.Main.Dev.P34
open TranspositionIID.Main
theorem solution {n : ℕ} (hn : 1024 ≤ n) (p : Fin n → ℝ)
    (hp : ActuarialValuation.isFiniteStateDistribution p)
    (hsort : Decreasing p) (hpos : ∀ i, 0 < p i)
    (x θ : ℝ) (hθ : 0 < θ) (hθcap : θ ≤ 1 / 2) :
    (∀ σ : ListState n,
      expectedAfter (auxiliaryKernel p x θ) σ (n ^ 4) (separatedInversions p x θ) ≤
        1 / 4 + Real.pi ^ 2 / (6 * θ ^ 2)) ∧
    (∀ v : ListState n → ℝ,
      GibbsCongestion.dirichletForm (auxiliaryKernel p x θ) (stationaryLaw p) v v ≤
        2 * (n : ℝ) ^ 2 * Real.exp (-x) *
          GibbsCongestion.dirichletForm (transpositionKernel p) (stationaryLaw p) v v) := by
  exact TranspositionIID.Main.Dev.P34.proposition_3_4_dev hn p hp hsort hpos x θ hθ hθcap
end
