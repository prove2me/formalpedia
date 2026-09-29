-- Prove2me | solution 1 for Rudin.ch05_taylor_corrected
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-14T03:55:55.759822+00:00
-- url     : https://prove2.me/submissions/1c9e0746-fd57-4f4f-b099-5737938edfb9

import Mathlib

open Filter Topology

namespace RudinTaylorAux

/-- The auxiliary function `g` of Rudin's proof, together with its iterated derivatives:
`taylorAux f al M n k j t` is the `k`-th derivative of
`t ↦ f t - P t - M (t - al)^n`, where `P` is the Taylor polynomial of `f` at `al` of degree
`n - 1`, provided `k + j = n`. -/
noncomputable def taylorAux (f : ℝ → ℝ) (al M : ℝ) (n k j : ℕ) (t : ℝ) : ℝ :=
  iteratedDeriv k f t
    - (∑ i ∈ Finset.range j, iteratedDeriv (i + k) f al / (i.factorial : ℝ) * (t - al) ^ i)
    - M * ((n.factorial : ℝ) / (j.factorial : ℝ)) * (t - al) ^ j

/-- The derivative of `t ↦ (t - al) ^ i`. -/
lemma hasDerivAt_sub_const_pow (al t : ℝ) (i : ℕ) :
    HasDerivAt (fun t : ℝ => (t - al) ^ i) ((i : ℝ) * (t - al) ^ (i - 1)) t := by
  have h0 : HasDerivAt (fun x : ℝ => x - al) 1 t := (hasDerivAt_id t).sub_const al
  have h1 := h0.pow i
  rw [mul_one] at h1
  exact h1

lemma taylorAux_self (f : ℝ → ℝ) (al M : ℝ) (n k j : ℕ) :
    taylorAux f al M n k (j + 1) al = 0 := by
  have hsum : (∑ i ∈ Finset.range (j + 1),
      iteratedDeriv (i + k) f al / (i.factorial : ℝ) * (al - al) ^ i)
      = iteratedDeriv k f al := by
    rw [Finset.sum_range_succ' (fun i => iteratedDeriv (i + k) f al / (i.factorial : ℝ)
      * (al - al) ^ i) j]
    have : ∀ i ∈ Finset.range j,
        iteratedDeriv (i + 1 + k) f al / ((i + 1).factorial : ℝ) * (al - al) ^ (i + 1) = 0 := by
      intro i _
      simp
    rw [Finset.sum_congr rfl this]
    simp
  rw [taylorAux, hsum]
  simp

lemma hasDerivAt_taylorAux (f : ℝ → ℝ) (al M : ℝ) (n k j : ℕ) (t : ℝ)
    (hf : DifferentiableAt ℝ (iteratedDeriv k f) t) :
    HasDerivAt (taylorAux f al M n k (j + 1)) (taylorAux f al M n (k + 1) j t) t := by
  have h1 : HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f t) t := by
    simpa [iteratedDeriv_succ] using hf.hasDerivAt
  have h2 : HasDerivAt
      (fun t : ℝ => ∑ i ∈ Finset.range (j + 1),
        iteratedDeriv (i + k) f al / (i.factorial : ℝ) * (t - al) ^ i)
      (∑ i ∈ Finset.range j,
        iteratedDeriv (i + (k + 1)) f al / (i.factorial : ℝ) * (t - al) ^ i) t := by
    have hterm : ∀ i ∈ Finset.range (j + 1),
        HasDerivAt (fun t : ℝ => iteratedDeriv (i + k) f al / (i.factorial : ℝ) * (t - al) ^ i)
          (iteratedDeriv (i + k) f al / (i.factorial : ℝ) * (i * (t - al) ^ (i - 1))) t := by
      intro i _
      have hpow := hasDerivAt_sub_const_pow al t i
      simpa using hpow.const_mul (iteratedDeriv (i + k) f al / (i.factorial : ℝ))
    have hsum : HasDerivAt
        (fun t : ℝ => ∑ i ∈ Finset.range (j + 1),
          iteratedDeriv (i + k) f al / (i.factorial : ℝ) * (t - al) ^ i)
        (∑ i ∈ Finset.range (j + 1),
          iteratedDeriv (i + k) f al / (i.factorial : ℝ) * (i * (t - al) ^ (i - 1))) t := by
      have hs := HasDerivAt.sum hterm
      have heq : (∑ i ∈ Finset.range (j + 1), fun t : ℝ =>
            iteratedDeriv (i + k) f al / (i.factorial : ℝ) * (t - al) ^ i)
          = fun t : ℝ => ∑ i ∈ Finset.range (j + 1),
            iteratedDeriv (i + k) f al / (i.factorial : ℝ) * (t - al) ^ i := by
        funext s
        simp [Finset.sum_apply]
      rwa [heq] at hs
    convert hsum using 1
    rw [Finset.sum_range_succ' (fun i => iteratedDeriv (i + k) f al / (i.factorial : ℝ)
      * (i * (t - al) ^ (i - 1))) j]
    have : ∀ i ∈ Finset.range j,
        iteratedDeriv (i + (k + 1)) f al / (i.factorial : ℝ) * (t - al) ^ i
        = iteratedDeriv (i + 1 + k) f al / ((i + 1).factorial : ℝ)
            * ((i + 1 : ℕ) * (t - al) ^ (i + 1 - 1)) := by
      intro i _
      have hfac : ((i + 1).factorial : ℝ) = (i + 1 : ℕ) * (i.factorial : ℝ) := by
        push_cast [Nat.factorial_succ]
        ring
      have hi1 : ((i : ℝ) + 1) ≠ 0 := by positivity
      have hfacpos : (i.factorial : ℝ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero i
      rw [hfac]
      have : i + 1 + k = i + (k + 1) := by omega
      rw [this]
      push_cast
      field_simp
    rw [Finset.sum_congr rfl this]
    simp
  have h3 : HasDerivAt
      (fun t : ℝ => M * ((n.factorial : ℝ) / ((j + 1).factorial : ℝ)) * (t - al) ^ (j + 1))
      (M * ((n.factorial : ℝ) / (j.factorial : ℝ)) * (t - al) ^ j) t := by
    have hd : HasDerivAt (fun t : ℝ => (t - al) ^ (j + 1)) ((j + 1 : ℕ) * (t - al) ^ j) t := by
      simpa using hasDerivAt_sub_const_pow al t (j + 1)
    have hcoef : M * ((n.factorial : ℝ) / ((j + 1).factorial : ℝ)) * ((j + 1 : ℕ) * (t - al) ^ j)
        = M * ((n.factorial : ℝ) / (j.factorial : ℝ)) * (t - al) ^ j := by
      have hfac : (((j + 1).factorial : ℕ) : ℝ) = ((j : ℝ) + 1) * (j.factorial : ℝ) := by
        push_cast [Nat.factorial_succ]
        ring
      have hfacpos : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
      have hj1 : ((j : ℝ) + 1) ≠ 0 := by positivity
      rw [hfac]
      push_cast
      field_simp
    rw [← hcoef]
    exact hd.const_mul (M * ((n.factorial : ℝ) / ((j + 1).factorial : ℝ)))
  exact (h1.sub h2).sub h3

lemma mem_uIoo_iff {u v x : ℝ} :
    x ∈ Set.uIoo u v ↔ (u < x ∧ x < v) ∨ (v < x ∧ x < u) := by
  have hmem : x ∈ Set.uIoo u v ↔ min u v < x ∧ x < max u v := by simp [Set.uIoo]
  rw [hmem]
  rcases lt_trichotomy u v with h | h | h
  · rw [min_eq_left h.le, max_eq_right h.le]
    constructor
    · rintro ⟨h1, h2⟩
      exact Or.inl ⟨h1, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, h2⟩
      · linarith
  · subst h
    simp
  · rw [min_eq_right h.le, max_eq_left h.le]
    constructor
    · rintro ⟨h1, h2⟩
      exact Or.inr ⟨h1, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · linarith
      · exact ⟨h1, h2⟩

lemma uIoo_subset_uIoo_of_mem {u v x : ℝ} (hx : x ∈ Set.uIoo u v) :
    Set.uIoo u x ⊆ Set.uIoo u v := by
  intro y hy
  rw [mem_uIoo_iff] at hx hy ⊢
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hy with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · exact Or.inl ⟨h3, by linarith⟩
  · linarith
  · linarith
  · exact Or.inr ⟨by linarith, h4⟩

lemma exists_deriv_eq_zero_uIoo {u v : ℝ} (huv : u ≠ v) {g g' : ℝ → ℝ}
    (hc : ContinuousOn g (Set.uIcc u v))
    (hd : ∀ x ∈ Set.uIoo u v, HasDerivAt g (g' x) x)
    (h : g u = g v) : ∃ y ∈ Set.uIoo u v, g' y = 0 := by
  rcases lt_or_gt_of_ne huv with hlt | hlt
  · have huIcc : Set.uIcc u v = Set.Icc u v := Set.uIcc_of_le hlt.le
    have huIoo : Set.uIoo u v = Set.Ioo u v := by
      simp [Set.uIoo, min_eq_left hlt.le, max_eq_right hlt.le]
    rw [huIoo]
    refine exists_hasDerivAt_eq_zero hlt (by rwa [huIcc] at hc) h ?_
    intro x hx
    exact hd x (by rwa [huIoo])
  · have huIcc : Set.uIcc u v = Set.Icc v u := Set.uIcc_of_ge hlt.le
    have huIoo : Set.uIoo u v = Set.Ioo v u := by
      simp [Set.uIoo, min_eq_right hlt.le, max_eq_left hlt.le]
    rw [huIoo]
    refine exists_hasDerivAt_eq_zero hlt (by rwa [huIcc] at hc) h.symm ?_
    intro x hx
    exact hd x (by rwa [huIoo])

end RudinTaylorAux

open RudinTaylorAux

/-- **Rudin, Theorem 5.15 (Taylor's theorem)**, with the hypotheses stated for all orders
`k ≤ n - 1`: if `f, f', …, f^(n-1)` are continuous on `[a,b]` and `f', …, f^(n)` exist on
`(a,b)`, and `α ≠ β` are points of `[a,b]`, then there is a point `x` strictly between `α` and
`β` with
`f β = ∑_{k<n} f^(k)(α)/k! (β-α)^k + f^(n)(x)/n! (β-α)^n`. -/
theorem solution (a b : ℝ) (hab : a < b) (f : ℝ → ℝ) (n : ℕ) (hn : 0 < n)
    (hcont : ∀ k ≤ n - 1, ContinuousOn (iteratedDeriv k f) (Set.Icc a b))
    (hderiv : ∀ k ≤ n - 1, ∀ t ∈ Set.Ioo a b, DifferentiableAt ℝ (iteratedDeriv k f) t)
    (α β : ℝ) (hα : α ∈ Set.Icc a b) (hβ : β ∈ Set.Icc a b) (hne : α ≠ β) :
    ∃ x : ℝ, ((α < x ∧ x < β) ∨ (β < x ∧ x < α)) ∧
      f β = (∑ k ∈ Finset.range n, iteratedDeriv k f α / (k.factorial : ℝ) * (β - α) ^ k)
        + iteratedDeriv n f x / (n.factorial : ℝ) * (β - α) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hcont hderiv
  -- the interval between `α` and `β` is contained in `[a, b]`
  have hsubIcc : Set.uIcc α β ⊆ Set.Icc a b := by
    rw [← Set.uIcc_of_le hab.le]
    exact Set.uIcc_subset_uIcc (by rwa [Set.uIcc_of_le hab.le])
      (by rwa [Set.uIcc_of_le hab.le])
  have hsubIoo : Set.uIoo α β ⊆ Set.Ioo a b := by
    intro x hx
    rw [mem_uIoo_iff] at hx
    obtain ⟨ha1, ha2⟩ := hα
    obtain ⟨hb1, hb2⟩ := hβ
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
  have hβα : β - α ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  set M : ℝ := (f β - ∑ k ∈ Finset.range (m + 1),
    iteratedDeriv k f α / (k.factorial : ℝ) * (β - α) ^ k) / (β - α) ^ (m + 1) with hM
  -- continuity of the auxiliary functions on any subinterval of `[a, b]`
  have hContAux : ∀ k ≤ m, ∀ j : ℕ, ∀ s ⊆ Set.Icc a b,
      ContinuousOn (taylorAux f α M (m + 1) k j) s := by
    intro k hk j s hs
    have h1 : ContinuousOn (iteratedDeriv k f) s := (hcont k hk).mono hs
    have h2 : Continuous fun t : ℝ =>
        ∑ i ∈ Finset.range j, iteratedDeriv (i + k) f α / (i.factorial : ℝ) * (t - α) ^ i := by
      fun_prop
    have h3 : Continuous fun t : ℝ =>
        M * (((m + 1).factorial : ℝ) / (j.factorial : ℝ)) * (t - α) ^ j := by fun_prop
    exact (h1.sub h2.continuousOn).sub h3.continuousOn
  -- derivative of the auxiliary functions on the open interval
  have hDerivAux : ∀ k ≤ m, ∀ j : ℕ, ∀ x ∈ Set.uIoo α β,
      HasDerivAt (taylorAux f α M (m + 1) k (j + 1)) (taylorAux f α M (m + 1) (k + 1) j x) x := by
    intro k hk j x hx
    exact hasDerivAt_taylorAux f α M (m + 1) k j x (hderiv k hk x (hsubIoo hx))
  -- the Rolle chain
  have key : ∀ i j : ℕ, i + j = m →
      ∃ x ∈ Set.uIoo α β, taylorAux f α M (m + 1) (i + 1) j x = 0 := by
    intro i
    induction i with
    | zero =>
      intro j hj
      obtain rfl : m = j := by omega
      have hval : taylorAux f α M (m + 1) 0 (m + 1) α
          = taylorAux f α M (m + 1) 0 (m + 1) β := by
        rw [taylorAux_self]
        have hzero : taylorAux f α M (m + 1) 0 (m + 1) β = 0 := by
          have hpow : ((β - α) ^ (m + 1)) ≠ 0 := pow_ne_zero _ hβα
          simp only [taylorAux, iteratedDeriv_zero, Nat.add_zero, hM]
          field_simp
          ring
        exact hzero.symm
      obtain ⟨y, hy, hy0⟩ :=
        exists_deriv_eq_zero_uIoo hne
          (g := taylorAux f α M (m + 1) 0 (m + 1))
          (g' := fun x => taylorAux f α M (m + 1) 1 m x)
          (hContAux 0 (by omega) _ _ hsubIcc)
          (fun x hx => hDerivAux 0 (by omega) m x hx) hval
      exact ⟨y, hy, hy0⟩
    | succ i ih =>
      intro j hj
      obtain ⟨x, hx, hx0⟩ := ih (j + 1) (by omega)
      have hxne : α ≠ x := by
        rw [mem_uIoo_iff] at hx
        rcases hx with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact ne_of_lt h1
        · exact (ne_of_gt h2)
      have hsub' : Set.uIoo α x ⊆ Set.uIoo α β := uIoo_subset_uIoo_of_mem hx
      have hsubIcc' : Set.uIcc α x ⊆ Set.Icc a b := by
        refine subset_trans ?_ hsubIcc
        refine Set.uIcc_subset_uIcc Set.left_mem_uIcc ?_
        exact Set.Ioo_subset_Icc_self hx
      obtain ⟨y, hy, hy0⟩ :=
        exists_deriv_eq_zero_uIoo hxne
          (g := taylorAux f α M (m + 1) (i + 1) (j + 1))
          (g' := fun z => taylorAux f α M (m + 1) (i + 2) j z)
          (hContAux (i + 1) (by omega) _ _ hsubIcc')
          (fun z hz => hDerivAux (i + 1) (by omega) j z (hsub' hz))
          (by rw [taylorAux_self, hx0])
      exact ⟨y, hsub' hy, hy0⟩
  obtain ⟨x, hx, hx0⟩ := key m 0 (by omega)
  refine ⟨x, (mem_uIoo_iff.mp hx), ?_⟩
  have hfac : ((m + 1).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (m + 1)
  have hx0' : iteratedDeriv (m + 1) f x = M * ((m + 1).factorial : ℝ) := by
    simp only [taylorAux, Finset.range_zero, Finset.sum_empty, Nat.factorial_zero, Nat.cast_one,
      div_one, pow_zero, mul_one, sub_zero] at hx0
    linarith
  have hpow : ((β - α) ^ (m + 1)) ≠ 0 := pow_ne_zero _ hβα
  rw [hx0']
  field_simp
  rw [hM]
  field_simp
  ring
