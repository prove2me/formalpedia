-- Prove2me | solution 1 for QuantumMaxCutEnergy.matching_dominated_of_bipartite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T04:40:58.18362+00:00
-- url     : https://prove2.me/submissions/3979f062-2fc8-40ae-b1dd-91d9e93b3d07

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Definitions.Def_QuantumMaxCutMatchingPadding
import Theorems.Thm_QuantumMaxCutEnergy_exists_matching_ge_perm_sum_support
import Theorems.Thm_QuantumMaxCutEnergy_padWeight_eq_sum_perm
import Theorems.Thm_QuantumMaxCutEnergy_two_mul_sum_edges_eq_sum_pairs
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators

open QuantumMaxCutEnergy

lemma permMatrix_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (a b : Fin n) :
    (Equiv.Perm.permMatrix ℝ σ) a b = if σ a = b then 1 else 0 := by
  rw [Equiv.Perm.permMatrix]
  simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_some_iff]

theorem padWeight_offdiag_eq {n : ℕ} (x : Edge n → ℝ) (lam : Equiv.Perm (Fin n) → ℝ)
    (h : ∑ σ, lam σ • Equiv.Perm.permMatrix ℝ σ = padWeight x) {a b : Fin n} (hab : a ≠ b) :
    pairWeight x a b = ∑ σ, lam σ * (if σ a = b then (1 : ℝ) else 0) := by
  have h1 : (∑ σ, lam σ • Equiv.Perm.permMatrix ℝ σ) a b = (padWeight x) a b := by rw [h]
  rw [padWeight_apply_of_ne x hab] at h1
  rw [← h1, Matrix.sum_apply]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Matrix.smul_apply, smul_eq_mul, permMatrix_apply]

theorem sum_pair_padWeight {n : ℕ} (w x : Edge n → ℝ) (lam : Equiv.Perm (Fin n) → ℝ)
    (h : ∑ σ, lam σ • Equiv.Perm.permMatrix ℝ σ = padWeight x) (a : Fin n) :
    ∑ b, pairWeight w a b * (padWeight x) a b
      = ∑ σ, lam σ * pairWeight w a (σ a) := by
  have hstep : ∀ b : Fin n, pairWeight w a b * (padWeight x) a b
      = ∑ σ, pairWeight w a b * (lam σ * (if σ a = b then (1 : ℝ) else 0)) := by
    intro b
    by_cases hab : a = b
    · subst hab
      rw [pairWeight_self]
      refine Eq.trans (zero_mul _) ?_
      refine (Finset.sum_eq_zero (fun σ _ => ?_)).symm
      ring
    · have h1 : (padWeight x) a b = ∑ σ, lam σ * (if σ a = b then (1:ℝ) else 0) := by
        rw [padWeight_apply_of_ne x hab]
        exact padWeight_offdiag_eq x lam h hab
      rw [h1, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun b _ => hstep b), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Finset.sum_eq_single (σ a)]
  · rw [if_pos rfl]; ring
  · intro b _ hb
    rw [if_neg (by omega)]; ring
  · intro hcon
    exact absurd (Finset.mem_univ (σ a)) hcon

/-- **If the Birkhoff weight of `σ` is nonzero, every nontrivial step of `σ` has nonzero pair weight.** -/
theorem pairWeight_step_ne_zero {n : ℕ} (x : Edge n → ℝ) (lam : Equiv.Perm (Fin n) → ℝ)
    (hlamnn : ∀ σ, 0 ≤ lam σ)
    (h : ∑ σ, lam σ • Equiv.Perm.permMatrix ℝ σ = padWeight x)
    (σ : Equiv.Perm (Fin n)) (hσ : lam σ ≠ 0) :
    ∀ a, σ a ≠ a → pairWeight x a (σ a) ≠ 0 := by
  intro a ha hzero
  have hid : pairWeight x a (σ a) = ∑ τ, lam τ * (if τ a = σ a then (1:ℝ) else 0) :=
    padWeight_offdiag_eq x lam h (Ne.symm ha)
  rw [hzero] at hid
  have hterm : lam σ * (if σ a = σ a then (1 : ℝ) else 0) ≤ ∑ τ, lam τ * (if τ a = σ a then (1:ℝ) else 0) := by
    refine Finset.single_le_sum (f := fun τ => lam τ * (if τ a = σ a then (1:ℝ) else 0))
      (fun τ _ => ?_) (Finset.mem_univ σ)
    by_cases hτ : τ a = σ a <;> simp [hτ, hlamnn τ]
  rw [← hid] at hterm
  rw [if_pos rfl, mul_one] at hterm
  exact hσ (le_antisymm hterm (hlamnn σ))

open QuantumMaxCutEnergy

/-- **Bipartite case of Edmonds' exactness.** A nonnegative edge weight with vertex loads at most `1` and
bipartite support is dominated by an integral matching. -/
theorem solution {n : ℕ} (w x : Edge n → ℝ) (c : Fin n → Bool)
    (hx : ∀ e, 0 ≤ x e) (hload : ∀ v, loadAt x v ≤ 1)
    (hc : ∀ e : Edge n, x e ≠ 0 → c e.val.1 ≠ c e.val.2) :
    ∃ M : Finset (Edge n),
      (∀ e ∈ M, ∀ e' ∈ M, e ≠ e' →
        e.val.1 ≠ e'.val.1 ∧ e.val.1 ≠ e'.val.2 ∧ e.val.2 ≠ e'.val.1 ∧ e.val.2 ≠ e'.val.2) ∧
      ∑ e, w e * x e ≤ ∑ e ∈ M, w e := by
  classical
  obtain ⟨lam, hlamnn, hlam1, hlam⟩ := padWeight_eq_sum_perm x hx hload
  -- main identity
  have hid : 2 * (∑ e, w e * x e) = ∑ σ, lam σ * (∑ a, pairWeight w a (σ a)) := by
    have h2 := two_mul_sum_edges_eq_sum_pairs (fun a b : Fin n => pairWeight w a b * pairWeight x a b)
      (fun a b => by rw [pairWeight_comm w a b, pairWeight_comm x a b, mul_comm])
      (fun a => by rw [pairWeight_self, zero_mul])
    have heq : ∀ e : Edge n,
        pairWeight w e.val.1 e.val.2 * pairWeight x e.val.1 e.val.2 = w e * x e := by
      intro e
      rw [pairWeight, pairWeight, dif_pos e.property, dif_pos e.property]
    have hmid : ∑ a, ∑ b, pairWeight w a b * pairWeight x a b
        = ∑ a, ∑ b, pairWeight w a b * (padWeight x) a b := by
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      by_cases h : a = b
      · subst h; rw [padWeight_apply_self, pairWeight_self]; ring
      · rw [padWeight_apply_of_ne x h]
    calc 2 * (∑ e, w e * x e)
        = 2 * ∑ e : Edge n, pairWeight w e.val.1 e.val.2 * pairWeight x e.val.1 e.val.2 := by
          rw [Finset.sum_congr rfl (fun e _ => (heq e).symm)]
      _ = ∑ a, ∑ b, pairWeight w a b * pairWeight x a b := h2
      _ = ∑ a, ∑ b, pairWeight w a b * (padWeight x) a b := hmid
      _ = ∑ a, ∑ σ, lam σ * pairWeight w a (σ a) :=
          Finset.sum_congr rfl (fun a _ => sum_pair_padWeight w x lam hlam a)
      _ = ∑ σ, lam σ * (∑ a, pairWeight w a (σ a)) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun σ _ => (Finset.mul_sum _ _ _).symm)
  -- choices
  have hex : ∀ σ : Equiv.Perm (Fin n), ∃ M : Finset (Edge n),
      (∀ e ∈ M, ∀ e' ∈ M, e ≠ e' →
        e.val.1 ≠ e'.val.1 ∧ e.val.1 ≠ e'.val.2 ∧ e.val.2 ≠ e'.val.1 ∧ e.val.2 ≠ e'.val.2) ∧
      (lam σ = 0 ∨ ∑ a, pairWeight w a (σ a) ≤ 2 * ∑ e ∈ M, w e) := by
    intro σ
    by_cases h0 : lam σ = 0
    · exact ⟨(∅ : Finset (Edge n)), by simp, Or.inl h0⟩
    · obtain ⟨M, hM, hle⟩ := exists_matching_ge_perm_sum_support w x c hc σ
        (pairWeight_step_ne_zero x lam hlamnn hlam σ h0)
      exact ⟨M, hM, Or.inr hle⟩
  set Mfn : Equiv.Perm (Fin n) → Finset (Edge n) := fun σ => Classical.choose (hex σ) with hMfn
  have hMfn := fun σ => Classical.choose_spec (hex σ)
  -- nonempty of the support of `lam`
  have hne : (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => lam σ ≠ 0)).Nonempty := by
    by_contra hc0
    rw [Finset.not_nonempty_iff_eq_empty] at hc0
    have hzero : ∀ σ : Equiv.Perm (Fin n), lam σ = 0 := by
      intro σ
      by_contra h
      have : σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => lam σ ≠ 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      rw [hc0] at this
      exact absurd this (Finset.notMem_empty σ)
    have : (∑ σ : Equiv.Perm (Fin n), lam σ) = 0 := Finset.sum_eq_zero (fun σ _ => hzero σ)
    rw [hlam1] at this
    exact one_ne_zero this
  obtain ⟨σ₀, hσ₀mem, hσ₀max⟩ := Finset.exists_max_image
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => lam σ ≠ 0))
    (fun σ => ∑ e ∈ Mfn σ, w e) hne
  set A : Equiv.Perm (Fin n) → ℝ := fun σ => ∑ e ∈ Mfn σ, w e with hA
  -- termwise bound
  have hterm : ∀ σ : Equiv.Perm (Fin n),
      lam σ * (∑ a, pairWeight w a (σ a)) ≤ lam σ * (2 * A σ) := by
    intro σ
    rcases (hMfn σ).2 with h0 | hle
    · rw [h0, zero_mul, zero_mul]
    · exact mul_le_mul_of_nonneg_left hle (hlamnn σ)
  have hstep1 : ∑ σ, lam σ * (∑ a, pairWeight w a (σ a)) ≤ ∑ σ, lam σ * (2 * A σ) :=
    Finset.sum_le_sum (fun σ _ => hterm σ)
  have hstep2 : ∑ σ, lam σ * (2 * A σ) = 2 * ∑ σ, lam σ * A σ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun σ _ => by ring)
  have hstep3 : ∑ σ, lam σ * A σ ≤ ∑ σ, lam σ * A σ₀ := by
    refine Finset.sum_le_sum (fun σ _ => ?_)
    by_cases h0 : lam σ = 0
    · rw [h0, zero_mul, zero_mul]
    · have hmem : σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => lam σ ≠ 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩
      exact mul_le_mul_of_nonneg_left (hσ₀max σ hmem) (hlamnn σ)
  have hstep4 : ∑ σ, lam σ * A σ₀ = A σ₀ := by
    rw [← Finset.sum_mul, hlam1, one_mul]
  refine ⟨Mfn σ₀, (hMfn σ₀).1, ?_⟩
  have : 2 * (∑ e, w e * x e) ≤ 2 * A σ₀ := by
    rw [hid]
    calc ∑ σ, lam σ * (∑ a, pairWeight w a (σ a))
        ≤ ∑ σ, lam σ * (2 * A σ) := hstep1
      _ = 2 * ∑ σ, lam σ * A σ := hstep2
      _ ≤ 2 * ∑ σ, lam σ * A σ₀ := by
          have := hstep3; linarith
      _ = 2 * A σ₀ := by rw [hstep4]
  linarith

#print axioms solution
