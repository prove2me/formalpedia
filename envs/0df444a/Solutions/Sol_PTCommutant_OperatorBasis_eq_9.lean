-- Prove2me | solution 1 for PTCommutant.OperatorBasis.eq_9
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T21:26:23.038777+00:00
-- url     : https://prove2.me/submissions/0b604880-a602-4df3-a9c5-d79c2319ba3f

import Mathlib
import Definitions.Def_PTCommutant_OperatorBasis_Model

open QAlgorithms.Schur PTCommutant.OperatorBasis

lemma lp_castLE {k j : ℕ} (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    liftPerm k j σ (Fin.castLE (Nat.le_add_right k j) i) = Fin.castLE (Nat.le_add_right k j) (σ i) := by
  unfold liftPerm
  simp only [Equiv.Perm.extendDomainHom_apply]
  have := Equiv.Perm.extendDomain_apply_image σ (Fin.castLEquiv (Nat.le_add_right k j)) i
  simpa using this

lemma lp_ge {k j : ℕ} (σ : Equiv.Perm (Fin k)) (i : Fin (k + j)) (hi : k ≤ i.val) :
    liftPerm k j σ i = i := by
  unfold liftPerm
  simp only [Equiv.Perm.extendDomainHom_apply]
  apply Equiv.Perm.extendDomain_apply_not_subtype
  omega

lemma lp_range {k j : ℕ} (τ : Equiv.Perm (Fin (k + j))) (h : ∀ i : Fin (k + j), k ≤ i.val → τ i = i) :
    τ ∈ Set.range (liftPerm k j) := by
  have hp : ∀ x : Fin (k + j), (τ x).val < k ↔ x.val < k := by
    intro x
    constructor
    · intro hx
      by_contra hc
      rw [not_lt] at hc
      have := h x hc
      rw [this] at hx; omega
    · intro hx
      by_contra hc
      rw [not_lt] at hc
      have h1 := h (τ x) hc
      have : τ x = x := τ.injective h1
      rw [this] at hc; omega
  refine ⟨(Fin.castLEquiv (Nat.le_add_right k j)).permCongr.symm (τ.subtypePerm hp), ?_⟩
  ext i
  by_cases hi : i.val < k
  · have : i = Fin.castLE (Nat.le_add_right k j) ⟨i.val, hi⟩ := by ext; simp
    rw [this, lp_castLE]
    simp [Equiv.Perm.subtypePerm_apply]
  · push_neg at hi
    rw [lp_ge _ _ hi, h i hi]

lemma mcast (m : ℕ) : (⟨m, by omega⟩ : Fin (m + 2)) =
    Fin.castLE (Nat.le_add_right (m + 1) 1) (Fin.last m) := by ext; simp

lemma fP_last {m : ℕ} (π : Fin (m + 1) → Equiv.Perm (Fin (m + 1)))
    (hπ : ∀ k, π k (Fin.last m) = k) (a b : Fin (m + 1)) (σ : Equiv.Perm (Fin m)) :
    fPerm π a b σ (Fin.last (m + 1)) = Fin.castLE (Nat.le_add_right (m + 1) 1) b := by
  unfold fPerm swapLast
  rw [← map_inv]
  simp only [Equiv.Perm.mul_apply]
  rw [lp_ge _ (Fin.last (m + 1)) (by simp), Equiv.swap_apply_right,
    lp_ge (j := 2) σ ⟨m, by omega⟩ (by simp), mcast, lp_castLE, hπ]

lemma fP_inv_last {m : ℕ} (π : Fin (m + 1) → Equiv.Perm (Fin (m + 1)))
    (hπ : ∀ k, π k (Fin.last m) = k) (a b : Fin (m + 1)) (σ : Equiv.Perm (Fin m)) :
    (fPerm π a b σ)⁻¹ (Fin.last (m + 1)) = Fin.castLE (Nat.le_add_right (m + 1) 1) a := by
  rw [Equiv.Perm.inv_eq_iff_eq]
  unfold fPerm swapLast
  rw [← map_inv]
  simp only [Equiv.Perm.mul_apply]
  have h1 : (π a)⁻¹ a = Fin.last m := by
    rw [Equiv.Perm.inv_eq_iff_eq, hπ]
  rw [lp_castLE, h1, ← mcast, Equiv.swap_apply_left,
    lp_ge (j := 2) σ (Fin.last (m + 1)) (by simp), lp_ge _ (Fin.last (m + 1)) (by simp)]

theorem solution {m : ℕ} (π : Fin (m + 1) → Equiv.Perm (Fin (m + 1)))
    (hπ : ∀ k, π k (Fin.last m) = k) :
    (∀ τ : Equiv.Perm (Fin (m + 2)), τ (Fin.last (m + 1)) ≠ Fin.last (m + 1) →
      ∃! t : Fin (m + 1) × Fin (m + 1) × Equiv.Perm (Fin m), fPerm π t.1 t.2.1 t.2.2 = τ) ∧
    (∀ (a b : Fin (m + 1)) (σ : Equiv.Perm (Fin m)),
      fPerm π a b σ (Fin.last (m + 1)) ≠ Fin.last (m + 1)) ∧
    (∀ τ : Equiv.Perm (Fin (m + 2)),
      τ (Fin.last (m + 1)) = Fin.last (m + 1) ↔ τ ∈ Set.range (liftPerm (m + 1) 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro τ hτ
    have hb : (τ (Fin.last (m + 1))).val < m + 1 := by
      have := (τ (Fin.last (m + 1))).isLt
      have : (τ (Fin.last (m + 1))).val ≠ m + 1 := fun h => hτ (by ext; simpa using h)
      omega
    have hτi : τ⁻¹ (Fin.last (m + 1)) ≠ Fin.last (m + 1) := by
      intro h
      rw [Equiv.Perm.inv_eq_iff_eq] at h
      exact hτ h.symm
    have ha : (τ⁻¹ (Fin.last (m + 1))).val < m + 1 := by
      have := (τ⁻¹ (Fin.last (m + 1))).isLt
      have : (τ⁻¹ (Fin.last (m + 1))).val ≠ m + 1 := fun h => hτi (by ext; simpa using h)
      omega
    set b : Fin (m + 1) := ⟨_, hb⟩ with hbdef
    set a : Fin (m + 1) := ⟨_, ha⟩ with hadef
    have hbc : Fin.castLE (Nat.le_add_right (m + 1) 1) b = τ (Fin.last (m + 1)) := by ext; simp [b]
    have hac : Fin.castLE (Nat.le_add_right (m + 1) 1) a = τ⁻¹ (Fin.last (m + 1)) := by ext; simp [a]
    set ρ : Equiv.Perm (Fin (m + 2)) :=
      (liftPerm (m + 1) 1 (π b))⁻¹ * τ * liftPerm (m + 1) 1 (π a) * swapLast m with hρ
    have hρfix : ∀ i : Fin (m + 2), m ≤ i.val → ρ i = i := by
      intro i hi
      have hi' : i = ⟨m, by omega⟩ ∨ i = Fin.last (m + 1) := by
        rcases Nat.lt_or_ge m i.val with h | h
        · right; ext; simp; omega
        · left; ext; simp; omega
      have hpb : (π b)⁻¹ b = Fin.last m := by rw [Equiv.Perm.inv_eq_iff_eq, hπ]
      rcases hi' with h | h <;> rw [h]
      · simp only [hρ, swapLast, Equiv.Perm.mul_apply, ← map_inv]
        rw [Equiv.swap_apply_left, lp_ge _ (Fin.last (m + 1)) (by simp), ← hbc, lp_castLE, hpb,
          ← mcast]
      · simp only [hρ, swapLast, Equiv.Perm.mul_apply, ← map_inv]
        rw [Equiv.swap_apply_right, mcast, lp_castLE, hπ, hac, (by simp : τ (τ⁻¹ (Fin.last (m + 1))) = Fin.last (m + 1)),
          lp_ge _ (Fin.last (m + 1)) (by simp)]
    obtain ⟨σ, hσ⟩ := lp_range (k := m) (j := 2) ρ hρfix
    have hsw : swapLast m * swapLast m = 1 := by
      unfold swapLast; exact Equiv.swap_mul_self _ _
    refine ⟨(a, b, σ), ?_, ?_⟩
    · show fPerm π a b σ = τ
      unfold fPerm
      rw [hσ, hρ]
      simp only [mul_assoc, hsw, mul_one, mul_inv_cancel, mul_inv_cancel_left]
    · rintro ⟨a', b', σ'⟩ h
      simp only at h
      have hb' : b' = b := by
        have := fP_last π hπ a' b' σ'
        rw [h, ← hbc] at this
        exact (Fin.castLE_injective _ this).symm
      have ha' : a' = a := by
        have := fP_inv_last π hπ a' b' σ'
        rw [h, ← hac] at this
        exact (Fin.castLE_injective _ this).symm
      subst hb' ha'
      have : liftPerm m 2 σ' = liftPerm m 2 σ := by
        rw [hσ, hρ, ← h]
        unfold fPerm
        simp only [mul_assoc, inv_mul_cancel, hsw, mul_one, inv_mul_cancel_left]
      have hinj : Function.Injective (liftPerm m 2) := by
        unfold liftPerm; exact Equiv.Perm.extendDomainHom_injective _
      rw [hinj this]
  · intro a b σ
    rw [fP_last π hπ]
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  · intro τ
    constructor
    · intro h
      apply lp_range
      intro i hi
      have : i = Fin.last (m + 1) := by ext; simp; omega
      rw [this, h]
    · rintro ⟨σ, rfl⟩
      exact lp_ge _ _ (by simp)
