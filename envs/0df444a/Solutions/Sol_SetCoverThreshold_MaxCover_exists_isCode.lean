-- Prove2me | solution 1 for SetCoverThreshold.MaxCover.exists_isCode
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T19:11:02.58999+00:00
-- url     : https://prove2.me/submissions/bbdc87c2-5df6-43fa-bbb7-931a9138b2da

import Definitions.Def_SetCoverThreshold_MaxCover_ProofSystem

set_option autoImplicit false
set_option linter.unusedVariables false

open SetCoverThreshold.MaxCover Classical

private lemma card_filter_bool_of_involution {ℓ : ℕ} (f : Fin ℓ → Bool) (σ : Fin ℓ ≃ Fin ℓ)
    (hσ : ∀ j, f (σ j) = !(f j)) :
    2 * (Finset.univ.filter (fun j => f j = true)).card = ℓ := by
  let S₁ := Finset.univ.filter (fun j : Fin ℓ => f j = true)
  let S₀ := Finset.univ.filter (fun j : Fin ℓ => f j = false)
  have hbij : S₁.card = S₀.card := by
    refine Finset.card_bij (fun j _ => σ j) ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_filter] at hj ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [hσ j, hj.2]
      rfl
    · intro j₁ _ j₂ _ h
      exact σ.injective h
    · intro j hj
      rw [Finset.mem_filter] at hj
      refine ⟨σ.symm j, ?_, σ.apply_symm_apply j⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have h1 := hσ (σ.symm j)
      rw [σ.apply_symm_apply] at h1
      cases hval : f (σ.symm j)
      · rw [hval] at h1
        exact absurd (hj.2.symm.trans h1) Bool.noConfusion
      · rfl
  have hunion : S₁ ∪ S₀ = Finset.univ := by
    ext j
    simp only [S₁, S₀, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    cases f j <;> simp
  have hdisj : Disjoint S₁ S₀ := by
    rw [Finset.disjoint_filter]
    intro j _ h1 h0
    rw [h1] at h0
    exact Bool.noConfusion h0
  have hsum : S₁.card + S₀.card = ℓ := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
  change 2 * S₁.card = ℓ
  omega

private def alphaFlip {m k : ℕ} (i : Fin k) :
    (Fin m × (Fin k → Bool)) ≃ (Fin m × (Fin k → Bool)) where
  toFun p := (p.1, fun i' => if i' = i then !p.2 i' else p.2 i')
  invFun p := (p.1, fun i' => if i' = i then !p.2 i' else p.2 i')
  left_inv p := by
    rcases p with ⟨s, x⟩
    ext i'
    · rfl
    · dsimp
      by_cases h : i' = i <;> simp [h]
  right_inv p := by
    rcases p with ⟨s, x⟩
    ext i'
    · rfl
    · dsimp
      by_cases h : i' = i <;> simp [h]

theorem solution (k ℓ₀ : ℕ) (hk : 1 ≤ k) :
    ∃ (ℓ : ℕ) (code : Fin k → Fin ℓ → Bool), ℓ₀ ≤ ℓ ∧ 1 ≤ ℓ ∧ IsCode code := by
  let α := Fin (ℓ₀ + 1) × (Fin k → Bool)
  let ℓ := Fintype.card α
  let e : Fin ℓ ≃ α := (Fintype.equivFin α).symm
  let code : Fin k → Fin ℓ → Bool := fun i j => (e j).2 i
  have hℓ_eq : ℓ = (ℓ₀ + 1) * 2 ^ k := by
    change Fintype.card (Fin (ℓ₀ + 1) × (Fin k → Bool)) = (ℓ₀ + 1) * 2 ^ k
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have hpow : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
  have hℓ₀ : ℓ₀ ≤ ℓ := by
    rw [hℓ_eq]
    nlinarith
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓ_eq]
    nlinarith
  refine ⟨ℓ, code, hℓ₀, hℓ1, ?_⟩
  let σ (i : Fin k) : Fin ℓ ≃ Fin ℓ := e.trans ((alphaFlip i).trans e.symm)
  have hσ_self : ∀ (i : Fin k) (j : Fin ℓ), code i (σ i j) = !(code i j) := by
    intro i j
    have h1 : e (σ i j) = alphaFlip i (e j) := e.apply_symm_apply _
    change (e (σ i j)).2 i = !(e j).2 i
    rw [h1]
    simp [alphaFlip]
  have hσ_other : ∀ (i i' : Fin k) (j : Fin ℓ), i ≠ i' → code i' (σ i j) = code i' j := by
    intro i i' j hii'
    have h1 : e (σ i j) = alphaFlip i (e j) := e.apply_symm_apply _
    change (e (σ i j)).2 i' = (e j).2 i'
    rw [h1]
    simp [alphaFlip, hii'.symm]
  constructor
  · intro i
    exact card_filter_bool_of_involution (code i) (σ i) (hσ_self i)
  · intro i i' hii'
    have hxor := card_filter_bool_of_involution (fun j => xor (code i j) (code i' j)) (σ i) (by
      intro j
      rw [hσ_self i j, hσ_other i i' j hii']
      cases code i j <;> cases code i' j <;> rfl)
    have hham : (Finset.univ.filter (fun j => xor (code i j) (code i' j) = true)).card =
        hammingDist (code i) (code i') := by
      change (Finset.univ.filter (fun j => xor (code i j) (code i' j) = true)).card =
        (Finset.univ.filter (fun j => code i j ≠ code i' j)).card
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      cases code i j <;> cases code i' j <;> decide
    rw [hham] at hxor
    omega
