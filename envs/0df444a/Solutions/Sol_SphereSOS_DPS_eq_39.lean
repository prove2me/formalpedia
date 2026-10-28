-- Prove2me | solution 1 for SphereSOS.DPS.eq_39
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:34:15.487956+00:00
-- url     : https://prove2.me/submissions/3e422004-303c-4796-b6b1-c385a8c14fae

import Mathlib
import Definitions.Def_SphereSOS_DPS_Setting

open scoped ComplexOrder
open Matrix

open SphereSOS.DPS in
theorem solution {dA dB m : ℕ} (Y : Matrix (Fin dA × (Fin (m + 1) → Fin dB)) (Fin dA × (Fin (m + 1) → Fin dB)) ℂ) (hY : Y.IsHermitian)
    (x : Fin dA → ℂ) (y : Fin dB → ℂ) :
    qf (tensVec 0 x y) (Y - symProj (m + 1) * Y * symProj (m + 1)) = 0 := by
  set v : Fin dA × (Fin (m + 1) → Fin dB) → ℂ := tensVec 0 x y with hvdef
  have hv : ∀ p, v p = x p.1 * ∏ i, y (p.2 i) := by
    intro p
    simp [hvdef, tensVec]
  have hP : ∀ σ : Equiv.Perm (Fin (m + 1)), (permOp (dA := dA) (dB := dB) σ) *ᵥ v = v := by
    intro σ
    funext p
    simp only [mulVec, dotProduct, permOp]
    rw [Finset.sum_eq_single (p.1, p.2 ∘ σ.symm)]
    · have hc : p.1 = (p.1, p.2 ∘ σ.symm).1 ∧ p.2 = (p.1, p.2 ∘ σ.symm).2 ∘ σ := by
        refine ⟨rfl, ?_⟩
        funext i; simp
      rw [if_pos hc, one_mul, hv, hv]
      congr 1
      exact Equiv.prod_comp σ.symm (fun i => y (p.2 i))
    · intro q _ hq
      rw [if_neg, zero_mul]
      rintro ⟨h1, h2⟩
      apply hq
      refine Prod.ext h1.symm ?_
      funext i
      simp [h2]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hP' : ∀ σ : Equiv.Perm (Fin (m + 1)), star v ᵥ* (permOp (dA := dA) (dB := dB) σ) = star v := by
    intro σ
    funext q
    simp only [vecMul, dotProduct, permOp]
    rw [Finset.sum_eq_single (q.1, q.2 ∘ σ)]
    · rw [if_pos ⟨rfl, rfl⟩, mul_one]
      simp only [Pi.star_apply, hv]
      congr 1
      congr 1
      exact Equiv.prod_comp σ (fun i => y (q.2 i))
    · intro p _ hp
      rw [if_neg, mul_zero]
      rintro ⟨h1, h2⟩
      exact hp (Prod.ext h1 h2)
    · intro h; exact absurd (Finset.mem_univ _) h
  have hfac : ((m + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hcard : (Finset.univ : Finset (Equiv.Perm (Fin (m + 1)))).card = (m + 1).factorial := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  have hS : symProj (dA := dA) (dB := dB) (m + 1) *ᵥ v = v := by
    unfold symProj
    rw [smul_mulVec, sum_mulVec]
    simp only [hP, Finset.sum_const, hcard]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hfac, one_smul]
  have hS' : star v ᵥ* symProj (dA := dA) (dB := dB) (m + 1) = star v := by
    unfold symProj
    rw [vecMul_smul, vecMul_sum]
    simp only [hP', Finset.sum_const, hcard]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hfac, one_smul]
  unfold qf
  rw [sub_mulVec, dotProduct_sub, ← mulVec_mulVec, ← mulVec_mulVec, hS,
    dotProduct_mulVec (star v) (symProj (dA := dA) (dB := dB) (m + 1)), hS',
    sub_self]
