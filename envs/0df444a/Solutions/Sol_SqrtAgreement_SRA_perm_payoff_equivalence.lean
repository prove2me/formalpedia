-- Prove2me | solution 1 for SqrtAgreement.SRA.perm_payoff_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:32:47.95152+00:00
-- url     : https://prove2.me/submissions/2714e6d7-8988-408f-993e-75936315a67f

import Mathlib
import Definitions.Def_SqrtAgreement_SRA_Model

set_option autoImplicit false

open Finset SqrtAgreement.SRA

namespace SqrtAgreement.SRA.PermProof

def unpermProfile {N M k : ℕ} (σ : Equiv.Perm (Fin k)) (Q : Profile N M k) : Profile N M k :=
  fun i j a b => Q i j a (σ b)

theorem fbar_comp_perm {N M k : ℕ} (S : Setting N M) (σ : Equiv.Perm (Fin k))
    (r : Reports N M k) (j : Fin M) (y : Fin k) :
    fbar S (fun i j' => σ (r i j')) j (σ y) = fbar S r j y := by
  unfold fbar
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  simp [σ.injective.eq_iff]

theorem e_comp_perm {N M k : ℕ} (K : ℝ) (S : Setting N M) (σ : Equiv.Perm (Fin k))
    (r : Reports N M k) (j : Fin M) (y : Fin k) :
    e K S (fun i j' => σ (r i j')) j (σ y) = e K S r j y := by
  unfold e
  rw [fbar_comp_perm]

theorem tau_comp_perm {N M k : ℕ} (K : ℝ) (S : Setting N M) (σ : Equiv.Perm (Fin k))
    (r : Reports N M k) (j : Fin M) :
    tau K S (fun i j' => σ (r i j')) j = tau K S r j := by
  unfold tau
  apply Finset.sum_congr rfl
  intro i _
  simp [σ.injective.eq_iff, e_comp_perm]

theorem expPay_unperm {m k N M : ℕ} (G : GenModel m k) (K : ℝ) (S : Setting N M)
    (σ : Equiv.Perm (Fin k)) (Q : Profile N M k) (j : Fin M) :
    expPay G K S Q j = expPay G K S (unpermProfile σ Q) j := by
  unfold expPay
  apply Finset.sum_congr rfl; intro x _
  apply Finset.sum_congr rfl; intro y _
  let φ : Reports N M k ≃ Reports N M k :=
    { toFun := fun r i j' => σ (r i j')
      invFun := fun r i j' => σ.symm (r i j')
      left_inv := fun r => by ext i j'; simp
      right_inv := fun r => by ext i j'; simp }
  rw [← Equiv.sum_comp φ]
  apply Finset.sum_congr rfl; intro r _
  simp only [φ, Equiv.coe_fn_mk, tau_comp_perm]
  rfl

theorem unperm_symm_perm (N M : ℕ) {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    unpermProfile σ (SqrtAgreement.SRA.symm (permStrat σ) : Profile N M k) =
      SqrtAgreement.SRA.symm (truthful k) := by
  ext i j a b
  simp [unpermProfile, SqrtAgreement.SRA.symm, permStrat, truthful, σ.injective.eq_iff]

theorem isDeviation_unperm {N M k : ℕ} (S : Setting N M) (σ : Equiv.Perm (Fin k))
    (Q' : Profile N M k) (j : Fin M)
    (hQ' : IsDeviation S (symm (permStrat σ)) Q' j) :
    IsDeviation S (symm (truthful k)) (unpermProfile σ Q') j := by
  obtain ⟨hstoch, hother, hnotask⟩ := hQ'
  refine ⟨?_, ?_, ?_⟩
  · intro i j'
    refine ⟨fun a b => (hstoch i j').1 a (σ b), fun a => ?_⟩
    simp only [unpermProfile]
    rw [Equiv.sum_comp σ (fun b => Q' i j' a b)]
    exact (hstoch i j').2 a
  · intro i j' hj'
    ext a b
    have h := congr_fun (congr_fun (hother i j' hj') a) (σ b)
    simpa [unpermProfile, symm, permStrat, truthful, σ.injective.eq_iff] using h
  · intro i hi
    ext a b
    have h := congr_fun (congr_fun (hnotask i hi) a) (σ b)
    simpa [unpermProfile, symm, permStrat, truthful, σ.injective.eq_iff] using h

end SqrtAgreement.SRA.PermProof

open SqrtAgreement.SRA.PermProof in
theorem solution {m k N M : ℕ} (G : GenModel m k) (K : ℝ) (S : Setting N M)
    (σ : Equiv.Perm (Fin k)) :
    (IsBNE G K S (symm (truthful k)) → IsBNE G K S (symm (permStrat σ))) ∧
    (IsStrictBNE G K S (symm (truthful k)) → IsStrictBNE G K S (symm (permStrat σ))) ∧
    ∀ j : Fin M,
      expPay G K S (symm (permStrat σ)) j = expPay G K S (symm (truthful k)) j := by
  have heq_symm : ∀ j : Fin M,
      expPay G K S (SqrtAgreement.SRA.symm (permStrat σ)) j =
        expPay G K S (SqrtAgreement.SRA.symm (truthful k)) j := by
    intro j
    rw [expPay_unperm G K S σ (SqrtAgreement.SRA.symm (permStrat σ)) j, unperm_symm_perm N M σ]
  refine ⟨?_, ?_, heq_symm⟩
  · intro hbne j Q' hQ'
    rw [expPay_unperm G K S σ Q' j, heq_symm j]
    exact hbne j (unpermProfile σ Q') (isDeviation_unperm S σ Q' j hQ')
  · intro hsbne j Q' hQ' ⟨i, hi, hne⟩
    rw [expPay_unperm G K S σ Q' j, heq_symm j]
    refine hsbne j (unpermProfile σ Q') (isDeviation_unperm S σ Q' j hQ') ⟨i, hi, ?_⟩
    intro heq
    apply hne
    ext a b
    have h := congr_fun (congr_fun heq a) (σ.symm b)
    simpa [unpermProfile, SqrtAgreement.SRA.symm, truthful, permStrat, Equiv.symm_apply_eq] using h
