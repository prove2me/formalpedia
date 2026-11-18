-- Prove2me | solution 1 for QSampVerif.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-17T15:04:34.723185+00:00
-- url     : https://prove2.me/submissions/65236058-d8a1-4eb2-b1d5-39b670973c9b

import Definitions.Def_QSampVerif_updateCZ


set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace QSampVerif
open QAlgorithms
open scoped Matrix Kronecker

lemma gateT_four : gateT ^ 4 = pauliZ := by
  rw [gateT,Matrix.diagonal_pow]
  change Matrix.diagonal _ = Matrix.diagonal _
  congr 1
  funext b
  cases b
  · simp [pauliZ]
  · change Complex.exp (Complex.I * Real.pi / 4) ^ 4 = -1
    rw [← Complex.exp_nat_mul]
    convert Complex.exp_pi_mul_I using 1 <;> ring

lemma gateT_eight : gateT ^ 8 = 1 := by
  have hZ : pauliZ ^ 2 = 1 := by
    rw [pauliZ,Matrix.diagonal_pow]
    ext a b
    cases a <;> cases b <;> simp
  calc
    gateT ^ 8 = (gateT ^ 4) ^ 2 := by rw [← pow_mul]
    _ = 1 := by rw [gateT_four,hZ]

lemma gateT_add_four (t : ZMod 8) : gateT ^ (t + 4).val = gateT ^ t.val * pauliZ := by
  have hval : (t + 4).val = (t.val + 4) % 8 := by
    simpa only [show (4 : ZMod 8).val = 4 from rfl] using ZMod.val_add t (4 : ZMod 8)
  rw [hval,← pow_eq_pow_mod (t.val + 4) gateT_eight,pow_add,gateT_four]

lemma padXT_add_four (x : ZMod 2) (t : ZMod 8) :
    padXT x (t + 4) = padXT x t * pauliZ := by
  simp only [padXT,gateT_add_four,Matrix.mul_assoc]

theorem pad_update (x₁ x₂ : ZMod 2) (t₁ t₂ : ZMod 8) :
    ∃ ω : ℂ, ‖ω‖ = 1 ∧
      (padXT x₁ t₁ ⊗ₖ padXT x₂ t₂) * controlled pauliZ =
        ω • (controlled pauliZ *
          (padXT (updateCZ x₁ t₁ x₂ t₂).1 (updateCZ x₁ t₁ x₂ t₂).2.1 ⊗ₖ
            padXT (updateCZ x₁ t₁ x₂ t₂).2.2.1 (updateCZ x₁ t₁ x₂ t₂).2.2.2)) := by
  refine ⟨if (x₁ = 1 ∧ x₂ = 1) then -1 else 1,?_,?_⟩
  · split_ifs <;> simp
  · have two_cases (x : ZMod 2) : x=0 ∨ x=1 := by
      have H : x.val=0 ∨ x.val=1 := by have := x.val_lt; omega
      rcases H with H | H
      · left; exact ZMod.val_injective 2 (by simpa using H)
      · right
        apply ZMod.val_injective 2
        change x.val=1
        exact H
    rcases two_cases x₁ with rfl | rfl <;> rcases two_cases x₂ with rfl | rfl
    all_goals
      simp only [updateCZ]
      simp only [ZMod.val_zero,ZMod.val_one,Nat.cast_zero,Nat.cast_one,mul_zero,
        mul_one,add_zero,padXT_add_four]
      ext p q
      rcases p with ⟨a,b⟩
      rcases q with ⟨c,d⟩
      cases a <;> cases b <;> cases c <;> cases d <;>
        simp [padXT,gateT,Matrix.diagonal_pow,controlled,pauliZ,pauliX,
          ZMod.val_one,ZMod.val_zero,
          Matrix.mul_apply,Matrix.kronecker_apply,Fintype.sum_prod_type,Fintype.sum_bool,
          Matrix.one_apply]

end QSampVerif

open QSampVerif
open QAlgorithms
open scoped Matrix
open scoped Kronecker

theorem solution (x₁ x₂ : ZMod 2) (t₁ t₂ : ZMod 8) :
    ∃ ω : ℂ, ‖ω‖ = 1 ∧
      (padXT x₁ t₁ ⊗ₖ padXT x₂ t₂) * controlled pauliZ =
        ω • (controlled pauliZ *
          (padXT (updateCZ x₁ t₁ x₂ t₂).1 (updateCZ x₁ t₁ x₂ t₂).2.1 ⊗ₖ
            padXT (updateCZ x₁ t₁ x₂ t₂).2.2.1 (updateCZ x₁ t₁ x₂ t₂).2.2.2))  := QSampVerif.pad_update x₁ x₂ t₁ t₂
