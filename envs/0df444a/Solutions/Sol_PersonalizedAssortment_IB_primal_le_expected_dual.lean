-- Prove2me | solution 1 for PersonalizedAssortment.IB.primal_le_expected_dual
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T20:03:54.767622+00:00
-- url     : https://prove2.me/submissions/82fcea3c-4325-41ac-92b6-cfcee48491f4

import Definitions.Def_PersonalizedAssortment_IB_ChoiceModel
import Definitions.Def_PersonalizedAssortment_IB_PenaltyFunction
import Definitions.Def_PersonalizedAssortment_IB_PrimalLP
import Definitions.Def_PersonalizedAssortment_IB_InventoryBalancing
import Theorems.Thm_PersonalizedAssortment_IB_expected_dual_value
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open scoped BigOperators
open Finset PersonalizedAssortment.IB

namespace PrimalLeExpectedDual

variable {n T : ℕ} {Z : Type*}

lemma step_add (φ : ChoiceModel n) (S : Finset (Fin n)) (I : Fin n → ℕ)
    (f g : (Fin n → ℕ) → ℝ) :
    stepExpect φ S I (fun J => f J + g J) = stepExpect φ S I f + stepExpect φ S I g := by
  simp only [stepExpect, mul_add, sum_add_distrib]
  ring

lemma step_smul (φ : ChoiceModel n) (S : Finset (Fin n)) (I : Fin n → ℕ)
    (a : ℝ) (f : (Fin n → ℕ) → ℝ) :
    stepExpect φ S I (fun J => a * f J) = a * stepExpect φ S I f := by
  unfold stepExpect
  rw [mul_add, mul_sum]
  congr 1
  · ring
  · apply sum_congr rfl
    intro i _
    ring

lemma step_const (φ : ChoiceModel n) (S : Finset (Fin n)) (I : Fin n → ℕ) (a : ℝ) :
    stepExpect φ S I (fun _ => a) = a := by
  simp only [stepExpect, ← sum_mul]
  ring

lemma update_le (c I : Fin n → ℕ) (hI : ∀ i, I i ≤ c i) (i j : Fin n) :
    Function.update I i (I i - 1) j ≤ c j := by
  by_cases hji : j = i
  · subst j; simpa using (Nat.sub_le (I i) 1).trans (hI i)
  · simpa [Function.update_of_ne hji] using hI j

lemma step_mono_le (φ : ChoiceModel n) (S : Finset (Fin n)) (c I : Fin n → ℕ)
    (hI : ∀ i, I i ≤ c i) (f g : (Fin n → ℕ) → ℝ)
    (hfg : ∀ J, (∀ i, J i ≤ c i) → f J ≤ g J) :
    stepExpect φ S I f ≤ stepExpect φ S I g := by
  unfold stepExpect
  have h1 : 0 ≤ 1 - ∑ i ∈ S, φ.prob S i := sub_nonneg.mpr (φ.sum_prob_le_one S)
  have h2 : (1 - ∑ i ∈ S, φ.prob S i) * f I ≤ (1 - ∑ i ∈ S, φ.prob S i) * g I :=
    mul_le_mul_of_nonneg_left (hfg I hI) h1
  have h3 : ∑ i ∈ S, φ.prob S i * f (Function.update I i (I i - 1)) ≤
      ∑ i ∈ S, φ.prob S i * g (Function.update I i (I i - 1)) := by
    apply sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hfg _ (update_le c I hI i)) (φ.prob_nonneg S i)
  linarith

lemma expect_add (φ : Z → ChoiceModel n) (z : Fin T → Z)
    (sel : Fin T → (Fin n → ℕ) → Finset (Fin n)) (c : Fin n → ℕ)
    (t : ℕ) (ht : t ≤ T) (f g : (Fin n → ℕ) → ℝ) :
    expectInv φ z sel c t ht (fun I => f I + g I) =
      expectInv φ z sel c t ht f + expectInv φ z sel c t ht g := by
  induction t generalizing f g with
  | zero => rfl
  | succ t ih =>
    simp only [expectInv]
    have heq : (fun I => stepExpect (φ (z ⟨t, ht⟩)) (sel ⟨t, ht⟩ I) I (fun J => f J + g J)) =
        fun I => stepExpect (φ (z ⟨t, ht⟩)) (sel ⟨t, ht⟩ I) I f +
          stepExpect (φ (z ⟨t, ht⟩)) (sel ⟨t, ht⟩ I) I g :=
      funext fun I => step_add _ _ _ _ _
    rw [heq]
    exact ih _ _ _

lemma expect_smul (φ : Z → ChoiceModel n) (z : Fin T → Z)
    (sel : Fin T → (Fin n → ℕ) → Finset (Fin n)) (c : Fin n → ℕ)
    (t : ℕ) (ht : t ≤ T) (a : ℝ) (f : (Fin n → ℕ) → ℝ) :
    expectInv φ z sel c t ht (fun I => a * f I) = a * expectInv φ z sel c t ht f := by
  induction t generalizing f with
  | zero => rfl
  | succ t ih =>
    simp only [expectInv]
    have heq : (fun I => stepExpect (φ (z ⟨t, ht⟩)) (sel ⟨t, ht⟩ I) I (fun J => a * f J)) =
        fun I => a * stepExpect (φ (z ⟨t, ht⟩)) (sel ⟨t, ht⟩ I) I f :=
      funext fun I => step_smul _ _ _ _ _
    rw [heq]
    exact ih _ _

lemma expect_const (φ : Z → ChoiceModel n) (z : Fin T → Z)
    (sel : Fin T → (Fin n → ℕ) → Finset (Fin n)) (c : Fin n → ℕ)
    (t : ℕ) (ht : t ≤ T) (a : ℝ) :
    expectInv φ z sel c t ht (fun _ => a) = a := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [expectInv]
    have heq : (fun I => stepExpect (φ (z ⟨t, ht⟩)) (sel ⟨t, ht⟩ I) I (fun _ => a)) =
        fun _ => a := funext fun I => step_const _ _ _ _
    rw [heq]
    exact ih _

lemma expect_sum {α : Type*} (φ : Z → ChoiceModel n) (z : Fin T → Z)
    (sel : Fin T → (Fin n → ℕ) → Finset (Fin n)) (c : Fin n → ℕ)
    (t : ℕ) (ht : t ≤ T) (s : Finset α) (f : α → (Fin n → ℕ) → ℝ) :
    expectInv φ z sel c t ht (fun I => ∑ x ∈ s, f x I) =
      ∑ x ∈ s, expectInv φ z sel c t ht (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using expect_const φ z sel c t ht 0
  | insert a s ha ih =>
    have heq : (fun I => ∑ x ∈ insert a s, f x I) =
        fun I => f a I + ∑ x ∈ s, f x I :=
      funext fun I => Finset.sum_insert ha
    rw [heq, expect_add, ih, Finset.sum_insert ha]

lemma expect_mono_le (φ : Z → ChoiceModel n) (z : Fin T → Z)
    (sel : Fin T → (Fin n → ℕ) → Finset (Fin n)) (c : Fin n → ℕ)
    (t : ℕ) (ht : t ≤ T) (f g : (Fin n → ℕ) → ℝ)
    (hfg : ∀ I, (∀ i, I i ≤ c i) → f I ≤ g I) :
    expectInv φ z sel c t ht f ≤ expectInv φ z sel c t ht g := by
  induction t generalizing f g with
  | zero => exact hfg c fun _ => le_rfl
  | succ t ih =>
    apply ih (Nat.le_of_succ_le ht)
    intro I hI
    exact step_mono_le (φ (z ⟨t, ht⟩)) (sel ⟨t, ht⟩ I) c I hI f g hfg

lemma frac_mem_Icc (c : Fin n → ℕ) (hc : ∀ i, 0 < c i) (I : Fin n → ℕ)
    (hI : ∀ i, I i ≤ c i) (i : Fin n) :
    (I i : ℝ) / (c i : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  have hcpos : (0 : ℝ) < c i := Nat.cast_pos.mpr (hc i)
  exact ⟨div_nonneg (Nat.cast_nonneg _) hcpos.le,
    (div_le_one hcpos).mpr (Nat.cast_le.mpr (hI i))⟩

lemma step_psi_le (φ : ChoiceModel n) (S : Finset (Fin n)) (c : Fin n → ℕ)
    (hc : ∀ i, 0 < c i) (Ψ : ℝ → ℝ) (hΨ : IsPenaltyFunction Ψ)
    (i : Fin n) (I : Fin n → ℕ) (hI : ∀ j, I j ≤ c j) :
    stepExpect φ S I (fun J => Ψ ((J i : ℝ) / (c i : ℝ))) ≤ Ψ ((I i : ℝ) / (c i : ℝ)) := by
  calc stepExpect φ S I (fun J => Ψ ((J i : ℝ) / (c i : ℝ)))
    _ ≤ stepExpect φ S I (fun _ => Ψ ((I i : ℝ) / (c i : ℝ))) := by
      unfold stepExpect
      have h1 : 0 ≤ 1 - ∑ j ∈ S, φ.prob S j := sub_nonneg.mpr (φ.sum_prob_le_one S)
      have h2 : ∑ j ∈ S, φ.prob S j * Ψ ((Function.update I j (I j - 1) i : ℝ) / (c i : ℝ)) ≤
          ∑ j ∈ S, φ.prob S j * Ψ ((I i : ℝ) / (c i : ℝ)) := by
        apply sum_le_sum
        intro j _
        have hle : Function.update I j (I j - 1) i ≤ I i := by
          by_cases hij : i = j
          · subst i; simp
          · simp [Function.update_of_ne hij]
        have hmono := hΨ.2.1
          (frac_mem_Icc c hc _ (update_le c I hI j) i)
          (frac_mem_Icc c hc I hI i)
          (div_le_div_of_nonneg_right (Nat.cast_le.mpr hle) (Nat.cast_nonneg _))
        exact mul_le_mul_of_nonneg_left hmono (φ.prob_nonneg S j)
      linarith
    _ = Ψ ((I i : ℝ) / (c i : ℝ)) := step_const φ S I _

lemma expect_psi_antitone (φ : Z → ChoiceModel n) (z : Fin T → Z)
    (sel : Fin T → (Fin n → ℕ) → Finset (Fin n)) (c : Fin n → ℕ)
    (hc : ∀ i, 0 < c i) (Ψ : ℝ → ℝ) (hΨ : IsPenaltyFunction Ψ)
    (i : Fin n) (k : ℕ) (hk : k ≤ T) (t : ℕ) (htk : t ≤ k) :
    expectInv φ z sel c k hk (fun I => Ψ ((I i : ℝ) / (c i : ℝ))) ≤
      expectInv φ z sel c t (htk.trans hk) (fun I => Ψ ((I i : ℝ) / (c i : ℝ))) := by
  induction k with
  | zero =>
    have ht0 : t = 0 := Nat.eq_zero_of_le_zero htk
    subst t
    exact le_rfl
  | succ k ih =>
    rcases Nat.le_succ_iff.mp htk with htk' | rfl
    · have hk' : k ≤ T := Nat.le_of_succ_le hk
      have hstep : expectInv φ z sel c (k + 1) hk (fun I => Ψ ((I i : ℝ) / (c i : ℝ))) ≤
          expectInv φ z sel c k hk' (fun I => Ψ ((I i : ℝ) / (c i : ℝ))) := by
        simp only [expectInv]
        exact expect_mono_le φ z sel c k hk' _ _ fun I hI =>
          step_psi_le (φ (z ⟨k, hk⟩)) (sel ⟨k, hk⟩ I) c hc Ψ hΨ i I hI
      exact hstep.trans (ih hk' htk')
    · exact le_rfl

end PrimalLeExpectedDual

open PrimalLeExpectedDual

theorem solution {n : ℕ} {Z : Type*} (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (c : Fin n → ℕ) (hc : ∀ i, 0 < c i) (𝒮 : Finset (Finset (Fin n))) (h𝒮 : ∅ ∈ 𝒮)
    (φ : Z → ChoiceModel n) (Ψ : ℝ → ℝ) (hΨ : IsPenaltyFunction Ψ) {T : ℕ} (z : Fin T → Z)
    (sel : Fin T → (Fin n → ℕ) → Finset (Fin n)) (hsel : IsIBRule Ψ r c 𝒮 φ z sel)
    (y : Fin T → Finset (Fin n) → ℝ) (hy : PrimalFeasible c 𝒮 φ z y) :
    primalObj r 𝒮 φ z y ≤
      expectInv φ z sel c T le_rfl (fun I => ∑ i : Fin n, r i *
        (∑ k ∈ Finset.Ioc (I i) (c i), Ψ ((k : ℝ) / (c i : ℝ)) +
          (c i : ℝ) * (1 - Ψ ((I i : ℝ) / (c i : ℝ))))) := by
  let Epsi : Fin n → ℝ := fun i =>
    expectInv φ z sel c T le_rfl (fun I => Ψ ((I i : ℝ) / (c i : ℝ)))
  have hEpsi_le_one : ∀ i : Fin n, Epsi i ≤ 1 := by
    intro i
    calc Epsi i ≤ expectInv φ z sel c T le_rfl (fun _ => (1 : ℝ)) :=
          expect_mono_le φ z sel c T le_rfl _ _ fun I hI =>
            (hΨ.1 (frac_mem_Icc c hc I hI i)).2
      _ = 1 := expect_const φ z sel c T le_rfl 1
  have hpart1 :
      (∑ t : Fin T, ∑ S ∈ 𝒮, ∑ i : Fin n, r i * (φ (z t)).prob S i * y t S * Epsi i) ≤
        expectInv φ z sel c T le_rfl
          (fun I => ∑ i : Fin n, r i * ∑ k ∈ Finset.Ioc (I i) (c i), Ψ ((k : ℝ) / (c i : ℝ))) := by
    rw [← expected_dual_value r c φ Ψ hΨ.2.2.1 z sel]
    apply sum_le_sum
    intro t _
    have hpoint : ∀ I, (∀ i, I i ≤ c i) →
        (∑ S ∈ 𝒮, ∑ i : Fin n,
          (r i * (φ (z t)).prob S i * y t S) * Ψ ((I i : ℝ) / (c i : ℝ))) ≤
          lamIB Ψ r c φ z sel t I := by
      intro I _
      have hS_bound : ∀ S ∈ 𝒮,
          (∑ i : Fin n, (r i * (φ (z t)).prob S i * y t S) * Ψ ((I i : ℝ) / (c i : ℝ))) ≤
            y t S * lamIB Ψ r c φ z sel t I := by
        intro S hS
        have heq1 :
            (∑ i : Fin n, (r i * (φ (z t)).prob S i * y t S) * Ψ ((I i : ℝ) / (c i : ℝ))) =
              y t S * ∑ i : Fin n, Ψ ((I i : ℝ) / (c i : ℝ)) * r i * (φ (z t)).prob S i := by
          rw [mul_sum]
          apply sum_congr rfl
          intro i _
          ring
        have heq2 :
            (∑ i : Fin n, Ψ ((I i : ℝ) / (c i : ℝ)) * r i * (φ (z t)).prob S i) =
              ibIndex Ψ r c (φ (z t)) I S := by
          unfold ibIndex
          symm
          apply sum_subset (subset_univ S)
          intro i _ hi
          rw [(φ (z t)).prob_eq_zero_of_not_mem S i hi, mul_zero]
        rw [heq1, heq2]
        exact mul_le_mul_of_nonneg_left ((hsel t I).2.1 S hS) (hy.1 t S hS)
      calc (∑ S ∈ 𝒮, ∑ i : Fin n,
            (r i * (φ (z t)).prob S i * y t S) * Ψ ((I i : ℝ) / (c i : ℝ)))
        _ ≤ ∑ S ∈ 𝒮, y t S * lamIB Ψ r c φ z sel t I := sum_le_sum hS_bound
        _ = (∑ S ∈ 𝒮, y t S) * lamIB Ψ r c φ z sel t I := (sum_mul _ _ _).symm
        _ = lamIB Ψ r c φ z sel t I := by rw [hy.2.1 t, one_mul]
    have hexp_t := expect_mono_le φ z sel c t.val t.isLt.le _ _ hpoint
    rw [expect_sum] at hexp_t
    have hexp_t' :
        (∑ S ∈ 𝒮, ∑ i : Fin n,
          r i * (φ (z t)).prob S i * y t S *
            expectInv φ z sel c t.val t.isLt.le (fun I => Ψ ((I i : ℝ) / (c i : ℝ)))) ≤
          expectInv φ z sel c t.val t.isLt.le (lamIB Ψ r c φ z sel t) := by
      refine le_trans (le_of_eq ?_) hexp_t
      apply sum_congr rfl
      intro S _
      rw [expect_sum]
      apply sum_congr rfl
      intro i _
      rw [expect_smul]
    refine le_trans ?_ hexp_t'
    apply sum_le_sum
    intro S hS
    apply sum_le_sum
    intro i _
    have hcoeff : 0 ≤ r i * (φ (z t)).prob S i * y t S :=
      mul_nonneg (mul_nonneg (hr i).le ((φ (z t)).prob_nonneg S i)) (hy.1 t S hS)
    exact mul_le_mul_of_nonneg_left
      (expect_psi_antitone φ z sel c hc Ψ hΨ i T le_rfl t.val t.isLt.le) hcoeff
  have hpart2 :
      (∑ t : Fin T, ∑ S ∈ 𝒮, ∑ i : Fin n, r i * (φ (z t)).prob S i * y t S * (1 - Epsi i)) ≤
        expectInv φ z sel c T le_rfl
          (fun I => ∑ i : Fin n, r i * ((c i : ℝ) * (1 - Ψ ((I i : ℝ) / (c i : ℝ))))) := by
    have hswap :
        (∑ t : Fin T, ∑ S ∈ 𝒮, ∑ i : Fin n, r i * (φ (z t)).prob S i * y t S * (1 - Epsi i)) =
          ∑ i : Fin n, (r i * (1 - Epsi i)) * ∑ t : Fin T, ∑ S ∈ 𝒮, (φ (z t)).prob S i * y t S := by
      trans ∑ t : Fin T, ∑ i : Fin n, ∑ S ∈ 𝒮, r i * (φ (z t)).prob S i * y t S * (1 - Epsi i)
      · apply sum_congr rfl
        intro t _
        exact sum_comm
      · trans ∑ i : Fin n, ∑ t : Fin T, ∑ S ∈ 𝒮, r i * (φ (z t)).prob S i * y t S * (1 - Epsi i)
        · exact sum_comm
        · apply sum_congr rfl
          intro i _
          rw [mul_sum]
          apply sum_congr rfl
          intro t _
          rw [mul_sum]
          apply sum_congr rfl
          intro S _
          ring
    have hrhs :
        expectInv φ z sel c T le_rfl
          (fun I => ∑ i : Fin n, r i * ((c i : ℝ) * (1 - Ψ ((I i : ℝ) / (c i : ℝ))))) =
          ∑ i : Fin n, (r i * (1 - Epsi i)) * (c i : ℝ) := by
      rw [expect_sum]
      apply sum_congr rfl
      intro i _
      have heq :
          (fun I : Fin n → ℕ => r i * ((c i : ℝ) * (1 - Ψ ((I i : ℝ) / (c i : ℝ))))) =
            fun I => (r i * (c i : ℝ)) * (1 : ℝ) + (-(r i * (c i : ℝ))) * Ψ ((I i : ℝ) / (c i : ℝ)) := by
        ext I; ring
      rw [heq, expect_add, expect_smul, PrimalLeExpectedDual.expect_const, expect_smul]
      dsimp only [Epsi]
      ring
    rw [hswap, hrhs]
    apply sum_le_sum
    intro i _
    have hcoeff : 0 ≤ r i * (1 - Epsi i) :=
      mul_nonneg (hr i).le (sub_nonneg.mpr (hEpsi_le_one i))
    exact mul_le_mul_of_nonneg_left (hy.2.2 i) hcoeff
  have hsum_lhs :
      primalObj r 𝒮 φ z y =
        (∑ t : Fin T, ∑ S ∈ 𝒮, ∑ i : Fin n, r i * (φ (z t)).prob S i * y t S * Epsi i) +
        (∑ t : Fin T, ∑ S ∈ 𝒮, ∑ i : Fin n, r i * (φ (z t)).prob S i * y t S * (1 - Epsi i)) := by
    unfold primalObj
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro t _
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro S _
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ring
  have hsum_rhs :
      expectInv φ z sel c T le_rfl (fun I => ∑ i : Fin n, r i *
        (∑ k ∈ Finset.Ioc (I i) (c i), Ψ ((k : ℝ) / (c i : ℝ)) +
          (c i : ℝ) * (1 - Ψ ((I i : ℝ) / (c i : ℝ))))) =
        expectInv φ z sel c T le_rfl
          (fun I => ∑ i : Fin n, r i * ∑ k ∈ Finset.Ioc (I i) (c i), Ψ ((k : ℝ) / (c i : ℝ))) +
        expectInv φ z sel c T le_rfl
          (fun I => ∑ i : Fin n, r i * ((c i : ℝ) * (1 - Ψ ((I i : ℝ) / (c i : ℝ))))) := by
    rw [← expect_add]
    congr 1
    ext I
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ring
  linarith
