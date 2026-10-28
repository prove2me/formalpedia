-- Prove2me | solution 1 for PersonalizedAssortment.IB.revenue_eq_expected_sales
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T10:39:25.363992+00:00
-- url     : https://prove2.me/submissions/69bf3f96-e23f-4314-928d-8daf5813ae90

import Mathlib.Algebra.BigOperators.Intervals
import Definitions.Def_PersonalizedAssortment_IB_InventoryBalancing
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
open scoped BigOperators
open Finset PersonalizedAssortment.IB
attribute [local instance] Classical.propDecidable Classical.decEq

namespace D26Inv
variable {n T : ℕ} {Z : Type*}

lemma step_sub (φ : ChoiceModel n) (S : Finset (Fin n)) (I : Fin n → ℕ)
    (f g : (Fin n → ℕ) → ℝ) :
    stepExpect φ S I (fun J => f J-g J) = stepExpect φ S I f-stepExpect φ S I g := by
  simp only [stepExpect,mul_sub,sum_sub_distrib]
  ring

lemma step_const (φ : ChoiceModel n) (S : Finset (Fin n)) (I : Fin n → ℕ) (a : ℝ) :
    stepExpect φ S I (fun _ => a) = a := by
  simp only [stepExpect,← sum_mul]
  ring

lemma expect_sub (φ : Z → ChoiceModel n) (z : Fin T → Z)
    (sel : Fin T → (Fin n → ℕ) → Finset (Fin n)) (c : Fin n → ℕ)
    (t : ℕ) (ht : t ≤ T) (f g : (Fin n → ℕ) → ℝ) :
    expectInv φ z sel c t ht (fun I => f I-g I) =
      expectInv φ z sel c t ht f-expectInv φ z sel c t ht g := by
  induction t generalizing f g with
  | zero => rfl
  | succ t ih =>
      simp only [expectInv]
      have heq : (fun I => stepExpect (φ (z ⟨t,ht⟩)) (sel ⟨t,ht⟩ I) I (fun J => f J-g J)) =
          fun I => stepExpect (φ (z ⟨t,ht⟩)) (sel ⟨t,ht⟩ I) I f -
            stepExpect (φ (z ⟨t,ht⟩)) (sel ⟨t,ht⟩ I) I g :=
        funext (fun I => step_sub _ _ _ _ _)
      rw [heq]
      exact ih _ _ _

lemma expect_const (φ : Z → ChoiceModel n) (z : Fin T → Z)
    (sel : Fin T → (Fin n → ℕ) → Finset (Fin n)) (c : Fin n → ℕ)
    (t : ℕ) (ht : t ≤ T) (a : ℝ) : expectInv φ z sel c t ht (fun _ => a) = a := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [expectInv]
      have heq : (fun I => stepExpect (φ (z ⟨t,ht⟩)) (sel ⟨t,ht⟩ I) I (fun _ => a)) =
          fun _ => a := funext (fun I => step_const _ _ _ _)
      rw [heq]
      exact ih _

lemma update_le (c I : Fin n → ℕ) (hI : ∀ i, I i ≤ c i) (i j : Fin n) :
    Function.update I i (I i-1) j ≤ c j := by
  by_cases hji : j=i
  · subst j; simpa using (Nat.sub_le (I i) 1).trans (hI i)
  · simpa [Function.update_of_ne hji] using hI j

lemma expect_congr_le (φ : Z → ChoiceModel n) (z : Fin T → Z)
    (sel : Fin T → (Fin n → ℕ) → Finset (Fin n)) (c : Fin n → ℕ)
    (t : ℕ) (ht : t ≤ T) (f g : (Fin n → ℕ) → ℝ)
    (hfg : ∀ I, (∀ i, I i ≤ c i) → f I=g I) :
    expectInv φ z sel c t ht f = expectInv φ z sel c t ht g := by
  induction t generalizing f g with
  | zero => exact hfg c (fun i => le_rfl)
  | succ t ih =>
      apply ih (Nat.le_of_succ_le ht)
      intro I hI
      simp only [stepExpect]
      rw [hfg I hI]
      congr 1
      apply sum_congr rfl
      intro i _
      rw [hfg _ (update_le c I hI i)]

lemma telescoping (φ : Z → ChoiceModel n) (z : Fin T → Z)
    (sel : Fin T → (Fin n → ℕ) → Finset (Fin n)) (c : Fin n → ℕ)
    (f : (Fin n → ℕ) → ℝ) (reward : Fin T → (Fin n → ℕ) → ℝ)
    (hstep : ∀ t : Fin T, ∀ I, (∀ i,I i ≤ c i) →
      stepExpect (φ (z t)) (sel t I) I f = f I-reward t I) :
    ∑ t : Fin T, expectInv φ z sel c t.val t.isLt.le (reward t) =
      f c-expectInv φ z sel c T le_rfl f := by
  let a : ℕ → ℝ := fun t => if h : t < T then expectInv φ z sel c t h.le (reward ⟨t,h⟩) else 0
  have hprefix : ∀ N (hN : N ≤ T), ∑ t ∈ range N, a t =
      f c-expectInv φ z sel c N hN f := by
    intro N
    induction N with
    | zero => intro hN; simp [expectInv]
    | succ N ih =>
        intro hN
        have hNT : N < T := Nat.lt_of_succ_le hN
        have hE : expectInv φ z sel c (N+1) hN f =
            expectInv φ z sel c N hNT.le f-
              expectInv φ z sel c N hNT.le (reward ⟨N,hNT⟩) := by
          change expectInv φ z sel c N _ (fun I => stepExpect _ _ I f) = _
          rw [expect_congr_le φ z sel c N hNT.le _ (fun I => f I-reward ⟨N,hNT⟩ I)
            (fun I hI => hstep ⟨N,hNT⟩ I hI), expect_sub]
        rw [sum_range_succ,ih hNT.le]
        simp only [a,dif_pos hNT]
        rw [hE]
        ring
  have hsum : (∑ t : Fin T, expectInv φ z sel c t.val t.isLt.le (reward t)) =
      ∑ t ∈ range T, a t := by
    have : (∑ t : Fin T, a t.val) = ∑ t ∈ range T, a t := Fin.sum_univ_eq_sum_range a T
    simpa [a] using this
  rw [hsum]
  exact hprefix T le_rfl

lemma sum_update_diff (r : Fin n → ℝ) (g : Fin n → ℕ → ℝ) (I : Fin n → ℕ) (i : Fin n) :
    (∑ j, r j * g j (I j)) -
      (∑ j, r j * g j (Function.update I i (I i-1) j)) =
      r i * (g i (I i)-g i (I i-1)) := by
  classical
  rw [← sum_sub_distrib]
  calc
    ∑ j, (r j*g j (I j)-r j*g j (Function.update I i (I i-1) j)) =
        ∑ j : Fin n, if j=i then r i*(g i (I i)-g i (I i-1)) else 0 := by
      apply sum_congr rfl
      intro j _
      by_cases hji : j=i
      · subst j; simp; ring
      · simp [hji,Function.update_of_ne hji]
    _ = _ := by simp

lemma potential_step (φ : ChoiceModel n) (S : Finset (Fin n)) (I : Fin n → ℕ)
    (r : Fin n → ℝ) (g : Fin n → ℕ → ℝ) :
    stepExpect φ S I (fun J => ∑ j,r j*g j (J j)) =
      (∑ j,r j*g j (I j)) - ∑ i ∈ S,φ.prob S i * (r i*(g i (I i)-g i (I i-1))) := by
  have hdiff (i : Fin n) := sum_update_diff r g I i
  unfold stepExpect
  calc
    (1-∑ i ∈ S,φ.prob S i)*(∑ j,r j*g j (I j)) +
        ∑ i ∈ S,φ.prob S i*(∑ j,r j*g j (Function.update I i (I i-1) j)) =
      (1-∑ i ∈ S,φ.prob S i)*(∑ j,r j*g j (I j)) +
        ∑ i ∈ S,φ.prob S i*((∑ j,r j*g j (I j))-r i*(g i (I i)-g i (I i-1))) := by
      congr 1
      apply sum_congr rfl; intro i _
      rw [← hdiff i]
      ring
    _ = _ := by simp only [mul_sub,sum_sub_distrib,← sum_mul]; ring

end D26Inv





theorem solution {n : ℕ} {Z : Type*} (r : Fin n → ℝ) (c : Fin n → ℕ)
    (φ : Z → ChoiceModel n) {T : ℕ} (z : Fin T → Z)
    (sel : Fin T → (Fin n → ℕ) → Finset (Fin n)) :
    ibRevenue r c φ z sel =
      expectInv φ z sel c T le_rfl (fun I => ∑ i : Fin n, r i * ((c i : ℝ) - (I i : ℝ))) := by
  classical
  let g : Fin n → ℕ → ℝ := fun _ k => (k:ℝ)
  let f : (Fin n → ℕ) → ℝ := fun I => ∑ i,r i*g i (I i)
  let reward : Fin T → (Fin n → ℕ) → ℝ := fun t I =>
    ∑ i,r i*(φ (z t)).prob (sel t I) i*(if 0<I i then 1 else 0)
  have hdiff (I : Fin n → ℕ) (i : Fin n) :
      g i (I i)-g i (I i-1) = if 0<I i then 1 else 0 := by
    cases h : I i with
    | zero => simp [g,h]
    | succ k => simp [g,h]
  have hreward (t : Fin T) (I : Fin n → ℕ) : reward t I =
      ∑ i ∈ sel t I,(φ (z t)).prob (sel t I) i*(r i*(g i (I i)-g i (I i-1))) := by
    dsimp only [reward]
    calc
      _ = ∑ i ∈ sel t I,r i*(φ (z t)).prob (sel t I) i*(if 0<I i then 1 else 0) := by
        symm
        apply sum_subset (subset_univ (sel t I))
        intro i _ hi
        rw [(φ (z t)).prob_eq_zero_of_not_mem _ _ hi,mul_zero,zero_mul]
      _ = _ := by apply sum_congr rfl; intro i _; rw [hdiff]; ring
  have hstep : ∀ t : Fin T, ∀ I, (∀ i,I i ≤ c i) →
      stepExpect (φ (z t)) (sel t I) I f = f I-reward t I := by
    intro t I hI
    dsimp only [f]
    rw [D26Inv.potential_step,← hreward]
  have ht := D26Inv.telescoping φ z sel c f reward hstep
  change (∑ t : Fin T,expectInv φ z sel c t.val t.isLt.le (reward t)) = _
  rw [ht]
  have hsales : (fun I : Fin n → ℕ => ∑ i,r i*((c i:ℝ)-(I i:ℝ))) =
      fun I => f c-f I := by
    funext I
    simp only [f,g,mul_sub,sum_sub_distrib]
  rw [hsales,D26Inv.expect_sub,D26Inv.expect_const]



#print axioms solution

