-- Prove2me | solution 1 for StructEstMDP.FiniteTime.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:03:23.382721+00:00
-- url     : https://prove2.me/submissions/1a327e03-7487-4a68-8233-dcdb9f812fe2

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_StructEstMDP_FiniteTime_Setting

open FoundationsML.ReinforcementLearning MeasureTheory

namespace Aux_StructEstMDP_FiniteTime_lemma_6
open FoundationsML.ReinforcementLearning StructEstMDP.FiniteTime

theorem occ_prob {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (π : S → A → ℝ) (hπ : IsPolicy π)
    (s0 : S) : ∀ t, (∀ s, 0 ≤ OccupationDist π P s0 t s) ∧ ∑ s, OccupationDist π P s0 t s = 1 := by
  have hIT0 : ∀ s s', 0 ≤ InducedTransition π P s s' := fun s s' =>
    Finset.sum_nonneg fun a _ => mul_nonneg ((hπ s).1 a) ((hP s a).1 s')
  have hIT1 : ∀ s, ∑ s', InducedTransition π P s s' = 1 := by
    intro s
    unfold InducedTransition
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, (hP s _).2, mul_one]
    exact (hπ s).2
  intro t
  induction t with
  | zero =>
    refine ⟨fun s => ?_, ?_⟩
    · simp only [OccupationDist]
      split_ifs <;> norm_num
    · simp [OccupationDist]
  | succ t ih =>
    refine ⟨fun s' => ?_, ?_⟩
    · simp only [OccupationDist]
      exact Finset.sum_nonneg fun s _ => mul_nonneg (ih.1 s) (hIT0 s s')
    · simp only [OccupationDist]
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, hIT1, mul_one]
      exact ih.2

theorem pv_diff {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (π : S → A → ℝ) (hπ : IsPolicy π)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (R1 R2 : S → A → ℝ) (B : ℝ)
    (hB : ∀ s, |InducedReward π R1 s - InducedReward π R2 s| ≤ B) (s : S) :
    |PolicyValue π P R1 γ s - PolicyValue π P R2 γ s| ≤ B / (1 - γ) := by
  have hocc := occ_prob P hP π hπ s
  have hgeo := summable_geometric_of_lt_one hγ0 hγ1
  have hbd : ∀ (R : S → A → ℝ) (t : ℕ),
      |∑ s', OccupationDist π P s t s' * InducedReward π R s'| ≤ ∑ s', |InducedReward π R s'| := by
    intro R t
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s' _ => ?_)
    rw [abs_mul, abs_of_nonneg ((hocc t).1 s')]
    have hle : OccupationDist π P s t s' ≤ 1 := by
      rw [← (hocc t).2]
      exact Finset.single_le_sum (f := fun x => OccupationDist π P s t x)
        (fun x _ => (hocc t).1 x) (Finset.mem_univ s')
    exact mul_le_of_le_one_left (abs_nonneg _) hle
  have hsum : ∀ R : S → A → ℝ,
      Summable (fun t : ℕ => γ ^ t * ∑ s', OccupationDist π P s t s' * InducedReward π R s') := by
    intro R
    refine Summable.of_norm_bounded (hgeo.mul_right (∑ s', |InducedReward π R s'|)) fun t => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hγ0 t)]
    exact mul_le_mul_of_nonneg_left (hbd R t) (pow_nonneg hγ0 t)
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB s)
  have hterm : ∀ t : ℕ, |γ ^ t * ∑ s', OccupationDist π P s t s' * InducedReward π R1 s' -
      γ ^ t * ∑ s', OccupationDist π P s t s' * InducedReward π R2 s'| ≤ γ ^ t * B := by
    intro t
    rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg (pow_nonneg hγ0 t)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hγ0 t)
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ s', |OccupationDist π P s t s' * InducedReward π R1 s' -
          OccupationDist π P s t s' * InducedReward π R2 s'|
        ≤ ∑ s', OccupationDist π P s t s' * B := by
          refine Finset.sum_le_sum fun s' _ => ?_
          rw [← mul_sub, abs_mul, abs_of_nonneg ((hocc t).1 s')]
          exact mul_le_mul_of_nonneg_left (hB s') ((hocc t).1 s')
      _ = B := by rw [← Finset.sum_mul, (hocc t).2, one_mul]
  unfold PolicyValue
  rw [← (hsum R1).tsum_sub (hsum R2)]
  have hS := (hsum R1).sub (hsum R2)
  have hG : Summable (fun t : ℕ => γ ^ t * B) := hgeo.mul_right B
  have hval : ∑' t : ℕ, γ ^ t * B = B / (1 - γ) := by
    rw [tsum_mul_right, tsum_geometric_of_lt_one hγ0 hγ1, div_eq_inv_mul]
  rw [abs_le]
  constructor
  · have := hS.neg.tsum_le_tsum (fun t => by have := abs_le.mp (hterm t); linarith) hG
    rw [tsum_neg, hval] at this
    linarith
  · have := hS.tsum_le_tsum (fun t => le_of_abs_le (hterm t)) hG
    rw [hval] at this
    exact this

end Aux_StructEstMDP_FiniteTime_lemma_6

open StructEstMDP.FiniteTime Aux_StructEstMDP_FiniteTime_lemma_6 in
theorem solution {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (γ : ℝ)
    (hP : IsTransitionKernel P) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    {p : ℕ} (r : S → A → EuclideanSpace ℝ (Fin p) → ℝ) (Lr Lg : ℝ)
    (h3 : Assumption3 r Lr Lg)
    (π : S → A → ℝ) (hπ : IsPolicy π) (θ θ' : EuclideanSpace ℝ (Fin p)) (s : S) (a : A) :
    |softQ P γ r θ π s a - softQ P γ r θ' π s a| ≤ Lr / (1 - γ) * ‖θ - θ'‖ := by
  set d := ‖θ - θ'‖ with hd
  have hLr : 0 < Lr := h3.1
  have hLip : ∀ s a, |r s a θ - r s a θ'| ≤ Lr * d := by
    intro s a
    obtain ⟨hdiff, hgb, -⟩ := h3.2.2 s a
    have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := r s a) (s := Set.univ)
      (fun x _ => hdiff x)
      (fun x _ => by rw [← toDual_gradient, LinearIsometryEquiv.norm_map]; exact hgb x)
      convex_univ (Set.mem_univ θ') (Set.mem_univ θ)
    rwa [Real.norm_eq_abs] at this
  have hIR : ∀ s', |InducedReward π (softReward r θ π) s' - InducedReward π (softReward r θ' π) s'|
      ≤ Lr * d := by
    intro s'
    unfold InducedReward softReward
    rw [← Finset.sum_sub_distrib]
    have e : ∀ a', π s' a' * (r s' a' θ + entropy (π s')) - π s' a' * (r s' a' θ' + entropy (π s'))
        = π s' a' * (r s' a' θ - r s' a' θ') := fun a' => by ring
    simp only [e]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ a', |π s' a' * (r s' a' θ - r s' a' θ')| ≤ ∑ a', π s' a' * (Lr * d) := by
          refine Finset.sum_le_sum fun a' _ => ?_
          rw [abs_mul, abs_of_nonneg ((hπ s').1 a')]
          exact mul_le_mul_of_nonneg_left (hLip s' a') ((hπ s').1 a')
      _ = Lr * d := by rw [← Finset.sum_mul, (hπ s').2, one_mul]
  have hV : ∀ s', |softV P γ r θ π s' - softV P γ r θ' π s'| ≤ Lr * d / (1 - γ) := by
    intro s'
    unfold softV
    exact pv_diff P hP π hπ γ hγ0 hγ1 _ _ _ hIR s'
  have hsumV : |∑ s', P s a s' * softV P γ r θ π s' - ∑ s', P s a s' * softV P γ r θ' π s'|
      ≤ Lr * d / (1 - γ) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ s', |P s a s' * softV P γ r θ π s' - P s a s' * softV P γ r θ' π s'|
        ≤ ∑ s', P s a s' * (Lr * d / (1 - γ)) := by
          refine Finset.sum_le_sum fun s' _ => ?_
          rw [← mul_sub, abs_mul, abs_of_nonneg ((hP s a).1 s')]
          exact mul_le_mul_of_nonneg_left (hV s') ((hP s a).1 s')
      _ = Lr * d / (1 - γ) := by rw [← Finset.sum_mul, (hP s a).2, one_mul]
  unfold softQ
  have h1γ : 0 < 1 - γ := by linarith
  have key : |r s a θ + γ * ∑ s', P s a s' * softV P γ r θ π s' -
      (r s a θ' + γ * ∑ s', P s a s' * softV P γ r θ' π s')| ≤ Lr * d + γ * (Lr * d / (1 - γ)) := by
    have e : r s a θ + γ * ∑ s', P s a s' * softV P γ r θ π s' -
        (r s a θ' + γ * ∑ s', P s a s' * softV P γ r θ' π s') =
        (r s a θ - r s a θ') + γ * (∑ s', P s a s' * softV P γ r θ π s' -
          ∑ s', P s a s' * softV P γ r θ' π s') := by ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add (hLip s a) ?_)
    rw [abs_mul, abs_of_nonneg hγ0]
    exact mul_le_mul_of_nonneg_left hsumV hγ0
  have hfin : Lr * d + γ * (Lr * d / (1 - γ)) = Lr / (1 - γ) * d := by
    field_simp <;> ring
  rw [← hfin]
  exact key
