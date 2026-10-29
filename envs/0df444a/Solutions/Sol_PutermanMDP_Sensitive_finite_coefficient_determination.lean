-- Prove2me | solution 1 for PutermanMDP.Sensitive.finite_coefficient_determination
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T04:32:09.148997+00:00
-- url     : https://prove2.me/submissions/bfee94b0-ceba-42c6-bbf9-7cb0b74aedff

import Mathlib
import Definitions.Def_PutermanMDP_Sensitive_Coefficients

open PutermanMDP.Sensitive
open Filter Topology

noncomputable def s225mbPM : Model (Fin 2) (Fin 2) where
  admissible := fun _ => Finset.univ
  admissible_nonempty := fun _ => Finset.univ_nonempty
  reward := fun _ a => if a = 0 then 1 else 0
  trans := fun s a t => if a = 0 then (if t = s then 1 else 0) else (if t = 1 then 1 else 0)
  trans_nonneg := by intro s a j; split_ifs <;> norm_num
  trans_sum := by
    intro s a
    fin_cases s <;> fin_cases a <;> simp [Fin.sum_univ_two]

def s225mbRd : DecisionRule s225mbPM := ⟨fun _ => 0, fun _ => Finset.mem_univ _⟩
def s225mbRδ : DecisionRule s225mbPM := ⟨fun s => if s = 0 then 1 else 0, fun _ => Finset.mem_univ _⟩

lemma s225mb_Pd : policyMatrix s225mbRd = 1 := by
  ext s t
  fin_cases s <;> fin_cases t <;> simp [policyMatrix, s225mbRd, s225mbPM]

def s225mbPδ : Matrix (Fin 2) (Fin 2) ℝ := fun _ t => if t = 1 then 1 else 0

lemma s225mb_Pδ : policyMatrix s225mbRδ = s225mbPδ := by
  ext s t
  fin_cases s <;> fin_cases t <;> simp [policyMatrix, s225mbRδ, s225mbPM, s225mbPδ]

lemma s225mb_Pδ_sq : s225mbPδ * s225mbPδ = s225mbPδ := by
  ext s t
  fin_cases s <;> fin_cases t <;> simp [Matrix.mul_apply, Fin.sum_univ_two, s225mbPδ]

lemma s225mb_Pδ_pow (k : ℕ) : s225mbPδ ^ (k + 1) = s225mbPδ := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, s225mb_Pδ_sq]

lemma s225mb_lim_one : BlackwellDiscreteDP.NearOne.limitMatrix (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
  unfold BlackwellDiscreteDP.NearOne.limitMatrix
  have : BlackwellDiscreteDP.NearOne.cesaroMean (1 : Matrix (Fin 2) (Fin 2) ℝ) = fun _ => 1 := by
    funext N
    unfold BlackwellDiscreteDP.NearOne.cesaroMean
    simp only [one_pow, Finset.sum_const, Finset.card_range, smul_smul]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    have : ((N : ℝ) + 1)⁻¹ * ((N + 1 : ℕ) : ℝ) = 1 := by
      push_cast; field_simp
    rw [this, one_smul]
  rw [this]
  exact tendsto_const_nhds.limUnder_eq

lemma s225mb_lim_Pδ : BlackwellDiscreteDP.NearOne.limitMatrix s225mbPδ = s225mbPδ := by
  unfold BlackwellDiscreteDP.NearOne.limitMatrix
  have hc : BlackwellDiscreteDP.NearOne.cesaroMean s225mbPδ =
      fun N : ℕ => s225mbPδ + (1 / ((N : ℝ) + 1)) • (1 - s225mbPδ) := by
    funext N
    unfold BlackwellDiscreteDP.NearOne.cesaroMean
    rw [Finset.sum_range_succ']
    have : ∑ k ∈ Finset.range N, s225mbPδ ^ (k + 1) = N • s225mbPδ := by
      simp [s225mb_Pδ_pow]
    rw [this, pow_zero, ← Nat.cast_smul_eq_nsmul ℝ, smul_add, smul_smul, smul_sub]
    have h1 : ((N : ℝ) + 1)⁻¹ * N = 1 - 1 / ((N : ℝ) + 1) := by
      field_simp; ring
    rw [h1, sub_smul, one_smul, one_div]
    abel
  rw [hc]
  apply Tendsto.limUnder_eq
  have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const (1 - s225mbPδ)
  rw [zero_smul] at this
  simpa using (tendsto_const_nhds (x := s225mbPδ)).add this

lemma s225mb_rc : recurrentCount (1 : Matrix (Fin 2) (Fin 2) ℝ) = 2 := by
  unfold recurrentCount
  have : {C : Finset (Fin 2) | RecurrentClass (1 : Matrix (Fin 2) (Fin 2) ℝ) C} =
      {{0}, {1}} := by
    ext C
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨x, hx⟩, -, hcomm⟩
      have hC : C = {x} := by
        ext y
        simp only [Finset.mem_singleton]
        constructor
        · intro hy
          obtain ⟨n, hn⟩ := hcomm y hy x hx
          rw [one_pow, Matrix.one_apply] at hn
          by_contra hne
          rw [if_neg hne] at hn
          exact lt_irrefl _ hn
        · rintro rfl; exact hx
      subst hC
      fin_cases x <;> simp
    · have key : ∀ x : Fin 2, RecurrentClass (1 : Matrix (Fin 2) (Fin 2) ℝ) {x} := by
        intro x
        refine ⟨Finset.singleton_nonempty x, ?_, ?_⟩
        · intro s hs t ht
          rw [Matrix.one_apply] at ht
          split_ifs at ht with h
          · rw [← h]; exact hs
          · exact absurd ht (lt_irrefl _)
        · intro s hs t ht
          rw [Finset.mem_singleton] at hs ht
          refine ⟨0, ?_⟩
          rw [hs, ht, pow_zero, Matrix.one_apply_eq]; norm_num
      rintro (rfl | rfl)
      · exact key 0
      · exact key 1
  rw [this, Set.ncard_pair (by decide)]

theorem solution : ¬ (∀ {S A : Type} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A]
    (M : Model S A) (δ d : DecisionRule M) (r : ℕ)
    (hr : recurrentCount (policyMatrix d) = r)
    (heq : ∀ k ∈ Set.Icc (-1 : ℤ) ((Fintype.card S : ℤ) - (r : ℤ) - 1),
      coefficient δ k = coefficient d k),
    ∀ k : ℤ, -1 ≤ k → coefficient δ k = coefficient d k) := by
  intro h
  have hrd : recurrentCount (policyMatrix s225mbRd) = 2 := by rw [s225mb_Pd, s225mb_rc]
  have hm1 : coefficient s225mbRδ (-1) = coefficient s225mbRd (-1) := by
    unfold coefficient
    rw [if_pos rfl, if_pos rfl, s225mb_Pd, s225mb_Pδ]
    simp only [limitingMatrix]
    rw [s225mb_lim_one, s225mb_lim_Pδ]
    funext s
    fin_cases s <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, s225mbPδ, rewardVector, s225mbRd,
        s225mbRδ, s225mbPM, Matrix.one_apply]
  have h0 := h s225mbPM s225mbRδ s225mbRd 2 hrd (by
    intro k hk
    have : k = -1 := by
      rcases hk with ⟨h1, h2⟩
      simp at h2
      omega
    rw [this]; exact hm1) 0 (by norm_num)
  have h00 := congrFun h0 0
  revert h00
  unfold coefficient
  rw [if_neg (by norm_num), if_neg (by norm_num), s225mb_Pd, s225mb_Pδ]
  simp only [deviationMatrix, BlackwellDiscreteDP.NearOne.deviationMatrix]
  rw [s225mb_lim_one, s225mb_lim_Pδ]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, s225mbPδ, rewardVector, s225mbRd,
    s225mbRδ, s225mbPM]
