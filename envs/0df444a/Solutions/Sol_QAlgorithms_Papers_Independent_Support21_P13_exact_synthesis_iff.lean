-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P13.exact_synthesis_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T21:04:59.407236+00:00
-- url     : https://prove2.me/submissions/0a927a67-5256-4cf1-9a11-ac693d2b7f13

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P13
import Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P13_state_preparation
import Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P13_state_unitary_reduction

noncomputable section

namespace X4P13G

open QAlgorithms.Papers.Independent.Support21.P13
open scoped Classical

local notation "s2" => ((Real.sqrt 2 : ℝ) : ℂ)

lemma s2inv_syn : s2⁻¹ ∈ synthesisRing := Subring.subset_closure (by simp)
lemma I_syn : Complex.I ∈ synthesisRing := Subring.subset_closure (by simp)

lemma om_syn : QAlgorithms.gateT true true ∈ synthesisRing := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hne : s2 ≠ 0 := by
    have : Real.sqrt 2 ≠ 0 := by positivity
    exact_mod_cast this
  have h : Complex.I * Real.pi / 4 = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have : QAlgorithms.gateT true true = (1 + Complex.I) * s2⁻¹ := by
    simp only [QAlgorithms.gateT, Matrix.diagonal_apply_eq, if_true]
    rw [h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_four, Real.sin_pi_div_four]
    field_simp
    apply Complex.ext <;> simp <;> nlinarith [hs]
  rw [this]; exact mul_mem (add_mem (one_mem _) I_syn) s2inv_syn

lemma letter_ring (l : HTLetter) : EntriesInRing (htMatrix l) := by
  intro a b
  cases l
  · simp only [htMatrix, QAlgorithms.hadamard, Matrix.of_apply]
    split_ifs
    · exact neg_mem (by simpa using s2inv_syn)
    · simpa using s2inv_syn
  · simp only [htMatrix, QAlgorithms.gateT, Matrix.diagonal_apply]
    split_ifs <;> first | exact zero_mem _ | exact one_mem _ | exact om_syn

lemma word_ring (c : List HTLetter) : EntriesInRing (htWordMatrix c) := by
  induction c using List.reverseRecOn with
  | nil => intro a b; simp only [htWordMatrix, List.map_nil, List.reverse_nil, List.prod_nil]
           by_cases h : a = b <;> simp [Matrix.one_apply, h]
  | append_singleton c l ih =>
    intro a b
    have : htWordMatrix (c ++ [l]) = htMatrix l * htWordMatrix c := by simp [htWordMatrix]
    rw [this, Matrix.mul_apply, Fintype.sum_bool]
    exact add_mem (mul_mem (letter_ring l _ _) (ih _ _)) (mul_mem (letter_ring l _ _) (ih _ _))

end X4P13G

open QAlgorithms.Papers.Independent.Support21.P13 in
open scoped Classical in
theorem solution (U : Matrix Bool Bool ℂ)
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ) :
    EntriesInRing U ↔ ∃ c : List HTLetter, htWordMatrix c = U := by
  constructor
  · intro hring
    let psi : EuclideanSpace ℂ Bool := WithLp.toLp 2 (fun b => U b false)
    have hst : QAlgorithms.IsState psi := by
      unfold QAlgorithms.IsState
      rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
      have h1 := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1 hU) false) false
      rw [Matrix.mul_apply, Fintype.sum_bool, Matrix.star_apply, Matrix.star_apply,
        Matrix.one_apply_eq] at h1
      have h1' : ((Complex.normSq (U true false) + Complex.normSq (U false false) : ℝ) : ℂ) = 1 := by
        push_cast; rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]; exact h1
      have h2 : Complex.normSq (U true false) + Complex.normSq (U false false) = 1 := by
        exact_mod_cast h1'
      rw [Fintype.sum_bool, Complex.sq_norm, Complex.sq_norm]
      exact h2
    obtain ⟨c, hc⟩ := state_preparation psi hst (fun b => hring b false)
    have hcol : ∀ b, htWordMatrix c b false = U b false := by
      intro b
      have := congrArg (fun v : EuclideanSpace ℂ Bool => v b) hc
      cases b <;> simpa [QAlgorithms.act, QAlgorithms.ket, Matrix.mulVec, dotProduct,
        Fintype.sum_bool, psi] using this
    obtain ⟨k, kp, -, -, h⟩ := state_unitary_reduction U hU hring c hcol
    exact ⟨_, h.1⟩
  · rintro ⟨c, rfl⟩
    exact X4P13G.word_ring c
