-- Prove2me | solution 1 for OnlineGND.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:09:35.120947+00:00
-- url     : https://prove2.me/submissions/a94e19bf-d88b-4d1c-89d0-18bbcb0a7f1c

import Definitions.Def_OnlineGND_Relaxation
import Definitions.Def_OnlineGND_PowerAlg

namespace Aux_OnlineGND_lemma_3

theorem two_rpow (a b p : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 1 ≤ p) :
    a ^ p + b ^ p ≤ (a + b) ^ p := by
  have hp0 : 0 ≤ p - 1 := by linarith
  have e1 : ∀ t : ℝ, 0 ≤ t → t ^ p = t * t ^ (p - 1) := by
    intro t ht
    have hsplit : t ^ p = t ^ ((1 : ℝ) + (p - 1)) := by
      congr 1; ring
    rw [hsplit, Real.rpow_add' ht (ne_of_gt (by linarith)), Real.rpow_one]
  rw [e1 a ha, e1 b hb, e1 (a + b) (by linarith)]
  have h1 : a ^ (p - 1) ≤ (a + b) ^ (p - 1) := Real.rpow_le_rpow ha (by linarith) hp0
  have h2 : b ^ (p - 1) ≤ (a + b) ^ (p - 1) := Real.rpow_le_rpow hb (by linarith) hp0
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

theorem sum_rpow_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (p : ℝ)
    (hp : 1 ≤ p) : ∑ i ∈ s, f i ^ p ≤ (∑ i ∈ s, f i) ^ p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, Real.zero_rpow (ne_of_gt (by linarith))]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    calc f a ^ p + ∑ i ∈ s, f i ^ p ≤ f a ^ p + (∑ i ∈ s, f i) ^ p := by linarith
      _ ≤ (f a + ∑ i ∈ s, f i) ^ p :=
          two_rpow _ _ _ (hf a) (Finset.sum_nonneg (fun i _ => hf i)) hp

end Aux_OnlineGND_lemma_3

open OnlineGND in
theorem solution {E : Type*} [Fintype E] [DecidableEq E] {N : ℕ} (c α : E → ℝ)
    (hc : ∀ e, 0 ≤ c e) (hα : ∀ e, 1 ≤ α e) (S : Finset E) (reqs : Fin N → Request E)
    (hw : ∀ i e, 1 ≤ (reqs i).w e) (sol : Fin N → Finset E) (hsol : IsReplyProfile reqs sol) :
    ∃ x : Fin N → Finset E → ℝ, IsPrimalFeasible reqs x ∧
      relaxObj c α S reqs x ≤
        (1 + alphaMax α * Real.exp (-alphaMax α)) * powerCost c α (load reqs sol) := by
  obtain ⟨X, hX⟩ : ∃ X : Fin N → Finset E → ℝ, X = fun i p => if p = sol i then 1 else 0 :=
    ⟨_, rfl⟩
  have hXip : ∀ i p, X i p = if p = sol i then 1 else 0 := fun i p => by rw [hX]
  have hsol' : ∀ i, sol i ∈ (reqs i).replies := hsol
  have hind : ∀ i e, ∑ p ∈ (reqs i).replies.filter (fun p => e ∈ p), X i p =
      if e ∈ sol i then 1 else 0 := by
    intro i e
    simp only [hXip]
    rw [Finset.sum_ite_eq']
    by_cases he : e ∈ sol i
    · rw [if_pos (Finset.mem_filter.mpr ⟨hsol' i, he⟩), if_pos he]
    · rw [if_neg (show sol i ∉ (reqs i).replies.filter (fun p => e ∈ p) from
        fun h => he (Finset.mem_filter.mp h).2), if_neg he]
  have hfl : ∀ e, fracLoad reqs X e = load reqs sol e := by
    intro e
    unfold fracLoad load
    apply Finset.sum_congr rfl
    intro i _
    rw [hind i e]
    split_ifs <;> ring
  obtain ⟨M, hM⟩ : ∃ M, M = alphaMax α := ⟨_, rfl⟩
  have haM : ∀ e, α e ≤ M := by
    intro e
    rw [hM]
    unfold alphaMax
    rw [Finset.le_fold_max]
    exact Or.inr ⟨e, Finset.mem_univ _, le_rfl⟩
  have hM1 : 1 ≤ M := by
    rw [hM]
    unfold alphaMax
    rw [Finset.le_fold_max]
    exact Or.inl le_rfl
  have hα0 : ∀ e, α e ≠ 0 := fun e => ne_of_gt (lt_of_lt_of_le one_pos (hα e))
  have hext : ∀ e, ∑ i, (reqs i).w e ^ α e *
      ∑ p ∈ (reqs i).replies.filter (fun p => e ∈ p), X i p =
      ∑ i, (if e ∈ sol i then (reqs i).w e else 0) ^ α e := by
    intro e
    apply Finset.sum_congr rfl
    intro i _
    rw [hind i e]
    by_cases he : e ∈ sol i
    · rw [if_pos he, if_pos he, mul_one]
    · rw [if_neg he, if_neg he, mul_zero, Real.zero_rpow (hα0 e)]
  have hsup : ∀ e, ∑ i, (if e ∈ sol i then (reqs i).w e else 0) ^ α e ≤
      load reqs sol e ^ α e := by
    intro e
    unfold load
    exact Aux_OnlineGND_lemma_3.sum_rpow_le Finset.univ
      (fun i => if e ∈ sol i then (reqs i).w e else 0)
      (fun i => by
        show 0 ≤ (if e ∈ sol i then (reqs i).w e else 0)
        split_ifs
        · linarith [hw i e]
        · exact le_rfl) (α e) (hα e)
  have hTnn : ∀ e, 0 ≤ ∑ i, (if e ∈ sol i then (reqs i).w e else 0) ^ α e := by
    intro e
    apply Finset.sum_nonneg
    intro i _
    apply Real.rpow_nonneg
    split_ifs
    · linarith [hw i e]
    · exact le_rfl
  have hexpM : 0 < Real.exp M := Real.exp_pos M
  have hcoef : ∀ e, c e * α e / Real.exp M ≤ M * Real.exp (-M) * c e := by
    intro e
    rw [Real.exp_neg, div_eq_mul_inv]
    have hinv : 0 < (Real.exp M)⁻¹ := inv_pos.mpr hexpM
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr (haM e)) (hc e)) hinv.le]
  have hcoef0 : ∀ e, 0 ≤ c e * α e / Real.exp M := fun e =>
    div_nonneg (mul_nonneg (hc e) (by linarith [hα e])) hexpM.le
  have hK : 0 ≤ M * Real.exp (-M) := mul_nonneg (by linarith) (Real.exp_pos _).le
  have hlnn : ∀ e, 0 ≤ c e * load reqs sol e ^ α e := by
    intro e
    apply mul_nonneg (hc e)
    apply Real.rpow_nonneg
    unfold load
    apply Finset.sum_nonneg
    intro i _
    split_ifs
    · linarith [hw i e]
    · exact le_rfl
  refine ⟨X, ⟨?_, ?_⟩, ?_⟩
  · intro i p _
    rw [hXip]
    split_ifs <;> norm_num
  · intro i
    simp only [hXip]
    exact le_of_eq (by rw [Finset.sum_ite_eq', if_pos (hsol' i)])
  · unfold relaxObj primalObj
    rw [← hM]
    have hprim : ∑ e, c e * fracLoad reqs X e ^ α e = powerCost c α (load reqs sol) := by
      unfold powerCost
      apply Finset.sum_congr rfl
      intro e _
      rw [hfl e]
    rw [hprim]
    have hextra : ∑ e ∈ S, c e * α e / Real.exp M *
        ∑ i, (reqs i).w e ^ α e * ∑ p ∈ (reqs i).replies.filter (fun p => e ∈ p), X i p ≤
        M * Real.exp (-M) * powerCost c α (load reqs sol) := by
      calc ∑ e ∈ S, c e * α e / Real.exp M *
            ∑ i, (reqs i).w e ^ α e * ∑ p ∈ (reqs i).replies.filter (fun p => e ∈ p), X i p
          ≤ ∑ e ∈ S, M * Real.exp (-M) * (c e * load reqs sol e ^ α e) := by
            apply Finset.sum_le_sum
            intro e _
            rw [hext e]
            calc c e * α e / Real.exp M * ∑ i, (if e ∈ sol i then (reqs i).w e else 0) ^ α e
                ≤ (M * Real.exp (-M) * c e) * load reqs sol e ^ α e :=
                  mul_le_mul (hcoef e) (hsup e) (hTnn e) (mul_nonneg hK (hc e))
              _ = M * Real.exp (-M) * (c e * load reqs sol e ^ α e) := by ring
        _ ≤ ∑ e, M * Real.exp (-M) * (c e * load reqs sol e ^ α e) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            intro e _ _
            exact mul_nonneg hK (hlnn e)
        _ = M * Real.exp (-M) * powerCost c α (load reqs sol) := by
            unfold powerCost
            rw [Finset.mul_sum]
    linarith
