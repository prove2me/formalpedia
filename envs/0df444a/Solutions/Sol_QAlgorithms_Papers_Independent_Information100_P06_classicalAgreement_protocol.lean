-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P06.classicalAgreement_protocol
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:32:41.694985+00:00
-- url     : https://prove2.me/submissions/e25e7048-1d31-49ab-a6ea-6e6b9f6b92c9

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P06

noncomputable section

open QAlgorithms.Papers.Independent.Information100.P06
open scoped Matrix ComplexOrder ENNReal Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

lemma S170bL_le1 {d : ℕ} [NeZero d] {P : Transition d} (hP : IsClassicalChannel P) (b a : ZMod d) :
    P b a ≤ 1 := by
  rw [← hP.2 a]
  exact Finset.single_le_sum (fun b _ => hP.1 b a) (Finset.mem_univ b)

lemma S170bL_fid_le {d : ℕ} [NeZero d] (P : Transition d) (a : ZMod d) : classicalFidelity P ≤ P a a :=
  csInf_le (Set.finite_range _).bddBelow ⟨a, rfl⟩

lemma S170bL_fid_nonneg {d : ℕ} [NeZero d] {P : Transition d} (hP : IsClassicalChannel P) :
    0 ≤ classicalFidelity P :=
  le_csInf (Set.range_nonempty _) (by rintro _ ⟨a, rfl⟩; exact hP.1 a a)

lemma S170bL_diag {d n : ℕ} [NeZero d] (P : Fin n → Transition d) (j : ZMod d) :
    agreementBranch P j j = (d : ℝ)⁻¹ * ∑ a, ∏ i, P i a a := by
  unfold agreementBranch
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  have : ∀ b : ZMod d, (j = j + a - b) ↔ (a = b) := fun b => by
    constructor
    · intro h; exact sub_eq_zero.1 (by linear_combination -h)
    · rintro rfl; ring
  simp only [this]
  rw [Finset.sum_ite_eq]; simp


theorem solution
    {d n : ℕ} [NeZero d] (hd : 2 ≤ d) (hn : 2 ≤ n)
    (P : Fin n → Transition d) (hP : ∀ i, IsClassicalChannel (P i)) :
    (∀ k, ∑ j, agreementBranch P j k = agreementSuccess P) ∧
    0 ≤ agreementSuccess P ∧ agreementSuccess P ≤ 1 ∧
    (0 < agreementSuccess P →
      IsClassicalChannel (agreementOutput P) ∧
      classicalFidelity (agreementOutput P) =
        (∑ a, ∏ i, P i a a) / (∑ a, ∑ b, ∏ i, P i b a)) ∧
    ((∀ i, IdentityBiased (P i) ∧ classicalFidelity (P i) < 1) →
      0 < agreementSuccess P ∧
      ∀ i, classicalFidelity (P i) < classicalFidelity (agreementOutput P)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdi : (0 : ℝ) < (d : ℝ)⁻¹ := inv_pos.2 hd0
  have hcol : ∀ k, ∑ j, agreementBranch P j k = agreementSuccess P := by
    intro k
    unfold agreementBranch agreementSuccess
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_ite_eq']; simp
  have hprod0 : ∀ b a, 0 ≤ ∏ i, P i b a := fun b a => Finset.prod_nonneg fun i _ => (hP i).1 b a
  have hs0 : 0 ≤ agreementSuccess P :=
    mul_nonneg hdi.le (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hprod0 b a)
  have i0 : Fin n := ⟨0, by omega⟩
  have hs1 : agreementSuccess P ≤ 1 := by
    unfold agreementSuccess
    have h : ∑ a, ∑ b, ∏ i, P i b a ≤ ∑ a : ZMod d, ∑ b, P i0 b a := by
      refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i0)]
      exact mul_le_of_le_one_right ((hP i0).1 b a)
        (Finset.prod_le_one (fun i _ => (hP i).1 b a) (fun i _ => S170bL_le1 (hP i) b a))
    have h2 : ∑ a : ZMod d, ∑ b, P i0 b a = d := by simp [(hP i0).2]
    calc (d : ℝ)⁻¹ * ∑ a, ∑ b, ∏ i, P i b a ≤ (d : ℝ)⁻¹ * ∑ a : ZMod d, ∑ b, P i0 b a :=
          mul_le_mul_of_nonneg_left h hdi.le
      _ = 1 := by rw [h2, inv_mul_cancel₀ hd0.ne']
  have hfid_out : 0 < agreementSuccess P →
      classicalFidelity (agreementOutput P) = (∑ a, ∏ i, P i a a) / (∑ a, ∑ b, ∏ i, P i b a) := by
    intro hpos
    have : (fun a => agreementOutput P a a) = fun _ => (∑ a, ∏ i, P i a a) / (∑ a, ∑ b, ∏ i, P i b a) := by
      funext j
      simp only [agreementOutput, S170bL_diag, agreementSuccess]
      rw [mul_div_mul_left _ _ hdi.ne']
    unfold classicalFidelity
    rw [this, Set.range_const, csInf_singleton]
  refine ⟨hcol, hs0, hs1, fun hpos => ⟨⟨fun b a => ?_, fun a => ?_⟩, hfid_out hpos⟩, fun hb => ?_⟩
  · refine div_nonneg (mul_nonneg hdi.le (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_)) hs0
    split_ifs
    · exact hprod0 _ _
    · exact le_rfl
  · simp only [agreementOutput]
    rw [← Finset.sum_div, hcol, div_self hpos.ne']
  -- strict improvement
  haveI : Fact (1 < d) := ⟨hd⟩
  have hD : ∀ a, 0 < ∏ i, P i a a := by
    intro a
    refine Finset.prod_pos fun i _ => ?_
    have hne : a + 1 ≠ a := by simp
    exact lt_of_le_of_lt ((hP i).1 (a + 1) a) ((hb i).1 a (a + 1) hne)
  have hT : ∀ a, ∏ i, P i a a ≤ ∑ b, ∏ i, P i b a := fun a =>
    Finset.single_le_sum (fun b _ => hprod0 b a) (Finset.mem_univ a)
  have hTpos : 0 < ∑ a, ∑ b, ∏ i, P i b a :=
    lt_of_lt_of_le (Finset.sum_pos (fun a _ => hD a) Finset.univ_nonempty) (Finset.sum_le_sum fun a _ => hT a)
  have hpos : 0 < agreementSuccess P := mul_pos hdi hTpos
  refine ⟨hpos, fun i => ?_⟩
  rw [hfid_out hpos, lt_div_iff₀ hTpos, Finset.mul_sum]
  set f := classicalFidelity (P i)
  have hf0 : 0 ≤ f := S170bL_fid_nonneg (hP i)
  have hf1 : f < 1 := (hb i).2
  obtain ⟨j0, hj0⟩ : ∃ j0 : Fin n, j0 ≠ i := by
    by_cases h : i.val = 0
    · exact ⟨⟨1, by omega⟩, fun h' => by rw [← h'] at h; simp at h⟩
    · exact ⟨⟨0, by omega⟩, fun h' => h (by rw [← h'])⟩
  refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun a _ => ?_
  -- per-column strict inequality
  set Q := ∏ j ∈ Finset.univ.erase i, P j a a
  have hQ : 0 < Q := Finset.prod_pos fun j _ => hD a |>.ne' |> fun _ => by
    exact lt_of_le_of_lt ((hP j).1 (a + 1) a) ((hb j).1 a (a + 1) (by simp))
  have hDa : ∏ j, P j a a = P i a a * Q := (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  have hTa : ∑ b, ∏ j, P j b a = ∏ j, P j a a + ∑ b ∈ Finset.univ.erase a, P i b a *
      ∏ j ∈ Finset.univ.erase i, P j b a := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  have hRb : ∀ b ∈ Finset.univ.erase a, ∏ j ∈ Finset.univ.erase i, P j b a < Q := by
    intro b hb'
    have hba : b ≠ a := Finset.ne_of_mem_erase hb'
    by_cases hz : ∃ j ∈ Finset.univ.erase i, P j b a = 0
    · obtain ⟨j, hj, hj0'⟩ := hz
      rw [Finset.prod_eq_zero hj hj0']; exact hQ
    · push_neg at hz
      refine Finset.prod_lt_prod (fun j hj => lt_of_le_of_ne ((hP j).1 b a) (hz j hj).symm)
        (fun j _ => ((hb j).1 a b hba).le) ⟨j0, Finset.mem_erase.2 ⟨hj0, Finset.mem_univ _⟩, (hb j0).1 a b hba⟩
  have hsumi : ∑ b ∈ Finset.univ.erase a, P i b a = 1 - P i a a := by
    rw [← (hP i).2 a, ← Finset.add_sum_erase _ _ (Finset.mem_univ a)]; ring
  rw [hTa, hDa]
  have hfP : f ≤ P i a a := S170bL_fid_le (P i) a
  rcases eq_or_lt_of_le (S170bL_le1 (hP i) a a) with h1 | h1
  · -- perfect column: other entries vanish
    have hz : ∀ b ∈ Finset.univ.erase a, P i b a = 0 := by
      have h0 : ∑ b ∈ Finset.univ.erase a, P i b a = 0 := by rw [hsumi, h1]; ring
      exact (Finset.sum_eq_zero_iff_of_nonneg fun b _ => (hP i).1 b a).1 h0
    rw [Finset.sum_eq_zero fun b hb' => by rw [hz b hb', zero_mul], add_zero, h1, one_mul]
    nlinarith
  · have hS : ∑ b ∈ Finset.univ.erase a, P i b a * ∏ j ∈ Finset.univ.erase i, P j b a <
        (1 - P i a a) * Q := by
      rw [← hsumi, Finset.sum_mul]
      obtain ⟨b, hb', hbpos⟩ : ∃ b ∈ Finset.univ.erase a, 0 < P i b a := by
        by_contra hcon
        push_neg at hcon
        have : ∑ b ∈ Finset.univ.erase a, P i b a = 0 :=
          Finset.sum_eq_zero fun b hb' => le_antisymm (hcon b hb') ((hP i).1 b a)
        rw [hsumi] at this; linarith
      exact Finset.sum_lt_sum (fun b hb' => mul_le_mul_of_nonneg_left (hRb b hb').le ((hP i).1 b a))
        ⟨b, hb', mul_lt_mul_of_pos_left (hRb b hb') hbpos⟩
    rcases eq_or_lt_of_le hf0 with hf | hf
    · have hPaa : 0 < P i a a := lt_of_le_of_lt ((hP i).1 (a + 1) a) ((hb i).1 a (a + 1) (by simp))
      rw [← hf, zero_mul]; exact mul_pos hPaa hQ
    · have : f * (1 - P i a a) ≤ P i a a * (1 - f) := by nlinarith
      nlinarith [mul_lt_mul_of_pos_left hS hf]

end
