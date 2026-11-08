-- Prove2me | solution 1 for PCLAssort.lemma_5_ip_values
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:51:59.538327+00:00
-- url     : https://prove2.me/submissions/accc95b0-a9f5-4a4d-867f-1c19f7f0355c

import Mathlib
import Definitions.Def_PCLAssort_PCLInstance
import Definitions.Def_PCLAssort_DownwardClosed
import Definitions.Def_PCLAssort_fValue
import Definitions.Def_PCLAssort_ip1Value
import Definitions.Def_PCLAssort_ip2Value
import Definitions.Def_PCLAssort_constrDicutValue
import Definitions.Def_PCLAssort_pclEdges
import Definitions.Def_PCLAssort_pclWeight

namespace Aux_PCL_l5
open PCLAssort

theorem coef_nonneg (a b γ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ a ^ (1 / γ) / (a ^ (1 / γ) + b ^ (1 / γ)) ^ (1 - γ) :=
  div_nonneg (Real.rpow_nonneg ha _)
    (Real.rpow_nonneg (add_nonneg (Real.rpow_nonneg ha _) (Real.rpow_nonneg hb _)) _)

theorem coef_le (a b γ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    a ^ (1 / γ) / (a ^ (1 / γ) + b ^ (1 / γ)) ^ (1 - γ) ≤ a := by
  set A := a ^ (1 / γ) with hA
  have hA0 : 0 ≤ A := Real.rpow_nonneg ha _
  have hB0 : 0 ≤ b ^ (1 / γ) := Real.rpow_nonneg hb _
  rcases hA0.eq_or_lt with h | h
  · rw [← h, zero_div]; exact ha
  · have h1 : A ^ (1 - γ) ≤ (A + b ^ (1 / γ)) ^ (1 - γ) :=
      Real.rpow_le_rpow hA0 (by linarith) (by linarith)
    have h2 : 0 < A ^ (1 - γ) := Real.rpow_pos_of_pos h _
    calc A / (A + b ^ (1 / γ)) ^ (1 - γ) ≤ A / A ^ (1 - γ) :=
          div_le_div_of_nonneg_left hA0 h2 h1
      _ = A ^ γ := by
          rw [div_eq_iff h2.ne', ← Real.rpow_add h, show γ + (1 - γ) = (1 : ℝ) by ring,
            Real.rpow_one]
      _ = a := by
          rw [hA, ← Real.rpow_mul ha, one_div, inv_mul_cancel₀ hγ0.ne', Real.rpow_one]

theorem xi_eq {n : ℕ} (I : PCLInstance n) (z : ℝ) (k l p : Fin n) :
    xiShare I z k l p = (I.r p - z) * (I.v p ^ (1 / I.γ k l) /
      (I.v k ^ (1 / I.γ k l) + I.v l ^ (1 / I.γ k l)) ^ (1 - I.γ k l)) := by
  unfold xiShare; rw [mul_div_assoc]


theorem term_eq {n : ℕ} (I : PCLInstance n) (z : ℝ) (S : Finset (Fin n)) (i j : Fin n) (hij : i ≠ j) :
    ((I.r i - z) * I.v i ^ (1 / I.γ i j) * (if i ∈ S then 1 else 0) +
        (I.r j - z) * I.v j ^ (1 / I.γ i j) * (if j ∈ S then 1 else 0)) /
      nestWeight I S i j ^ (1 - I.γ i j) =
    nestWeight I S i j ^ I.γ i j * (nestRevenue I S i j - z) := by
  have hγ := I.γ_pos i j hij
  set a := I.v i ^ (1 / I.γ i j) * (if i ∈ S then (1 : ℝ) else 0) with ha
  set b := I.v j ^ (1 / I.γ i j) * (if j ∈ S then (1 : ℝ) else 0) with hb
  have ha0 : 0 ≤ a := mul_nonneg (Real.rpow_nonneg (I.v_nonneg i) _) (by split_ifs <;> norm_num)
  have hb0 : 0 ≤ b := mul_nonneg (Real.rpow_nonneg (I.v_nonneg j) _) (by split_ifs <;> norm_num)
  have hW : nestWeight I S i j = a + b := rfl
  have hR : nestRevenue I S i j = (I.r i * a + I.r j * b) / (a + b) := by
    unfold nestRevenue; rw [hW, ha, hb]; ring_nf
  have hnum : (I.r i - z) * I.v i ^ (1 / I.γ i j) * (if i ∈ S then 1 else 0) +
      (I.r j - z) * I.v j ^ (1 / I.γ i j) * (if j ∈ S then 1 else 0) =
      I.r i * a + I.r j * b - z * (a + b) := by rw [ha, hb]; ring
  rw [hnum, hR, hW]
  rcases (add_nonneg ha0 hb0).eq_or_lt with h0 | hpos
  · have ha' : a = 0 := by linarith
    have hb' : b = 0 := by linarith
    rw [← h0, Real.zero_rpow hγ.ne']; simp [ha', hb']
  · rw [Real.rpow_sub hpos, Real.rpow_one]
    field_simp

theorem w_sign {n : ℕ} (I : PCLInstance n) (z : ℝ) (e : Option (Fin n) × Option (Fin n))
    (he : e ∈ pclEdges n) (i : Fin n) (hi : e.1 = some i) :
    ∃ K, 0 ≤ K ∧ pclWeight I z e = (I.r i - z) * K := by
  obtain ⟨e1, e2⟩ := e
  simp only at hi
  subst hi
  have hne : some i ≠ e2 := (Finset.mem_filter.mp he).2.2
  rcases e2 with _ | j
  · refine ⟨∑ k ∈ Finset.univ.erase i,
      (I.v i ^ (1 / I.γ i k) / (I.v i ^ (1 / I.γ i k) + I.v k ^ (1 / I.γ i k)) ^ (1 - I.γ i k) +
       I.v i ^ (1 / I.γ k i) / (I.v k ^ (1 / I.γ k i) + I.v i ^ (1 / I.γ k i)) ^ (1 - I.γ k i)),
      Finset.sum_nonneg (fun k _ => add_nonneg (coef_nonneg _ _ _ (I.v_nonneg i) (I.v_nonneg k))
        (by
          have := coef_nonneg (I.v i) (I.v k) (I.γ k i) (I.v_nonneg i) (I.v_nonneg k)
          rwa [add_comm (I.v i ^ (1 / I.γ k i))] at this)), ?_⟩
    simp only [pclWeight]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    unfold xiShare
    ring
  · have hij : i ≠ j := fun h => hne (by rw [h])
    have hC1 := coef_le (I.v i) (I.v j) (I.γ i j) (I.v_nonneg i) (I.v_nonneg j)
      (I.γ_pos i j hij) (I.γ_le_one i j hij)
    have hC2 := coef_le (I.v i) (I.v j) (I.γ j i) (I.v_nonneg i) (I.v_nonneg j)
      (I.γ_pos j i (Ne.symm hij)) (I.γ_le_one j i (Ne.symm hij))
    rw [add_comm (I.v i ^ (1 / I.γ j i))] at hC2
    refine ⟨2 * I.v i - I.v i ^ (1 / I.γ i j) / (I.v i ^ (1 / I.γ i j) + I.v j ^ (1 / I.γ i j)) ^ (1 - I.γ i j)
      - I.v i ^ (1 / I.γ j i) / (I.v j ^ (1 / I.γ j i) + I.v i ^ (1 / I.γ j i)) ^ (1 - I.γ j i),
      by linarith, ?_⟩
    simp only [pclWeight, if_neg hij]
    unfold xiShare
    ring

end Aux_PCL_l5

open PCLAssort Aux_PCL_l5 in
theorem solution {n : ℕ} (I : PCLInstance n) (F : Set (Finset (Fin n)))
    (hF : DownwardClosed F) (z : ℝ) :
    ip1Value I F z = fValue I F z ∧
      ip2Value I F z = constrDicutValue (pclEdges n) (pclWeight I z) F := by
  constructor
  · unfold ip1Value fValue
    congr 1
    funext S
    unfold ip1Objective hz
    apply Finset.sum_congr rfl
    intro p hp
    exact term_eq I z S.1 p.1 p.2 (Finset.mem_offDiag.mp hp).2.2
  · haveI : Nonempty F := ⟨⟨∅, hF.1⟩⟩
    unfold ip2Value constrDicutValue
    set Q := {q : Finset (Fin n) × Finset (Option (Fin n) × Option (Fin n)) //
      q.1 ∈ F ∧ q.2 ⊆ pclEdges n ∧ ∀ e ∈ q.2, e.1 ∈ q.1.image some ∧ e.2 ∉ q.1.image some}
    haveI : Nonempty Q := ⟨⟨(∅, ∅), hF.1, Finset.empty_subset _, by simp⟩⟩
    have bddQ : BddAbove (Set.range fun q : Q => ∑ e ∈ q.1.2, pclWeight I z e) :=
      (Set.finite_range _).bddAbove
    have bddF : BddAbove (Set.range fun S : F => cutValue (pclEdges n) (pclWeight I z) (S.1.image some)) :=
      (Set.finite_range _).bddAbove
    apply le_antisymm
    · apply ciSup_le
      rintro ⟨⟨S, E'⟩, hSF, hE', hcut⟩
      simp only
      set S' := S.filter (fun i => z ≤ I.r i) with hS'
      have hS'F : S' ∈ F := hF.2 S hSF S' (Finset.filter_subset _ _)
      refine le_trans ?_ (le_ciSup bddF ⟨S', hS'F⟩)
      simp only [cutValue]
      rw [← Finset.sum_filter_add_sum_filter_not E' (fun e => e.1 ∈ S'.image some)]
      have hneg : ∑ e ∈ E'.filter (fun e => ¬ e.1 ∈ S'.image some), pclWeight I z e ≤ 0 := by
        apply Finset.sum_nonpos
        intro e he
        obtain ⟨heE, hnot⟩ := Finset.mem_filter.mp he
        obtain ⟨h1, _⟩ := hcut e heE
        obtain ⟨i, hiS, hie⟩ := Finset.mem_image.mp h1
        have hri : I.r i < z := by
          by_contra hc; push_neg at hc
          exact hnot (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hiS, hc⟩, hie⟩)
        obtain ⟨K, hK, hw⟩ := w_sign I z e (hE' heE) i hie.symm
        rw [hw]; nlinarith
      have hsub : E'.filter (fun e => e.1 ∈ S'.image some) ⊆
          (pclEdges n).filter (fun e => e.1 ∈ S'.image some ∧ e.2 ∉ S'.image some) := by
        intro e he
        obtain ⟨heE, h1⟩ := Finset.mem_filter.mp he
        refine Finset.mem_filter.mpr ⟨hE' heE, h1, fun h2 => (hcut e heE).2 ?_⟩
        obtain ⟨i, hi, hie⟩ := Finset.mem_image.mp h2
        exact Finset.mem_image.mpr ⟨i, Finset.mem_of_mem_filter i hi, hie⟩
      have hpos : ∑ e ∈ E'.filter (fun e => e.1 ∈ S'.image some), pclWeight I z e ≤
          ∑ e ∈ (pclEdges n).filter (fun e => e.1 ∈ S'.image some ∧ e.2 ∉ S'.image some),
            pclWeight I z e := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro e he _
        obtain ⟨heE, h1, _⟩ := Finset.mem_filter.mp he
        obtain ⟨i, hiS, hie⟩ := Finset.mem_image.mp h1
        have hri : z ≤ I.r i := (Finset.mem_filter.mp hiS).2
        obtain ⟨K, hK, hw⟩ := w_sign I z e heE i hie.symm
        rw [hw]; nlinarith
      linarith
    · apply ciSup_le
      rintro ⟨S, hSF⟩
      simp only [cutValue]
      have hq : ((S, (pclEdges n).filter (fun e => e.1 ∈ S.image some ∧ e.2 ∉ S.image some)) :
          Finset (Fin n) × Finset (Option (Fin n) × Option (Fin n))) ∈
          {q : Finset (Fin n) × Finset (Option (Fin n) × Option (Fin n)) |
            q.1 ∈ F ∧ q.2 ⊆ pclEdges n ∧ ∀ e ∈ q.2, e.1 ∈ q.1.image some ∧ e.2 ∉ q.1.image some} :=
        ⟨hSF, Finset.filter_subset _ _, fun e he => (Finset.mem_filter.mp he).2⟩
      exact le_ciSup bddQ ⟨_, hq⟩
