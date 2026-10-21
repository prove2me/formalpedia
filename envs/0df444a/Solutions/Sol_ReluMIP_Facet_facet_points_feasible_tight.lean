-- Prove2me | solution 1 for ReluMIP.Facet.facet_points_feasible_tight
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:56:16.500974+00:00
-- url     : https://prove2.me/submissions/8f80a004-7b0a-4cb7-979a-c41373c56037

import Mathlib
import Definitions.Def_ReluMIP_Facet_Setting

set_option autoImplicit false
open ReluMIP.Facet ReluMIP.Ideal

lemma RMF_winward {η : ℕ} (w : Fin η → ℝ) (i : Fin η) : w i * inward w i = |w i| := by
  unfold inward
  split_ifs with h
  · rw [mul_one, abs_of_nonneg h]
  · push Not at h
    rw [mul_neg_one, abs_of_neg h]

lemma RMF_Lb {η : ℕ} (w : Fin η → ℝ) (L U : Fin η → ℝ) (hLU : ∀ i, L i < U i) (i : Fin η) :
    L i ≤ Lbrev w L U i ∧ Lbrev w L U i ≤ U i := by
  unfold Lbrev
  have := hLU i
  split_ifs <;> constructor <;> linarith

lemma RMF_Ub {η : ℕ} (w : Fin η → ℝ) (L U : Fin η → ℝ) (hLU : ∀ i, L i < U i) (i : Fin η) :
    L i ≤ Ubrev w L U i ∧ Ubrev w L U i ≤ U i := by
  unfold Ubrev
  have := hLU i
  split_ifs <;> constructor <;> linarith

lemma RMF_stepL {η : ℕ} (w : Fin η → ℝ) (L U : Fin η → ℝ) (hLU : ∀ i, L i < U i) (i : Fin η)
    (ε : ℝ) (hε : 0 < ε) (hεU : ε ≤ U i - L i) :
    L i ≤ Lbrev w L U i + ε * inward w i ∧ Lbrev w L U i + ε * inward w i ≤ U i := by
  unfold Lbrev inward
  split_ifs <;> constructor <;> linarith

lemma RMF_stepU {η : ℕ} (w : Fin η → ℝ) (L U : Fin η → ℝ) (hLU : ∀ i, L i < U i) (i : Fin η)
    (ε : ℝ) (hε : 0 < ε) (hεU : ε ≤ U i - L i) :
    L i ≤ Ubrev w L U i - ε * inward w i ∧ Ubrev w L U i - ε * inward w i ≤ U i := by
  unfold Ubrev inward
  split_ifs <;> constructor <;> linarith

lemma RMF_sum_single {η : ℕ} (w : Fin η → ℝ) (J : Finset (Fin η)) (i : Fin η) (c : ℝ) :
    ∑ k ∈ J, w k * (Pi.single i c : Fin η → ℝ) k = if i ∈ J then w i * c else 0 := by
  simp [Pi.single_apply, mul_ite]

lemma RMF_sum_single_univ {η : ℕ} (w : Fin η → ℝ) (i : Fin η) (c : ℝ) :
    ∑ k, w k * (Pi.single i c : Fin η → ℝ) k = w i * c := by
  simp [Pi.single_apply, mul_ite]

lemma RMF_rhs_L {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) (J : Finset (Fin η)) :
    rhs6b w b L U J (Lbrev w L U) 0 = 0 := by
  simp [rhs6b]

lemma RMF_rhs_U {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) (J : Finset (Fin η)) :
    rhs6b w b L U J (Ubrev w L U) 1 = affineFn w b (Ubrev w L U) := by
  unfold rhs6b affineFn
  simp only [sub_self, mul_zero, sub_zero, mul_one, Finset.sum_const_zero, zero_add]
  have := Finset.sum_add_sum_compl J (fun k => w k * Ubrev w L U k)
  rw [Finset.compl_eq_univ_sdiff] at this
  linarith

lemma RMF_rhs_L_step {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) (J : Finset (Fin η))
    (i : Fin η) (c : ℝ) :
    rhs6b w b L U J (Lbrev w L U + Pi.single i c) 0 = if i ∈ J then w i * c else 0 := by
  unfold rhs6b
  simp only [mul_zero, add_zero, sub_zero, mul_one, Pi.add_apply]
  rw [← RMF_sum_single w J i c]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma RMF_rhs_U_step {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) (J : Finset (Fin η))
    (i : Fin η) (c : ℝ) :
    rhs6b w b L U J (Ubrev w L U - Pi.single i c) 1 =
      affineFn w b (Ubrev w L U) - (if i ∈ J then w i * c else 0) := by
  unfold rhs6b affineFn
  simp only [sub_self, mul_zero, sub_zero, mul_one, Pi.sub_apply]
  rw [← RMF_sum_single w J i c]
  have := Finset.sum_add_sum_compl J (fun k => w k * Ubrev w L U k)
  rw [Finset.compl_eq_univ_sdiff] at this
  have e : ∑ k ∈ J, w k * (Ubrev w L U k - (Pi.single i c : Fin η → ℝ) k) =
      ∑ k ∈ J, w k * Ubrev w L U k - ∑ k ∈ J, w k * (Pi.single i c : Fin η → ℝ) k := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  rw [e]
  linarith

lemma RMF_aff_L {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) (i : Fin η) (c : ℝ) :
    affineFn w b (Lbrev w L U + Pi.single i c) = Mminus w b L U + w i * c := by
  unfold affineFn Mminus
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  rw [RMF_sum_single_univ]; ring

lemma RMF_aff_U {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) (i : Fin η) (c : ℝ) :
    affineFn w b (Ubrev w L U - Pi.single i c) = Mplus w b L U - w i * c := by
  unfold affineFn Mplus
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  rw [RMF_sum_single_univ]; ring

theorem solution {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ)
    (hLU : ∀ i, L i < U i) (hSA : ReluMIP.Ideal.StrictActivity w b L U) :
    ∀ I : Finset (Fin η), I ⊆ ReluMIP.Ideal.supp w → ∃ ε : ℝ, 0 < ε ∧ ∀ j,
      facetPts w b L U I ε j ∈ form6 w b L U ∧
      (facetPts w b L U I ε j).2.1 =
        ReluMIP.Ideal.rhs6b w b L U I (facetPts w b L U I ε j).1 (facetPts w b L U I ε j).2.2 := by
  intro I _
  obtain ⟨hm, hp⟩ := hSA
  set m := min (-Mminus w b L U) (Mplus w b L U) with hmdef
  have hm0 : 0 < m := lt_min (by linarith) hp
  set S := ∑ i, |w i| with hS
  set T := ∑ i, 1 / (U i - L i) with hT
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hT0 : 0 ≤ T := Finset.sum_nonneg (fun i _ => by have := hLU i; apply div_nonneg (by norm_num); linarith)
  set K := 1 + T + (S + 1) / m with hK
  have hK0 : 0 < K := by
    have : 0 ≤ (S + 1) / m := by positivity
    linarith
  refine ⟨1 / K, by positivity, ?_⟩
  set ε := 1 / K with hε
  have hε0 : 0 < ε := by positivity
  have hεU : ∀ i, ε ≤ U i - L i := by
    intro i
    have hd : 0 < U i - L i := by have := hLU i; linarith
    have h1 : 1 / (U i - L i) ≤ T :=
      Finset.single_le_sum (f := fun i => 1 / (U i - L i))
        (fun i _ => by have := hLU i; apply div_nonneg (by norm_num); linarith) (Finset.mem_univ i)
    have h2 : 0 ≤ (S + 1) / m := by positivity
    have h3 : 1 / (U i - L i) ≤ K := by linarith
    rw [hε, div_le_iff₀ hK0]
    rw [div_le_iff₀ hd] at h3
    linarith
  have hεw : ∀ i, ε * |w i| ≤ m := by
    intro i
    have hwi : |w i| ≤ S :=
      Finset.single_le_sum (f := fun i => |w i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 : (S + 1) / m ≤ K := by
      have : 0 ≤ T := hT0
      linarith
    have h3 : S + 1 ≤ K * m := by rwa [div_le_iff₀ hm0] at h2
    have : ε * (S + 1) ≤ m := by
      rw [hε, one_div, inv_mul_le_iff₀ hK0]; linarith
    calc ε * |w i| ≤ ε * (S + 1) := mul_le_mul_of_nonneg_left (by linarith) hε0.le
      _ ≤ m := this
  have hεm1 : ∀ i, ε * |w i| ≤ -Mminus w b L U := fun i => (hεw i).trans (min_le_left _ _)
  have hεm2 : ∀ i, ε * |w i| ≤ Mplus w b L U := fun i => (hεw i).trans (min_le_right _ _)
  have hMm : Mminus w b L U = affineFn w b (Lbrev w L U) := rfl
  have hMp : Mplus w b L U = affineFn w b (Ubrev w L U) := rfl
  have hbL : Lbrev w L U ∈ box L U := fun i => RMF_Lb w L U hLU i
  have hbU : Ubrev w L U ∈ box L U := fun i => RMF_Ub w L U hLU i
  intro j
  rcases j with k | i
  · have hk01 : k = 0 ∨ k = 1 := by fin_cases k <;> simp
    rcases hk01 with rfl | rfl
    · -- p⁰
      have hpt : facetPts w b L U I ε (Sum.inl 0) = (Lbrev w L U, 0, 0) := by simp [facetPts]
      rw [hpt]
      refine ⟨⟨⟨?_, ?_, hbL, le_refl _, le_refl _, zero_le_one⟩, Or.inl rfl⟩, ?_⟩
      · show affineFn w b (Lbrev w L U) ≤ 0
        rw [← hMm]; linarith
      · intro J _
        show (0:ℝ) ≤ rhs6b w b L U J (Lbrev w L U) 0
        rw [RMF_rhs_L]
      · show (0:ℝ) = rhs6b w b L U I (Lbrev w L U) 0
        rw [RMF_rhs_L]
    · -- p¹
      have hpt : facetPts w b L U I ε (Sum.inl 1) =
          (Ubrev w L U, affineFn w b (Ubrev w L U), 1) := by simp [facetPts]
      rw [hpt]
      refine ⟨⟨⟨le_refl _, ?_, hbU, ?_, zero_le_one, le_refl _⟩, Or.inr rfl⟩, ?_⟩
      · intro J _
        show affineFn w b (Ubrev w L U) ≤ rhs6b w b L U J (Ubrev w L U) 1
        rw [RMF_rhs_U]
      · show 0 ≤ affineFn w b (Ubrev w L U)
        rw [← hMp]; exact hp.le
      · show affineFn w b (Ubrev w L U) = rhs6b w b L U I (Ubrev w L U) 1
        rw [RMF_rhs_U]
  · have hw : w i * (ε * inward w i) = ε * |w i| := by rw [mul_left_comm, RMF_winward]
    have hnn : 0 ≤ ε * |w i| := by positivity
    by_cases hi : i ∈ I
    · have hpt : facetPts w b L U I ε (Sum.inr i) =
          (Ubrev w L U - Pi.single i (ε * inward w i),
            affineFn w b (Ubrev w L U - Pi.single i (ε * inward w i)), 1) := by simp [facetPts, hi]
      rw [hpt]
      have hay : affineFn w b (Ubrev w L U - Pi.single i (ε * inward w i)) =
          Mplus w b L U - ε * |w i| := by
        rw [RMF_aff_U, hw]
      refine ⟨⟨⟨le_refl _, ?_, ?_, ?_, zero_le_one, le_refl _⟩, Or.inr rfl⟩, ?_⟩
      · intro J _
        show affineFn w b (Ubrev w L U - Pi.single i (ε * inward w i)) ≤
          rhs6b w b L U J (Ubrev w L U - Pi.single i (ε * inward w i)) 1
        rw [RMF_rhs_U_step, hay, ← hMp]
        split_ifs
        · rw [hw]
        · linarith
      · intro k
        show L k ≤ (Ubrev w L U - (Pi.single i (ε * inward w i) : Fin η → ℝ)) k ∧
          (Ubrev w L U - (Pi.single i (ε * inward w i) : Fin η → ℝ)) k ≤ U k
        by_cases hk : k = i
        · subst hk
          simpa using RMF_stepU w L U hLU k ε hε0 (hεU k)
        · simpa [Pi.single_apply, hk] using RMF_Ub w L U hLU k
      · show 0 ≤ affineFn w b (Ubrev w L U - Pi.single i (ε * inward w i))
        rw [hay]; linarith [hεm2 i]
      · show affineFn w b (Ubrev w L U - Pi.single i (ε * inward w i)) =
          rhs6b w b L U I (Ubrev w L U - Pi.single i (ε * inward w i)) 1
        rw [RMF_rhs_U_step, if_pos hi, ← hMp, hay, hw]
    · have hpt : facetPts w b L U I ε (Sum.inr i) =
          (Lbrev w L U + Pi.single i (ε * inward w i), 0, 0) := by simp [facetPts, hi]
      rw [hpt]
      have hay : affineFn w b (Lbrev w L U + Pi.single i (ε * inward w i)) =
          Mminus w b L U + ε * |w i| := by
        rw [RMF_aff_L, hw]
      refine ⟨⟨⟨?_, ?_, ?_, le_refl _, le_refl _, zero_le_one⟩, Or.inl rfl⟩, ?_⟩
      · show affineFn w b (Lbrev w L U + Pi.single i (ε * inward w i)) ≤ 0
        rw [hay]; linarith [hεm1 i]
      · intro J _
        show (0:ℝ) ≤ rhs6b w b L U J (Lbrev w L U + Pi.single i (ε * inward w i)) 0
        rw [RMF_rhs_L_step]
        split_ifs
        · rw [hw]; exact hnn
        · exact le_refl _
      · intro k
        show L k ≤ (Lbrev w L U + (Pi.single i (ε * inward w i) : Fin η → ℝ)) k ∧
          (Lbrev w L U + (Pi.single i (ε * inward w i) : Fin η → ℝ)) k ≤ U k
        by_cases hk : k = i
        · subst hk
          simpa using RMF_stepL w L U hLU k ε hε0 (hεU k)
        · simpa [Pi.single_apply, hk] using RMF_Lb w L U hLU k
      · show (0:ℝ) = rhs6b w b L U I (Lbrev w L U + Pi.single i (ε * inward w i)) 0
        rw [RMF_rhs_L_step, if_neg hi]
