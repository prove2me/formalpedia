-- Prove2me | solution 1 for ReluMIP.Facet.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:01:17.351127+00:00
-- url     : https://prove2.me/submissions/0bde4ad4-7ab8-4390-87b4-8fbb2a04adfc

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

theorem RMF_ft {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ)
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

lemma RMF_key {η : ℕ} (lam : Fin η → ℝ) (I : Finset (Fin η)) (A B : ℝ) (c : Fin η → ℝ) (j : Fin η) :
    ∑ i, lam i * (if i ∈ I then A - (Pi.single i (c i) : Fin η → ℝ) j
        else B + (Pi.single i (c i) : Fin η → ℝ) j) =
      A * ∑ i, lam i * (if i ∈ I then 1 else 0) + B * ∑ i, lam i * (if i ∈ I then 0 else 1) +
        lam j * (if j ∈ I then -c j else c j) := by
  have e : ∀ i, lam i * (if i ∈ I then A - (Pi.single i (c i) : Fin η → ℝ) j
        else B + (Pi.single i (c i) : Fin η → ℝ) j) =
      A * (lam i * (if i ∈ I then 1 else 0)) + B * (lam i * (if i ∈ I then 0 else 1)) +
        lam i * (if i ∈ I then -(Pi.single i (c i) : Fin η → ℝ) j else (Pi.single i (c i) : Fin η → ℝ) j) := by
    intro i
    split_ifs <;> ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_eq_single j]
  · by_cases hj : j ∈ I <;> simp [hj, Pi.single_apply]
  · intro i _ hij
    simp [Pi.single_apply, Ne.symm hij]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem RMF_ai {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ)
    (I : Finset (Fin η)) (hI : I ⊆ ReluMIP.Ideal.supp w) (ε : ℝ) (hε : 0 < ε) :
    AffineIndependent ℝ (facetPts w b L U I ε) := by
  rw [affineIndependent_iff_of_fintype]
  intro lam hs h
  rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ hs 0,
    Finset.weightedVSubOfPoint_apply] at h
  simp only [vsub_eq_sub, sub_zero] at h
  rw [Fintype.sum_sum_type, Fin.sum_univ_two] at hs h
  let pz : (Fin η → ℝ) × ℝ × ℝ →ₗ[ℝ] ℝ := (LinearMap.snd ℝ _ _) ∘ₗ (LinearMap.snd ℝ _ _)
  let px : Fin η → (Fin η → ℝ) × ℝ × ℝ →ₗ[ℝ] ℝ := fun j => (LinearMap.proj j) ∘ₗ (LinearMap.fst ℝ _ _)
  have hz := congrArg pz h
  simp only [map_add, map_smul, map_sum, map_zero, smul_eq_mul] at hz
  have hx := fun j => congrArg (px j) h
  simp only [map_add, map_smul, map_sum, map_zero, smul_eq_mul] at hx
  have hz0 : pz (facetPts w b L U I ε (Sum.inl 0)) = 0 := by simp [facetPts, pz]
  have hz1 : pz (facetPts w b L U I ε (Sum.inl 1)) = 1 := by simp [facetPts, pz]
  have hzi : ∀ i, pz (facetPts w b L U I ε (Sum.inr i)) = if i ∈ I then 1 else 0 := by
    intro i
    by_cases hi : i ∈ I <;> simp [facetPts, pz, hi]
  have hx0 : ∀ j, px j (facetPts w b L U I ε (Sum.inl 0)) = ReluMIP.Ideal.Lbrev w L U j := by
    intro j; simp [facetPts, px]
  have hx1 : ∀ j, px j (facetPts w b L U I ε (Sum.inl 1)) = ReluMIP.Ideal.Ubrev w L U j := by
    intro j; simp [facetPts, px]
  have hxi : ∀ j i, px j (facetPts w b L U I ε (Sum.inr i)) =
      if i ∈ I then ReluMIP.Ideal.Ubrev w L U j - (Pi.single i (ε * inward w i) : Fin η → ℝ) j
      else ReluMIP.Ideal.Lbrev w L U j + (Pi.single i (ε * inward w i) : Fin η → ℝ) j := by
    intro j i
    by_cases hi : i ∈ I <;> simp [facetPts, px, hi]
  simp only [hz0, hz1, hzi] at hz
  simp only [hx0, hx1, hxi] at hx
  have hxj : ∀ j, ReluMIP.Ideal.Lbrev w L U j * (lam (Sum.inl 0) + ∑ i, lam (Sum.inr i) * (if i ∈ I then 0 else 1)) +
      ReluMIP.Ideal.Ubrev w L U j * (lam (Sum.inl 1) + ∑ i, lam (Sum.inr i) * (if i ∈ I then 1 else 0)) +
      lam (Sum.inr j) * (if j ∈ I then -(ε * inward w j) else ε * inward w j) = 0 := by
    intro j
    have := hx j
    rw [RMF_key (fun i => lam (Sum.inr i)) I (ReluMIP.Ideal.Ubrev w L U j) (ReluMIP.Ideal.Lbrev w L U j)
      (fun i => ε * inward w i) j] at this
    linarith
  have hsum : (∑ i, lam (Sum.inr i)) = (∑ i, lam (Sum.inr i) * (if i ∈ I then 1 else 0)) +
      ∑ i, lam (Sum.inr i) * (if i ∈ I then 0 else 1) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    split_ifs <;> ring
  have hA : lam (Sum.inl 1) + ∑ i, lam (Sum.inr i) * (if i ∈ I then 1 else 0) = 0 := by linarith
  have hB : lam (Sum.inl 0) + ∑ i, lam (Sum.inr i) * (if i ∈ I then 0 else 1) = 0 := by linarith
  have hinv : ∀ j, inward w j ≠ 0 := by
    intro j; unfold inward; split_ifs <;> norm_num
  have hrec : ∀ j, lam (Sum.inr j) = 0 := by
    intro j
    have := hxj j
    rw [hA, hB] at this
    have hne : (if j ∈ I then -(ε * inward w j) else ε * inward w j) ≠ 0 := by
      have : ε * inward w j ≠ 0 := mul_ne_zero hε.ne' (hinv j)
      split_ifs <;> simpa using this
    have : lam (Sum.inr j) * (if j ∈ I then -(ε * inward w j) else ε * inward w j) = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right hne
  have hsum0 : ∑ i, lam (Sum.inr i) * (if i ∈ I then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero; intro i _; rw [hrec i]; ring
  have hsum1 : ∑ i, lam (Sum.inr i) * (if i ∈ I then 0 else 1) = 0 := by
    apply Finset.sum_eq_zero; intro i _; rw [hrec i]; ring
  intro i
  rcases i with k | j
  · fin_cases k
    · simp; linarith
    · simp; linarith
  · exact hrec j

theorem solution {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ)
    (hLU : ∀ i, L i < U i) (hSA : ReluMIP.Ideal.StrictActivity w b L U) :
    ∀ I : Finset (Fin η), I ⊆ ReluMIP.Ideal.supp w →
      IsFacetDefining (convexHull ℝ (form6 w b L U))
        (fun p => p.2.1 - ReluMIP.Ideal.rhs6b w b L U I p.1 p.2.2) := by
  intro I hI
  set A : ℝ := ∑ i ∈ I, w i * Lbrev w L U i with hA
  set B : ℝ := b + ∑ i ∈ Finset.univ \ I, w i * Ubrev w L U i with hB
  let ℓ : ((Fin η → ℝ) × ℝ × ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun p => p.2.1 - ∑ i ∈ I, w i * p.1 i - (A + B) * p.2.2
      map_add' := by
        intro p q
        simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]; ring
      map_smul' := by
        intro c p
        simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        have : ∑ i ∈ I, w i * (c * p.1 i) = c * ∑ i ∈ I, w i * p.1 i := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
        rw [this]; ring }
  have hℓ : ∀ p : (Fin η → ℝ) × ℝ × ℝ, ℓ p = p.2.1 - ∑ i ∈ I, w i * p.1 i - (A + B) * p.2.2 := fun p => rfl
  have hg : ∀ p : (Fin η → ℝ) × ℝ × ℝ,
      p.2.1 - ReluMIP.Ideal.rhs6b w b L U I p.1 p.2.2 = ℓ p + A := by
    intro p
    rw [hℓ]
    unfold ReluMIP.Ideal.rhs6b
    have e : ∑ i ∈ I, w i * (p.1 i - Lbrev w L U i * (1 - p.2.2)) =
        ∑ i ∈ I, w i * p.1 i - A * (1 - p.2.2) := by
      rw [hA, Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i _; ring
    rw [e]
    have : b + ∑ i ∈ Finset.univ \ I, w i * Ubrev w L U i = B := rfl
    rw [this]
    ring
  -- validity
  have hvalid : ∀ p ∈ form6 w b L U, p.2.1 - ReluMIP.Ideal.rhs6b w b L U I p.1 p.2.2 ≤ 0 := by
    intro p hp
    have := hp.1.2.1 I hI
    linarith
  have hconv : Convex ℝ {p : (Fin η → ℝ) × ℝ × ℝ | p.2.1 - ReluMIP.Ideal.rhs6b w b L U I p.1 p.2.2 ≤ 0} := by
    have : {p : (Fin η → ℝ) × ℝ × ℝ | p.2.1 - ReluMIP.Ideal.rhs6b w b L U I p.1 p.2.2 ≤ 0} =
        {p | ℓ p ≤ -A} := by
      ext p; simp only [Set.mem_setOf_eq, hg]; constructor <;> intro h <;> linarith
    rw [this]
    exact convex_halfSpace_le ℓ.isLinear (-A)
  have hvalid' : ∀ p ∈ convexHull ℝ (form6 w b L U),
      p.2.1 - ReluMIP.Ideal.rhs6b w b L U I p.1 p.2.2 ≤ 0 :=
    fun p hp => convexHull_min hvalid hconv hp
  -- the points
  obtain ⟨ε, hε, hft⟩ := RMF_ft w b L U hLU hSA I hI
  have hAI := RMF_ai w b L U I hI ε hε
  have hpt_mem : ∀ j, facetPts w b L U I ε j ∈ convexHull ℝ (form6 w b L U) :=
    fun j => subset_convexHull ℝ _ (hft j).1
  have hpt_tight : ∀ j, (facetPts w b L U I ε j).2.1 -
      ReluMIP.Ideal.rhs6b w b L U I (facetPts w b L U I ε j).1 (facetPts w b L U I ε j).2.2 = 0 :=
    fun j => sub_eq_zero.2 (hft j).2
  set face := convexHull ℝ (form6 w b L U) ∩
    {p : (Fin η → ℝ) × ℝ × ℝ | p.2.1 - ReluMIP.Ideal.rhs6b w b L U I p.1 p.2.2 = 0} with hface
  have hrange : Set.range (facetPts w b L U I ε) ⊆ face := by
    rintro _ ⟨j, rfl⟩
    exact ⟨hpt_mem j, hpt_tight j⟩
  -- dimension counts
  have hcard : Fintype.card (Fin 2 ⊕ Fin η) = (η + 1) + 1 := by simp; ring
  have hfin1 : Module.finrank ℝ (vectorSpan ℝ (Set.range (facetPts w b L U I ε))) = η + 1 :=
    hAI.finrank_vectorSpan hcard
  have hlow : η + 1 ≤ Module.finrank ℝ (vectorSpan ℝ face) := by
    rw [← hfin1]
    exact Submodule.finrank_mono (vectorSpan_mono ℝ hrange)
  have hspan : vectorSpan ℝ face ≤ LinearMap.ker ℓ := by
    rw [vectorSpan_def]
    apply Submodule.span_le.2
    rintro v ⟨p, hp, q, hq, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, vsub_eq_sub, map_sub]
    have h1 := hp.2
    have h2 := hq.2
    simp only [Set.mem_setOf_eq, hg] at h1 h2
    linarith
  have hrange_top : LinearMap.range ℓ = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro r
    refine ⟨(0, r, 0), ?_⟩
    simp [hℓ]
  have hker : Module.finrank ℝ (LinearMap.ker ℓ) = η + 1 := by
    have := LinearMap.finrank_range_add_finrank_ker ℓ
    rw [hrange_top, finrank_top] at this
    simp at this
    omega
  have hup : Module.finrank ℝ (vectorSpan ℝ face) ≤ η + 1 := by
    rw [← hker]; exact Submodule.finrank_mono hspan
  have hfaceDim : Module.finrank ℝ (vectorSpan ℝ face) = η + 1 := le_antisymm hup hlow
  -- a point strictly inside
  have hsupp : ∃ i0, w i0 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hm, hp⟩ := hSA
    have h1 : Mminus w b L U = b := by simp [Mminus, hcon]
    have h2 : Mplus w b L U = b := by simp [Mplus, hcon]
    linarith
  obtain ⟨i0, hi0⟩ := hsupp
  have hi0s : i0 ∈ ReluMIP.Ideal.supp w := by simp [ReluMIP.Ideal.supp, hi0]
  obtain ⟨I', hI', hI'mem⟩ : ∃ I' : Finset (Fin η), I' ⊆ ReluMIP.Ideal.supp w ∧ (i0 ∈ I' ↔ i0 ∉ I) := by
    by_cases h : i0 ∈ I
    · refine ⟨I.erase i0, ?_, ?_⟩
      · exact (Finset.erase_subset _ _).trans hI
      · simp [h]
    · refine ⟨insert i0 I, ?_, ?_⟩
      · exact Finset.insert_subset hi0s hI
      · simp [h]
  obtain ⟨ε', hε', hft'⟩ := RMF_ft w b L U hLU hSA I' hI'
  have hq_mem : facetPts w b L U I' ε' (Sum.inr i0) ∈ convexHull ℝ (form6 w b L U) :=
    subset_convexHull ℝ _ (hft' _).1
  have hw : w i0 * (ε' * inward w i0) = ε' * |w i0| := by rw [mul_left_comm, RMF_winward]
  have hpos : 0 < ε' * |w i0| := mul_pos hε' (abs_pos.2 hi0)
  have hq_neg : (facetPts w b L U I' ε' (Sum.inr i0)).2.1 -
      ReluMIP.Ideal.rhs6b w b L U I (facetPts w b L U I' ε' (Sum.inr i0)).1
        (facetPts w b L U I' ε' (Sum.inr i0)).2.2 < 0 := by
    by_cases h : i0 ∈ I'
    · have hn : i0 ∉ I := fun h' => (hI'mem.1 h) h'
      have hpt : facetPts w b L U I' ε' (Sum.inr i0) =
          (Ubrev w L U - Pi.single i0 (ε' * inward w i0),
            affineFn w b (Ubrev w L U - Pi.single i0 (ε' * inward w i0)), 1) := by
        simp [facetPts, h]
      rw [hpt]
      show affineFn w b (Ubrev w L U - Pi.single i0 (ε' * inward w i0)) -
        rhs6b w b L U I (Ubrev w L U - Pi.single i0 (ε' * inward w i0)) 1 < 0
      rw [RMF_rhs_U_step, if_neg hn, RMF_aff_U, hw]
      have : Mplus w b L U = affineFn w b (Ubrev w L U) := rfl
      linarith
    · have hn : i0 ∈ I := by
        by_contra h'
        exact h (hI'mem.2 h')
      have hpt : facetPts w b L U I' ε' (Sum.inr i0) =
          (Lbrev w L U + Pi.single i0 (ε' * inward w i0), 0, 0) := by
        simp [facetPts, h]
      rw [hpt]
      dsimp only
      rw [RMF_rhs_L_step, if_pos hn, hw]
      linarith
  -- strict dimension jump
  have hp0 := hpt_mem (Sum.inl 0)
  have hp0g := hpt_tight (Sum.inl 0)
  have hlt : vectorSpan ℝ face < vectorSpan ℝ (convexHull ℝ (form6 w b L U)) := by
    refine lt_of_le_of_ne (vectorSpan_mono ℝ Set.inter_subset_left) ?_
    intro heq
    have hv : (facetPts w b L U I' ε' (Sum.inr i0)) -ᵥ (facetPts w b L U I ε (Sum.inl 0)) ∈
        vectorSpan ℝ (convexHull ℝ (form6 w b L U)) := vsub_mem_vectorSpan ℝ hq_mem hp0
    rw [← heq] at hv
    have := hspan hv
    simp only [LinearMap.mem_ker, vsub_eq_sub, map_sub] at this
    have h1 := hg (facetPts w b L U I' ε' (Sum.inr i0))
    have h2 := hg (facetPts w b L U I ε (Sum.inl 0))
    linarith
  have hlt' := Submodule.finrank_lt_finrank_of_lt hlt
  have hle_amb : Module.finrank ℝ (vectorSpan ℝ (convexHull ℝ (form6 w b L U))) ≤ η + 2 := by
    have := Submodule.finrank_le (vectorSpan ℝ (convexHull ℝ (form6 w b L U)))
    simpa [Module.finrank_prod, Module.finrank_fin_fun, add_assoc] using this
  refine ⟨hvalid', ⟨_, hp0, hp0g⟩, ?_⟩
  show Module.finrank ℝ (vectorSpan ℝ face) + 1 =
    Module.finrank ℝ (vectorSpan ℝ (convexHull ℝ (form6 w b L U)))
  omega
