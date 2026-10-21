-- Prove2me | solution 1 for ReluMIP.Facet.facet_points_affineIndependent
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:51:11.941629+00:00
-- url     : https://prove2.me/submissions/760fa611-8a8a-4234-9d8e-5caf43d9b12f

import Mathlib
import Definitions.Def_ReluMIP_Facet_Setting

set_option autoImplicit false
open ReluMIP.Facet

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

theorem solution {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ)
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
