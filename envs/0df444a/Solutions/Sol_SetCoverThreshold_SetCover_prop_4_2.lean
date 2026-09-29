-- Prove2me | solution 1 for SetCoverThreshold.SetCover.prop_4_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:47:21.082285+00:00
-- url     : https://prove2.me/submissions/0e737b6b-c155-4f40-8c42-b453d45cc142

import Mathlib
import Definitions.Def_SetCoverThreshold_SetCover_Formula
import Definitions.Def_SetCoverThreshold_SetCover_ProofSystem
import Definitions.Def_SetCoverThreshold_SetCover_Reduction

namespace SetCoverThreshold.SetCover

lemma aux_p42_threeM (φ : Formula5) : 3 * φ.M = 5 * φ.n := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (f := fun cp : Fin φ.M × Fin 3 => (φ.clause cp.1 cp.2).2)
    (s := Finset.univ) (t := Finset.univ) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h
  rw [mul_comm, h]
  simp [φ.five, mul_comm]

lemma aux_p42_count (φ : Formula5) {ℓ k : ℕ} (code : Fin k → Fin ℓ → Bool) (i : Fin k)
    (q : φ.ProverQuestion code i) :
    (Finset.univ.filter (fun r : φ.RandomString ℓ => φ.question code r i = q.1)).card =
      ∏ j, (if code i j = true then 3 else 5) := by
  classical
  have : (Finset.univ.filter (fun r : φ.RandomString ℓ => φ.question code r i = q.1)) =
      Fintype.piFinset (fun j => Finset.univ.filter (fun p : Fin φ.M × Fin 3 =>
        (if code i j = true then Sum.inl p.1 else Sum.inr (φ.var p.1 p.2)) = q.1 j)) := by
    ext r
    simp [Fintype.mem_piFinset, Formula5.question, funext_iff]
  rw [this, Fintype.card_piFinset]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  have hq := q.2 j
  cases hc : code i j
  · rw [hc] at hq
    obtain ⟨v, hv⟩ : ∃ v, q.1 j = Sum.inr v := by
      cases h : q.1 j with
      | inl c => rw [h] at hq; simp at hq
      | inr v => exact ⟨v, rfl⟩
    simp only [hv, Bool.false_eq_true, if_false, Sum.inr.injEq]
    exact φ.five v
  · rw [hc] at hq
    obtain ⟨c, hcq⟩ : ∃ c, q.1 j = Sum.inl c := by
      cases h : q.1 j with
      | inl c => exact ⟨c, rfl⟩
      | inr v => rw [h] at hq; simp at hq
    simp only [hcq, if_true, Sum.inl.injEq]
    have : (Finset.univ.filter (fun p : Fin φ.M × Fin 3 => p.1 = c)) =
        ({c} : Finset (Fin φ.M)) ×ˢ (Finset.univ : Finset (Fin 3)) := by
      ext ⟨p1, p2⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
        Finset.mem_singleton, and_true]
    rw [this, Finset.card_product]
    simp

end SetCoverThreshold.SetCover

open SetCoverThreshold.SetCover

theorem solution (φ : Formula5) (ℓ k m : ℕ) (code : Fin k → Fin ℓ → Bool)
    (hcode : IsCode ℓ k code) (hk : 0 < k) (hm : 2 ≤ m)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (𝒞 : Finset (φ.SetIdx code))
    (h𝒞 : (𝒞.card : ℝ) ≤ (1 - δ) * k * φ.numQuestions ℓ * Real.log m) :
    δ / 2 ≤
      ((Finset.univ.filter (fun r : φ.RandomString ℓ =>
          (φ.weight code 𝒞 r : ℝ) < (1 - δ / 2) * k * Real.log m)).card : ℝ) /
        Fintype.card (φ.RandomString ℓ) := by
  classical
  obtain ⟨hw, -⟩ := hcode
  have hℓ : ℓ = 2 * (ℓ / 2) := by have := hw ⟨0, hk⟩; omega
  set a := ℓ / 2 with ha
  have hcount : ∀ (i : Fin k) (q : φ.ProverQuestion code i),
      (Finset.univ.filter (fun r : φ.RandomString ℓ => φ.question code r i = q.1)).card
        = 15 ^ a := by
    intro i q
    rw [aux_p42_count, Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    have h1 := hw i
    have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin ℓ)))
      (fun j => code i j = true)
    simp only [Finset.card_univ, Fintype.card_fin] at h2
    have e1 : (Finset.univ.filter (fun j => code i j = true)).card = a := by omega
    have e2 : (Finset.univ.filter (fun j => ¬ code i j = true)).card = a := by omega
    rw [e1, e2, ← mul_pow]
    norm_num
  have hsum : ∑ r : φ.RandomString ℓ, φ.weight code 𝒞 r = 𝒞.card * 15 ^ a := by
    simp only [Formula5.weight, Finset.card_filter]
    rw [Finset.sum_comm]
    simp_rw [← Finset.card_filter]
    rw [Finset.sum_congr rfl (fun x _ => hcount x.1 x.2.1), Finset.sum_const, smul_eq_mul]
  have h3 := aux_p42_threeM φ
  have hMpos := φ.M_pos
  have hnpos : 0 < φ.n := by omega
  have hR : Fintype.card (φ.RandomString ℓ) = (φ.M * 3) ^ ℓ := by simp
  have hkey : 15 ^ a * φ.numQuestions ℓ = Fintype.card (φ.RandomString ℓ) := by
    rw [hR, Formula5.numQuestions, ← ha, hℓ, pow_mul, ← mul_pow, ← mul_pow]
    congr 1
    nlinarith
  -- real-valued Markov argument
  set w : φ.RandomString ℓ → ℕ := fun r => φ.weight code 𝒞 r with hwdef
  set A : ℝ := (1 - δ / 2) * k * Real.log m with hA
  set R : ℝ := (Fintype.card (φ.RandomString ℓ) : ℝ) with hRdef
  set Nq : ℝ := (φ.numQuestions ℓ : ℝ) with hNq
  have hRpos : 0 < R := by
    rw [hRdef, hR]; positivity
  have hNqpos : 0 < Nq := by
    rw [hNq, Formula5.numQuestions]; positivity
  have hlog : 0 < Real.log m := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  set K : ℝ := (k : ℝ) * Real.log m with hK
  have hKpos : 0 < K := mul_pos hkpos hlog
  have hAK : A = (1 - δ / 2) * K := by rw [hA, hK]; ring
  have hsumR : (∑ r, (w r : ℝ)) * Nq = (𝒞.card : ℝ) * R := by
    have : ((∑ r, w r : ℕ) : ℝ) * Nq = (𝒞.card : ℝ) * R := by
      rw [hsum, hNq, hRdef, ← hkey]; push_cast; ring
    simpa using this
  have hsumle : (∑ r, (w r : ℝ)) ≤ (1 - δ) * K * R := by
    have h𝒞' : (𝒞.card : ℝ) ≤ (1 - δ) * K * Nq := by
      rw [hK]; nlinarith [h𝒞]
    have : (∑ r, (w r : ℝ)) * Nq ≤ ((1 - δ) * K * R) * Nq := by
      rw [hsumR]; nlinarith
    exact le_of_mul_le_mul_right this hNqpos
  set S := Finset.univ.filter (fun r : φ.RandomString ℓ => (w r : ℝ) < A) with hS
  set T := Finset.univ.filter (fun r : φ.RandomString ℓ => ¬ (w r : ℝ) < A) with hT
  have hST : (S.card : ℝ) + T.card = R := by
    have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun r : φ.RandomString ℓ => (w r : ℝ) < A)
    rw [Finset.card_univ] at this
    rw [hRdef, hS, hT, ← this]
    push_cast
    rfl
  have hmarkov : (T.card : ℝ) * A ≤ ∑ r, (w r : ℝ) := by
    calc (T.card : ℝ) * A = ∑ r ∈ T, A := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ r ∈ T, (w r : ℝ) := Finset.sum_le_sum (fun r hr => by
          rw [hT, Finset.mem_filter] at hr; linarith [hr.2])
      _ ≤ ∑ r, (w r : ℝ) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => by positivity)
  have hSnn : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have key : δ / 2 * R ≤ S.card := by
    have h1 : (T.card : ℝ) * (1 - δ / 2) * K ≤ (1 - δ) * K * R := by
      have := le_trans hmarkov hsumle
      rw [hAK] at this; linarith
    have h2 : (T.card : ℝ) * (1 - δ / 2) ≤ (1 - δ) * R := by
      have : ((T.card : ℝ) * (1 - δ / 2)) * K ≤ ((1 - δ) * R) * K := by linarith
      exact le_of_mul_le_mul_right this hKpos
    have hT' : (T.card : ℝ) = R - S.card := by linarith
    rw [hT'] at h2
    nlinarith
  show δ / 2 ≤ (S.card : ℝ) / R
  rw [le_div_iff₀ hRpos]
  exact key
