-- Prove2me | solution 1 for UniversalSubmod.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:47:07.345649+00:00
-- url     : https://prove2.me/submissions/2c9a82c6-d92d-44bb-8cf3-bec218f690df

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Theorems.Thm_UniversalSubmod_concavity_segment

section
set_option autoImplicit false

namespace UniversalSubmod.Dev.Lemma21

open NonmonotoneSubmod.Shared

variable {n : ℕ}

lemma F_nonneg (f : Finset (Fin n) → ℝ) (hf0 : ∀ S, 0 ≤ f S) (x : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ F f x := by
  unfold F
  refine Finset.sum_nonneg (fun S _ => mul_nonneg (hf0 S) (Finset.prod_nonneg (fun l _ => ?_)))
  split_ifs
  · exact (hx l).1
  · linarith [(hx l).2]

lemma F_ind (f : Finset (Fin n) → ℝ) (S : Finset (Fin n)) :
    F f (fun i => if i ∈ S then (1 : ℝ) else 0) = f S := by
  unfold F
  rw [Finset.sum_eq_single S]
  · have : ∏ i : Fin n, (if i ∈ S then (if i ∈ S then (1 : ℝ) else 0)
        else 1 - (if i ∈ S then (1 : ℝ) else 0)) = 1 := by
      refine Finset.prod_eq_one (fun i _ => ?_)
      by_cases h : i ∈ S <;> simp [h]
    rw [this, mul_one]
  · intro T _ hT
    have : ∏ i : Fin n, (if i ∈ T then (if i ∈ S then (1 : ℝ) else 0)
        else 1 - (if i ∈ S then (1 : ℝ) else 0)) = 0 := by
      have : ∃ i, ¬ (i ∈ T ↔ i ∈ S) := by
        by_contra hc
        push Not at hc
        exact hT (Finset.ext hc)
      obtain ⟨i, hi⟩ := this
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      by_cases h1 : i ∈ T <;> by_cases h2 : i ∈ S <;> simp_all
    rw [this, mul_zero]
  · intro h; exact absurd (Finset.mem_univ S) h

lemma concave_ineq (g : ℝ → ℝ) (hg : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) g) (p : ℝ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) : (1 - p) * g 0 + p * g 1 ≤ g p := by
  have := hg.2 (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp) (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp)
    (show 0 ≤ 1 - p by linarith) hp0 (show (1 - p) + p = 1 by ring)
  simpa using this

end UniversalSubmod.Dev.Lemma21

namespace UniversalSubmod

open NonmonotoneSubmod.Shared

theorem chk_lemma_2_1 {n : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p * (1 - p) * OPT f ≤ F f (fun _ => p) := by
  obtain ⟨S, -, hS⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Finset (Fin n))) f
  have hOPT : OPT f = f S := hS
  rw [hOPT]
  set a : Fin n → ℝ := fun i => if i ∈ S then 0 else p with ha
  set b : Fin n → ℝ := fun i => if i ∈ S then 1 else p with hb
  set c : Fin n → ℝ := fun i => if i ∈ S then 1 else 0 with hc
  have ha_box : ∀ i, a i ∈ Set.Icc (0 : ℝ) 1 := fun i => by
    by_cases h : i ∈ S <;> simp [ha, h, hp0, hp1]
  have hb_box : ∀ i, b i ∈ Set.Icc (0 : ℝ) 1 := fun i => by
    by_cases h : i ∈ S <;> simp [hb, h, hp0, hp1]
  have hc_box : ∀ i, c i ∈ Set.Icc (0 : ℝ) 1 := fun i => by
    by_cases h : i ∈ S <;> simp [hc, h]
  have h1_box : ∀ i : Fin n, (1 : Fin n → ℝ) i ∈ Set.Icc (0 : ℝ) 1 := fun i => by simp
  have hab : ∀ i, a i ≤ b i := fun i => by
    by_cases h : i ∈ S <;> simp [ha, hb, h, hp0, hp1]
  have hc1 : ∀ i, c i ≤ (1 : Fin n → ℝ) i := fun i => by
    by_cases h : i ∈ S <;> simp [hc, h]
  have seg1 := (concavity_segment f hf0 hf).2 a b ha_box hb_box hab
  have seg2 := (concavity_segment f hf0 hf).2 c 1 hc_box h1_box hc1
  have i1 := Dev.Lemma21.concave_ineq _ seg1 p hp0 hp1
  have i2 := Dev.Lemma21.concave_ineq _ seg2 p hp0 hp1
  have e1 : a + p • (b - a) = fun _ => p := by
    ext i; by_cases h : i ∈ S <;> simp [ha, hb, h]
  have e2 : a + (0 : ℝ) • (b - a) = a := by simp
  have e3 : a + (1 : ℝ) • (b - a) = b := by simp
  have e4 : c + p • ((1 : Fin n → ℝ) - c) = b := by
    ext i; by_cases h : i ∈ S <;> simp [hc, hb, h]
  have e5 : c + (0 : ℝ) • ((1 : Fin n → ℝ) - c) = c := by simp
  have e6 : c + (1 : ℝ) • ((1 : Fin n → ℝ) - c) = 1 := by simp
  simp only [e1, e2, e3, e4, e5, e6] at i1 i2
  have hFa := Dev.Lemma21.F_nonneg f hf0 a ha_box
  have hF1 := Dev.Lemma21.F_nonneg f hf0 1 h1_box
  have hFc : F f c = f S := Dev.Lemma21.F_ind f S
  have hfS := hf0 S
  nlinarith [mul_nonneg hp0 hFa, mul_nonneg hp0 (sub_nonneg.2 hp1), mul_nonneg hp0 hF1,
    mul_nonneg hp0 hfS]

end UniversalSubmod
end

theorem solution : type_of% @UniversalSubmod.chk_lemma_2_1 := @UniversalSubmod.chk_lemma_2_1
