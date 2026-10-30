-- Prove2me | solution 1 for ZhangTangLabelCut.LP2.configuration_count
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T06:06:47.680195+00:00
-- url     : https://prove2.me/submissions/aa893d9d-437e-420c-a075-6afcf1732118

import Mathlib
import Definitions.Def_ZhangTangLabelCut_LP2_Configurations

set_option autoImplicit false

namespace ZhangTangLabelCut.LP2

open Finset in
lemma card_small_subsets (d m : ℕ) (hd : 1 ≤ d) :
    ((Finset.univ : Finset (Finset (Fin d))).filter (fun s => s.card ≤ m)).card ≤ (m + 1) * d ^ m := by
  classical
  have hsub : ((Finset.univ : Finset (Finset (Fin d))).filter (fun s => s.card ≤ m)) ⊆
      (Finset.range (m + 1)).biUnion (fun i => Finset.powersetCard i (Finset.univ : Finset (Fin d))) := by
    intro s hs
    have hs' := (Finset.mem_filter.1 hs).2
    refine Finset.mem_biUnion.2 ⟨s.card, Finset.mem_range.2 (by omega), ?_⟩
    exact Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, rfl⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ i ∈ Finset.range (m + 1), (Finset.powersetCard i (Finset.univ : Finset (Fin d))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ i ∈ Finset.range (m + 1), d ^ m := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
        calc d.choose i ≤ d ^ i := Nat.choose_le_pow d i
          _ ≤ d ^ m := Nat.pow_le_pow_right hd (by have := Finset.mem_range.1 hi; omega)
    _ = (m + 1) * d ^ m := by simp

def Phi {k d : ℕ} (F : Finset (Fin k × Fin d)) : Fin k → Finset (Fin d) :=
  fun μ => (F.filter (fun l => l.1 = μ)).image Prod.snd

lemma mem_Phi {k d : ℕ} (F : Finset (Fin k × Fin d)) (μ : Fin k) (x : Fin d) :
    x ∈ Phi F μ ↔ (μ, x) ∈ F := by
  unfold Phi
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨y, ⟨hy, h1⟩, h2⟩
    have : y = (μ, x) := Prod.ext h1 h2
    rw [← this]; exact hy
  · intro h
    exact ⟨(μ, x), ⟨h, rfl⟩, rfl⟩

lemma Phi_inj {k d : ℕ} (F G : Finset (Fin k × Fin d)) (h : Phi F = Phi G) : F = G := by
  ext ⟨μ, x⟩
  rw [← mem_Phi, ← mem_Phi, h]

lemma Phi_card {k d : ℕ} (S : Finset (Fin k × Fin d)) (μ : Fin k) :
    (Phi (configuration S) μ).card ≤ ⌊4 * average k S.card⌋₊ := by
  classical
  by_cases hμ : μ ∈ light S
  · unfold Phi
    refine le_trans Finset.card_image_le ?_
    apply Nat.le_floor
    have h1 : ((configuration S).filter (fun l => l.1 = μ)) = S.filter (fun l => l.1 = μ) := by
      ext l
      simp only [configuration, Finset.mem_filter]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3 ▸ hμ⟩, h3⟩
    rw [h1]
    have h2 := (Finset.mem_filter.1 hμ).2
    simpa [counts] using h2
  · have : Phi (configuration S) μ = ∅ := by
      ext x
      rw [mem_Phi]
      simp only [Finset.notMem_empty, iff_false]
      intro hx
      simp only [configuration, Finset.mem_filter] at hx
      exact hμ hx.2
    rw [this]; simp

lemma cc_aux (k d c : ℕ) (hd : 1 ≤ d) (hc : 0 < c) :
    ((configurations k d c).card : ℝ) ≤ countBound k (average k c) d := by
  classical
  set m := ⌊4 * average k c⌋₊ with hm
  set B : Finset (Finset (Fin d)) := (Finset.univ : Finset (Finset (Fin d))).filter (fun s => s.card ≤ m)
    with hB
  have hcard : (configurations k d c).card ≤ (Fintype.piFinset (fun _ : Fin k => B)).card := by
    apply Finset.card_le_card_of_injOn Phi
    · intro F hF
      unfold configurations at hF
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_univ, true_and] at hF
      obtain ⟨S, hS, rfl⟩ := hF
      rw [Finset.mem_coe, Fintype.mem_piFinset]
      intro μ
      rw [hB, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have := Phi_card S μ
      rw [hS] at this
      exact this
    · intro F _ G _ h
      exact Phi_inj F G h
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hcard
  have hB1 : B.card ≤ (m + 1) * d ^ m := card_small_subsets d m hd
  have hk : (configurations k d c).card ≤ ((m + 1) * d ^ m) ^ k :=
    le_trans hcard (Nat.pow_le_pow_left hB1 k)
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set a := average k c with ha
  have ha0 : 0 ≤ a := by
    rw [ha]; unfold average; positivity
  have hm1 : ((m : ℝ)) ≤ 4 * a := Nat.floor_le (by positivity)
  have hreal : ((configurations k d c).card : ℝ) ≤ (((m : ℝ) + 1) * (d : ℝ) ^ m) ^ k := by
    exact_mod_cast hk
  refine le_trans hreal ?_
  unfold countBound
  have hd0 : (0 : ℝ) ≤ d := by linarith
  rw [Real.rpow_natCast, Real.rpow_mul hd0, Real.rpow_natCast, ← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  apply mul_le_mul (by linarith) _ (by positivity) (by linarith)
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le hdR (by linarith)

theorem configuration_count_aux (k d c : ℕ) (hk : 2 ≤ k) (hc : 0 < c)
    (hreg : 8 * average k c < (d : ℝ)) :
    ((configurations k d c).card : ℝ) ≤ countBound k (average k c) d := by
  have ha : 0 ≤ average k c := by unfold average; positivity
  have hd : 1 ≤ d := by
    by_contra h
    have : d = 0 := by omega
    subst this
    simp at hreg
    linarith
  exact cc_aux k d c hd hc

end ZhangTangLabelCut.LP2

theorem solution (k d c : ℕ) (hk : 2 ≤ k) (hc : 0 < c)
    (hreg : 8 * ZhangTangLabelCut.LP2.average k c < (d : ℝ)) :
    ((ZhangTangLabelCut.LP2.configurations k d c).card : ℝ) ≤
      ZhangTangLabelCut.LP2.countBound k (ZhangTangLabelCut.LP2.average k c) d :=
  ZhangTangLabelCut.LP2.configuration_count_aux k d c hk hc hreg
