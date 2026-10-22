-- Prove2me | solution 1 for ObfImpossibility.PseudoOracle.triangle_chain
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:42:39.700207+00:00
-- url     : https://prove2.me/submissions/1ac10f3b-0794-4517-85b1-295f89adad1f

import Mathlib
import Definitions.Def_ObfImpossibility_PseudoOracle_Setting

set_option autoImplicit false
open ObfImpossibility.PseudoOracle Filter

lemma obf_real (a1 a2 t s : ℝ) (ht : 0 < t) (hts : t ≤ s) (h1 : 0 ≤ a1) (h2 : a1 ≤ t)
    (h3 : a1 ≤ a2) (h4 : a2 ≤ a1 + (s - t)) : |a1 / t - a2 / s| ≤ (s - t) / s := by
  have hs : 0 < s := lt_of_lt_of_le ht hts
  rw [abs_le]
  constructor
  · have e : (a1 / t - a2 / s) + (s - t) / s = (a1 * s - a2 * t + t * (s - t)) / (t * s) := by
      field_simp
    have hnum : 0 ≤ a1 * s - a2 * t + t * (s - t) := by
      nlinarith [mul_nonneg h1 (sub_nonneg.2 hts), mul_nonneg ht.le (sub_nonneg.2 h4)]
    have := div_nonneg hnum (mul_pos ht hs).le
    linarith
  · have e : (s - t) / s - (a1 / t - a2 / s) = (t * (s - t) - a1 * s + a2 * t) / (t * s) := by
      field_simp
      ring
    have hnum : 0 ≤ t * (s - t) - a1 * s + a2 * t := by
      nlinarith [mul_nonneg (sub_nonneg.2 hts) (sub_nonneg.2 h2), mul_nonneg ht.le (sub_nonneg.2 h3)]
    have := div_nonneg hnum (mul_pos ht hs).le
    linarith

lemma obf_avg_sub {α : Type} [DecidableEq α] (U T : Finset α) (f : α → Bool) (hT : T ⊆ U) :
    |avg T f - avg U f| ≤ ((U.card : ℝ) - T.card) / U.card := by
  have hTU : T.card ≤ U.card := Finset.card_le_card hT
  have ha1 : (T.filter fun a => f a = true).card ≤ T.card := Finset.card_filter_le _ _
  have ha2 : (U.filter fun a => f a = true).card ≤ U.card := Finset.card_filter_le _ _
  by_cases hU0 : U.card = 0
  · have : T.card = 0 := by omega
    simp [avg, hU0, this]
  by_cases hT0 : T.card = 0
  · have h1 : (T.filter fun a => f a = true).card = 0 := by omega
    have hUpos : (0 : ℝ) < U.card := by exact_mod_cast Nat.pos_of_ne_zero hU0
    have hle : ((U.filter fun a => f a = true).card : ℝ) ≤ U.card := by exact_mod_cast ha2
    simp only [avg, h1, hT0, Nat.cast_zero, zero_div, zero_sub, abs_neg, sub_zero]
    rw [abs_of_nonneg (by positivity), div_le_div_iff_of_pos_right hUpos]
    exact hle
  · have ht : (0 : ℝ) < T.card := by exact_mod_cast Nat.pos_of_ne_zero hT0
    have hts : (T.card : ℝ) ≤ U.card := by exact_mod_cast hTU
    have h3 : (T.filter fun a => f a = true).card ≤ (U.filter fun a => f a = true).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ hT)
    have h4 : (U.filter fun a => f a = true).card
        ≤ (T.filter fun a => f a = true).card + (U.card - T.card) := by
      calc (U.filter fun a => f a = true).card
          ≤ ((T.filter fun a => f a = true) ∪ (U \ T)).card := by
            apply Finset.card_le_card
            intro x hx
            simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff] at hx ⊢
            by_cases hxT : x ∈ T
            · left; exact ⟨hxT, hx.2⟩
            · right; exact ⟨hx.1, hxT⟩
        _ ≤ (T.filter fun a => f a = true).card + (U \ T).card := Finset.card_union_le _ _
        _ = _ := by rw [Finset.card_sdiff_of_subset hT]
    have h4' : ((U.filter fun a => f a = true).card : ℝ)
        ≤ (T.filter fun a => f a = true).card + ((U.card : ℝ) - T.card) := by
      have := (Nat.cast_le (α := ℝ)).mpr h4
      rw [Nat.cast_add, Nat.cast_sub hTU] at this
      exact this
    exact obf_real _ _ _ _ ht hts (Nat.cast_nonneg _) (by exact_mod_cast ha1)
      (by exact_mod_cast h3) h4'

theorem solution :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∃ K₀ : ℕ, ∀ K L : ℕ, K₀ ≤ K → K ^ 2 ≤ L →
      ∀ (D : Fin L → QTree K L) (G : Fin K ↪ Fin L) (S SG : Finset (Fin K)),
        SG ⊆ S →
        (1 - (K : ℝ) ^ (-(3 * δ))) * (S.card : ℝ) ≤ (SG.card : ℝ) →
        1 / (K : ℝ) ^ δ < |prX D G - prY D G| →
        |avg S (fun x => (D (G x)).run G) - prX D G| ≤ 1 / (4 * (K : ℝ) ^ δ) →
        |prX D G - prY D G|
            - |avg SG (fun x => (D (G x)).run G) - avg S (fun x => (D (G x)).run G)|
            - |avg S (fun x => (D (G x)).run G) - prX D G|
            - |prY D G - avg (LG G SG) (fun y => (D y).run G)|
          ≤ |avg SG (fun x => (D (G x)).run G) - avg (LG G SG) (fun y => (D y).run G)| ∧
        1 / (2 * (K : ℝ) ^ δ) <
          |avg SG (fun x => (D (G x)).run G) - avg (LG G SG) (fun y => (D y).run G)| := by
  intro δ hδ hδ1
  have e1 : ∀ᶠ K : ℕ in atTop, (3 : ℝ) ≤ (K : ℝ) ^ δ :=
    ((tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 3
  have e2 : ∀ᶠ K : ℕ in atTop, (8 : ℝ) ≤ (K : ℝ) ^ (1 - δ) :=
    ((tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 - δ)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop 8
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp (e1.and (e2.and (eventually_ge_atTop 2)))
  refine ⟨K₀, fun K L hK hKL D G S SG hSG hcard hgap hc => ?_⟩
  obtain ⟨hq3, hq8, hK2⟩ := hK₀ K hK
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  set q : ℝ := (K : ℝ) ^ δ with hq
  have hqpos : 0 < q := by positivity
  have hKq : (K : ℝ) = (K : ℝ) ^ (1 - δ) * q := by
    rw [hq, ← Real.rpow_add hKpos]; simp
  have hKge : 8 * q ≤ (K : ℝ) := by
    rw [hKq]; exact mul_le_mul_of_nonneg_right hq8 hqpos.le
  -- the gamma bound
  have hγ : (K : ℝ) ^ (-(3 * δ)) = 1 / q ^ 3 := by
    rw [hq, Real.rpow_neg hKpos.le, one_div, ← Real.rpow_natCast, ← Real.rpow_mul hKpos.le]
    norm_num
    ring_nf
  have hγ1 : (K : ℝ) ^ (-(3 * δ)) ≤ 1 / (8 * q) := by
    rw [hγ, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg q]
  -- b bound
  set f : Fin K → Bool := fun x => (D (G x)).run G with hf
  have hb : |avg SG f - avg S f| ≤ 1 / (8 * q) := by
    refine (obf_avg_sub S SG f hSG).trans ?_
    by_cases hS0 : S.card = 0
    · simp [hS0]; positivity
    · have hSpos : (0 : ℝ) < S.card := by exact_mod_cast Nat.pos_of_ne_zero hS0
      rw [div_le_iff₀ hSpos]
      have : (S.card : ℝ) - SG.card ≤ (K : ℝ) ^ (-(3 * δ)) * S.card := by nlinarith
      calc (S.card : ℝ) - SG.card ≤ (K : ℝ) ^ (-(3 * δ)) * S.card := this
        _ ≤ 1 / (8 * q) * S.card := mul_le_mul_of_nonneg_right hγ1 hSpos.le
  -- d bound
  have hMcard : (LG G SG).card + ((Finset.univ \ SG).map G).card = L := by
    unfold LG
    rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _)]
    simp
  have hM : ((Finset.univ \ SG).map G).card ≤ K := by
    rw [Finset.card_map]
    calc (Finset.univ \ SG).card ≤ (Finset.univ : Finset (Fin K)).card := Finset.card_le_card (Finset.sdiff_subset)
      _ = K := by simp
  have hLpos : (0 : ℝ) < L := by
    have : 0 < L := lt_of_lt_of_le (by positivity) hKL
    exact_mod_cast this
  have hd : |prY D G - avg (LG G SG) (fun y => (D y).run G)| ≤ 1 / (8 * q) := by
    have hsub := obf_avg_sub (Finset.univ : Finset (Fin L)) (LG G SG) (fun y => (D y).run G)
      (Finset.subset_univ _)
    rw [abs_sub_comm] at hsub
    refine hsub.trans ?_
    have hLG : ((Finset.univ : Finset (Fin L)).card : ℝ) - (LG G SG).card
        = (((Finset.univ \ SG).map G).card : ℝ) := by
      have : (Finset.univ : Finset (Fin L)).card = L := by simp
      rw [this]
      have : ((LG G SG).card : ℝ) + (((Finset.univ \ SG).map G).card : ℝ) = L := by exact_mod_cast hMcard
      linarith
    rw [hLG, show ((Finset.univ : Finset (Fin L)).card : ℝ) = L by simp]
    rw [div_le_div_iff₀ hLpos (by positivity)]
    have hMK : (((Finset.univ \ SG).map G).card : ℝ) ≤ K := by exact_mod_cast hM
    have hKL' : ((K : ℝ)) ^ 2 ≤ L := by exact_mod_cast hKL
    nlinarith
  -- assemble
  have t1 := abs_sub_le (prX D G) (avg S f) (prY D G)
  have t2 := abs_sub_le (avg S f) (avg SG f) (prY D G)
  have t3 := abs_sub_le (avg SG f) (avg (LG G SG) (fun y => (D y).run G)) (prY D G)
  have c1 := abs_sub_comm (avg S f) (prX D G)
  have c2 := abs_sub_comm (avg S f) (avg SG f)
  have c3 := abs_sub_comm (avg (LG G SG) (fun y => (D y).run G)) (prY D G)
  have hq1 : 1 / (4 * q) = 2 * (1 / (8 * q)) := by field_simp; ring
  refine ⟨?_, ?_⟩
  · linarith [abs_sub_comm (avg SG f) (avg S f)]
  · have hqq : 1 / q = 8 * (1 / (8 * q)) := by field_simp
    have hhalf : 1 / (2 * q) = 4 * (1 / (8 * q)) := by field_simp; ring
    rw [hhalf]
    rw [hqq] at hgap
    rw [hq1] at hc
    linarith [abs_sub_comm (avg SG f) (avg S f)]
