-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.cm_simple_to_regular
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:35:27.836089+00:00
-- url     : https://prove2.me/submissions/82785224-f544-4de8-8ae8-ad273afd912b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PottsRapidMixing_Ensemble
import Definitions.Def_AFIsingKS_Matching
import Definitions.Def_AFIsingKS_toGraph
import Definitions.Def_ZeroFreeRRG_Hardcore_Models
import Theorems.Thm_AFIsingKS_cm_simple_uniform
import Theorems.Thm_AFIsingKS_cm_simple_prob

open scoped Classical
open Filter Topology AFIsingKS
open ZeroFreeRRG.Hardcore

theorem solution (m : Model) (d : ℕ) (hd : 3 ≤ d) (U : Set ℂ)
    (h : Tendsto (fun n => cmProb (fun M : Matching n d => IsSimpleM M →
        ∀ z ∈ U, m.Zgraph d (toGraph M) z ≠ 0))
      (atTop ⊓ 𝓟 {n : ℕ | Even (n * d)}) (𝓝 1)) :
    PottsRapidMixing.WithHighProb d (fun n G => ∀ z ∈ U, m.Zgraph d G z ≠ 0) := by
  classical
  let ℓ := atTop ⊓ 𝓟 {n : ℕ | Even (n * d)}
  let Q : ∀ n : ℕ, SimpleGraph (Fin n) → Prop :=
    fun n G => ∀ z ∈ U, m.Zgraph d G z ≠ 0
  let P (n : ℕ) (M : Matching n d) : Prop := IsSimpleM M → Q n (toGraph M)
  let A (n : ℕ) := Finset.univ.filter
    (fun M : Matching n d => IsSimpleM M ∧ Q n (toGraph M))
  let B (n : ℕ) := Finset.univ.filter (fun M : Matching n d => IsSimpleM M)
  let C (n : ℕ) := Finset.univ.filter
    (fun M : Matching n d => IsSimpleM M ∧ ¬ Q n (toGraph M))
  let T (n : ℕ) : ℕ := Fintype.card (Matching n d)

  have hcount (n : ℕ) (R : SimpleGraph (Fin n) → Prop) :
      (Finset.univ.filter (fun M : Matching n d => IsSimpleM M ∧ R (toGraph M))).card =
        d.factorial ^ n * ((PottsRapidMixing.regularGraphs n d).filter R).card := by
    let RG := PottsRapidMixing.regularGraphs n d
    let s := Finset.univ.filter (fun M : Matching n d => IsSimpleM M ∧ R (toGraph M))
    have hmap : Set.MapsTo (fun M : Matching n d => toGraph M) (s : Set (Matching n d))
        ((RG.filter R : Finset (SimpleGraph (Fin n))) : Set (SimpleGraph (Fin n))) := by
      intro M hM
      simp only [Finset.mem_coe, s, Finset.mem_filter, Finset.mem_univ, true_and] at hM
      simp only [Finset.mem_coe, Finset.mem_filter]
      refine ⟨?_, hM.2⟩
      change toGraph M ∈ PottsRapidMixing.regularGraphs n d
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (AFIsingKS.cm_simple_uniform n d).1 M hM.1⟩
    change s.card = d.factorial ^ n * (RG.filter R).card
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    calc
      (∑ G ∈ RG.filter R, {M ∈ s | toGraph M = G}.card) =
          ∑ _G ∈ RG.filter R, d.factorial ^ n := by
        apply Finset.sum_congr rfl
        intro G hG
        simp only [Finset.mem_filter] at hG
        have heq : {M ∈ s | toGraph M = G} =
            Finset.univ.filter (fun M : Matching n d => IsSimpleM M ∧ toGraph M = G) := by
          ext M
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, s]
          constructor
          · rintro ⟨⟨hS, hR⟩, hEq⟩
            exact ⟨hS, hEq⟩
          · rintro ⟨hS, hEq⟩
            refine ⟨⟨hS, ?_⟩, hEq⟩
            simpa [hEq] using hG.2
        rw [heq]
        exact (AFIsingKS.cm_simple_uniform n d).2 G hG.1
      _ = d.factorial ^ n * (RG.filter R).card := by
        simp [mul_comm]

  have hBcount (n : ℕ) :
      (B n).card = d.factorial ^ n * (PottsRapidMixing.regularGraphs n d).card := by
    simpa [B, PottsRapidMixing.regularGraphs] using hcount n (fun _ => True)

  have hAC (n : ℕ) : (A n).card + (C n).card = (B n).card := by
    simpa [A, B, C, Finset.filter_filter] using
      (Finset.card_filter_add_card_filter_not
        (s := Finset.univ.filter (fun M : Matching n d => IsSimpleM M))
        (fun M => Q n (toGraph M)))

  have hPC (n : ℕ) :
      (Finset.univ.filter (P n)).card + (C n).card = T n := by
    simpa [P, C, T, Classical.not_imp] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Matching n d))) (P n))

  obtain ⟨c, hc, N, hN⟩ := AFIsingKS.cm_simple_prob d hd

  have hsimple (n : ℕ) (hn : N ≤ n) (he : Even (n * d)) :
      c ≤ ((B n).card : ℝ) / (T n) := by
    simpa [B, T, cmProb] using hN n hn he

  have hTpos (n : ℕ) (hn : N ≤ n) (he : Even (n * d)) : 0 < (T n : ℝ) := by
    have hp : 0 < ((B n).card : ℝ) / (T n) := lt_of_lt_of_le hc (hsimple n hn he)
    exact (div_pos_iff.mp hp).resolve_right (fun hneg => (not_lt_of_ge (Nat.cast_nonneg _)) hneg.1) |>.2

  have hBpos (n : ℕ) (hn : N ≤ n) (he : Even (n * d)) : 0 < ((B n).card : ℝ) := by
    exact (div_pos_iff_of_pos_right (hTpos n hn he)).mp
      (lt_of_lt_of_le hc (hsimple n hn he))

  have hreg_ratio (n : ℕ) :
      PottsRapidMixing.regularProb n d (Q n) = ((A n).card : ℝ) / (B n).card := by
    have hk : (d.factorial : ℝ) ^ n ≠ 0 := by positivity
    rw [PottsRapidMixing.regularProb, hcount n (Q n), hBcount n]
    simp only [Nat.cast_mul, Nat.cast_pow]
    exact (mul_div_mul_left
      (((PottsRapidMixing.regularGraphs n d).filter (Q n)).card : ℝ)
      ((PottsRapidMixing.regularGraphs n d).card : ℝ) hk).symm

  change Tendsto (fun n => cmProb (P n)) ℓ (𝓝 1) at h

  have hlarge : ∀ᶠ n in ℓ, N ≤ n :=
    (Filter.eventually_atTop.2 ⟨N, fun _ hn => hn⟩).filter_mono inf_le_left
  have heven : ∀ᶠ n in ℓ, Even (n * d) :=
    Filter.eventually_inf_principal.2 (Filter.Eventually.of_forall fun _ hne => hne)

  have hbad : Tendsto (fun n => ((C n).card : ℝ) / (T n)) ℓ (𝓝 0) := by
    have hh : Tendsto (fun n => 1 - cmProb (P n)) ℓ (𝓝 (1 - 1)) :=
      tendsto_const_nhds.sub h
    have heq : (fun n => 1 - cmProb (P n)) =ᶠ[ℓ]
        (fun n => ((C n).card : ℝ) / (T n)) := by
      filter_upwards [hlarge, heven] with n hn he
      have hp : cmProb (P n) + ((C n).card : ℝ) / (T n) = 1 := by
        have hpc : (Finset.univ.filter (P n)).card + (C n).card =
            Fintype.card (Matching n d) := by
          simpa [T] using hPC n
        have hsum : (((Finset.univ.filter (P n)).card : ℝ) + ((C n).card : ℝ)) =
            (Fintype.card (Matching n d) : ℝ) := by
          exact_mod_cast hpc
        have hden : 0 < (Fintype.card (Matching n d) : ℝ) := by
          simpa [T] using hTpos n hn he
        simp only [cmProb, T]
        rw [← add_div]
        apply (div_eq_one_iff_eq (ne_of_gt hden)).2
        convert hsum using 1
        norm_cast
        apply congrArg (fun k : ℕ => k + (C n).card)
        apply congrArg Finset.card
        ext M
        simp
      linarith
    simpa using hh.congr' heq

  have hscaled : Tendsto (fun n => (1 / c) * (((C n).card : ℝ) / (T n))) ℓ (𝓝 0) := by
    simpa using hbad.const_mul (1 / c)

  have hcomp : Tendsto
      (fun n => 1 - PottsRapidMixing.regularProb n d (Q n)) ℓ (𝓝 0) := by
    apply squeeze_zero' _ _ hscaled
    · filter_upwards [hlarge, heven] with n hn he
      have hp : PottsRapidMixing.regularProb n d (Q n) +
          ((C n).card : ℝ) / (B n).card = 1 := by
        rw [hreg_ratio n, ← add_div, ← Nat.cast_add, hAC n]
        exact div_self (ne_of_gt (hBpos n hn he))
      have hnonneg : 0 ≤ ((C n).card : ℝ) / (B n).card :=
        div_nonneg (Nat.cast_nonneg _) (le_of_lt (hBpos n hn he))
      linarith
    · filter_upwards [hlarge, heven] with n hn he
      have hp : PottsRapidMixing.regularProb n d (Q n) +
          ((C n).card : ℝ) / (B n).card = 1 := by
        rw [hreg_ratio n, ← add_div, ← Nat.cast_add, hAC n]
        exact div_self (ne_of_gt (hBpos n hn he))
      have hrewrite : 1 - PottsRapidMixing.regularProb n d (Q n) =
          ((C n).card : ℝ) / (B n).card := by linarith
      rw [hrewrite]
      calc
        ((C n).card : ℝ) / (B n).card ≤ ((C n).card : ℝ) / (c * (T n)) :=
          div_le_div_of_nonneg_left (Nat.cast_nonneg _)
            (mul_pos hc (hTpos n hn he)) ((le_div_iff₀ (hTpos n hn he)).mp (hsimple n hn he))
        _ = (1 / c) * (((C n).card : ℝ) / (T n)) := by
          rw [div_mul_eq_div_mul_one_div]
          ring

  have hfinal : Tendsto (fun n => PottsRapidMixing.regularProb n d (Q n)) ℓ (𝓝 1) := by
    have hh : Tendsto (fun n => (1 : ℝ) -
        (1 - PottsRapidMixing.regularProb n d (Q n))) ℓ (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hcomp
    simpa using hh
  simpa [PottsRapidMixing.WithHighProb, Q, ℓ] using hfinal
