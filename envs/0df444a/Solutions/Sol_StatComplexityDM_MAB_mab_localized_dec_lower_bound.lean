-- Prove2me | solution 1 for StatComplexityDM.MAB.mab_localized_dec_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T11:09:06.644946+00:00
-- url     : https://prove2.me/submissions/4f8b1512-4120-4878-9152-fcb4742eb5ba

import Mathlib.Data.Fintype.Order
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_FoundationsRL_GeneralDM_DEC
import Definitions.Def_StatComplexityDM_LowerBound_Core
import Definitions.Def_StatComplexityDM_MAB_Bernoulli

import Theorems.Thm_StatComplexityDM_MAB_hard_family_dec_lower_bound
import Theorems.Thm_StatComplexityDM_MAB_ber_family_is_hard
import Theorems.Thm_StatComplexityDM_MAB_ber_family_subset_localized

open FoundationsRL.GeneralDM

/- The three imported theorem statements are platform-verified dependencies.
The order arguments below supply the nonemptiness and boundedness needed by
the real-valued infima and suprema in the published definition of `decGf`. -/

private theorem finite_dec_mono
    {S Y : Type*} [Fintype S] [Fintype Y] [Nonempty S]
    (small big : Set (S → Y → ℝ)) (rew : Y → ℝ)
    (piStar : (S → Y → ℝ) → S) (γ : ℝ) (mbar : S → Y → ℝ)
    (hsmall : small.Nonempty) (hfinite : small.Finite) (hsub : small ⊆ big)
    (hbounded : ∀ p : S → ℝ, (∀ i, 0 ≤ p i) → (∑ i, p i = 1) →
      BddAbove ((fun m : S → Y → ℝ =>
        ∑ i, p i * (fM rew m (piStar m) - fM rew m i -
          γ * hellingerSq (m i) (mbar i))) '' big)) :
    decGf small rew piStar γ mbar ≤ decGf big rew piStar γ mbar := by
  classical
  let P : Set (S → ℝ) := {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}
  let payoff : (S → ℝ) → (S → Y → ℝ) → ℝ := fun p m =>
    ∑ i, p i * (fM rew m (piStar m) - fM rew m i -
      γ * hellingerSq (m i) (mbar i))
  have hP : P.Nonempty := by
    let a : S := Classical.choice (inferInstance : Nonempty S)
    refine ⟨fun i => if i = a then 1 else 0, ?_, ?_⟩
    · intro i
      dsimp only
      split <;> norm_num
    · simp
  obtain ⟨m₀, hm₀⟩ := hsmall
  obtain ⟨b, hb⟩ := (Set.finite_range (fun i : S =>
    fM rew m₀ (piStar m₀) - fM rew m₀ i -
      γ * hellingerSq (m₀ i) (mbar i))).bddBelow
  have hlower : BddBelow ((fun p => sSup (payoff p '' small)) '' P) := by
    refine ⟨b, ?_⟩
    rintro z ⟨p, hp, rfl⟩
    have hvalue : b ≤ payoff p m₀ := by
      calc
        b = ∑ i, p i * b := by rw [← Finset.sum_mul, hp.2, one_mul]
        _ ≤ payoff p m₀ := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_left (hb (Set.mem_range_self i)) (hp.1 i)
    exact hvalue.trans (le_csSup (hfinite.image (payoff p)).bddAbove ⟨m₀, hm₀, rfl⟩)
  change sInf ((fun p => sSup (payoff p '' small)) '' P) ≤
    sInf ((fun p => sSup (payoff p '' big)) '' P)
  apply le_csInf (hP.image _)
  rintro z ⟨p, hp, rfl⟩
  exact (csInf_le hlower ⟨p, hp, rfl⟩).trans
    (csSup_le_csSup (hbounded p hp.1 hp.2)
      (Set.Nonempty.image (fun m => payoff p m) ⟨m₀, hm₀⟩) (Set.image_mono hsub))

private theorem bernoulli_payoff_bddAbove
    (A : ℕ) (C : Set (Fin A → Bool → ℝ)) (hC : C ⊆ StatComplexityDM.MAB.bernoulliBandits A)
    (piStar : (Fin A → Bool → ℝ) → Fin A) (γ : ℝ) (hγ : 0 ≤ γ)
    (mbar : Fin A → Bool → ℝ) (p : Fin A → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    BddAbove ((fun m : Fin A → Bool → ℝ =>
      ∑ i, p i * (fM StatComplexityDM.MAB.berRew m (piStar m) -
        fM StatComplexityDM.MAB.berRew m i -
        γ * hellingerSq (m i) (mbar i))) '' C) := by
  refine ⟨1, ?_⟩
  rintro z ⟨m, hm, rfl⟩
  have hmodel := hC hm
  have hreward (i : Fin A) :
      0 ≤ fM StatComplexityDM.MAB.berRew m i ∧
        fM StatComplexityDM.MAB.berRew m i ≤ 1 := by
    have hi := hmodel i
    have hs : m i false + m i true = 1 := by
      simpa [StatComplexityDM.LowerBound.IsDist, Fintype.sum_bool, add_comm] using hi.2
    have hn0 := hi.1 false
    have hn1 := hi.1 true
    simp only [fM, Fintype.sum_bool, StatComplexityDM.MAB.berRew,
      Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero, mul_one]
    exact ⟨hn1, by linarith⟩
  calc
    _ ≤ ∑ i, p i * 1 := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hp i)
      have hdist : 0 ≤ hellingerSq (m i) (mbar i) :=
        Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have hpenalty := mul_nonneg hγ hdist
      have htop := (hreward (piStar m)).2
      have hbottom := (hreward i).1
      linarith
    _ = 1 := by simpa using hsum

theorem solution (A : ℕ) (hA : 2 ≤ A)
    (piStar : (Fin A → Bool → ℝ) → Fin A)
    (hpiStar : StatComplexityDM.LowerBound.IsArgmaxSel StatComplexityDM.MAB.berRew piStar)
    (γ : ℝ) (hγ : (A : ℝ) / 3 ≤ γ) :
    (2 : ℝ) ^ (-6 : ℤ) * ((A : ℝ) / γ) ≤
      decGf (StatComplexityDM.LowerBound.linfLocalized
          (StatComplexityDM.MAB.bernoulliBandits A) StatComplexityDM.MAB.berRew piStar
          (fun _ => StatComplexityDM.MAB.ber (1 / 2)) ((A : ℝ) / (12 * γ)))
        StatComplexityDM.MAB.berRew piStar γ (fun _ => StatComplexityDM.MAB.ber (1 / 2)) := by
  classical
  have hApos : 0 < A := lt_of_lt_of_le (by decide : 0 < 2) hA
  have hAr : (0 : ℝ) < A := Nat.cast_pos.mpr hApos
  have hγpos : 0 < γ := lt_of_lt_of_le (div_pos hAr (by norm_num)) hγ
  letI : Nonempty (Fin A) := ⟨⟨0, hApos⟩⟩
  let Δ : ℝ := (A : ℝ) / (12 * γ)
  have hΔpos : 0 < Δ := div_pos hAr (mul_pos (by norm_num) hγpos)
  have hΔquarter : Δ ≤ 1 / 4 := by
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 12) hγpos)).2
    linarith
  have hΔhalf : Δ < 1 / 2 := lt_of_le_of_lt hΔquarter (by norm_num)
  have hhard := StatComplexityDM.MAB.ber_family_is_hard A hA piStar hpiStar Δ hΔpos hΔhalf
  have hlocalized := StatComplexityDM.MAB.ber_family_subset_localized A hA piStar hpiStar Δ hΔpos hΔhalf
  have hfamily := StatComplexityDM.MAB.hard_family_dec_lower_bound
    StatComplexityDM.MAB.berRew piStar (StatComplexityDM.MAB.bernoulliBandits A)
    (fun _ => StatComplexityDM.MAB.ber (1 / 2))
    (StatComplexityDM.MAB.berFamily A Δ) Δ (3 * Δ ^ 2) 0
    (by positivity) hhard γ hγpos
  have hmono := finite_dec_mono
    (Set.range (StatComplexityDM.MAB.berFamily A Δ))
    (StatComplexityDM.LowerBound.linfLocalized (StatComplexityDM.MAB.bernoulliBandits A)
      StatComplexityDM.MAB.berRew piStar (fun _ => StatComplexityDM.MAB.ber (1 / 2)) Δ)
    StatComplexityDM.MAB.berRew piStar γ (fun _ => StatComplexityDM.MAB.ber (1 / 2))
    (Set.range_nonempty _) (Set.finite_range _) hlocalized (by
      intro p hp hsum
      apply bernoulli_payoff_bddAbove A _ _ piStar γ hγpos.le _ p hp hsum
      intro m hm
      exact hm.1)
  have hscalar : (2 : ℝ) ^ (-6 : ℤ) * ((A : ℝ) / γ) ≤
      Δ / 2 - γ * (3 * Δ ^ 2 / A + 0) := by
    have hidentity : Δ / 2 - γ * (3 * Δ ^ 2 / A + 0) =
        (1 / 48 : ℝ) * ((A : ℝ) / γ) := by
      dsimp [Δ]
      field_simp [ne_of_gt hAr, ne_of_gt hγpos]
      <;> ring
    rw [hidentity]
    norm_num
    exact mul_le_mul_of_nonneg_right (by norm_num) (div_nonneg hAr.le hγpos.le)
  exact hscalar.trans (hfamily.trans hmono)

#print axioms solution
