-- Prove2me | solution 1 for OpenGA.SurgeryVolumeProfile.card_surgeryTimes_le
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-10T18:48:48.718778+00:00
-- url     : https://prove2.me/submissions/fd135667-93c7-4219-ba11-3e3a675ef41c

import Theorems.Thm_OpenGA_SurgeryVolumeProfile_surgeryTimes_finite
import Mathlib.Tactic

set_option autoImplicit false

open Set

namespace OpenGASurgeryCardAux

open OpenGA

variable {a b : ℝ} (P : SurgeryVolumeProfile a b)

/-- The discounted volume of a forward time slice is nonnegative. -/
lemma discounted_nonneg {t : ℝ} (ht : t ∈ Icc a b) : 0 ≤ P.discounted t := by
  have := P.volAfter_nonneg t ht
  unfold SurgeryVolumeProfile.discounted
  positivity

/-- Passing a surgery decreases the discounted volume by at least `P.quantum`. -/
lemma discounted_step {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ P.surgeryTimes) (hst : s < t) :
    P.discounted t + P.quantum ≤ P.discounted s := by
  have htmem : t ∈ Ioc a b := P.surgeryTimes_subset ht
  have htIcc : t ∈ Icc a b := ⟨htmem.1.le, htmem.2⟩
  have hchain : P.volAfter t + P.surgeryScale ^ 3 ≤
      P.volAfter s * Real.exp (P.growthRate * (t - s)) :=
    le_trans (P.drop t ht) (P.growth s hs t htIcc hst)
  have hexp : (0:ℝ) < Real.exp (-(P.growthRate * (t - a))) := Real.exp_pos _
  have hmul := mul_le_mul_of_nonneg_right hchain hexp.le
  have hrw : P.volAfter s * Real.exp (P.growthRate * (t - s)) *
      Real.exp (-(P.growthRate * (t - a))) = P.discounted s := by
    unfold SurgeryVolumeProfile.discounted
    rw [mul_assoc, ← Real.exp_add]
    ring_nf
  have hquant : P.quantum ≤ P.surgeryScale ^ 3 * Real.exp (-(P.growthRate * (t - a))) := by
    unfold SurgeryVolumeProfile.quantum
    have hle : -(P.growthRate * (b - a)) ≤ -(P.growthRate * (t - a)) := by
      have : P.growthRate * (t - a) ≤ P.growthRate * (b - a) := by
        apply mul_le_mul_of_nonneg_left _ P.growthRate_nonneg
        linarith [htmem.2]
      linarith
    have hmono := Real.exp_le_exp.mpr hle
    nlinarith [pow_pos P.surgeryScale_pos 3, Real.exp_pos (-(P.growthRate * (b - a)))]
  calc P.discounted t + P.quantum
      ≤ P.volAfter t * Real.exp (-(P.growthRate * (t - a)))
        + P.surgeryScale ^ 3 * Real.exp (-(P.growthRate * (t - a))) := by
        unfold SurgeryVolumeProfile.discounted; linarith
    _ = (P.volAfter t + P.surgeryScale ^ 3) * Real.exp (-(P.growthRate * (t - a))) := by ring
    _ ≤ P.volAfter s * Real.exp (P.growthRate * (t - s)) *
          Real.exp (-(P.growthRate * (t - a))) := hmul
    _ = P.discounted s := hrw

/-- A finite set of surgery times lying strictly after a time `s` has cardinality at most
the discounted volume at `s` divided by the per-surgery quantum. -/
lemma card_mul_quantum_le (F : Finset ℝ) :
    ∀ s ∈ Icc a b, (F : Set ℝ) ⊆ P.surgeryTimes → (∀ x ∈ F, s < x) →
      (F.card : ℝ) * P.quantum ≤ P.discounted s := by
  classical
  induction F using Finset.strongInduction with
  | _ F ih =>
    intro s hs hF hgt
    rcases F.eq_empty_or_nonempty with rfl | hne
    · simpa using discounted_nonneg P hs
    · set m := F.min' hne with hm
      have hmF : m ∈ F := F.min'_mem hne
      have hmS : m ∈ P.surgeryTimes := hF (by exact_mod_cast hmF)
      have hmIoc : m ∈ Ioc a b := P.surgeryTimes_subset hmS
      have hmIcc : m ∈ Icc a b := ⟨hmIoc.1.le, hmIoc.2⟩
      have hcard : (F.erase m).card + 1 = F.card := Finset.card_erase_add_one hmF
      have hsub : ((F.erase m : Finset ℝ) : Set ℝ) ⊆ P.surgeryTimes := by
        intro x hx
        simp only [Finset.coe_erase, mem_sdiff] at hx
        exact hF hx.1
      have hgt' : ∀ x ∈ F.erase m, m < x := by
        intro x hx
        exact lt_of_le_of_ne (F.min'_le x (Finset.mem_of_mem_erase hx))
          (Ne.symm (Finset.ne_of_mem_erase hx))
      have hIH : ((F.erase m).card : ℝ) * P.quantum ≤ P.discounted m :=
        ih (F.erase m) (Finset.erase_ssubset hmF) m hmIcc hsub hgt'
      have hstep : P.discounted m + P.quantum ≤ P.discounted s :=
        discounted_step P hs hmS (hgt m hmF)
      have hcast : (F.card : ℝ) = ((F.erase m).card : ℝ) + 1 := by
        exact_mod_cast (hcard ▸ rfl : (F.card : ℕ) = (F.erase m).card + 1)
      rw [hcast]
      nlinarith

end OpenGASurgeryCardAux

open OpenGASurgeryCardAux in
theorem solution {a b : ℝ} (P : OpenGA.SurgeryVolumeProfile a b) (hab : a ≤ b) :
    (P.surgeryTimes.ncard : ℝ) * P.surgeryScale ^ 3 ≤
      P.volAfter a * Real.exp (P.growthRate * (b - a)) := by
  classical
  have hfin : P.surgeryTimes.Finite := P.surgeryTimes_finite hab
  have hcard : (hfin.toFinset : Finset ℝ).card = P.surgeryTimes.ncard :=
    (Set.ncard_eq_toFinset_card P.surgeryTimes hfin).symm
  have hsub : ((hfin.toFinset : Finset ℝ) : Set ℝ) ⊆ P.surgeryTimes := by
    intro x hx
    simpa using hx
  have hgt : ∀ x ∈ hfin.toFinset, a < x := by
    intro x hx
    have hxS : x ∈ P.surgeryTimes := by simpa using hx
    exact (P.surgeryTimes_subset hxS).1
  have key := card_mul_quantum_le P hfin.toFinset a (left_mem_Icc.mpr hab) hsub hgt
  rw [hcard] at key
  have hdisc : P.discounted a = P.volAfter a := by
    unfold OpenGA.SurgeryVolumeProfile.discounted
    simp
  rw [hdisc] at key
  unfold OpenGA.SurgeryVolumeProfile.quantum at key
  have hexp : (0:ℝ) < Real.exp (P.growthRate * (b - a)) := Real.exp_pos _
  have hmul := mul_le_mul_of_nonneg_right key hexp.le
  have hone : Real.exp (-(P.growthRate * (b - a))) * Real.exp (P.growthRate * (b - a)) = 1 := by
    rw [← Real.exp_add]
    simp
  calc (P.surgeryTimes.ncard : ℝ) * P.surgeryScale ^ 3
      = (P.surgeryTimes.ncard : ℝ) *
        (P.surgeryScale ^ 3 * Real.exp (-(P.growthRate * (b - a)))) *
        Real.exp (P.growthRate * (b - a)) := by
        rw [mul_assoc, mul_assoc, hone, mul_one]
    _ ≤ P.volAfter a * Real.exp (P.growthRate * (b - a)) := hmul
