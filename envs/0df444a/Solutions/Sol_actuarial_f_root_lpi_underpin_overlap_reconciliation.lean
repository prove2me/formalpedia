-- Prove2me | solution 1 for actuarial_f_root_lpi_underpin_overlap_reconciliation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:07:49.93789+00:00
-- url     : https://prove2.me/submissions/1e56774e-f1c0-4cc8-951d-5cea7467f675

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_memberDue
import Definitions.Def_actuarial_f_spouseDue
import Definitions.Def_actuarial_f_estateDue
import Definitions.Def_actuarial_f_awardBase
import Definitions.Def_actuarial_f_fixedChoicePayment
import Definitions.Def_actuarial_f_monthlyScheduledGrowth
import Definitions.Def_actuarial_f_gmpValidYYYYMMDD
import Definitions.Def_actuarial_f_gmpDaysInMonth
import Definitions.Def_actuarial_f_gmpBoundedMemberMinimum
import Definitions.Def_actuarial_f_gmpBoundedPost88Growth
import Definitions.Def_actuarial_f_gmpProtectedContractualSurvivor
import Definitions.Def_actuarial_f_gmpProtectedSurvivorReplacement
import Definitions.Def_actuarial_f_gmpProtectedDirectEPV
import Definitions.Def_actuarial_f_gmpProtectedStateEPV
import Definitions.Def_actuarial_f_gmpProtectedReplacementEPV
import Definitions.Def_actuarial_f_gmpProtectedDisplaceableEPV
import Definitions.Def_actuarial_f_afLaterEarningsAddition
import Definitions.Def_actuarial_f_afMemberSection87WeeklyFloor
import Definitions.Def_actuarial_f_afSurvivorSection87WeeklyFloor
import Definitions.Def_actuarial_f_afStatutoryWeeklyToMonthly
import Definitions.Def_actuarial_f_afMemberSection87TopUp
import Definitions.Def_actuarial_f_afSurvivorCombinedMinimum

open ActuarialUnderpinsF

theorem B1h_expect_sum (n h m : ℕ) (p : ℕ → ℕ → ℕ → ℝ) (d : ℕ → ℝ)
    (F : ℕ → ℕ → ℕ → ℕ → ℝ) :
    ActuarialUnderpinsF.expect n h p (fun z i j => ∑ t ∈ Finset.range m, d t * F t z i j) =
      ∑ t ∈ Finset.range m, d t * ActuarialUnderpinsF.expect n h p (fun z i j => F t z i j) := by
  unfold ActuarialUnderpinsF.expect ActuarialJointD.expect
  simp only [Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

theorem B1h_repl_ge (P : Prop) (c s : ℝ) :
    s ≤ gmpProtectedSurvivorReplacement P c s := by
  unfold gmpProtectedSurvivorReplacement gmpProtectedSurvivorParallel
  split_ifs
  · exact le_rfl
  · exact le_max_right _ _

theorem B1h_disp (P : Prop) (c s : ℝ) :
    gmpProtectedSurvivorParallel c s =
      gmpProtectedSurvivorReplacement P c s + gmpProtectedSurvivorDisplaceable P c s := by
  unfold gmpProtectedSurvivorReplacement gmpProtectedSurvivorParallel
    gmpProtectedSurvivorDisplaceable
  split_ifs
  · rw [max_def, max_def]; split_ifs <;> linarith
  · simp

theorem solution
    (n h retirement guarantee firstA firstB firstC : ℕ)
    (p : ℕ → ℕ → ℕ → ℝ)
    (disc a b c estate : ℕ → ℝ)
    (sa sb : ℕ → ℕ → ℝ)
    (inflationA inflationB inflationC inflationS : ℕ → ℝ)
    (survivorFirst : ℕ → ℕ) (ge : ℕ → ℝ)
    (floorA capA floorB capB floorC capC floorS capS : ℝ)
    (dateOf : ℕ → ℕ) (memberDeathDate : ℕ → ℕ → ℕ)
    (gmpPayableDate cessationDate : ℕ)
    (pre88Gmp post88Gmp : ℕ → ℝ)
    (survivorPre88 survivorPost88 : ℕ → ℕ → ℝ)
    (survivorGmpEligible : ℕ → ℕ → Bool)
    (survivorGmpPayableDate : ℕ → ℕ → ℕ)
    (gmpAnnualOrderRate : ℕ → ℝ)
    (memberLeftBefore1985 memberContractingOutEndedBefore1985
       memberFullEntitlement memberCompleteSubstitute
       memberLaterAccrualApplies : ℕ → Bool)
    (memberRelevantWeekly memberGmpAtCessationWeekly
       memberAppropriateWeekly memberAssumedLaterWeekly : ℕ → ℝ)
    (survivorFullEntitlement survivorCompleteSubstitute
       survivorLaterAccrualApplies : ℕ → ℕ → Bool)
    (survivorRelevantWeekly survivorAppropriateWeekly
       survivorAssumedLaterWeekly survivorExcludedTransferGrowth : ℕ → ℕ → ℝ)
    (memberExcludedTransferGrowth : ℕ → ℝ)
    (hv : 0 < n ∧
      (∀ z ∈ Finset.range n, ∀ i ∈ Finset.range (h + 1),
        ∀ j ∈ Finset.range (h + 1), 0 ≤ p z i j) ∧
      (∑ z ∈ Finset.range n, ∑ i ∈ Finset.range (h + 1),
        ∑ j ∈ Finset.range (h + 1), p z i j) = 1)
    (hr : retirement ≤ h)
    (ha : retirement < firstA ∧ firstA ≤ retirement + 12)
    (hb : retirement < firstB ∧ firstB ≤ retirement + 12)
    (hc : retirement < firstC ∧ firstC ≤ retirement + 12)
    (hs : ∀ i ∈ Finset.range h,
      i + 1 < survivorFirst i ∧ survivorFirst i ≤ i + 13)
    (hfa : 0 ≤ floorA ∧ floorA ≤ capA)
    (hfb : 0 ≤ floorB ∧ floorB ≤ capB)
    (hfc : 0 ≤ floorC ∧ floorC ≤ capC)
    (hfs : 0 ≤ floorS ∧ floorS ≤ capS)
    (hdate : ∀ t ≤ h + 1, gmpValidYYYYMMDD (dateOf t))
    (hdateMono : ∀ t < h + 1, dateOf t < dateOf (t + 1))
    (hcalendar : ∀ t < h,
      let y := dateOf t / 10000
      let m := dateOf t % 10000 / 100
      let nextY := if m = 12 then y + 1 else y
      let nextM := if m = 12 then 1 else m + 1
      dateOf (t + 1) =
        nextY * 10000 + nextM * 100 +
          min (dateOf 0 % 100) (gmpDaysInMonth nextY nextM))
    (hdeath : ∀ z ∈ Finset.range n, ∀ i ∈ Finset.range h,
      gmpValidYYYYMMDD (memberDeathDate z i) ∧
      dateOf i ≤ memberDeathDate z i ∧
      memberDeathDate z i < dateOf (i + 1))
    (hSurvivorGmpDate : ∀ z ∈ Finset.range n, ∀ i ∈ Finset.range h,
      gmpValidYYYYMMDD (survivorGmpPayableDate z i) ∧
      memberDeathDate z i ≤ survivorGmpPayableDate z i)
    (htransferM : ∀ z ∈ Finset.range n, 0 ≤ memberExcludedTransferGrowth z)
    (htransferS : ∀ z ∈ Finset.range n,
      ∀ i ∈ Finset.range h, 0 ≤ survivorExcludedTransferGrowth z i) :
    let ga : ℕ → ℝ := fun t =>
      monthlyScheduledGrowth retirement firstA floorA capA inflationA t
    let gb : ℕ → ℝ := fun t =>
      monthlyScheduledGrowth retirement firstB floorB capB inflationB t
    let gc : ℕ → ℝ := fun t =>
      monthlyScheduledGrowth retirement firstC floorC capC inflationC t
    let gs : ℕ → ℕ → ℝ := fun i t =>
      monthlyScheduledGrowth (i + 1) (survivorFirst i)
        floorS capS inflationS t
    let memberStatutoryWeekly : ℕ → ℕ → ℝ := fun z t =>
      let gmpWeekly :=
        gmpBoundedMemberMinimum (pre88Gmp z) (post88Gmp z)
          gmpPayableDate (dateOf t) gmpAnnualOrderRate * 12 / 52
      let antifrankWeekly :=
        afMemberSection87WeeklyFloor cessationDate gmpPayableDate
          (dateOf t) (memberLeftBefore1985 z) (memberContractingOutEndedBefore1985 z)
          (memberFullEntitlement z) (memberCompleteSubstitute z)
          (memberLaterAccrualApplies z) (memberRelevantWeekly z) gmpWeekly
          (memberGmpAtCessationWeekly z) (memberAppropriateWeekly z)
          (afLaterEarningsAddition (memberRelevantWeekly z)
            (memberGmpAtCessationWeekly z) (memberAssumedLaterWeekly z))
          (memberExcludedTransferGrowth z)
      max gmpWeekly antifrankWeekly
    let memberSupplement : ℕ → ℕ → ℕ → ℝ := fun z i t =>
      if gmpPayableDate ≤ dateOf t then
        afMemberSection87TopUp retirement i t
          (fixedChoicePayment a b ga gb z t + c z * gc t)
          (memberStatutoryWeekly z t)
      else 0
    let survivorMinimum : ℕ → ℕ → ℕ → ℕ → ℝ := fun z i j t =>
      if spouseDue h i j t = 1 then
        let gmpMonthly :=
          if survivorGmpEligible z i = true ∧
              survivorGmpPayableDate z i ≤ dateOf t then
            max 0 (survivorPre88 z i +
              survivorPost88 z i *
                gmpBoundedPost88Growth (survivorGmpPayableDate z i)
                  (dateOf t) gmpAnnualOrderRate)
          else 0
        let antifrankWeekly :=
          afSurvivorSection87WeeklyFloor cessationDate (memberDeathDate z i)
            gmpPayableDate (dateOf t) (memberLeftBefore1985 z) (memberContractingOutEndedBefore1985 z)
            (survivorFullEntitlement z i) (survivorCompleteSubstitute z i)
            (survivorLaterAccrualApplies z i)
            (survivorRelevantWeekly z i) (gmpMonthly * 12 / 52)
            (memberGmpAtCessationWeekly z) (survivorAppropriateWeekly z i)
            (afLaterEarningsAddition (survivorRelevantWeekly z i)
              (memberGmpAtCessationWeekly z / 2)
              (survivorAssumedLaterWeekly z i))
            (survivorExcludedTransferGrowth z i)
        afSurvivorCombinedMinimum gmpMonthly antifrankWeekly
      else 0
    (gmpProtectedDirectEPV n h retirement guarantee p disc a b c sa sb
        estate ga gb gc gs ge memberSupplement survivorMinimum =
      gmpProtectedStateEPV n h retirement guarantee p disc a b c sa sb
        estate ga gb gc gs ge memberSupplement survivorMinimum) ∧
    (gmpProtectedDirectEPV n h retirement guarantee p disc a b c sa sb
        estate ga gb gc gs ge memberSupplement survivorMinimum =
      gmpProtectedReplacementEPV n h retirement guarantee p disc a b c
        sa sb estate ga gb gc gs ge memberSupplement survivorMinimum +
      gmpProtectedDisplaceableEPV n h retirement guarantee p disc a b
        sa sb gs survivorMinimum) ∧
    (∀ z ∈ Finset.range n,
      a z ≤ awardBase a b z ∧ b z ≤ awardBase a b z) ∧
    (∀ z i j t, t ≤ h →
      survivorMinimum z i j t ≤
        gmpProtectedSurvivorReplacement
          (estateDue h retirement guarantee i t = 1)
          (gmpProtectedContractualSurvivor h z i j t a b sa sb gs)
          (survivorMinimum z i j t)) ∧
    (∀ z i t, t ≤ h →
      memberDue retirement i t = 1 →
      gmpPayableDate ≤ dateOf t →
      afStatutoryWeeklyToMonthly (memberStatutoryWeekly z t) ≤
      fixedChoicePayment a b ga gb z t +
        c z * gc t + memberSupplement z i t) := by
  intro ga gb gc gs memberStatutoryWeekly memberSupplement survivorMinimum
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold gmpProtectedDirectEPV gmpProtectedStateEPV
    rw [B1h_expect_sum]
  · unfold gmpProtectedDirectEPV gmpProtectedReplacementEPV gmpProtectedDisplaceableEPV
    rw [B1h_expect_sum, B1h_expect_sum, B1h_expect_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [ActuarialUnderpinsF.expect, ActuarialJointD.expect, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => ?_
    unfold gmpProtectedParallelInstalment gmpProtectedReplacementInstalment
      gmpProtectedDisplaceableInstalment
    rw [B1h_disp (estateDue h retirement guarantee i t = 1)]
    ring
  · intro z _
    exact ⟨le_max_left _ _, le_max_right _ _⟩
  · intro z i j t _
    exact B1h_repl_ge _ _ _
  · intro z i t _ hdue hgpd
    have hms : memberSupplement z i t = afMemberSection87TopUp retirement i t
        (fixedChoicePayment a b ga gb z t + c z * gc t) (memberStatutoryWeekly z t) :=
      if_pos hgpd
    rw [hms]
    unfold afMemberSection87TopUp
    rw [hdue, mul_one]
    have := le_max_right 0 (afStatutoryWeeklyToMonthly (memberStatutoryWeekly z t) -
      (fixedChoicePayment a b ga gb z t + c z * gc t))
    linarith
