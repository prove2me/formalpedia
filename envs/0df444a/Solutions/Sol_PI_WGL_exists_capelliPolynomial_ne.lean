-- Prove2me | solution 1 for PI.WGL.exists_capelliPolynomial_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:08:53.987889+00:00
-- url     : https://prove2.me/submissions/982644e4-550e-40fe-9289-93a2c095223e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_HwIrred
import Definitions.Def_Formalism_PeriodIntegrals_GTBranch
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_IoExistsOfCap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions MvPolynomial
namespace PI.WGL
theorem _root_.solution {n : ℕ} (mu sg : DomWeight n) (hne : mu.w ≠ sg.w) : ∃ u, capP mu u ≠ capP sg u := by
  by_contra hall
  push_neg at hall
  apply hne
  have hzero : ∀ (nu : DomWeight n) (i : Fin n), capP nu (((i : ℕ) : ℂ) - ((nu.w i : ℤ) : ℂ)) = 0 := by
    intro nu i
    unfold capP
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    ring
  have hmem : ∀ (nu nu' : DomWeight n), (∀ u, capP nu u = capP nu' u) →
      ∀ i : Fin n, ∃ k : Fin n, ((k : ℕ) : ℤ) - nu'.w k = ((i : ℕ) : ℤ) - nu.w i := by
    intro nu nu' heq i
    have h0 := hzero nu i
    rw [heq] at h0
    unfold capP at h0
    obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp h0
    refine ⟨k, ?_⟩
    have : ((((k : ℕ) : ℤ) - nu'.w k : ℤ) : ℂ) = ((((i : ℕ) : ℤ) - nu.w i : ℤ) : ℂ) := by
      push_cast
      linear_combination -hk
    exact_mod_cast this
  have hmono : ∀ nu : DomWeight n, StrictMono (fun k : Fin n => ((k : ℕ) : ℤ) - nu.w k) := by
    intro nu i j hij
    have h1 := nu.anti hij.le
    have h2 : (i : ℕ) < j := hij
    simp only
    omega
  have hrange : Set.range (fun k : Fin n => ((k : ℕ) : ℤ) - mu.w k) =
      Set.range (fun k : Fin n => ((k : ℕ) : ℤ) - sg.w k) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      obtain ⟨k, hk⟩ := hmem mu sg hall i
      exact ⟨k, hk⟩
    · rintro ⟨i, rfl⟩
      obtain ⟨k, hk⟩ := hmem sg mu (fun u => (hall u).symm) i
      exact ⟨k, hk⟩
  have hab := ((hmono mu).range_inj (hmono sg)).mp hrange
  funext k
  have := congrFun hab k
  omega
end PI.WGL
