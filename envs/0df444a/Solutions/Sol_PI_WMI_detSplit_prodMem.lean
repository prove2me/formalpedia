-- Prove2me | solution 1 for PI.WMI.detSplit_prodMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:10:29.397691+00:00
-- url     : https://prove2.me/submissions/40e9955c-1754-48b2-a1fa-608ba079ce8f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_IsPolyMon
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_DetSplit
import Theorems.Thm_Formalism_GradedWeylDivisibility_bidetMem
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylMul
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
open PI PI.WMI
open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace
namespace PI.WMI
theorem _root_.solution {N K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ N) (I : ∀ k, Fin (sz k) → Fin N)
    (s : Finset (Fin K)) :
    ∏ k ∈ s, initMinor ℂ (I k) (hsz k) ∈
      Formalism.GradedWeylDivisibility.dualWeyl ℂ N N (fun t => (s.filter fun k => t.val < sz k).card) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · have h := (Formalism.GradedWeylDivisibility.dualWeylMul ℂ N N 0 0 1 1).2
    convert h using 2
    · funext t; simp
    · simp
  · intro a s ha ih
    have h1 : initMinor ℂ (I a) (hsz a) ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N (shapeDeg (fun _ : Fin 1 => sz a)) := by
      have := Formalism.GradedWeylDivisibility.bidetMem ℂ N N 1 (fun _ => sz a) (fun _ => hsz a) (fun _ => I a)
      simpa only [bideterminant, Fin.prod_univ_one] using this
    have h2 := (Formalism.GradedWeylDivisibility.dualWeylMul ℂ N N _ _ _ _).1 h1 ih
    rw [Finset.prod_insert ha]
    convert h2 using 2
    funext t
    simp only [shapeDeg, Pi.add_apply, Finset.filter_insert]
    split_ifs with ht
    · rw [Finset.card_insert_of_notMem (by simp [ha])]
      simp [ht, add_comm]
    · simp [ht]
end PI.WMI
