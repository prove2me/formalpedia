-- Prove2me | solution 1 for PI.WMI.detSplit_fullMinor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:17:48.833384+00:00
-- url     : https://prove2.me/submissions/5c1d5c47-4d65-4eac-b33a-10734cda1772

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_IsPolyMon
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_DetSplit
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
theorem _root_.solution {N : ℕ} (s : ℕ) (I : Fin s → Fin N) (hs : s ≤ N) (hN : s = N) :
    ∃ e : ℂ, initMinor ℂ (n := N) I hs = C e * detPoly N := by
  subst hN
  by_cases hI : Function.Injective I
  · have hb : Function.Bijective I := (Fintype.bijective_iff_injective_and_card I).2 ⟨hI, rfl⟩
    refine ⟨((Equiv.Perm.sign (Equiv.ofBijective I hb) : ℤ) : ℂ), ?_⟩
    have h := Matrix.det_permute (Equiv.ofBijective I hb)
      (Matrix.of fun i j : Fin s => (X (i, j) : MvPolynomial (Fin s × Fin s) ℂ))
    have hM : initMinor ℂ (n := s) I hs =
        ((Matrix.of fun i j : Fin s => (X (i, j) : MvPolynomial (Fin s × Fin s) ℂ)).submatrix
          (Equiv.ofBijective I hb) id).det := by
      unfold initMinor
      congr 1
    rw [hM, h, detPoly, map_intCast]
  · refine ⟨0, ?_⟩
    simp only [Function.Injective, not_forall] at hI
    obtain ⟨i, j, hij, hne⟩ := hI
    rw [map_zero, zero_mul]
    unfold initMinor
    exact Matrix.det_zero_of_row_eq hne (funext fun q => by simp [hij])
end PI.WMI
