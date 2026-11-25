-- Prove2me | solution 1 for PI.WGL.LTF.G_rowW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:08:30.382142+00:00
-- url     : https://prove2.me/submissions/09692205-c4cf-4323-9f94-249a6c7684c2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleF
import Theorems.Thm_PI_WGL_LTF_gmin_rowW
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
open PI PI.WGL PI.WGL.LTF
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTA PI.WGL.LTM PI.WGL.LTC PI.WGL.LTD PI.WGL.LTE
namespace PI.WGL.LTF
theorem _root_.solution {n N : ℕ} (h : n + 1 = N) {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (L : Finset (Fin K))
    (k : Fin K) (ρ : Fin (sz k) → Fin n) :
    IsWeightedHomogeneous (rowW N N)
      (if k ∈ L then lif h ρ (by have := hsz k; omega) else unl h ρ (by have := hsz k; omega))
      (wk h ρ (k ∈ L)) := by
  unfold wk
  split_ifs with hk
  · unfold lif
    have hg : IsWeightedHomogeneous (rowW N N)
        (initMinor ℤ (liftRows h ρ) (by have := hsz k; omega : sz k + 1 ≤ N))
        (∑ p, (Pi.single (liftRows h ρ p) 1 : Fin N → ℕ)) :=
      gmin_rowW (liftRows h ρ) (Fin.castLE (by have := hsz k; omega : sz k + 1 ≤ N))
    have hw : (∑ p, (Pi.single (liftRows h ρ p) 1 : Fin N → ℕ)) =
        (∑ q, (Pi.single (eRow h (ρ q)) 1 : Fin N → ℕ)) + Pi.single (⟨N - 1, by omega⟩ : Fin N) 1 := by
      rw [Fin.sum_univ_castSucc]
      simp [liftRows]
    rw [hw] at hg
    exact hg
  · unfold unl
    have hg : IsWeightedHomogeneous (rowW N N)
        (initMinor ℤ (eRow h ∘ ρ) (by have := hsz k; omega : sz k ≤ N))
        (∑ p, (Pi.single (eRow h (ρ p)) 1 : Fin N → ℕ)) :=
      gmin_rowW (eRow h ∘ ρ) (Fin.castLE (by have := hsz k; omega : sz k ≤ N))
    rw [add_zero]
    exact hg
end PI.WGL.LTF
