-- Prove2me | solution 1 for PI.WGL.capZ_scalar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:32:48.91574+00:00
-- url     : https://prove2.me/submissions/094e0e93-94f4-4777-ba80-091e38e63f28

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliShift
import Definitions.Def_Lemmata_GeneralBFactRight_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliZ
import Theorems.Thm_PI_WGL_list_scalar
import Theorems.Thm_PI_WGL_capF_scalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
namespace PI.WGL
theorem _root_.solution (hC : CapScalar) {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg mu : DomWeight n)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) (hφ : IsEqv h mu lam φ)
    (s : MvPolynomial (Fin n × Fin n) ℂ) (hs : s ∈ nablaSq ℂ n mu) :
    capZ h lam sg (φ s) = ((zScalar h lam sg mu : ℤ) : ℂ) • φ s := by
  unfold capZ
  rw [list_scalar (List.finRange n) _
    (fun i => ∏ v ∈ (Rset h lam sg i).erase (sg.w i),
      ∏ j : Fin n, ((((v - (i.1 : ℤ)) - mu.w j + (j.1 : ℤ) : ℤ)) : ℂ)) (φ s)]
  · rw [← Fin.prod_univ_def]
    unfold zScalar
    push_cast
    rfl
  · intro i _
    rw [list_scalar _ _ (fun v => ∏ j : Fin n, ((((v - (i.1 : ℤ)) - mu.w j + (j.1 : ℤ) : ℤ)) : ℂ)) (φ s),
      Finset.prod_map_toList]
    intro v _
    exact capF_scalar hC h lam mu φ hφ s hs i v
end PI.WGL
