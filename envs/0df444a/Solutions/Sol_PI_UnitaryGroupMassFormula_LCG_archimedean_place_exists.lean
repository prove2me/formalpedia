-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.archimedean_place_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:13:20.959132+00:00
-- url     : https://prove2.me/submissions/6d623297-43b1-47e1-aa31-6038d90bb242

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_GramLowOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_ArchPlace
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_gram
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_AC
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_DC
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_DD
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_kernel
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_ap_hs_sq
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.UnitaryGroupMassFormula.LCG
theorem _root_.solution : ArchPlaceOf := by
  unfold ArchPlaceOf ArchIneq ArchPlace
  intro hA I x y δ k u b' v hu hsp hb hperp
  have hCS : ∀ w : Fin I.n → ℂ, PI.UnitaryGroupMassFormula.LSC.nsq (amat I x y v δ *ᵥ w) ≤
      hsN (amat I x y v δ) ^ 2 * PI.UnitaryGroupMassFormula.LSC.nsq w := by
    intro w
    unfold PI.UnitaryGroupMassFormula.LSC.nsq
    rw [ap_hs_sq, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 : ‖(amat I x y v δ *ᵥ w) i‖ ≤ ∑ j, ‖amat I x y v δ i j‖ * ‖w j‖ := by
      simp only [Matrix.mulVec, dotProduct]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      simp [norm_mul]
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖amat I x y v δ i j‖) (fun j => ‖w j‖)
    calc ‖(amat I x y v δ *ᵥ w) i‖ ^ 2 ≤ (∑ j, ‖amat I x y v δ i j‖ * ‖w j‖) ^ 2 := by
          nlinarith [h1, norm_nonneg ((amat I x y v δ *ᵥ w) i)]
      _ ≤ (∑ j, ‖amat I x y v δ i j‖ ^ 2) * ∑ j, ‖w j‖ ^ 2 := h2
  have key := hA I.n k (amat I x y v δ) (colM I y v u) (Formalism.REAL.Jm (I.ε v) * colM I y v b')
    (hsN (amat I x y v δ) ^ 2) (sq_nonneg _) hCS (ap_kernel I x y v δ k u b' hu hsp hb hperp)
  rw [ap_AC, ap_DD, ap_DC, ← ap_gram, ← ap_gram, ← pow_mul] at key
  rw [RingHom.map_det, RingHom.mapMatrix_apply]
  exact key
end PI.UnitaryGroupMassFormula.LCG
