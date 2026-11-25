-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.gramOK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:03:21.684131+00:00
-- url     : https://prove2.me/submissions/9747a9c9-6477-41e8-9874-21d155f54daf

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PHermSk
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PHermC
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution : GramOK := by
  intro F E _ _ _ _ σ hσ V _ _ _ h M b hsy hnd
  refine ⟨?_, ?_⟩
  · unfold PI.UnitaryApproxDefs.IsHerm PI.UnitaryApproxDefs.cT
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply, AlgHom.coe_toRingHom, hσ, gramOf]
    rw [← starRingEnd_apply]
    exact hsy.eq (b j) (b i)
  · rw [isUnit_iff_ne_zero]
    intro hdet
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    apply hc0
    have hbw : ∀ i, h (b i) (∑ j, c j • b j) = 0 := by
      intro i
      have hi := congrFun hc i
      simp only [Matrix.mulVec, dotProduct, gramOf, Pi.zero_apply] at hi
      simp only [map_sum, map_smul, smul_eq_mul]
      rw [← hi]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hw : ∀ x, h x (∑ j, c j • b j) = 0 := by
      intro x
      generalize hwd : (∑ j, c j • b j) = w at hbw ⊢
      rw [← b.sum_repr x]
      simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, hbw, smul_zero,
        Finset.sum_const_zero]
    have hw0 := hnd.2 _ hw
    funext j
    exact Fintype.linearIndependent_iff.1 b.linearIndependent c hw0 j
end PI.UnitaryGroupMassFormula.UJClassMass
