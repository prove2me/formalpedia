-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleDim_proof_ca6c5fc10660
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:36:07.724987+00:00
-- url     : https://prove2.me/submissions/54e884b7-d922-442e-b5bf-2a70c4ce59a5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleDimSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PDimTie
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleDim_funField_le_42b65e05bc34
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleDim_le_funField_1d98adab0225
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_proof_1c887bca4a14
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_proof_820eda5b4c8e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_proof_28dc9e797b4e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_primeOf_of_isHomogeneous_ce26327b239d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial AmpleAffineGen
noncomputable section
universe u w
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace VeryAmpleDim
theorem _root_.solution : VeryAmpleDim.Statement.{u, w} := by
  intro k _ Ω _ _ N x e Nb r h hx hv
  obtain ⟨i, hi⟩ := hx.relevant
  have hxi : x i ≠ 0 := by
    intro h0
    apply hi
    rw [mem_primeOf_of_isHomogeneous x (isHomogeneous_X k i), aeval_X, h0]
  obtain ⟨j, hj⟩ : ∃ j, h j ≠ 0 := by
    by_contra hc
    push Not at hc
    obtain ⟨Q', hQ'⟩ := Nb.invertible (singleChart hxi)
    have hbot : Nb.sub (singleChart hxi) = ⊥ := by
      rw [← hv.generates (singleChart hxi), Submodule.span_eq_bot]
      rintro _ ⟨l, rfl⟩
      exact hc l
    rw [hbot, Submodule.bot_mul] at hQ'
    have h1 : (1 : Ω) ∈ (⊥ : Submodule (chartRing k x (singleChart hxi)) Ω) := by
      rw [hQ']; exact Submodule.one_le.mp le_rfl
    exact one_ne_zero ((Submodule.mem_bot _).mp h1)
  have hfield : funField (k := k) x = funField (k := k) h :=
    le_antisymm (VeryAmpleDim.le_funField Nb hv hj) (VeryAmpleDim.funField_le Nb hv hxi)
  have hdx : dimCl k x = e := (DimTie.proof k Ω N x (Function.ne_iff.mpr ⟨i, hxi⟩) e).mp hx
  refine (DimTie.proof k Ω r h (Function.ne_iff.mpr ⟨j, hj⟩) e).mpr ?_
  rw [← hdx]
  unfold dimCl
  rw [hfield]
end VeryAmpleDim
end GroundTheory.Heights₂.Heights.Kleiman
