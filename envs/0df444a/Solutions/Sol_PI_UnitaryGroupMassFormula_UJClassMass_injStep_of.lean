-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.injStep_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:10:50.521911+00:00
-- url     : https://prove2.me/submissions/f5026393-a40b-48d5-8c28-97130b64e7bb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_EquivFunLinOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_CardStepOf
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_linOf_matGL
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_matGL_mem
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_image_latSet
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_set_of_coords_inj
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_Lam_emb_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_emb_mem
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_sfin_of_Lam_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (hR : PI.UnitaryGroupMassFormula.UJClassFin.RatDense) (hC : CrdBounds) : InjStep := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ _ _ _ _ hL _ g g' u hu e
  obtain ⟨hb1, hb2⟩ := hC F E V M b L0 hL
  have hR' := hR F E σ M (gramOf h b) (crdOf b L0) hb1 hb2
  set U : UJ (σ : E →+* E) (gramOf h b) := ⟨matGL b u, matGL_mem σ hσ h b hu⟩ with hUdef
  have e1 : (linOf b (matGL b u) : V → V) '' latSet σ (gramOf h b) b L0 g' = latSet σ (gramOf h b) b L0 g := by
    rw [linOf_matGL]; exact e
  rw [image_latSet] at e1
  have e2 := set_of_coords_inj b e1
  have e3 : PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ (gramOf h b) (crdOf b L0) (PI.UnitaryGroupMassFormula.UJClassFin.emb σ (gramOf h b) U * g') =
      PI.UnitaryGroupMassFormula.UJClassFin.abelian₂ σ (gramOf h b) (crdOf b L0) g := by
    rw [PI.UnitaryGroupMassFormula.UJClassFin.Lam_emb_mul]; exact e2
  have hk := PI.UnitaryGroupMassFormula.UJClassFin.sfin_of_Lam_eq σ (gramOf h b) (crdOf b L0) hR' _ _ e3
  refine ⟨⟨_, PI.UnitaryGroupMassFormula.UJClassFin.emb_mem σ (gramOf h b) U⟩, ⟨_, hk⟩, ?_⟩
  simp only [mul_inv_cancel_left]
end PI.UnitaryGroupMassFormula.UJClassMass
