-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm.E_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:22:12.302883+00:00
-- url     : https://prove2.me/submissions/d3c618c5-29ed-47c6-bb3a-e78f9f86576a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_IrredA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitaryGroupOfForm_actM_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitaryGroupOfForm_actM_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitaryGroupOfForm_actM_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitaryGroupOfForm_actM_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
open ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm
variable {n : ℕ}
variable {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
namespace ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm
theorem _root_.solution (ε : Fin n → Bool) (a b : Fin n) :
    E a b = (1 / 2 : ℂ) • (actM E (Matrix.single a b 1 - Jm ε * (Matrix.single a b 1)ᴴ * Jm ε) -
      Complex.I • actM E (Complex.I • (Matrix.single a b 1 + Jm ε * (Matrix.single a b 1)ᴴ * Jm ε))) := by
  rw [actM_sub, actM_smul, actM_add, actM_single, smul_smul, Complex.I_mul_I, neg_one_smul]
  have h2 : ∀ A B : Module.End ℂ M, A - B - -(A + B) = (2 : ℂ) • A := fun A B => by
    rw [two_smul]
    abel
  rw [h2, smul_smul]
  norm_num
end ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm
