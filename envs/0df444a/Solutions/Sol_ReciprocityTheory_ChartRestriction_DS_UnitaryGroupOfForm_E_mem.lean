-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm.E_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:35:38.537795+00:00
-- url     : https://prove2.me/submissions/ce56fffe-badb-4152-8196-1c23a6220078

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_IrredA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitaryGroupOfForm_inG_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitaryGroupOfForm_inG_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitaryGroupOfForm_E_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitaryGroupOfForm_actM_mem

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
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
variable {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
namespace ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm
theorem _root_.solution (hD : IsDerivedOn ε σ D E) (T : Submodule ℂ H) (hTc : IsClosed (T : Set H))
    (hTG : ∀ g ∈ UJset ε, ∀ x ∈ T, σ g x ∈ T) (a b : Fin n) (v : D) (hv : (v : H) ∈ T) :
    ((E a b v : D) : H) ∈ T := by
  have h := E_eq E ε a b
  have e : ((E a b v : D) : H) = (1 / 2 : ℂ) • (((actM E (Matrix.single a b 1 - Jm ε * (Matrix.single a b 1)ᴴ * Jm ε) v : D) : H) -
      Complex.I • ((actM E (Complex.I • (Matrix.single a b 1 + Jm ε * (Matrix.single a b 1)ᴴ * Jm ε)) v : D) : H)) := by
    rw [h]
    simp
  rw [e]
  exact T.smul_mem _ (T.sub_mem (actM_mem hD T hTc hTG (inG_sub ε _) v hv)
    (T.smul_mem _ (actM_mem hD T hTc hTG (inG_add ε _) v hv)))
end ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm
