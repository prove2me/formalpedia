-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm.closGen_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:44:24.958407+00:00
-- url     : https://prove2.me/submissions/33d59a81-e6de-4b05-bdd2-2ad33e323895

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_IrredA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitaryGroupOfForm_E_mem

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
    (hTG : ∀ g ∈ UJset ε, ∀ x ∈ T, σ g x ∈ T) (V : Submodule ℂ D) (hV : ∀ v ∈ V, (v : H) ∈ T) :
    ((genSub E V).map D.subtype).topologicalClosure ≤ T := by
  refine Submodule.topologicalClosure_minimal _ ?_ hTc
  have hle : genSub E V ≤ T.comap D.subtype :=
    sInf_le ⟨fun v hv => hV v hv, fun a b v hv => E_mem hD T hTc hTG a b v hv⟩
  rintro _ ⟨v, hv, rfl⟩
  exact hle hv
end ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm
