-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CntFormula.dvr_prim_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:01:33.718849+00:00
-- url     : https://prove2.me/submissions/7c2a0700-a5d5-40d7-8024-62b2d06533b3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_DensGSDvr
import Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_indep_of_red
import Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_sat_of_red
import Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_red_of_indep_sat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CntFormula
open Classical ValuativeRel
variable (F : Type) [Field F] [ValuativeRel F]
variable {F}
namespace PI.UnitaryGroupMassFormula.CntFormula
theorem _root_.solution [IsDiscreteValuationRing 𝒪[F]] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    {ι : Type} [Fintype ι] {n : ℕ} (X : ι → Fin n → F) (hX : ∀ i k, X i k ∈ 𝒪[F]) :
    (LinearIndependent F X ∧ SatF F X) ↔ LinearIndependent 𝓀[F] (redM F X) :=
  ⟨fun h => red_of_indep_sat hϖ X hX h.1 h.2, fun h => ⟨indep_of_red X hX h, sat_of_red X hX h⟩⟩
end PI.UnitaryGroupMassFormula.CntFormula
