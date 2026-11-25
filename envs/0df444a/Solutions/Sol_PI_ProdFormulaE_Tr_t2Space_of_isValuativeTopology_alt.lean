-- Prove2me | solution 1 for PI.ProdFormulaE.Tr.t2Space_of_isValuativeTopology_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:06:11.138126+00:00
-- url     : https://prove2.me/submissions/663893fa-471e-42fb-94ba-8d141e66d532

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_TrBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_T2SpaceOfIsValuativeTopology

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField TensorProduct ValuativeRel Filter Topology
open PI PI.ProdFormulaE PI.ProdFormulaE.Tr
variable {F : Type} [Field F] [NumberField F]
namespace PI.ProdFormulaE.Tr
theorem _root_.solution (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsValuativeTopology K] : T2Space K := by
  apply IsTopologicalAddGroup.t2Space_of_zero_sep
  intro x hx
  refine ⟨{z | valuation K z < valuation K x}, ?_, fun h => lt_irrefl (valuation K x) h⟩
  rw [IsValuativeTopology.mem_nhds_zero_iff]
  exact ⟨Units.mk0 _ ((Valuation.ne_zero_iff _).2 hx), fun z hz => by simpa using hz⟩
end PI.ProdFormulaE.Tr
