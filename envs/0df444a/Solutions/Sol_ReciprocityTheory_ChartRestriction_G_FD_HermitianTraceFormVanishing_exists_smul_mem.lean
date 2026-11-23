-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.exists_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:52.02813+00:00
-- url     : https://prove2.me/submissions/0406605d-c9ee-4c4d-ad75-3fbdadc8227d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Lemmata_GeneralBFactAltForm_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Theorems.Thm_Bl_general_b_fact_alt_form_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing
open NumberField ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing
theorem _root_.solution {R F X : Type*} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [AddCommGroup X] [Module F X] [Module R X] [IsScalarTower R F X]
    (S : Submodule R X) {x : X}
    (hx : x ∈ Submodule.span F (S : Set X)) : ∃ d : R, d ≠ 0 ∧ d • x ∈ S := by
  exact Bl.general_b_fact_alt_form.goal1 S hx
end ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing
