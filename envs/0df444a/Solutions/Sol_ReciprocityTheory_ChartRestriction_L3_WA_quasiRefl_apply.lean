-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L3.WA.quasiRefl_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:20:31.068909+00:00
-- url     : https://prove2.me/submissions/f7dc2cd9-aa68-4184-98ba-c3cc7bbc7b5f

import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsIsomFix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
namespace ReciprocityTheory.ChartRestriction.L3.WA
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (u : V) (a : K) (v : V) :
    quasiRefl h u a v = v - (a * h u v) • u := by
  simp [quasiRefl, smul_smul]
end ReciprocityTheory.ChartRestriction.L3.WA
