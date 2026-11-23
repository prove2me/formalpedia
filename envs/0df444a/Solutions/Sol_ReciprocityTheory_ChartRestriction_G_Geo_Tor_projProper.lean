-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.projProper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:29:21.368917+00:00
-- url     : https://prove2.me/submissions/92b1e590-7f8b-4bef-9c7e-03e55676c2c0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArcSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isProper_str

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] MvPolynomial.gradedAlgebra
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution : ProjProperSt := by
  intro R _ X f hf
  obtain ⟨N, i, hi, rfl⟩ := hf
  haveI := hi
  haveI := isProper_str R N
  infer_instance
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
