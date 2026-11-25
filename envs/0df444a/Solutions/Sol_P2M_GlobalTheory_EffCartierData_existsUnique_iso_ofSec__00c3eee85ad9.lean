-- Prove2me | solution 1 for P2M_GlobalTheory_EffCartierData_existsUnique_iso_ofSec__00c3eee85ad9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:33:22.612514+00:00
-- url     : https://prove2.me/submissions/d81100a5-98eb-44bf-ae5e-a51da8b885e9

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
import Theorems.Thm_GlobalTheory_Cartier_existsUnique_secMaps


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open Cartier
open GlobalTheory.EffCartierData
variable {X Y Z : Scheme.{0}}
variable (D D' : EffCartierData X)
namespace GlobalTheory.EffCartierData
theorem _root_.solution {L : LB X} (hL : L.IsLB) (s : L.Sec) (hs : IsRegularSec s) :
    ∃! w : LB.Iso (ofSec hL s hs).lb L, w.IsGen ∧ SecMaps w (ofSec hL s hs).canonical s :=
  existsUnique_secMaps (A := (ofSec hL s hs).lb) hs fun p q => ((ofSec hL s hs).assoc p q).symm
end GlobalTheory.EffCartierData
