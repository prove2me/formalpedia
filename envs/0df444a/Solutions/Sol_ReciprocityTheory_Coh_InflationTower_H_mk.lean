-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationTower.H_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:27.169381+00:00
-- url     : https://prove2.me/submissions/466d1973-75cc-48ff-b6f1-88fcdd4e177b

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_IsSuccSubset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
noncomputable section
universe u
open Cx
open ReciprocityTheory.Coh.InflationTower
variable {R : Type u} [CommRing R]
namespace ReciprocityTheory.Coh.InflationTower
theorem _root_.solution {A B : Cx R} (φ : Hom A B) (n : ℕ) (z : A.Z n) :
    φ.H n (Submodule.Quotient.mk z) = Submodule.Quotient.mk (φ.Z n z) := rfl
end ReciprocityTheory.Coh.InflationTower
