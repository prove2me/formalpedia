-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.xp_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:34:06.925871+00:00
-- url     : https://prove2.me/submissions/3c98c49c-b1ee-408c-a12b-ebd536dd67dd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_coeff_xp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (k : ℕ) (f : PowerSeries R) :
    xp k (f.map φ) = (xp k f).map φ := by
  ext n
  simp only [coeff_xp, PowerSeries.coeff_map]
  split_ifs <;> simp
end ReciprocityTheory.ChartRestriction.L1
