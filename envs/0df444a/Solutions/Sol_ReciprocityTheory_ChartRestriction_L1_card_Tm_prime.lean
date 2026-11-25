-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.card_Tm_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:54:13.511671+00:00
-- url     : https://prove2.me/submissions/ca9ad1d5-0325-4312-ad05-6c8d798722b0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFrobSer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModKronSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Tm_prime
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Tm_prime_notMem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_Tm_prime_inj

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
theorem _root_.solution {p : ℕ} (hp : p.Prime) : (Tm p).card = p + 1 := by
  rw [Tm_prime hp, Finset.card_insert_of_notMem (Tm_prime_notMem hp),
    Finset.card_image_of_injective _ (Tm_prime_inj p), Finset.card_range]
end ReciprocityTheory.ChartRestriction.L1
