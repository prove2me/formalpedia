-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.B3.IotaPl.mem_smallIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:08:34.077156+00:00
-- url     : https://prove2.me/submissions/f8db34b8-d04f-461c-b66d-c71663c90fe3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_LatticeEmbeddings_IotaPlaceB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_LatticeEmbeddings_IotaPlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.B3 ReciprocityTheory.ChartRestriction.B3.IotaPl
variable {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
namespace ReciprocityTheory.ChartRestriction.B3.IotaPl
theorem _root_.solution (ι : K →+* ℂ_[p]) (y : 𝓞 K) : y ∈ smallIdeal ι ↔ ‖ι (y : K)‖ < 1 := Iff.rfl
end ReciprocityTheory.ChartRestriction.B3.IotaPl
