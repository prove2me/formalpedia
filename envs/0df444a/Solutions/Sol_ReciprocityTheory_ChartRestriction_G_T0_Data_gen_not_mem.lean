-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.gen_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:12:19.441353+00:00
-- url     : https://prove2.me/submissions/45412e6b-7279-4b25-9500-01d69b2379ee

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DiscLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscBDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormFactorizationClause
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UnitAtIntAt
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_T0_Data_gen_prime__368b34e1e491
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_gen_span
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValUFD_gen_dvd_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution {p q : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) (hq : q ∈ d.HtOne)
    (hqp : q ≠ p) : d.gen q ∉ p := by
  intro hm
  rw [d.gen_span hp, Ideal.mem_span_singleton] at hm
  have e := (ValUFD.gen_dvd_iff (fun p hp hh => d.gen_span ⟨hp, hh⟩) hp (d.gen_prime' hq)).mp hm
  exact hqp (by rw [e, ← d.gen_span hq])
end ReciprocityTheory.ChartRestriction.G.T0.Data
