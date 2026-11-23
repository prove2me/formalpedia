-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.unif_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:08.086522+00:00
-- url     : https://prove2.me/submissions/73bf7144-a762-4beb-bd6b-115163ed4541

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OpIsDVR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K] (D N : ℕ)
omit [NumberField K]
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    (Data.unif la : 𝓞 K) ∈ la.asIdeal ∧ (Data.unif la : 𝓞 K) ∉ la.asIdeal ^ 2 := by
  have hex : ∃ ϖ : 𝓞 K, ϖ ∈ la.asIdeal ∧ ϖ ∉ la.asIdeal ^ 2 := by
    obtain ⟨π, hπ⟩ := la.intValuation_exists_uniformizer
    refine ⟨π, ?_, ?_⟩
    · rw [← la.intValuation_lt_one_iff_mem, hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      norm_num
    · rw [← la.intValuation_le_pow_iff_mem, hπ, WithZero.exp_le_exp]
      norm_num
  rw [Data.unif, dif_pos hex]
  exact hex.choose_spec
end ReciprocityTheory.ChartRestriction.G.T0
