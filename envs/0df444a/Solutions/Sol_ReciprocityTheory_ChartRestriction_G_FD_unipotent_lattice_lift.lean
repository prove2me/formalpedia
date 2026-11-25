-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.unipotent_lattice_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:41:20.999564+00:00
-- url     : https://prove2.me/submissions/320c46f0-6b8c-4f09-a4b6-d40f4925f202

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscrMulHermitianIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentLatticeLift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_DataX_LZ_periodic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_DataX_exists_gamma
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_DataX_freq_to_beta


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution : UnipotentLatticeLift (E := E) := by
  intro r X u hu hmem
  exact ⟨fun b hb => X.exists_gamma u hu hmem b hb,
    fun la P hP hχ b hb x hx => X.LZ_periodic u hu hmem la P hP hχ b hb x hx,
    fun χ hχ hf => X.freq_to_beta χ hχ hf⟩
end ReciprocityTheory.ChartRestriction.G.FD
