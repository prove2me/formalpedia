-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L3.mass_pos_of_ortho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:57:57.743664+00:00
-- url     : https://prove2.me/submissions/34fe3b03-dbbb-49a1-bf4f-fb614509ffb0

import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_MassSt
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_FiniteDimensionalOfOrtho
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_finiteDimensional_of_ortho
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_isLattice_of_ortho
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_trace_pos_of_ortho
import Theorems.Thm_Formalism_HermitianLatticesTheory_massBasic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L3
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
open StandardSymmetricSums
namespace ReciprocityTheory.ChartRestriction.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) {L : Submodule (𝓞 K) V} {n : ℕ} (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) :
    0 < Formalism.HermitianLatticesTheory.mass h L := by
  have := finiteDimensional_of_ortho hL
  exact (Formalism.HermitianLatticesTheory.massBasic K V h hs (trace_pos_of_ortho hK hs hL) L (isLattice_of_ortho hL)).2.2
end ReciprocityTheory.ChartRestriction.L3
