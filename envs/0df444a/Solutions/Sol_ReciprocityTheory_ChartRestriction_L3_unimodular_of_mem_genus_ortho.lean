-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L3.unimodular_of_mem_genus_ortho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:28:16.30746+00:00
-- url     : https://prove2.me/submissions/77d340a5-ddbf-4dc6-a273-a451e38ea2ee

import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_FiniteDimensionalOfOrtho
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_UnimodularOfMemGenusOrtho
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_loc_gmap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_isUnimodularAt_gmap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_isUnimodularAt_of_loc_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_isUnimodularAt_of_ortho


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
namespace ReciprocityTheory.ChartRestriction.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) {I : Submodule (𝓞 K) V} {n : ℕ} (hI : Formalism.HermitianLatticesTheory.IsOrthoLattice h I n)
    {L : Submodule (𝓞 K) V} (hL : L ∈ Formalism.HermitianLatticesTheory.genus h I) :
    Submodule.IsLattice K L ∧ ∀ p : Ideal (𝓞 K), p.IsMaximal → Formalism.HermitianLatticesTheory.IsUnimodularAt h p L := by
  refine ⟨hL.1, fun p hp => ?_⟩
  obtain ⟨g, hg, hgI⟩ := hL.2 p hp
  rw [← loc_gmap] at hgI
  rw [← isUnimodularAt_of_loc_eq p hgI, isUnimodularAt_gmap hg]
  exact isUnimodularAt_of_ortho hK hs hI p hp
end ReciprocityTheory.ChartRestriction.L3
