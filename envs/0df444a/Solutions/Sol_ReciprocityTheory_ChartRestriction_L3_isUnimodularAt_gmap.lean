-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L3.isUnimodularAt_gmap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:19:06.115536+00:00
-- url     : https://prove2.me/submissions/40ccf91b-4e1c-4900-b380-9615e91fd4a1

import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_FiniteDimensionalOfOrtho
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_UnimodularOfMemGenusOrtho
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_loc_gmap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_gmap_injective
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovolBound_dualAt_gmap


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
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} {g : V ≃ₗ[K] V}
    (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (p : Ideal (𝓞 K)) (L : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.IsUnimodularAt h p (Formalism.HermitianLatticesTheory.gmap g L) ↔ Formalism.HermitianLatticesTheory.IsUnimodularAt h p L := by
  unfold Formalism.HermitianLatticesTheory.IsUnimodularAt
  rw [loc_gmap, Formalism.HermitianLatticesTheory.genusCovolBound_dualAt_gmap h g hg]
  exact (gmap_injective g).eq_iff
end ReciprocityTheory.ChartRestriction.L3
