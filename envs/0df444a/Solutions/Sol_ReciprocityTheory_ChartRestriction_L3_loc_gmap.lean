-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L3.loc_gmap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:37.800214+00:00
-- url     : https://prove2.me/submissions/59f4b04b-68eb-4903-aa25-e2f295ac87cb

import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_FiniteDimensionalOfOrtho
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_UnimodularOfMemGenusOrtho
import Theorems.Thm_Formalism_HermitianLatticesTheory_gmap_locS_comm


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
theorem _root_.solution (g : V ≃ₗ[K] V) (p : Ideal (𝓞 K)) (L : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.loc (K := K) p (Formalism.HermitianLatticesTheory.gmap g L) = Formalism.HermitianLatticesTheory.gmap g (Formalism.HermitianLatticesTheory.loc (K := K) p L) :=
  (Formalism.HermitianLatticesTheory.gmap_locS_comm g (Formalism.HermitianLatticesTheory.hcompl (K := K) p) L).symm
end ReciprocityTheory.ChartRestriction.L3
