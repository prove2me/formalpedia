-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L3.isUnimodularAt_of_loc_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:41:45.520918+00:00
-- url     : https://prove2.me/submissions/7ca1ffc4-a865-494c-b8fa-fe8d18f3e5dc

import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_FiniteDimensionalOfOrtho
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_UnimodularOfMemGenusOrtho

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
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} (p : Ideal (𝓞 K))
    {L M : Submodule (𝓞 K) V} (he : Formalism.HermitianLatticesTheory.loc (K := K) p L = Formalism.HermitianLatticesTheory.loc (K := K) p M) :
    Formalism.HermitianLatticesTheory.IsUnimodularAt h p L ↔ Formalism.HermitianLatticesTheory.IsUnimodularAt h p M := by
  unfold Formalism.HermitianLatticesTheory.IsUnimodularAt
  rw [he]
end ReciprocityTheory.ChartRestriction.L3
