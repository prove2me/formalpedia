-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L3.isLattice_of_ortho
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:37.549642+00:00
-- url     : https://prove2.me/submissions/28dbf892-3d03-4ded-87e6-e658d5ee070a

import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_MassSt
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_FiniteDimensionalOfOrtho

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
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {n : ℕ}
    (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) : Submodule.IsLattice K L := by
  obtain ⟨e, hli, hsp, rfl, -⟩ := hL
  refine ⟨Submodule.fg_span (Set.finite_range e), ?_⟩
  rw [Submodule.span_span_of_tower, hsp]
end ReciprocityTheory.ChartRestriction.L3
