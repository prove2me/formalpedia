-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L3.StandardSymmetricSums.mem_lat_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:18.84659+00:00
-- url     : https://prove2.me/submissions/5a469656-a55f-4785-b0fa-1b8be8ccb771

import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_MassSt
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_FiniteDimensionalOfOrtho
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L3
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
open ReciprocityTheory.ChartRestriction.L3.StandardSymmetricSums
namespace ReciprocityTheory.ChartRestriction.L3.StandardSymmetricSums
theorem _root_.solution {n : ℕ} {e : Fin n → V} (x : V) :
    x ∈ Submodule.span (𝓞 K) (Set.range e) ↔
      ∃ c : Fin n → 𝓞 K, ∑ i, algebraMap (𝓞 K) K (c i) • e i = x := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  simp only [algebraMap_smul]
end ReciprocityTheory.ChartRestriction.L3.StandardSymmetricSums
