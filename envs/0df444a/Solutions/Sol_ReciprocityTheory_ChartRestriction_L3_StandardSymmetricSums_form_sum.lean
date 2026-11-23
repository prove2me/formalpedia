-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L3.StandardSymmetricSums.form_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:37.270806+00:00
-- url     : https://prove2.me/submissions/09015893-90eb-497d-910f-8822dc40c73b

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
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} {n : ℕ} {e : Fin n → V}
    (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (c d : Fin n → K) :
    h (∑ i, c i • e i) (∑ j, d j • e j) = ∑ i, star (c i) * d i := by
  simp [map_sum, LinearMap.sum_apply, he, mul_comm, starRingEnd_apply]
end ReciprocityTheory.ChartRestriction.L3.StandardSymmetricSums
