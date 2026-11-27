-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_isPullBC_frame_self_2ef26e93f100
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:00:36.141811+00:00
-- url     : https://prove2.me/submissions/eae938ed-9869-4ba6-9c24-65e716298e9e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_InstFintypeSumElim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ScaledRankOneLeStandardRankOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
theorem _root_.solution {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    {x : (Σ k, ι k) → Ω} {z : (Σ k, ι' k) → Ω} (hx : ∀ p, x p = 1)
    (hxz : ∀ p, bcCoord (Ω₁ := Ω) x z p = 1) {N : ℕ} {V : Type*} [AddCommGroup V] [Module Ω V]
    (b : Module.Basis (Fin N) Ω V) :
    IsPullBC O (Ω₁ := Ω) x z (LinearEquiv.refl Ω V).toLinearMap (frameBundle O (mseg x) b)
      (frameBundle O (mseg (bcCoord x z)) b) := by
  intro s _
  have tr : ∀ a : Ω, a ∈ chartRing O (mseg (bcCoord (Ω₁ := Ω) x z)) s ↔
      a ∈ chartRing O (mseg x) (restrictChart s) := fun a => by
    rw [mem_chartRing_of_one hxz, mem_chartRing_of_one hx]
  apply le_antisymm
  · intro v hv
    apply AddSubgroup.subset_closure
    exact ⟨1, one_mem _, v, mem_frameLat.mpr fun q => (tr _).mp (mem_frameLat.mp hv q),
      by simp⟩
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨a, ha, e, he, rfl⟩
    refine mem_frameLat.mpr fun q => ?_
    rw [LinearEquiv.coe_toLinearMap, LinearEquiv.refl_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact mul_mem ha ((tr _).mpr (mem_frameLat.mp he q))
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
