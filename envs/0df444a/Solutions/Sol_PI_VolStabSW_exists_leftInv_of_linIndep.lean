-- Prove2me | solution 1 for PI.VolStabSW.exists_leftInv_of_linIndep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:55:44.416993+00:00
-- url     : https://prove2.me/submissions/958502fb-66a0-4e18-a794-7508fd69b645

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVSecSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVSec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct
namespace PI.VolStabSW
theorem _root_.solution {K : Type} [CommRing K] [IsSemisimpleRing K] {a M : ℕ}
    (Z : Fin a → Fin M → K) (hZ : LinearIndependent K Z) :
    ∃ q : Fin M → Fin a → K, ∀ i i', ∑ k, Z i k * q k i' = if i = i' then 1 else 0 := by
  classical
  let f : (Fin a → K) →ₗ[K] (Fin M → K) := ∑ i, (LinearMap.proj i).smulRight (Z i)
  have hf_apply : ∀ c, f c = ∑ i, c i • Z i := by
    intro c
    simp [f, LinearMap.sum_apply]
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    rw [hf_apply] at hc
    funext i
    exact Fintype.linearIndependent_iff.1 hZ c hc i
  obtain ⟨g, hg⟩ : ∃ g : (Fin M → K) →ₗ[K] (Fin a → K), g ∘ₗ f = LinearMap.id := by
    first
    | exact IsSemisimpleModule.extension_property f hf LinearMap.id
    | (obtain ⟨C, hC⟩ := exists_isCompl (LinearMap.range f)
       exact ⟨(LinearEquiv.ofInjective f hf).symm.toLinearMap ∘ₗ
         Submodule.linearProjOfIsCompl _ _ hC, by
           ext c : 1
           simp [Submodule.linearProjOfIsCompl_apply_left]⟩)
  refine ⟨fun k i' => g (fun j => if k = j then 1 else 0) i', fun i i' => ?_⟩
  have hZi : Z i = ∑ k, Z i k • (fun j => if k = j then (1 : K) else 0) := pi_eq_sum_univ (Z i)
  have key : g (Z i) = fun j => if i = j then 1 else 0 := by
    have hZf : Z i = f (fun j => if i = j then 1 else 0) := by
      rw [hf_apply]
      simp
    rw [hZf, ← LinearMap.comp_apply, hg, LinearMap.id_apply]
  have h2 := congrFun key i'
  rw [hZi, map_sum] at h2
  simpa [Finset.sum_apply, map_smul] using h2
end PI.VolStabSW
