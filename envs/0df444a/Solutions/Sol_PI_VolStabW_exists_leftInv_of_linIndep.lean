-- Prove2me | solution 1 for PI.VolStabW.exists_leftInv_of_linIndep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:01:56.107796+00:00
-- url     : https://prove2.me/submissions/37358433-a06b-4c6e-89ba-42e9b1f598a5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVSecSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVSec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct
namespace PI.VolStabW
theorem _root_.solution {K : Type} [CommRing K] [IsSemisimpleRing K] {a M : ℕ}
    (Z : Fin a → Fin M → K) (hZ : LinearIndependent K Z) :
    ∃ q : Fin M → Fin a → K, ∀ i i', ∑ k, Z i k * q k i' = if i = i' then 1 else 0 := by
  classical
  let ι : (Fin a → K) →ₗ[K] (Fin M → K) := Fintype.linearCombination K Z
  have hinj : Function.Injective ι := by
    intro x y hxy
    have h0 : ∑ i, (x - y) i • Z i = 0 := by
      have := congrArg (fun v => v) hxy
      simp only [ι, Fintype.linearCombination_apply] at this
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, this, sub_self]
    funext i
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hZ _ h0 i)
  obtain ⟨q, hq⟩ := exists_isCompl (LinearMap.range ι)
  let e := LinearEquiv.ofInjective ι hinj
  let p : (Fin M → K) →ₗ[K] (Fin a → K) :=
    e.symm.toLinearMap ∘ₗ (LinearMap.range ι).projectionOnto q hq
  have hp : ∀ x, p (ι x) = x := by
    intro x
    have e1 : ι x = ((e x : LinearMap.range ι) : Fin M → K) := rfl
    simp only [p, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [e1, Submodule.projectionOnto_apply_left, LinearEquiv.symm_apply_apply]
  refine ⟨fun k i' => p (Pi.single k 1) i', fun i i' => ?_⟩
  have hZi : Z i = ∑ k, Z i k • (Pi.single k (1 : K) : Fin M → K) := by
    funext j; simp [Finset.sum_apply, Pi.single_apply]
  have hι : ι (Pi.single i 1) = Z i := by
    simp [ι, Fintype.linearCombination_apply_single]
  have e1 : ∑ k, Z i k * p (Pi.single k 1) i' = p (Z i) i' := by
    conv_rhs => rw [hZi]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [e1, ← hι, hp, Pi.single_apply]
  by_cases h : i = i'
  · subst h; simp
  · simp [h, Ne.symm h]
end PI.VolStabW
