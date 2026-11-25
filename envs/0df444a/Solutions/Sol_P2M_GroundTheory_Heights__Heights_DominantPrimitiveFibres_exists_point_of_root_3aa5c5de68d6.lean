-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DominantPrimitiveFibres_exists_point_of_root_3aa5c5de68d6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:45:38.559118+00:00
-- url     : https://prove2.me/submissions/edc10c3b-ee1b-4f63-be71-5b88fa9cbc5f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StDominantPrimitiveFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDominantFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveElementFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PDominantPrimitiveFibres
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DominantPrimitiveFibres_exists_lift_of_ringHom_66129c592bd6

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets
open GroundTheory.Heights₂.Heights.DominantPrimitiveFibres
namespace GroundTheory.Heights₂.Heights.DominantPrimitiveFibres
theorem _root_.solution {R' B' : Type*} [CommRing R'] [CommRing B'] [Algebra R' B']
    [Algebra.IsIntegral R' B'] (ℓ : B') (m : Polynomial R')
    (hdiv : ∀ p : Polynomial R', Polynomial.aeval ℓ p = 0 → m ∣ p) (ev : R' →+* ℂ)
    (hev : Function.Surjective ev) (τ : ℂ) (hτ : (m.map ev).IsRoot τ) :
    ∃ ψ : B' →+* ℂ, ψ.comp (algebraMap R' B') = ev ∧ ψ ℓ = τ := by
  let f : Polynomial R' →+* B' := (Polynomial.aeval ℓ).toRingHom
  have hc : f.comp Polynomial.C = algebraMap R' B' := RingHom.ext fun r => Polynomial.aeval_C ℓ r
  have hfint : f.IsIntegral := by
    intro z
    obtain ⟨p, hp, hpz⟩ := Algebra.IsIntegral.isIntegral (R := R') z
    refine ⟨p.map Polynomial.C, hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, hc]
    exact hpz
  let evτ : Polynomial R' →+* ℂ := (Polynomial.evalRingHom τ).comp (Polynomial.mapRingHom ev)
  have hsurj : Function.Surjective evτ := fun z => by
    obtain ⟨r, rfl⟩ := hev z
    exact ⟨Polynomial.C r, by simp [evτ]⟩
  have hker : RingHom.ker f ≤ RingHom.ker evτ := by
    intro p hp
    obtain ⟨q, rfl⟩ := hdiv p hp
    rw [RingHom.mem_ker, map_mul]
    have : evτ m = 0 := hτ
    rw [this, zero_mul]
  obtain ⟨ψ, hψ⟩ := exists_lift_of_ringHom f hfint evτ hsurj hker
  refine ⟨ψ, RingHom.ext fun r => ?_, ?_⟩
  · have h := DFunLike.congr_fun hψ (Polynomial.C r)
    simpa [f, evτ] using h
  · have h := DFunLike.congr_fun hψ Polynomial.X
    simpa [f, evτ] using h
end GroundTheory.Heights₂.Heights.DominantPrimitiveFibres
