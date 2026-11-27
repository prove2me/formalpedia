-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_IntegralOnModel_proof_9bf168785d1d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:54:45.913939+00:00
-- url     : https://prove2.me/submissions/401bea3c-f01d-4ca2-a982-3de85838cb96

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_KrullDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsIntegralPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PIntegralOnModel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_exists_prime_mul_eq_of_not_dvd_4251d0fa5e4b
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open IsDedekindDomain NumberField
namespace GroundTheory.Heights₂.Heights.FourB
namespace IntegralOnModel
theorem _root_.solution (hpt : IntegralPointThroughPrime.Statement) :
    IntegralOnModel.Statement := by
  intro F _ _ R _ _ _ _ _ _ r g s ⟨hs, hg, hpts⟩
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing (𝓞 F) R
  by_contra hndvd
  have hnd : ¬ algebraMap (𝓞 F) R s ∣ r := fun ⟨r', h⟩ => hndvd ⟨r', h⟩
  obtain ⟨P, hP, w, hw, c, hc, hwc⟩ := exists_prime_mul_eq_of_not_dvd hnd
  have hsP : algebraMap (𝓞 F) R s ∈ P := by
    have : w * algebraMap (𝓞 F) R s ∈ P := hwc ▸ P.mul_mem_right r hc
    exact (hP.mem_or_mem this).resolve_left hw
  have hpP : (P.comap (algebraMap (𝓞 F) R)).IsPrime := Ideal.comap_isPrime _ P
  have hp0 : P.comap (algebraMap (𝓞 F) R) ≠ ⊥ := by
    intro h
    have : s ∈ P.comap (algebraMap (𝓞 F) R) := hsP
    rw [h, Submodule.mem_bot] at this
    exact hs this
  let v : HeightOneSpectrum (𝓞 F) := ⟨P.comap (algebraMap (𝓞 F) R), hpP, hp0⟩
  obtain ⟨L, _, _, _, y, hcomp, hint, hyg, ⟨bw, hbw, hbwint⟩, hPnon⟩ :=
    hpt F R v P w g ⟨hP, rfl, hw, hg⟩
  have hys : y (algebraMap (𝓞 F) R s) ≠ 0 := by
    rw [← RingHom.comp_apply, hcomp]
    simp only [RingHom.comp_apply, ne_eq, map_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff]
    exact hs
  have hyr := hpts v L y hcomp hint hyg
  apply hPnon c hc (y r / y (algebraMap (𝓞 F) R s) * bw) _ (RingHom.IsIntegralElem.mul _ hyr hbwint)
  have h1 : y w * y (algebraMap (𝓞 F) R s) = y c * y r := by rw [← map_mul, ← map_mul, hwc]
  calc y r / y (algebraMap (𝓞 F) R s) * bw * y c
      = bw * y w * ((y c * y r) / (y w * y (algebraMap (𝓞 F) R s))) := by
        have hyw : y w ≠ 0 := fun h0 => by simp [h0] at hbw
        field_simp
    _ = 1 := by rw [hbw, ← h1, div_self (mul_ne_zero (fun h0 => by simp [h0] at hbw) hys), one_mul]
end IntegralOnModel
end GroundTheory.Heights₂.Heights.FourB
