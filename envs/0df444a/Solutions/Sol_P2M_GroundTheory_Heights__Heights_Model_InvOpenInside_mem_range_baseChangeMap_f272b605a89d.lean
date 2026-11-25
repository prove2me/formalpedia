-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_InvOpenInside_mem_range_baseChangeMap_f272b605a89d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:05:01.278941+00:00
-- url     : https://prove2.me/submissions/da126782-5452-4d66-bea5-fe9a9695a9a1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsInvOpenInside
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PInvOpenInside

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open GroundTheory.Heights₂.Heights.Model.InvOpenInside
namespace GroundTheory.Heights₂.Heights.Model.InvOpenInside
theorem _root_.solution {X : Scheme.{0}} (f : X ⟶ SpecZ) (p : Nat.Primes) (x : X)
    (hx : Disjoint ((Ideal.span {((p : ℕ) : ℤ)}).primeCompl : Set ℤ) (f.base x).asIdeal) :
    x ∈ Set.range (baseChangeMap f (ZLoc p)) := by
  have hr := PrimeSpectrum.localization_comap_range (ZLoc p)
    (Ideal.span {((p : ℕ) : ℤ)}).primeCompl
  obtain ⟨y, hy⟩ : f.base x ∈ Set.range (PrimeSpectrum.comap (algebraMap ℤ (ZLoc p))) := by
    rw [hr]; exact hx
  have e : algebraMap ℤ (ZLoc p) = Int.castRingHom (ZLoc p) := RingHom.ext_int _ _
  have hy' : f.base x = PrimeSpectrum.comap (Int.castRingHom (ZLoc p)) y :=
    hy.symm.trans (congrFun (congrArg PrimeSpectrum.comap e) y)
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f)
    (g := Spec.map (CommRingCat.ofHom (Int.castRingHom (ZLoc p)))) x y hy'
  exact ⟨z, hz⟩
end GroundTheory.Heights₂.Heights.Model.InvOpenInside
