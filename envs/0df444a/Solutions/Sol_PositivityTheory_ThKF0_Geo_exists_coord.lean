-- Prove2me | solution 1 for PositivityTheory.ThKF0.Geo.exists_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:09:05.192505+00:00
-- url     : https://prove2.me/submissions/cf9a6745-1c9e-4755-8df7-f297c51ee3bd

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_LagrangianUniqueness_GeoAlg
import Theorems.Thm_PositivityTheory_ThKF0_Geo_emb_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix GlobalTheory.WeilM Module
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Geo
variable {F : Type} [Field F] {A : Type} [CommRing A] [Algebra F A]
variable {VA : Type} [AddCommGroup VA] [Module A VA] [Module F VA] [IsScalarTower F A VA] {BA : VA → VA → A}
  {κ : Type} [Fintype κ] {V : Type} [AddCommGroup V] [Module F V]
namespace PositivityTheory.ThKF0.Geo
theorem _root_.solution (hA : Function.Injective (algebraMap F A)) (co : Darboux BA κ) (inc : V →ₗ[F] VA)
    (hr : ∀ x, ∃ w, co.e (inc x) = emb (F := F) A κ w) :
    ∃ r : V →ₗ[F] (κ → F) × (κ → F), ∀ x, co.e (inc x) = emb A κ (r x) := by
  choose f hf using hr
  refine ⟨{ toFun := f, map_add' := ?_, map_smul' := ?_ }, hf⟩
  · intro x y
    apply emb_inj hA
    rw [map_add, ← hf, ← hf, ← hf, map_add, map_add]
  · intro c x
    apply emb_inj hA
    rw [RingHom.id_apply, map_smul, ← hf, ← hf, map_smul]
    exact co.e.toLinearMap.map_smul_of_tower c (inc x)
end PositivityTheory.ThKF0.Geo
