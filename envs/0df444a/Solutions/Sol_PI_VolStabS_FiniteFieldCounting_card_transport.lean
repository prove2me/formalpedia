-- Prove2me | solution 1 for PI.VolStabS.FiniteFieldCounting.card_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:50:52.108853+00:00
-- url     : https://prove2.me/submissions/87e7de93-a187-48a7-906e-df20affd033c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS
open PI.VolStabS.FiniteFieldCounting
namespace PI.VolStabS.FiniteFieldCounting
theorem _root_.solution {k K : Type} [Field k] [CommRing K] [Algebra k K] (σ : K ≃ₐ[k] K)
    (e : K ≃ₐ[k] k × k) (he : ∀ x, e (σ x) = (e x).swap) {M a : ℕ}
    (J : Matrix (Fin M) (Fin M) K) (T : Matrix (Fin a) (Fin a) K) :
    Nat.card {X : Fin a → Fin M → K // ffGram (σ : K →+* K) J X = T} =
      Nat.card {Y : Fin a → Fin M → k × k //
        ffGram (FiniteFieldSplitting.swapR k) (J.map e) Y = T.map e} := by
  apply Nat.card_congr
  refine Equiv.subtypeEquiv (Equiv.piCongrRight fun _ => Equiv.piCongrRight fun _ => e.toEquiv) ?_
  intro X
  have key : ffGram (FiniteFieldSplitting.swapR k) (J.map e)
      ((Equiv.piCongrRight fun _ => Equiv.piCongrRight fun _ => e.toEquiv) X) =
        (ffGram (σ : K →+* K) J X).map e := by
    funext i j
    show ∑ a', ∑ b, (e (X i a')).swap * e (J a' b) * e (X j b) =
      e (∑ a', ∑ b, σ (X i a') * J a' b * X j b)
    rw [map_sum]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, map_mul, he]
  rw [key]
  constructor
  · intro h
    rw [h]
  · intro h
    ext i j
    exact e.injective (congrFun (congrFun h i) j)
end PI.VolStabS.FiniteFieldCounting
