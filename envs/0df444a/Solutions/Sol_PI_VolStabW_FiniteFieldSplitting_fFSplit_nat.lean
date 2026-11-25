-- Prove2me | solution 1 for PI.VolStabW.FiniteFieldSplitting.fFSplit_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:30:31.621648+00:00
-- url     : https://prove2.me/submissions/7c5b959a-701a-4589-b352-2a1f5d58cd5c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFS
import Theorems.Thm_PI_VolStabW_FiniteFieldSplitting_card_pairs
import Theorems.Thm_PI_VolStabW_FiniteFieldSplitting_gram_iff

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
open PI.VolStabW.FiniteFieldSplitting
open Matrix
variable {k : Type} [Field k] [Finite k] {M a : ℕ}
namespace PI.VolStabW.FiniteFieldSplitting
theorem _root_.solution (M a : ℕ) (ha : a ≤ M)
    (J : Matrix (Fin M) (Fin M) (k × k)) (hJ : ∀ i j, (J j i).swap = J i j) (hJd : IsUnit J.det)
    (T : Matrix (Fin a) (Fin a) (k × k)) (hT : ∀ i j, (T j i).swap = T i j) (hTd : IsUnit T.det) :
    Nat.card {X : Fin a → Fin M → k × k // ffGram (swapR k) J X = T} =
      (∏ i : Fin a, (Nat.card k ^ M - Nat.card k ^ (i : ℕ))) * Nat.card k ^ (a * (M - a)) := by
  classical
  set A := J.map Prod.fst with hA
  set T1 := T.map Prod.fst with hT1
  have hAd : IsUnit A.det := by
    have := hJd.map (RingHom.fst k k)
    rwa [RingHom.map_det] at this
  have hT1d : IsUnit T1.det := by
    have := hTd.map (RingHom.fst k k)
    rwa [RingHom.map_det] at this
  let e : (Fin a → Fin M → k × k) ≃ Matrix (Fin a) (Fin M) k × Matrix (Fin M) (Fin a) k :=
    { toFun := fun X ↦ (T1⁻¹ * V1 X, A * (U1 X)ᵀ)
      invFun := fun WP r i ↦ ((A⁻¹ * WP.2)ᵀ r i, (T1 * WP.1) r i)
      left_inv := fun X ↦ by
        funext r i
        simp only [Matrix.nonsing_inv_mul_cancel_left _ _ hAd,
          Matrix.mul_nonsing_inv_cancel_left _ _ hT1d, Matrix.transpose_transpose]
        rfl
      right_inv := fun WP ↦ by
        have h1 : V1 (fun r i ↦ ((A⁻¹ * WP.2)ᵀ r i, (T1 * WP.1) r i)) = T1 * WP.1 := rfl
        have h2 : U1 (fun r i ↦ ((A⁻¹ * WP.2)ᵀ r i, (T1 * WP.1) r i)) = (A⁻¹ * WP.2)ᵀ := rfl
        simp only [h1, h2, Matrix.transpose_transpose, Matrix.nonsing_inv_mul_cancel_left _ _ hT1d,
          Matrix.mul_nonsing_inv_cancel_left _ _ hAd] }
  have hcond : ∀ X, ffGram (swapR k) J X = T ↔ (e X).1 * (e X).2 = 1 := by
    intro X
    rw [gram_iff J hJ T hT X, ← hT1, ← hA]
    change V1 X * A * (U1 X)ᵀ = T1 ↔ T1⁻¹ * V1 X * (A * (U1 X)ᵀ) = 1
    have hre : T1⁻¹ * V1 X * (A * (U1 X)ᵀ) = T1⁻¹ * (V1 X * A * (U1 X)ᵀ) := by
      simp only [Matrix.mul_assoc]
    rw [hre]
    constructor
    · intro h
      rw [h, Matrix.nonsing_inv_mul _ hT1d]
    · intro h
      calc V1 X * A * (U1 X)ᵀ = T1 * (T1⁻¹ * (V1 X * A * (U1 X)ᵀ)) :=
            (Matrix.mul_nonsing_inv_cancel_left _ _ hT1d).symm
        _ = T1 := by rw [h, Matrix.mul_one]
  rw [Nat.card_congr (Equiv.subtypeEquiv (p := fun X ↦ ffGram (swapR k) J X = T)
    (q := fun WP : Matrix (Fin a) (Fin M) k × Matrix (Fin M) (Fin a) k ↦ WP.1 * WP.2 = 1) e hcond),
    card_pairs ha]
end PI.VolStabW.FiniteFieldSplitting
