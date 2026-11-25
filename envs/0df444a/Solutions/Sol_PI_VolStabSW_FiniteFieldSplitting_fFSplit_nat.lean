-- Prove2me | solution 1 for PI.VolStabSW.FiniteFieldSplitting.fFSplit_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:20:24.424551+00:00
-- url     : https://prove2.me/submissions/2c3745d7-fba5-42c9-9b4e-1dcdd01369d8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFS
import Theorems.Thm_PI_VolStabSW_FiniteFieldSplitting_card_pairs
import Theorems.Thm_PI_VolStabSW_FiniteFieldSplitting_gram_iff

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
open PI.VolStabSW.FiniteFieldSplitting
open Matrix
variable {k : Type} [Field k] [Finite k] {M a : ℕ}
namespace PI.VolStabSW.FiniteFieldSplitting
theorem _root_.solution (M a : ℕ) (ha : a ≤ M)
    (J : Matrix (Fin M) (Fin M) (k × k)) (hJ : ∀ i j, (J j i).swap = J i j) (hJd : IsUnit J.det)
    (T : Matrix (Fin a) (Fin a) (k × k)) (hT : ∀ i j, (T j i).swap = T i j) (hTd : IsUnit T.det) :
    Nat.card {X : Fin a → Fin M → k × k // ffGram (swapR k) J X = T} =
      (∏ i : Fin a, (Nat.card k ^ M - Nat.card k ^ (i : ℕ))) * Nat.card k ^ (a * (M - a)) := by
  classical
  have hJ1 : IsUnit (J.map Prod.fst).det := by
    have h1 := (Prod.isUnit_iff.mp hJd).1
    rwa [show J.det.1 = (J.map Prod.fst).det from RingHom.map_det (RingHom.fst k k) J] at h1
  have hT1 : IsUnit (T.map Prod.fst).det := by
    have h1 := (Prod.isUnit_iff.mp hTd).1
    rwa [show T.det.1 = (T.map Prod.fst).det from RingHom.map_det (RingHom.fst k k) T] at h1
  have e : {X : Fin a → Fin M → k × k // ffGram (swapR k) J X = T} ≃
      {WP : Matrix (Fin a) (Fin M) k × Matrix (Fin M) (Fin a) k // WP.1 * WP.2 = 1} :=
    { toFun := fun X => ⟨((T.map Prod.fst)⁻¹ * V1 X.1, J.map Prod.fst * (U1 X.1)ᵀ), by
        have h := (gram_iff J hJ T hT X.1).1 X.2
        show (T.map Prod.fst)⁻¹ * V1 X.1 * (J.map Prod.fst * (U1 X.1)ᵀ) = 1
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (V1 X.1), h, Matrix.nonsing_inv_mul _ hT1]⟩
      invFun := fun WP => ⟨fun r i => ((((J.map Prod.fst)⁻¹ * WP.1.2)ᵀ) r i,
          (T.map Prod.fst * WP.1.1) r i), by
        rw [gram_iff J hJ T hT]
        have hU : U1 (fun r i => ((((J.map Prod.fst)⁻¹ * WP.1.2)ᵀ) r i,
            (T.map Prod.fst * WP.1.1) r i)) = ((J.map Prod.fst)⁻¹ * WP.1.2)ᵀ := rfl
        have hV : V1 (fun r i => ((((J.map Prod.fst)⁻¹ * WP.1.2)ᵀ) r i,
            (T.map Prod.fst * WP.1.1) r i)) = T.map Prod.fst * WP.1.1 := rfl
        rw [hU, hV, Matrix.transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc (J.map Prod.fst),
          Matrix.mul_nonsing_inv _ hJ1, Matrix.one_mul, Matrix.mul_assoc, WP.2, Matrix.mul_one]⟩
      left_inv := fun X => by
        apply Subtype.ext
        funext r i
        apply Prod.ext
        · show (((J.map Prod.fst)⁻¹ * (J.map Prod.fst * (U1 X.1)ᵀ))ᵀ) r i = (X.1 r i).1
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJ1, Matrix.one_mul,
            Matrix.transpose_transpose]
          rfl
        · show (T.map Prod.fst * ((T.map Prod.fst)⁻¹ * V1 X.1)) r i = (X.1 r i).2
          rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hT1, Matrix.one_mul]
          rfl
      right_inv := fun WP => by
        apply Subtype.ext
        apply Prod.ext
        · show (T.map Prod.fst)⁻¹ * (T.map Prod.fst * WP.1.1) = WP.1.1
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hT1, Matrix.one_mul]
        · show J.map Prod.fst * (((J.map Prod.fst)⁻¹ * WP.1.2)ᵀ)ᵀ = WP.1.2
          rw [Matrix.transpose_transpose, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hJ1,
            Matrix.one_mul] }
  rw [Nat.card_congr e, card_pairs ha]
end PI.VolStabSW.FiniteFieldSplitting
