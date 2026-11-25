-- Prove2me | solution 1 for PI.VolStabSW.FFHS.card_isom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:59:20.330451+00:00
-- url     : https://prove2.me/submissions/0bad4d5a-a11a-4f72-ae9b-9e7fd2cc6e90

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFCnt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFIn
import Theorems.Thm_PI_VolStabSW_FFHS_IsSq_ext_basis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.FFHS
open Module Polynomial
namespace PI.VolStabSW.FFHS
theorem _root_.solution {K : Type} [Field K] {σ : K →+* K} {U V : Type} [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] {hU : U → U → K} {hV : V → V → K} (hsU : IsSq σ hU)
    (hsV : IsSq σ hV) {ι : Type} (b : Basis ι K U) :
    Nat.card {φ : U →ₗ[K] V // ∀ x y, hV (φ x) (φ y) = hU x y} =
      Nat.card {Y : ι → V // ∀ i j, hV (Y i) (Y j) = hU (b i) (b j)} := by
  refine Nat.card_congr
    { toFun := fun φ => ⟨fun i => φ.1 (b i), fun i j => φ.2 (b i) (b j)⟩
      invFun := fun Y => ⟨b.constr K Y.1, fun x y => ?_⟩
      left_inv := fun φ => ?_
      right_inv := fun Y => ?_ }
  · have hs1 : IsSq σ (fun x y => hV (b.constr K Y.1 x) (b.constr K Y.1 y)) :=
      { add_right := fun x y z => by
          simp only [map_add]
          exact hsV.add_right _ _ _
        smul_right := fun c x y => by
          simp only [map_smul]
          exact hsV.smul_right _ _ _
        herm := fun x y => hsV.herm _ _ }
    exact hs1.ext_basis hsU b (fun i j => by simpa only [Basis.constr_basis] using Y.2 i j) x y
  · apply Subtype.ext
    exact b.ext fun i => by simp [Basis.constr_basis]
  · apply Subtype.ext
    funext i
    simp [Basis.constr_basis]
end PI.VolStabSW.FFHS
