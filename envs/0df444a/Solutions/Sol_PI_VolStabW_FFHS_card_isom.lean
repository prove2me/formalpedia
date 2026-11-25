-- Prove2me | solution 1 for PI.VolStabW.FFHS.card_isom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:04:42.885703+00:00
-- url     : https://prove2.me/submissions/94565757-abaa-4962-b709-f1a58e935c29

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFCnt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFIn
import Theorems.Thm_PI_VolStabW_FFHS_IsSq_ext_basis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.FFHS
open Module Polynomial
namespace PI.VolStabW.FFHS
theorem _root_.solution {K : Type} [Field K] {σ : K →+* K} {U V : Type} [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] {hU : U → U → K} {hV : V → V → K} (hsU : IsSq σ hU)
    (hsV : IsSq σ hV) {ι : Type} (b : Basis ι K U) :
    Nat.card {φ : U →ₗ[K] V // ∀ x y, hV (φ x) (φ y) = hU x y} =
      Nat.card {Y : ι → V // ∀ i j, hV (Y i) (Y j) = hU (b i) (b j)} :=
  Nat.card_congr (Equiv.subtypeEquiv (b.constr K).symm.toEquiv (fun φ => by
    simp only [LinearEquiv.coe_toEquiv, Basis.constr_symm_apply]
    constructor
    · intro H i j; exact H _ _
    · intro H x y
      have hs2 : IsSq σ (fun x y => hV (φ x) (φ y)) :=
        ⟨fun x y z => by simp only [map_add, hsV.add_right],
          fun c x y => by simp only [map_smul, hsV.smul_right],
          fun x y => hsV.herm _ _⟩
      exact (hs2.ext_basis hsU b H x y)))
end PI.VolStabW.FFHS
