-- Prove2me | solution 1 for P2M_Formalism_HermitianLattices_Ext_L3_FirstPropositionFrame_card_lift_unimod__01843a216c6e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:43:52.289001+00:00
-- url     : https://prove2.me/submissions/44888c7b-0435-473c-93ee-26dfdac99267

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftMatrix
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftUnimod
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FirstPropositionFrame_card_lift_unimod
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HermitianSublattices_card_entSub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HermitianSublattices_card_hermSub_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.FirstPropositionFrame
open Matrix
variable {A A' : Type*} [CommRing A] [StarRing A] [CommRing A'] [StarRing A']
variable {m : Type*} [Fintype m] [DecidableEq m]
namespace Formalism.HermitianLattices.Ext.L3.FirstPropositionFrame
theorem _root_.solution [Finite A] (π : A →+* A') (hπ : Function.Surjective π)
    (hπs : ∀ a, π (star a) = star (π a))
    (h2 : ∀ a ∈ RingHom.ker π, ∀ b ∈ RingHom.ker π, a * b = 0) {θ e : A}
    (he : (θ - star θ) * e = 1) (H : Matrix m m A) (hH : Hᴴ = H) (hu : IsUnit H.det) (q : ℕ)
    (hq : Nat.card (RingHom.ker π) = q ^ 2) :
    Nat.card {X : Matrix m m A // Xᴴ * H * X = H} =
      q ^ (Fintype.card m ^ 2) * Nat.card {X' : Matrix m m A' // X'ᴴ * (H.map π) * X' = H.map π} := by
  have h1 := card_lift_unimod π hπ hπs h2 he H hH hu
  have hJ : ∀ a ∈ RingHom.ker π, star a ∈ RingHom.ker π := fun a ha => by
    rw [RingHom.mem_ker] at ha ⊢
    rw [hπs, ha, star_zero]
  have hE : Nat.card (HermitianSublattices.entSub m m (RingHom.ker π)) = q ^ (2 * Fintype.card m ^ 2) := by
    rw [HermitianSublattices.card_entSub, hq, ← pow_mul]
    ring
  have hHs : Nat.card (HermitianSublattices.hermSub m (RingHom.ker π)) = q ^ (Fintype.card m ^ 2) := by
    have h3 := HermitianSublattices.card_hermSub_sq (r := m) hJ he
    rw [hE] at h3
    have e2 : q ^ (2 * Fintype.card m ^ 2) = (q ^ (Fintype.card m ^ 2)) ^ 2 := by
      rw [← pow_mul]
      ring
    rw [e2] at h3
    exact Nat.pow_left_injective two_ne_zero h3
  rw [hHs, hE] at h1
  have hq0 : 0 < q := by
    have h4 : 0 < Nat.card (RingHom.ker π) := Nat.card_pos
    rw [hq] at h4
    exact Nat.pos_of_ne_zero fun h => by simp [h] at h4
  have e3 : q ^ (2 * Fintype.card m ^ 2) = q ^ (Fintype.card m ^ 2) * q ^ (Fintype.card m ^ 2) := by
    rw [← pow_add]
    ring
  rw [e3] at h1
  exact Nat.eq_of_mul_eq_mul_right (pow_pos hq0 _) (by rw [h1]; ring)
end Formalism.HermitianLattices.Ext.L3.FirstPropositionFrame
