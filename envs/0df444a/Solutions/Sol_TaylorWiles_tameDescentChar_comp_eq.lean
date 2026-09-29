-- Prove2me | solution 1 for TaylorWiles.tameDescentChar_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/f43e57f6-a78c-55bc-a30f-5940927a4688

import Mathlib
import Definitions.Def_Deformations_TameDescent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TaylorWiles_tameDescentChar_comp_eq

set_option autoImplicit false

universe u v w

open Function

theorem solution {G : Type u} {Δ : Type v} {A : Type w} [Group G] [Group Δ] [CommRing A]
    (π : G →* Δ) (hπ : Function.Surjective π) (χ : G →* Aˣ)
    (hχ : ∀ g ∈ π.ker, χ g = 1) (g : G) :
    TaylorWiles.tameDescentChar π hπ χ hχ (π g) = χ g := by
  have h : (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm (π g) =
      QuotientGroup.mk g := by
    apply (QuotientGroup.quotientKerEquivOfSurjective π hπ).injective
    rw [MulEquiv.apply_symm_apply]
    exact (QuotientGroup.kerLift_mk (φ := π) g).symm
  show (QuotientGroup.lift π.ker χ hχ)
      ((QuotientGroup.quotientKerEquivOfSurjective π hπ).symm (π g)) = χ g
  rw [h]
  rfl

end S_TaylorWiles_tameDescentChar_comp_eq
end P2MW
export P2MW.S_TaylorWiles_tameDescentChar_comp_eq (solution)
