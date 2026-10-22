-- Prove2me | solution 1 for RInf.reid_lift
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T01:00:34.62166+00:00
-- url     : https://prove2.me/submissions/0a655084-be74-4fc4-8233-6c5a118f4375

import Mathlib
import Definitions.Def_RInf_alg
import Definitions.Def_RInf_braid
open RInf

theorem solution {G H : Type*} [Group G] [Group H]
    (pi : G →* H) (hsurj : ∀ y : H, ∃ x : G, pi x = y)
    (α : G ≃* G) (β : H ≃* H) (hcomm : ∀ x : G, pi (α x) = β (pi x))
    (hβ : ReidInf β.toMonoidHom) : ReidInf α.toMonoidHom := by
  obtain ⟨f, hf⟩ := hβ
  choose s hs using hsurj
  refine ⟨fun i => s (f i), fun i j hij hc => hf i j hij ?_⟩
  obtain ⟨z, hz⟩ := hc
  refine ⟨pi z, ?_⟩
  have := congrArg pi hz
  simp only [map_mul, map_inv, hs, MulEquiv.coe_toMonoidHom] at this ⊢
  rw [this, hcomm]
