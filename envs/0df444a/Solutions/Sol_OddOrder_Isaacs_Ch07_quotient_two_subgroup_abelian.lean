-- Prove2me | solution 1 for OddOrder.Isaacs.Ch07.quotient_two_subgroup_abelian
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:49:02.157554+00:00
-- url     : https://prove2.me/submissions/7183314d-7887-466e-accd-9996fb6e512c

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7A2_NormalPThm75.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7A1_JpGL2p
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7A2_NormalPThm75

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7A2_NormalPThm75.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

open scoped IsMulCommutative

variable {G : Type*} [Group G]

/-- The hypothesis that every `2`-subgroup is abelian descends to a quotient.

This is the Sylow-lift bridge needed in Isaacs Thm 7.5 for applying the reduced theorem to
`G/K`: a `2`-subgroup of `G/K` is the image of a Sylow `2`-subgroup of its preimage, and
that Sylow subgroup is abelian by the upstairs hypothesis. -/
theorem _root_.solution
    {G : Type*} [Group G] [Finite G] {K : Subgroup G} [K.Normal]
    (h2abelian : ∀ S : Subgroup G, IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x)
    (S : Subgroup (G ⧸ K)) (hS2 : IsPGroup 2 S) :
    ∀ x y : ↥S, x * y = y * x := by
  let q : G →* G ⧸ K := QuotientGroup.mk' K
  let T : Subgroup G := Subgroup.comap q S
  let f : T →* S :=
    { toFun := fun t => ⟨q t, t.property⟩
      map_one' := by
        ext
        simp [q]
      map_mul' := by
        intro a b
        ext
        simp [q] }
  have hf : Function.Surjective f := by
    intro s
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective K (s : G ⧸ K)
    refine ⟨⟨g, ?_⟩, ?_⟩
    · change q g ∈ S
      simp [q, hg, s.property]
    · ext
      simpa [f, q] using hg
  let R : Sylow 2 T := default
  let Rbar : Sylow 2 S := R.mapSurjective hf
  have hRbar_top : (Rbar : Subgroup S) = ⊤ := by
    have htop2 : IsPGroup 2 (⊤ : Subgroup S) := hS2.to_subgroup ⊤
    exact (Rbar.is_maximal' htop2 le_top).symm
  have hRcomm : ∀ a b : ↥R, a * b = b * a := by
    have hRG2 : IsPGroup 2 ((R : Subgroup T).map T.subtype) :=
      R.isPGroup'.map T.subtype
    have hRGcomm := h2abelian ((R : Subgroup T).map T.subtype) hRG2
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    let ag : ↥((R : Subgroup T).map T.subtype) :=
      ⟨((a : T) : G), ⟨(a : T), a.property, rfl⟩⟩
    let bg : ↥((R : Subgroup T).map T.subtype) :=
      ⟨((b : T) : G), ⟨(b : T), b.property, rfl⟩⟩
    have h := congrArg (fun z : ↥((R : Subgroup T).map T.subtype) => (z : G))
      (hRGcomm ag bg)
    simpa using h
  intro x y
  have hxRbar : x ∈ (Rbar : Subgroup S) := by
    rw [hRbar_top]
    trivial
  have hyRbar : y ∈ (Rbar : Subgroup S) := by
    rw [hRbar_top]
    trivial
  rw [Sylow.coe_mapSurjective] at hxRbar hyRbar
  rcases hxRbar with ⟨rx, hrx, hfx⟩
  rcases hyRbar with ⟨ry, hry, hfy⟩
  let rxR : R := ⟨rx, hrx⟩
  let ryR : R := ⟨ry, hry⟩
  have hxyT : rx * ry = ry * rx :=
    congrArg (fun z : ↥R => (z : T)) (hRcomm rxR ryR)
  calc
    x * y = f rx * f ry := by rw [← hfx, ← hfy]
    _ = f (rx * ry) := by rw [map_mul]
    _ = f (ry * rx) := by rw [hxyT]
    _ = f ry * f rx := by rw [map_mul]
    _ = y * x := by rw [hfy, hfx]

end OddOrder.Isaacs.Ch07
