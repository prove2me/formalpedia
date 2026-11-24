-- Prove2me | solution 1 for QuadExt.Main.lemma_4_19
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T13:58:50.96343+00:00
-- url     : https://prove2.me/submissions/cb608f55-c3c0-48e8-b1b2-7a6dede0eee6

import Mathlib
import Definitions.Def_QuadExt_Main_Sources
import Definitions.Def_QuadExt_Main_Pure

open QuadExt.Main

theorem solution (n s r : ℕ) (q : ℝ) (f : (Fin s → ZMod 2) → (Fin n → ZMod 2))
    (hf : IsQuadraticMap f) (hpure : IsPure q f)
    (L : (Fin r → ZMod 2) → (Fin s → ZMod 2)) (hL : IsInjAffine L) :
    IsPure q (f ∘ L) := by
  rintro ⟨V, ⟨ℓ, b, hV⟩, hq⟩
  obtain ⟨⟨A, c, hAc⟩, hinj⟩ := hL
  have hAinj : Function.Injective A := by
    intro x y hxy
    apply hinj
    rw [hAc, hAc, hxy]
  obtain ⟨g, hg⟩ :=
    LinearMap.exists_leftInverse_of_injective A (LinearMap.ker_eq_bot.mpr hAinj)
  let LA : (Fin r → ZMod 2) →ᵃ[ZMod 2] (Fin s → ZMod 2) :=
    { toFun := L, linear := A, map_vadd' := fun p v => by
        show L (v + p) = A v + L p
        rw [hAc, hAc, map_add, add_assoc] }
  apply hpure
  refine ⟨V.map LA, ⟨ℓ ∘ₗ g, b - ℓ (g c), ?_⟩, ?_⟩
  · intro y hy
    rw [AffineSubspace.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have h1 := hV x hx
    simp only [Function.comp_apply] at h1
    have hgA : g (A x) = x := by simpa using LinearMap.congr_fun hg x
    show f (L x) = ℓ (g (L x)) + (b - ℓ (g c))
    rw [h1, hAc, map_add, hgA, map_add]
    abel
  · have himg : (f '' ((V.map LA : AffineSubspace (ZMod 2) (Fin s → ZMod 2)) :
        Set (Fin s → ZMod 2))) = (f ∘ L) '' (V : Set (Fin r → ZMod 2)) := by
      rw [AffineSubspace.coe_map, ← Set.image_comp]
      rfl
    rw [himg]
    exact hq
