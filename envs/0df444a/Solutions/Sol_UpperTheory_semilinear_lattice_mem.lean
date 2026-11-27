-- Prove2me | solution 1 for UpperTheory.semilinear_lattice_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:34:11.212701+00:00
-- url     : https://prove2.me/submissions/a448a8c7-39bf-4050-a51d-141ebe803bbd

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SemilinearLatticeMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory
theorem _root_.solution :
    ∀ (R K C V W : Type) [CommRing R] [Field K] [Field C] [Algebra R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] [AddCommGroup W] [Module C W] (e : K →+* C) (U : Submodule K V) (Φ : U →ₛₗ[e] W) (A : Set C) (L : AddSubgroup W) (G : Set V), (∀ a ∈ A, ∀ y ∈ L, a • y ∈ L) → (∀ r : R, e (algebraMap R K r) ∈ A) → (∀ g ∈ G, ∃ h : g ∈ U, Φ ⟨g, h⟩ ∈ L) → ∀ (s : R), algebraMap R K s ≠ 0 → e (algebraMap R K s)⁻¹ ∈ A → ∀ v : U, s • (v : V) ∈ Submodule.span R G → Φ v ∈ L := by
  intro R K C V W _ _ _ _ _ _ _ _ _ _ e U Φ A L G hA hR hG s hs hsA v hv
  have key : ∀ x ∈ Submodule.span R G, ∃ h : x ∈ U, Φ ⟨x, h⟩ ∈ L := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hG x hx
    | zero =>
      refine ⟨U.zero_mem, ?_⟩
      have h0 : (⟨0, U.zero_mem⟩ : U) = 0 := rfl
      rw [h0, map_zero]
      exact L.zero_mem
    | add x y _ _ hx hy =>
      obtain ⟨hxU, hx⟩ := hx
      obtain ⟨hyU, hy⟩ := hy
      refine ⟨U.add_mem hxU hyU, ?_⟩
      have h0 : (⟨x + y, U.add_mem hxU hyU⟩ : U) = ⟨x, hxU⟩ + ⟨y, hyU⟩ := rfl
      rw [h0, map_add]
      exact L.add_mem hx hy
    | smul r x _ hx =>
      obtain ⟨hxU, hx⟩ := hx
      have hm : r • x ∈ U := by
        rw [← algebraMap_smul K r x]
        exact U.smul_mem _ hxU
      refine ⟨hm, ?_⟩
      have h0 : (⟨r • x, hm⟩ : U) = algebraMap R K r • (⟨x, hxU⟩ : U) :=
        Subtype.ext (algebraMap_smul K r x).symm
      rw [h0, LinearMap.map_smulₛₗ]
      exact hA _ (hR r) _ hx
  obtain ⟨hU, hL⟩ := key _ hv
  have h1 : v = (algebraMap R K s)⁻¹ • (⟨s • (v : V), hU⟩ : U) := by
    apply Subtype.ext
    change (v : V) = (algebraMap R K s)⁻¹ • (s • (v : V))
    rw [← algebraMap_smul K s (v : V), inv_smul_smul₀ hs]
  rw [h1, LinearMap.map_smulₛₗ]
  exact hA _ hsA _ hL
end UpperTheory
