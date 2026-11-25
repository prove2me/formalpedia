-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_module_finite_of_semilinear_0775f0fbfa71
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:05:45.926603+00:00
-- url     : https://prove2.me/submissions/7f54b21e-26c5-4701-a9c8-801dd363c308

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_FiniteIntegralClosureCharP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open scoped nonZeroDivisors
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution {B R M N : Type*} [CommRing B] [CommRing R] [Algebra R B]
    [IsNoetherianRing R] [Module.Finite R B] [AddCommGroup M] [Module B M] [AddCommGroup N]
    [Module B N] [Module R N] [IsScalarTower R B N] [Module.Finite B N]
    (σ : B →+* R) (hσ : Function.Surjective σ) (φ : M →+ N) (hφ : Function.Injective φ)
    (hφσ : ∀ (b : B) (m : M), φ (b • m) = σ b • φ m) : Module.Finite B M := by
  have : Module.Finite R N := Module.Finite.trans B N
  have : IsNoetherian R N := isNoetherian_of_isNoetherianRing_of_finite R N
  let P : Submodule R N :=
    { carrier := Set.range φ
      add_mem' := by
        rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        exact ⟨x + y, map_add φ x y⟩
      zero_mem' := ⟨0, map_zero φ⟩
      smul_mem' := by
        rintro r _ ⟨x, rfl⟩
        obtain ⟨b, rfl⟩ := hσ r
        exact ⟨b • x, hφσ b x⟩ }
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian P : P.FG)
  have hsP : ∀ n ∈ s, ∃ m, φ m = n := fun n hn => by
    have : n ∈ P := hs ▸ Submodule.subset_span hn
    exact this
  choose! g hg using hsP
  classical
  refine ⟨⟨s.image g, ?_⟩⟩
  rw [eq_top_iff]
  rintro m -
  let Q : Submodule B M := Submodule.span B (s.image g : Set M)
  let Q' : Submodule R N :=
    { carrier := φ '' Q
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x + y, Q.add_mem hx hy, map_add φ x y⟩
      zero_mem' := ⟨0, Q.zero_mem, map_zero φ⟩
      smul_mem' := by
        rintro r _ ⟨x, hx, rfl⟩
        obtain ⟨b, rfl⟩ := hσ r
        exact ⟨b • x, Q.smul_mem b hx, hφσ b x⟩ }
  have hsQ' : (s : Set N) ⊆ Q' := by
    intro n hn
    refine ⟨g n, Submodule.subset_span ?_, hg n hn⟩
    exact Finset.mem_coe.mpr (Finset.mem_image_of_mem g hn)
  have hPQ : P ≤ Q' := hs ▸ Submodule.span_le.mpr hsQ'
  obtain ⟨m', hm', he⟩ := hPQ (⟨m, rfl⟩ : φ m ∈ P)
  exact hφ he ▸ hm'
end GroundTheory.Heights₂.Heights.Model
