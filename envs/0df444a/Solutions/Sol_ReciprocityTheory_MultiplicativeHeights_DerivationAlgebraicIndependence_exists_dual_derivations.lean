-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence.exists_dual_derivations
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:16:33.185802+00:00
-- url     : https://prove2.me/submissions/782dadc6-9e06-4213-8b76-22733d00795b

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgebraicIndependentOfDerivations
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsDualDerivations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.MultiplicativeHeights
namespace DerivationAlgebraicIndependence
open MvPolynomial
section CoeffDer
variable {K Ω σ : Type*} [CommRing K] [CommRing Ω] [Algebra K Ω]
end CoeffDer
private theorem exists_linearMap_dual_of_linearIndependent {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V]
    {D : ℕ} (v : Fin D → V) (hli : LinearIndependent Ω v) (a : Fin D) :
    ∃ g : V →ₗ[Ω] Ω, ∀ b, g (v b) = if a = b then 1 else 0 := by
  open Module in
  classical
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Basis.span hli).coord a)
  refine ⟨g, fun b => ?_⟩
  have hmem : v b ∈ Submodule.span Ω (Set.range v) := Submodule.subset_span ⟨b, rfl⟩
  have h1 : g (v b) = (Basis.span hli).coord a ⟨v b, hmem⟩ := LinearMap.congr_fun hg ⟨v b, hmem⟩
  have h2 : (⟨v b, hmem⟩ : Submodule.span Ω (Set.range v)) = Basis.span hli b :=
    Subtype.ext (by rw [Basis.span_apply])
  rw [h1, h2, Basis.coord_apply, Basis.repr_self]
  by_cases h : a = b
  · subst h
    simp
  · simp [h]
end DerivationAlgebraicIndependence
end ReciprocityTheory.MultiplicativeHeights
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
open MvPolynomial
namespace ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
theorem _root_.solution {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] {D m : ℕ}
    (x : Fin m → Ω) (J : Fin D → Fin m)
    (hli : LinearIndependent Ω fun a => KaehlerDifferential.D K Ω (x (J a))) :
    ∃ δ : Fin D → Derivation K Ω Ω, ∀ a b, δ a (x (J b)) = if a = b then 1 else 0 := by
  choose g hg using exists_linearMap_dual_of_linearIndependent (fun a => KaehlerDifferential.D K Ω (x (J a))) hli
  exact ⟨fun a => (g a).compDer (KaehlerDifferential.D K Ω), fun a b => hg a b⟩
end ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
