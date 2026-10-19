-- Prove2me | solution 1 for PermanentFormulaLowerBound.exists_matchingDiagonal_prodCongr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/aef093c9-3a34-4e48-97fc-afdaad6aa3f1

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {ell m : ℕ}
    (d : (Fin ell ⊕ Fin ell) ↪
      Fin ((ell + ell) + m) × Fin ((ell + ell) + m))
    (hrows : Function.Injective (fun y => (d y).1))
    (hcols : Function.Injective (fun y => (d y).2)) :
    ∃ r c : Equiv.Perm (Fin ((ell + ell) + m)),
      ∀ y : Fin ell ⊕ Fin ell,
        Equiv.prodCongr r c
          (matchingDiagonalEmbedding ell m y) = d y := by
  classical
  let d₀ := matchingDiagonalEmbedding ell m
  let r₀ : (Fin ell ⊕ Fin ell) ↪ Fin ((ell + ell) + m) :=
    ⟨fun y => (d₀ y).1, by
      intro x y h
      change matchingBlockIndexEquiv ell m (.inl x) =
        matchingBlockIndexEquiv ell m (.inl y) at h
      exact Sum.inl_injective
        ((matchingBlockIndexEquiv ell m).injective h)⟩
  let c₀ : (Fin ell ⊕ Fin ell) ↪ Fin ((ell + ell) + m) :=
    ⟨fun y => (d₀ y).2, by
      intro x y h
      change matchingBlockIndexEquiv ell m (.inl x) =
        matchingBlockIndexEquiv ell m (.inl y) at h
      exact Sum.inl_injective
        ((matchingBlockIndexEquiv ell m).injective h)⟩
  let rd : (Fin ell ⊕ Fin ell) ↪ Fin ((ell + ell) + m) :=
    ⟨fun y => (d y).1, hrows⟩
  let cd : (Fin ell ⊕ Fin ell) ↪ Fin ((ell + ell) + m) :=
    ⟨fun y => (d y).2, hcols⟩
  refine ⟨matchingEmbeddingPermutation r₀ rd,
    matchingEmbeddingPermutation c₀ cd, ?_⟩
  intro y
  apply Prod.ext
  · change matchingEmbeddingPermutation r₀ rd (r₀ y) = rd y
    exact matchingEmbeddingPermutation_apply r₀ rd y
  · change matchingEmbeddingPermutation c₀ cd (c₀ y) = cd y
    exact matchingEmbeddingPermutation_apply c₀ cd y
end PermanentFormulaLowerBound
