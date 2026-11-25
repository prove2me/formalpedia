-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.Tot.hasLen_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:49:44.017022+00:00
-- url     : https://prove2.me/submissions/ceb5c07a-5de5-45fb-9533-9a4d50ce9f00

import Definitions.Def_ReciprocityTheory_DualLattices_EigenLengthFrobeniusStatement
import Definitions.Def_ReciprocityTheory_DualLattices_UpSmith
import Definitions.Def_ReciprocityTheory_DualLattices_ProdDvdOfIso
import Definitions.Def_ReciprocityTheory_DualLattices_EigenLengthProductStatementHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.Up.Tot
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.Up.Tot
theorem _root_.solution {m : ℕ} (M : Fin m → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (X : Fin m → NNReal) (h : ∀ i, HasLen v R (M i) (X i)) :
    HasLen v R ((i : Fin m) → M i) (∏ i, X i) := by
  classical
  choose n c he hX using h
  let e : ∀ i, M i ≃ₗ[R] ((j : Fin (n i)) → R ⧸ Ideal.span {c i j}) := fun i => (he i).some
  let σ : Fin (Fintype.card (Σ i, Fin (n i))) ≃ (Σ i, Fin (n i)) := (Fintype.equivFin _).symm
  refine ⟨Fintype.card (Σ i, Fin (n i)), fun k => c (σ k).1 (σ k).2, ⟨?_⟩, ?_⟩
  · exact (LinearEquiv.piCongrRight e).trans
      ((LinearEquiv.piCurry R (fun i j => R ⧸ Ideal.span {c i j})).symm.trans
        (LinearEquiv.piCongrLeft R (fun p : Σ i, Fin (n i) => R ⧸ Ideal.span {c p.1 p.2}) σ).symm)
  · rw [Fintype.prod_equiv σ (fun k => v (algebraMap R C (c (σ k).1 (σ k).2)))
      (fun p => v (algebraMap R C (c p.1 p.2))) (fun k => rfl), Fintype.prod_sigma]
    exact Finset.prod_congr rfl fun i _ => hX i
end ReciprocityTheory.PGsh.Up.Tot
