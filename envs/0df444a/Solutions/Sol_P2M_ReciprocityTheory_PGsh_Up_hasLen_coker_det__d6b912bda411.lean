-- Prove2me | solution 1 for P2M_ReciprocityTheory_PGsh_Up_hasLen_coker_det__d6b912bda411
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:37:34.078518+00:00
-- url     : https://prove2.me/submissions/a95f189f-d938-4845-9d62-1beffc8ff318

import Definitions.Def_ReciprocityTheory_DualLattices_LenIdBStatement
import Definitions.Def_ReciprocityTheory_DualLattices_UpSmith
import Definitions.Def_ReciprocityTheory_DualLattices_HasLenCokerDet
import Theorems.Thm_ReciprocityTheory_PGsh_Up_hasLen_of_equiv
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_hasLen_coker_det


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
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] (hv : v.Integers R) (κ : Type) [Fintype κ] [DecidableEq κ] (X : Matrix κ κ R) :
    HasLen v R ((κ → R) ⧸ LinearMap.range X.mulVecLin) (v (algebraMap R C X.det)) := by
  set e := Fintype.equivFin κ
  set X' := X.submatrix e.symm e.symm
  have hdet : X'.det = X.det := Matrix.det_submatrix_equiv_self e.symm X
  let Φ : (κ → R) ≃ₗ[R] (Fin (Fintype.card κ) → R) := LinearEquiv.funCongrLeft R R e.symm
  have hrange : (LinearMap.range X.mulVecLin).map (Φ : (κ → R) →ₗ[R] (Fin (Fintype.card κ) → R)) =
      LinearMap.range X'.mulVecLin := by
    ext z
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      refine ⟨y ∘ e.symm, ?_⟩
      funext i
      show (X' *ᵥ (y ∘ e.symm)) i = (X *ᵥ y) (e.symm i)
      simp only [X', Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Function.comp_apply]
      exact Equiv.sum_comp e.symm (fun k => X (e.symm i) k * y k)
    · rintro ⟨y, rfl⟩
      refine ⟨X *ᵥ (y ∘ e), ⟨y ∘ e, rfl⟩, ?_⟩
      funext i
      simp only [Matrix.mulVecLin_apply, X', Matrix.submatrix_mulVec_equiv, Φ,
        LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, Function.comp_apply]
      simp
  have h := Smith.hasLen_coker_det hv X'
  rw [hdet] at h
  exact hasLen_of_equiv (Submodule.Quotient.equiv _ _ Φ hrange) h
end ReciprocityTheory.PGsh.Up
