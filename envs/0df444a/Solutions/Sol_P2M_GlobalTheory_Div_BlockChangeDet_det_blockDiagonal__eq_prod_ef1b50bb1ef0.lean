-- Prove2me | solution 1 for P2M_GlobalTheory_Div_BlockChangeDet_det_blockDiagonal__eq_prod_ef1b50bb1ef0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:06:58.68077+00:00
-- url     : https://prove2.me/submissions/7ef8e44a-6d20-467d-8365-8e16c9a0d4bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetBlockChangeOfBasisViaTwoFamiliesImplicit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Div GlobalTheory.Div.BlockChangeDet
open Matrix
namespace GlobalTheory.Div.BlockChangeDet
theorem _root_.solution {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
    {κ : ι → Type} [∀ c, Fintype (κ c)] [∀ c, DecidableEq (κ c)]
    (M : ∀ c, Matrix (κ c) (κ c) R) :
    (Matrix.blockDiagonal' M).det = ∏ c, (M c).det := by
  classical
  set f := Fintype.equivFin ι
  let b : (Σ c, κ c) → Fin (Fintype.card ι) := fun p => f p.1
  have hb : (Matrix.blockDiagonal' M).BlockTriangular b := by
    rintro ⟨c, i⟩ ⟨c', j⟩ h
    exact Matrix.blockDiagonal'_apply_ne M i j (fun hc => by subst hc; exact lt_irrefl _ h)
  rw [hb.det_fintype]
  symm
  refine Fintype.prod_equiv f _ _ (fun c => ?_)
  let e : κ c ≃ {p : (Σ c, κ c) // b p = f c} :=
    { toFun := fun i => ⟨⟨c, i⟩, rfl⟩
      invFun := fun p => cast (congrArg κ (f.injective p.2)) p.1.2
      left_inv := fun i => rfl
      right_inv := by
        rintro ⟨⟨c', i⟩, h⟩
        have hc : c' = c := f.injective h
        subst hc
        rfl }
  rw [← Matrix.det_submatrix_equiv_self e]
  congr 1
  ext i j
  exact (Matrix.blockDiagonal'_apply_eq M c i j).symm
end GlobalTheory.Div.BlockChangeDet
