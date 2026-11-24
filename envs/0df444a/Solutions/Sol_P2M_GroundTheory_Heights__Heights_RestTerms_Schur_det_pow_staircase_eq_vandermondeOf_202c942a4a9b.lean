-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Schur_det_pow_staircase_eq_vandermondeOf_202c942a4a9b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:28:06.587369+00:00
-- url     : https://prove2.me/submissions/57f41f05-cc45-4789-ad8a-7d062f697764

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Schur
open MvPolynomial Finset
noncomputable section
variable {m : ℕ}
namespace GroundTheory.Heights₂.Heights.RestTerms.Schur
theorem _root_.solution {R : Type*} [CommRing R] (v : Fin m → R) :
    (Matrix.of fun i j : Fin m => v j ^ (m - 1 - (i : ℕ))).det = vandermondeOf v := by
  rw [← Matrix.det_transpose]
  have h1 : (Matrix.of fun i j : Fin m => v j ^ (m - 1 - (i : ℕ))).transpose =
      (Matrix.vandermonde (v ∘ Fin.rev)).submatrix Fin.revPerm Fin.revPerm := by
    ext a b
    simp [Matrix.vandermonde, Fin.val_rev]
    congr 1
    omega
  rw [h1, Matrix.det_submatrix_equiv_self, Matrix.det_vandermonde, vandermondeOf]
  have h2 : ∀ g : Fin m → Fin m → R,
      ∏ i : Fin m, ∏ j ∈ Ioi i, g i j = ∏ i : Fin m, ∏ j : Fin m, if i < j then g i j else 1 := by
    intro g
    apply prod_congr rfl
    intro i _
    rw [← prod_filter]
    congr 1
    ext j; simp
  rw [h2, h2]
  have h3 : (∏ i : Fin m, ∏ j : Fin m, if i < j then (v ∘ Fin.rev) j - (v ∘ Fin.rev) i else 1) =
      ∏ a : Fin m, ∏ b : Fin m, if b < a then v b - v a else 1 := by
    rw [← Fintype.prod_equiv Fin.revPerm (fun a => ∏ j : Fin m,
      if Fin.rev a < j then (v ∘ Fin.rev) j - (v ∘ Fin.rev) (Fin.rev a) else 1)]
    · apply prod_congr rfl
      intro a _
      rw [← Fintype.prod_equiv Fin.revPerm (fun b => if Fin.rev a < Fin.rev b then
        (v ∘ Fin.rev) (Fin.rev b) - (v ∘ Fin.rev) (Fin.rev a) else 1)]
      · apply prod_congr rfl
        intro b _
        simp [Fin.rev_lt_rev]
      · intro b; rfl
    · intro a; rfl
  rw [h3, prod_comm]
end GroundTheory.Heights₂.Heights.RestTerms.Schur
