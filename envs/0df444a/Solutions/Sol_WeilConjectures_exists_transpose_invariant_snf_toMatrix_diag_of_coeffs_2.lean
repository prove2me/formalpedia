-- Prove2me | solution 2 for WeilConjectures.exists_transpose_invariant_snf_toMatrix_diag_of_coeffs
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T16:57:18.386561+00:00
-- url     : https://prove2.me/submissions/dd0fa765-bfa6-4ab6-9f6c-ad2209b1166b

import Mathlib
import Theorems.Thm_WeilConjectures_exists_common_snf_toMatrix_diag_of_transpose

/-!
A64a: transpose-invariant SNF `toMatrix`-diag from any coeffs assignment.
Reduce to common-diag for `M` and `Mᵀ` (A64b); glue by Quotient.out on the
transpose involution setoid (A41x SYM-CHOOSE).
-/

open Classical Matrix

theorem solution
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (d0 : Matrix ι ι (Polynomial K) → (ι → Polynomial K))
    (hd0 : ∀ M, ∃ (bSrc bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K)),
      LinearMap.toMatrix bSrc bTgt (Matrix.toLin' M) = Matrix.diagonal (d0 M)) :
    ∃ (d : Matrix ι ι (Polynomial K) → (ι → Polynomial K)),
      (∀ M i, d M i = d M.transpose i) ∧
      (∀ M, ∃ (bSrc bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K)),
        LinearMap.toMatrix bSrc bTgt (Matrix.toLin' M) =
          Matrix.diagonal (d M)) := by
  classical
  have hcommon :=
    WeilConjectures.exists_common_snf_toMatrix_diag_of_transpose d0 hd0
  let rM : Matrix ι ι (Polynomial K) → Matrix ι ι (Polynomial K) → Prop :=
    fun A B => B = A ∨ B = Aᵀ
  let S : Setoid (Matrix ι ι (Polynomial K)) :=
    { r := rM
      iseqv := {
        refl := fun _ => Or.inl rfl
        symm := by
          intro A B h
          rcases h with (e | e)
          · exact Or.inl e.symm
          · exact Or.inr (by rw [e, transpose_transpose])
        trans := by
          intro A B C h1 h2
          rcases h1 with (e1 | e1) <;> rcases h2 with (e2 | e2)
          · exact Or.inl (e2.trans e1)
          · exact Or.inr (e1 ▸ e2)
          · exact Or.inr (e2.trans e1)
          · exact Or.inl (by rw [e2, e1, transpose_transpose])
      } }
  let d : Matrix ι ι (Polynomial K) → (ι → Polynomial K) := fun M =>
    Classical.choose (hcommon (Quotient.out (Quotient.mk S M)))
  refine ⟨d, ?_, ?_⟩
  · intro M i
    dsimp only [d]
    have mk_eq : Quotient.mk S M = Quotient.mk S Mᵀ := Quotient.sound (Or.inr rfl)
    rw [mk_eq]
  · intro M
    set N := Quotient.out (Quotient.mk S M) with hN
    have hc := Classical.choose_spec (hcommon N)
    have hrel : rM N M := by
      have : Quotient.mk S N = Quotient.mk S M := by simp [hN, Quotient.out_eq]
      exact Quotient.exact this
    change ∃ bSrc bTgt, LinearMap.toMatrix bSrc bTgt (toLin' M) =
      diagonal (Classical.choose (hcommon N))
    rcases hrel with (h | h)
    · rw [h]; exact hc.1
    · rw [h]; exact hc.2
