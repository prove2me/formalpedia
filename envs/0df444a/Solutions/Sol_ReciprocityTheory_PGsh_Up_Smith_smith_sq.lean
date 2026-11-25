-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.Smith.smith_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:13:12.797016+00:00
-- url     : https://prove2.me/submissions/23984607-3729-49ab-8527-2761317b4d61

import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_UpSmith
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_det_colop

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
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.Smith
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.Up.Smith
theorem _root_.solution (hv : v.Integers R) : ∀ (b : ℕ) (X : Matrix (Fin b) (Fin b) R),
    ∃ c : Fin b → R, Nonempty (((Fin b → R) ⧸ LinearMap.range X.mulVecLin) ≃ₗ[R]
      ((i : Fin b) → R ⧸ Ideal.span {c i})) ∧
      v (algebraMap R C X.det) = ∏ i, v (algebraMap R C (c i))
  | 0, X => ⟨Fin.elim0, ⟨LinearEquiv.ofSubsingleton _ _⟩, by simp⟩
  | b + 1, X => by
    classical
    set g : Fin (b + 1) → Fin (b + 1) → R := fun j i => X i j with hg
    have hrange : LinearMap.range X.mulVecLin = Submodule.span R (Set.range g) := by
      rw [Matrix.range_mulVecLin]; rfl
    obtain ⟨i0, a, u, s, hu, hau, hs, hz, hnz⟩ := exists_pivot hv g
    obtain ⟨e1⟩ := pivot_equiv g i0 a u s hu hau hs
    set h : Fin (b + 1) → Fin (b + 1) → R := fun j => g j - s j • a • u with hh
    have e0 := Submodule.quotEquivOfEq _ _ hrange
    have hprod : ∀ c' : Fin b → R, ∏ i, v (algebraMap R C ((Fin.cons a c' : Fin (b + 1) → R) i)) =
        v (algebraMap R C a) * ∏ k, v (algebraMap R C (c' k)) := by
      intro c'
      rw [Fin.prod_univ_succ]
      rfl
    by_cases ha : a = 0
    · obtain ⟨c', ⟨e2⟩⟩ := smith_gen hv b (fun j => Fin.removeNth i0 (g j - s j • a • u))
      refine ⟨Fin.cons a c', ⟨(e0.trans (e1.trans ((LinearEquiv.refl R _).prodCongr e2))).trans
        (consEquiv a c')⟩, ?_⟩
      have hX : X = 0 := by
        ext i j
        have := congrFun (hz ha j) i
        simpa [hg] using this
      rw [hprod, hX, Matrix.det_zero, ha]
      simp
    · obtain ⟨j0, hj0, hs0⟩ := hnz ha
      set X'' : Matrix (Fin b) (Fin b) R :=
        Matrix.of fun k l => h (j0.succAbove l) (i0.succAbove k) with hX''
      have hspan'' : Submodule.span R (Set.range fun j => Fin.removeNth i0 (g j - s j • a • u)) =
          LinearMap.range X''.mulVecLin := by
        rw [Matrix.range_mulVecLin]
        apply le_antisymm
        · rw [Submodule.span_le]
          rintro _ ⟨j, rfl⟩
          by_cases hj : j = j0
          · subst hj
            have : g j - s j • a • u = 0 := by rw [hj0, hs0, one_smul, sub_self]
            have hz0 : Fin.removeNth i0 (0 : Fin (b + 1) → R) = 0 := rfl
            show Fin.removeNth i0 (g j - s j • a • u) ∈ _
            rw [this, hz0]
            exact Submodule.zero_mem _
          · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hj
            exact Submodule.subset_span ⟨l, rfl⟩
        · rw [Submodule.span_le]
          rintro _ ⟨l, rfl⟩
          exact Submodule.subset_span ⟨j0.succAbove l, rfl⟩
      obtain ⟨c', ⟨e2⟩, hdet''⟩ := solution hv b X''
      refine ⟨Fin.cons a c', ⟨(e0.trans (e1.trans ((LinearEquiv.refl R _).prodCongr
        ((Submodule.quotEquivOfEq _ _ hspan'').trans e2)))).trans (consEquiv a c')⟩, ?_⟩
      rw [hprod, ← hdet'', ← det_colop X j0 s, Matrix.det_succ_row _ i0,
        Finset.sum_eq_single j0]
      · have hsub : (Matrix.of fun i j => if j = j0 then X i j0 else X i j - s j * X i j0).submatrix
            i0.succAbove j0.succAbove = X'' := by
          ext k l
          simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.succAbove_ne, if_false, hX'', hh,
            hg, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          have : X (i0.succAbove k) j0 = a * u (i0.succAbove k) := by
            have := congrFun hj0 (i0.succAbove k)
            simpa [hg] using this
          rw [this]
        have hX0 : X i0 j0 = a := by
          have := congrFun hj0 i0
          simpa [hg, hu] using this
        simp only [Matrix.of_apply, if_true, hsub, hX0, map_mul, map_pow, map_neg, map_one]
        simp
      · intro j _ hj
        have hX0 : X i0 j0 = a := by
          have := congrFun hj0 i0
          simpa [hg, hu] using this
        have hXj : X i0 j = a * s j := hs j
        simp [hj, hXj, hX0, mul_comm]
      · intro h'; exact absurd (Finset.mem_univ _) h'
end ReciprocityTheory.PGsh.Up.Smith
