-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.hasLen_le_of_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:22:03.375204+00:00
-- url     : https://prove2.me/submissions/c0314fe8-adb4-4a23-93e4-bf49a47b0e05

import Definitions.Def_ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatement
import Definitions.Def_ReciprocityTheory_DualLattices_PowMemCarrier
import Definitions.Def_ReciprocityTheory_DualLattices_IsLocalOfIntegers
import Definitions.Def_ReciprocityTheory_DualLattices_MemOfSumSingleEqZero
import Definitions.Def_ReciprocityTheory_DualLattices_EigenLiftsFrobenius
import Definitions.Def_ReciprocityTheory_DualLattices_HasLenLeOfSurj
import Theorems.Thm_ReciprocityTheory_PGsh_Up_prod_le_of_gen


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
open ReciprocityTheory.PGsh.L2
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] (hv : v.Integers R) {M : Type} [AddCommGroup M] [Module R M] {z : NNReal}
    (hz : HasLen v R M z) (q : R) (r : ℕ)
    (π : M →ₗ[R] ((t : Fin r) → R ⧸ Ideal.span {q})) (hπ : Function.Surjective π) :
    z ≤ v (algebraMap R C q) ^ r := by
  obtain ⟨m, c, ⟨e⟩, hzc⟩ := hz
  have hx : HasLen v R ((t : Fin r) → R ⧸ Ideal.span {q}) (v (algebraMap R C q) ^ r) :=
    ⟨r, fun _ => q, ⟨LinearEquiv.refl R _⟩, by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]⟩
  have hs : Submodule.span R (Set.range fun i : Fin m =>
      (Pi.single i 1 : (j : Fin m) → R ⧸ Ideal.span {c j})) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [show x = ∑ i, (Pi.single i (x i) : (j : Fin m) → R ⧸ Ideal.span {c j}) from
      (Finset.univ_sum_single x).symm]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (x i)
    have hsi : (Pi.single i (x i) : (j : Fin m) → R ⧸ Ideal.span {c j}) = a • Pi.single i 1 := by
      rw [← ha]
      ext j
      by_cases hj : j = i
      · subst hj
        rw [Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same, Algebra.smul_def, mul_one,
          Ideal.Quotient.algebraMap_eq]
      · simp [Pi.single_eq_of_ne hj]
    rw [hsi]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hy : Submodule.span R (Set.range fun i : Fin m =>
      π (e.symm (Pi.single i 1 : (j : Fin m) → R ⧸ Ideal.span {c j}))) = ⊤ := by
    have hr : (Set.range fun i : Fin m => π (e.symm (Pi.single i 1 : (j : Fin m) → R ⧸ Ideal.span {c j}))) =
        (π ∘ₗ e.symm.toLinearMap) '' Set.range fun i : Fin m =>
          (Pi.single i 1 : (j : Fin m) → R ⧸ Ideal.span {c j}) := by
      rw [← Set.range_comp]
      rfl
    rw [hr, Submodule.span_image, hs, Submodule.map_top, LinearMap.range_eq_top]
    exact hπ.comp e.symm.surjective
  have key := prod_le_of_gen hv hx _ hy c (fun i => ⟨0, ?_⟩)
  · rw [← hzc]
    exact key
  · simp only [Pi.zero_apply, ite_self, zero_smul, Finset.sum_const_zero]
    have h0 : c i • (Pi.single i 1 : (j : Fin m) → R ⧸ Ideal.span {c j}) = 0 := by
      ext j
      by_cases hj : j = i
      · subst hj
        simp only [Pi.smul_apply, Pi.single_eq_same, Pi.zero_apply]
        rw [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]
        exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
      · simp [Pi.single_eq_of_ne hj]
    rw [← LinearMap.map_smul, ← LinearEquiv.map_smul, h0, map_zero, map_zero]
end ReciprocityTheory.PGsh.Up
