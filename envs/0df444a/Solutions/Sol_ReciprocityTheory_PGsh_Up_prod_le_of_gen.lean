-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.prod_le_of_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:05:16.66523+00:00
-- url     : https://prove2.me/submissions/0ef1723a-e99f-4525-8386-19874be7f1ff

import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_IsLocalOfIntegers
import Theorems.Thm_ReciprocityTheory_PGsh_Up_det_mem_span_prod
import Theorems.Thm_ReciprocityTheory_PGsh_Up_isLocal_of_integers

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
theorem _root_.solution {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] (hv : v.Integers R) {M : Type} [AddCommGroup M] [Module R M] {x : NNReal}
    (hx : HasLen v R M x) {n : ℕ} (y : Fin n → M)
    (hy : Submodule.span R (Set.range y) = ⊤) (δ : Fin n → R)
    (hrel : ∀ i, ∃ a : Fin n → R, δ i • y i = ∑ j, (if j < i then a j else 0) • y j) :
    ∏ i, v (algebraMap R C (δ i)) ≤ x := by
  haveI := isLocal_of_integers hv
  obtain ⟨m, c, ⟨e⟩, hxc⟩ := hx
  choose a ha using hrel
  obtain ⟨q, hqdef⟩ : ∃ q : Fin n → ((j : Fin m) → R ⧸ Ideal.span {c j}), q = fun i => e (y i) :=
    ⟨_, rfl⟩
  have hq : Submodule.span R (Set.range q) = ⊤ := by
    have h1 : Set.range q = (e : M →ₗ[R] _) '' Set.range y := by
      ext z
      simp [hqdef]
    rw [h1, Submodule.span_image, hy, Submodule.map_top, LinearEquiv.range]
  obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin n) (Fin n) R,
      T = fun i j => (if j = i then δ i else 0) - (if j < i then a i j else 0) := ⟨_, rfl⟩
  have hrelT : ∀ k, ∑ i, T k i • q i = 0 := by
    intro k
    have h := congrArg e (ha k)
    simp only [map_smul, map_sum, ite_smul, zero_smul] at h
    simp only [hT, hqdef, sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [h, sub_eq_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hdet := det_mem_span_prod m c n q hq T hrelT
  have hdetT : T.det = ∏ i, δ i := by
    rw [Matrix.det_of_lowerTriangular]
    · refine Finset.prod_congr rfl fun i _ => ?_
      simp [hT]
    · intro i j hij
      have h' : i < j := OrderDual.toDual_lt_toDual.mp hij
      simp [hT, h'.ne', not_lt.mpr h'.le]
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hdet
  calc ∏ i, v (algebraMap R C (δ i)) = v (algebraMap R C (∏ i, δ i)) := by simp [map_prod]
    _ = v (algebraMap R C r) * ∏ j, v (algebraMap R C (c j)) := by
        rw [← hdetT, ← hr]
        simp [map_prod]
    _ ≤ 1 * ∏ j, v (algebraMap R C (c j)) := by
        gcongr
        exact hv.map_le_one r
    _ = x := by rw [one_mul, hxc]
end ReciprocityTheory.PGsh.Up
