-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.Nb.isPrecomplete_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:44:53.811199+00:00
-- url     : https://prove2.me/submissions/dedf7f53-032d-4e7d-b070-c1adc4ded72a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_GenericFiberGluing_SemistableCompleteSplit
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.Tower
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_IsPrecompleteOfBasis
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Nb_coord_mem_of_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Nb_mem_of_coord_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open IsLocalRing Polynomial
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Semi.Nb
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.Semi.Nb
theorem _root_.solution (I : Ideal R) [IsPrecomplete I R] (b : Module.Basis ι R M) :
    IsPrecomplete I M := by
  have hI : ∀ n : ℕ, (I ^ n • ⊤ : Submodule R R) = I ^ n := fun n => by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  refine ⟨fun f hf => ?_⟩
  have key : ∀ i, ∃ L : R, ∀ n, b.repr (f n) i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro i
    refine IsPrecomplete.prec' (I := I) (fun n => b.repr (f n) i) ?_
    intro m n hmn
    have h0 := coord_mem_of_mem b (I ^ m) (SModEq.sub_mem.mp (hf hmn)) i
    rw [SModEq.sub_mem, hI]
    simpa using h0
  choose L hL using key
  refine ⟨∑ i, L i • b i, fun n => ?_⟩
  rw [SModEq.sub_mem]
  apply mem_of_coord_mem b
  intro i
  have h1 := hL i n
  rw [SModEq.sub_mem, hI] at h1
  have hs : b.repr (f n - ∑ j, L j • b j) i = b.repr (f n) i - L i := by
    rw [map_sub, Finsupp.sub_apply, map_sum, Finsupp.finset_sum_apply]
    congr 1
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Finsupp.single_apply, hj, Ne.symm hj]
    · simp
  rw [hs]
  exact h1
end ReciprocityTheory.ChartRestriction.G.Semi.Nb
