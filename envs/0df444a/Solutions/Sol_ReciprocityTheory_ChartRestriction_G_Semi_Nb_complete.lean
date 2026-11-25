-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.Nb.complete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:52:07.298035+00:00
-- url     : https://prove2.me/submissions/3b563afa-d7dc-4bf7-ac39-18cf8e7a4712

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Nb_isPrecomplete_of_basis

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
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable (f : V[X]) (hf : f.Monic) (hg : Irreducible (f.map (residue V)))
include hf hg
namespace ReciprocityTheory.ChartRestriction.G.Semi.Nb
theorem _root_.solution [IsLocalRing (AdjoinRoot f)] [IsAdicComplete (maximalIdeal V) V] :
    IsAdicComplete (maximalIdeal (AdjoinRoot f)) (AdjoinRoot f) := by
  let b := (AdjoinRoot.powerBasis' hf).basis
  have key : ∀ (n : ℕ) (x : AdjoinRoot f),
      x ∈ (maximalIdeal (AdjoinRoot f) ^ n • ⊤ : Submodule (AdjoinRoot f) (AdjoinRoot f)) ↔
        x ∈ ((maximalIdeal V) ^ n • ⊤ : Submodule V (AdjoinRoot f)) := by
    intro n x
    rw [Ideal.smul_eq_mul, Ideal.mul_top, maxEq f hf hg, ← Ideal.map_pow, Ideal.smul_top_eq_map,
      Submodule.restrictScalars_mem]
  have hP : IsPrecomplete (maximalIdeal V) (AdjoinRoot f) := isPrecomplete_of_basis _ b
  have hH : IsHausdorff (maximalIdeal (AdjoinRoot f)) (AdjoinRoot f) := by
    refine ⟨fun x hx => ?_⟩
    have h1 : ∀ n, x ∈ ((maximalIdeal V) ^ n • ⊤ : Submodule V (AdjoinRoot f)) := fun n =>
      (key n x).mp (by simpa using SModEq.sub_mem.mp (hx n))
    have h2 : ∀ i, b.repr x i = 0 := fun i =>
      IsHausdorff.haus' (I := maximalIdeal V) (b.repr x i) fun n => by
        rw [SModEq.sub_mem, sub_zero, Ideal.smul_eq_mul, Ideal.mul_top]
        exact coord_mem_of_mem b _ (h1 n) i
    rw [← b.sum_repr x]
    simp [h2]
  have hC : IsPrecomplete (maximalIdeal (AdjoinRoot f)) (AdjoinRoot f) := by
    refine ⟨fun g hg' => ?_⟩
    obtain ⟨L, hL⟩ := hP.prec' g fun {a c} hac => by
      rw [SModEq.sub_mem, ← key]
      exact SModEq.sub_mem.mp (hg' hac)
    exact ⟨L, fun n => by
      rw [SModEq.sub_mem, key]
      exact SModEq.sub_mem.mp (hL n)⟩
  exact IsAdicComplete.mk
end ReciprocityTheory.ChartRestriction.G.Semi.Nb
