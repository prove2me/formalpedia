-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.Nb.resEquiv_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:16.315168+00:00
-- url     : https://prove2.me/submissions/9b518251-1382-4aa5-9074-f3a17b771647

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
theorem _root_.solution [IsLocalRing (AdjoinRoot f)] :
    have := locHom f hf hg
    (resEquiv f hf hg).toRingHom.comp (ResidueField.map (algebraMap V (AdjoinRoot f))) =
      AdjoinRoot.of (f.map (residue V)) := by
  intro hl
  refine RingHom.ext fun x => ?_
  obtain ⟨y, rfl⟩ := residue_surjective x
  refine (AdjoinRoot.quotEquivQuotMap_apply_mk f (C y) (maximalIdeal V)).trans ?_
  rw [Polynomial.map_C]
  rfl
end ReciprocityTheory.ChartRestriction.G.Semi.Nb
