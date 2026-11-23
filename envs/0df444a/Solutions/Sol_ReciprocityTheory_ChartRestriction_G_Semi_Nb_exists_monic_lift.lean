-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.Nb.exists_monic_lift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:15.520452+00:00
-- url     : https://prove2.me/submissions/4280f965-0a48-4e1c-a1b4-6cb174c513f9

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
namespace ReciprocityTheory.ChartRestriction.G.Semi.Nb
theorem _root_.solution (g : (ResidueField V)[X]) (hg : g.Monic) :
    ∃ f : V[X], f.map (residue V) = g ∧ f.natDegree = g.natDegree ∧ f.Monic := by
  obtain ⟨q, hq⟩ := Polynomial.map_surjective (residue V) residue_surjective g
  exact lifts_and_natDegree_eq_and_monic ((mem_lifts g).2 ⟨q, hq⟩) hg
end ReciprocityTheory.ChartRestriction.G.Semi.Nb
