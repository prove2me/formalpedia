-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.Nb.isLocal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:15.924625+00:00
-- url     : https://prove2.me/submissions/5ced71ba-d1a5-4f68-ac99-9b345f48b29c

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Nb_finite

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
theorem _root_.solution : IsLocalRing (AdjoinRoot f) := by
  haveI := finite f hf
  refine IsLocalRing.of_unique_max_ideal ⟨_, J_max f hf hg, fun P hP => ?_⟩
  haveI := hP
  have hc : P.comap (algebraMap V (AdjoinRoot f)) = maximalIdeal V :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P)
  have hle : (maximalIdeal V).map (algebraMap V (AdjoinRoot f)) ≤ P := by
    rw [← hc]
    exact Ideal.map_comap_le
  exact ((J_max f hf hg).eq_of_le hP.ne_top hle).symm
end ReciprocityTheory.ChartRestriction.G.Semi.Nb
