-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.Nb.dvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:45:05.091649+00:00
-- url     : https://prove2.me/submissions/cffc4686-158d-447c-bcf3-6f9145138521

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Nb_inj

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
theorem _root_.solution [IsDomain (AdjoinRoot f)] [IsLocalRing (AdjoinRoot f)] :
    IsDiscreteValuationRing (AdjoinRoot f) := by
  haveI := finite f hf
  haveI : IsNoetherianRing (AdjoinRoot f) := isNoetherian_of_tower V inferInstance
  obtain ⟨w, hw⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hmV : maximalIdeal V = Ideal.span {w} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer w).mp hw
  have hmA : maximalIdeal (AdjoinRoot f) = Ideal.span {algebraMap V (AdjoinRoot f) w} := by
    rw [maxEq f hf hg, hmV, Ideal.map_span, Set.image_singleton]
  have hne : algebraMap V (AdjoinRoot f) w ≠ 0 := by
    rw [← map_zero (algebraMap V (AdjoinRoot f))]
    exact fun h => hw.ne_zero (inj f hf hg h)
  have hnf : ¬IsField (AdjoinRoot f) := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hmA, Ideal.span_singleton_eq_bot]
    exact hne
  have hpr : (maximalIdeal (AdjoinRoot f)).IsPrincipal := ⟨⟨_, hmA⟩⟩
  exact ((IsDiscreteValuationRing.TFAE (AdjoinRoot f) hnf).out 0 4).mpr hpr
end ReciprocityTheory.ChartRestriction.G.Semi.Nb
