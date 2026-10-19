-- Prove2me | solution 1 for SoficGroups.KunRootedWordPower.pairedDefectWordAverage_eq_unitaryFinsetMarkov_iterate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/659d504b-4f21-46f6-a1c8-ed1b54aebdf7

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedWordPower_representationFamilyMarkovLinear_subtype_pow_apply
import Theorems.Thm_SoficGroups_KunRootedWordPower_representationFamilyMarkovLinear_pair_of_equivariant
import Theorems.Thm_SoficGroups_KunRootedWordPower_linear_pairedWordAverage_pow

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedWordPower
open Filter Topology
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace Pointwise
universe u v w
namespace SoficGroups.KunRootedWordPower
theorem _root_.solution
    {G H : Type*} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : SoficGroups.UnitaryRepresentation G H)
    (S : Finset G) (v : G × G → H)
    (hequivariant : ∀ a g h : G,
      π a (v (g, h)) = v (a * g, a * h))
    (k : ℕ) :
    pairedDefectWordAverage (fun i : ↥S => (i : G)) v k =
      ((unitaryFinsetMarkov π S)^[k])
        (pairedDefectWordAverage (fun i : ↥S => (i : G)) v 0) := by
  let s : ↥S → G := fun i => (i : G)
  let L : H →ₗ[ℂ] H := representationFamilyMarkovLinear π s
  have hbase : ∀ q, L (v q) = pairedWordAverage s v 1 q :=
    fun q => representationFamilyMarkovLinear_pair_of_equivariant
      π s v hequivariant q
  have hpow :
      (L ^ k) (pairedDefectWordAverage s v 0) =
        pairedDefectWordAverage s v k := by
    simp only [pairedDefectWordAverage, pairedWordAverage,
      map_smul, map_sum]
    apply congrArg (fun x => (Fintype.card (↥S) : ℂ)⁻¹ • x)
    exact Finset.sum_congr rfl fun i _ =>
      linear_pairedWordAverage_pow s L v hbase k (s i, 1)
  have hrewrite :=
    representationFamilyMarkovLinear_subtype_pow_apply
      π S k (pairedDefectWordAverage s v 0)
  exact hpow.symm.trans hrewrite
end SoficGroups.KunRootedWordPower
