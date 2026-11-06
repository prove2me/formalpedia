-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.localKaehler_map_injective_of_splitResidue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:01:14.945616+00:00
-- url     : https://prove2.me/submissions/785d40df-c680-4e4a-830a-20321a135ec9

import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.LocalRing.Module
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalKaehlerCyclic
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_localKaehler_span_parameter_of_splitResidue

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable (k V : Type*) [CommRing k] [CommRing V] [Algebra k V]
variable [IsLocalRing V] [Algebra.EssFiniteType k V]
variable (K : Type*) [Field K] [Algebra k K] [Algebra V K]
variable [IsScalarTower k V K] [SMulCommClass k V K]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    (e : V →ₐ[k] k) (he : RingHom.ker e = IsLocalRing.maximalIdeal V)
    (pi : V) (hpi : IsLocalRing.maximalIdeal V = Ideal.span {pi})
    (hfaith : Function.Injective (algebraMap V K))
    (hd : KaehlerDifferential.D k K (algebraMap V K pi) ≠ 0) :
    Function.Injective (KaehlerDifferential.map k k V K) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro omega homega
  have hspan : omega ∈ Submodule.span V {KaehlerDifferential.D k V pi} := by
    rw [localKaehler_span_parameter_of_splitResidue k V e he pi hpi]
    trivial
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hspan
  have hz : (KaehlerDifferential.map k k V K) (c • KaehlerDifferential.D k V pi) = 0 := by
    rw [hc]
    exact homega
  rw [map_smul,KaehlerDifferential.map_D] at hz
  rw [← IsScalarTower.algebraMap_smul K c] at hz
  have hc0 : c = 0 := hfaith (by
    rw [map_zero]
    exact (smul_eq_zero.mp hz).resolve_right hd)
  rw [← hc,hc0,zero_smul]
  exact Submodule.zero_mem _
end QEC.Coding.AlgebraicGeometry
