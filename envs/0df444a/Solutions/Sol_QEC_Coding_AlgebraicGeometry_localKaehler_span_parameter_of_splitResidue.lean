-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.localKaehler_span_parameter_of_splitResidue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:00:32.441788+00:00
-- url     : https://prove2.me/submissions/a5da6e03-a46f-4f85-a3d2-9428177e7017

import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.LocalRing.Module
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalKaehlerCyclic

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable (k V : Type*) [CommRing k] [CommRing V] [Algebra k V]
variable [IsLocalRing V] [Algebra.EssFiniteType k V]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    (e : V →ₐ[k] k) (he : RingHom.ker e = IsLocalRing.maximalIdeal V)
    (pi : V) (hpi : IsLocalRing.maximalIdeal V = Ideal.span {pi}) :
    Submodule.span V {KaehlerDifferential.D k V pi} = ⊤ := by
  let U := Submodule.span V {KaehlerDifferential.D k V pi}
  let m := IsLocalRing.maximalIdeal V
  have hpim : pi ∈ m := by change pi ∈ IsLocalRing.maximalIdeal V; rw [hpi]; exact Ideal.mem_span_singleton_self pi
  have htop : (⊤ : Submodule V (KaehlerDifferential k V)) ≤ U ⊔ m • ⊤ := by
    conv_lhs => rw [← KaehlerDifferential.span_range_derivation]
    apply Submodule.span_le.mpr
    rintro _ ⟨f,rfl⟩
    have hmem : f - algebraMap k V (e f) ∈ m := by
      change f - algebraMap k V (e f) ∈ IsLocalRing.maximalIdeal V
      rw [← he]
      change e (f-algebraMap k V (e f)) = 0
      simp
    change f - algebraMap k V (e f) ∈ IsLocalRing.maximalIdeal V at hmem
    rw [hpi] at hmem
    obtain ⟨a,ha⟩ := Ideal.mem_span_singleton'.mp hmem
    have hf : f = a*pi + algebraMap k V (e f) := (eq_sub_iff_add_eq.mp ha).symm
    rw [hf,map_add,Derivation.leibniz,Derivation.map_algebraMap,add_zero]
    exact (U ⊔ m • ⊤).add_mem
      (Submodule.mem_sup_left (U.smul_mem a (Submodule.mem_span_singleton_self _)))
      (Submodule.mem_sup_right (Submodule.smul_mem_smul hpim (Submodule.mem_top)))
  apply top_le_iff.mp
  exact Submodule.le_of_le_smul_of_le_jacobson_bot
    (Module.finite_def.mp inferInstance) (IsLocalRing.maximalIdeal_le_jacobson ⊥) htop
end QEC.Coding.AlgebraicGeometry
