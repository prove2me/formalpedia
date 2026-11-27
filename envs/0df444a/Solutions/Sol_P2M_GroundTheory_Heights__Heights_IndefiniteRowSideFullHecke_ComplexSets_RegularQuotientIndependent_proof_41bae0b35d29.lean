-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RegularQuotientIndependent_proof_41bae0b35d29
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:04:30.080577+00:00
-- url     : https://prove2.me/submissions/21818736-8833-4ce9-b0d4-eae6137bcde3

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularQuotientIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegularQuotientIndependent
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_isRegularLocalRing_quotient


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open IsLocalRing Ideal
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace RegularQuotientIndependent
theorem _root_.solution : RegularQuotientIndependent.Statement := by
  intro S _ _ h
  induction h generalizing S with
  | zero =>
    intro x _ _
    have hr : Set.range x = ∅ := Set.range_eq_empty x
    rw [hr, Ideal.span_empty]
    exact IsRegularLocalRing.of_ringEquiv (RingEquiv.quotientBot S).symm
  | succ h ih =>
    intro x hxm hind
    have hx02 : x 0 ∉ maximalIdeal S ^ 2 := by
      intro hc
      have h1 := hind (Pi.single 0 1) (by simpa [Pi.single_apply] using hc) 0
      simp at h1
    have hne : span {x 0} ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top
      ((span_singleton_le_iff_mem _).mpr (hxm 0))
    have : Nontrivial (S ⧸ span {x 0}) := Ideal.Quotient.nontrivial_iff.mpr hne
    have : IsLocalRing (S ⧸ span {x 0}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    have := (GroundTheory.Arith.SchemeCoh.isRegularLocalRing_quotient (hxm 0) hx02).1
    set f := Ideal.Quotient.mk (span {x 0}) with hf
    have hmax : (maximalIdeal S).map f = maximalIdeal (S ⧸ span {x 0}) :=
      map_maximalIdeal_of_surjective f Ideal.Quotient.mk_surjective
    let y : Fin h → S ⧸ span {x 0} := fun i ↦ f (x i.succ)
    have hy : ∀ i, y i ∈ maximalIdeal (S ⧸ span {x 0}) := fun i ↦
      hmax ▸ Ideal.mem_map_of_mem f (hxm i.succ)
    have hyind : ∀ b : Fin h → S ⧸ span {x 0}, ∑ i, b i * y i ∈ maximalIdeal (S ⧸ span {x 0}) ^ 2 →
        ∀ i, b i ∈ maximalIdeal (S ⧸ span {x 0}) := by
      intro b hb i
      choose a ha using fun i ↦ Ideal.Quotient.mk_surjective (I := span {x 0}) (b i)
      have hsum : ∑ i, b i * y i = f (∑ i, a i * x i.succ) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by simp only [map_mul, ← ha i, hf, y]
      rw [hsum, ← hmax, ← Ideal.map_pow, hf, Ideal.mem_quotient_iff_mem_sup] at hb
      obtain ⟨z, hz, w, hw, hzw⟩ := Submodule.mem_sup.mp hb
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hw
      have h2 := hind (Fin.cons (-c) a) (by
        rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        have : -c * x 0 + ∑ i, a i * x i.succ = z := by rw [← hzw]; ring
        rw [this]; exact hz) i.succ
      simp only [Fin.cons_succ] at h2
      rw [← ha i, ← hmax]
      exact Ideal.mem_map_of_mem _ h2
    have hreg := ih (S ⧸ span {x 0}) y hy hyind
    set J : Ideal S := span (Set.range (fun i : Fin h ↦ x i.succ)) with hJ
    have hspan : span (Set.range y) = J.map f := by
      rw [hJ, Ideal.map_span, ← Set.range_comp]
      rfl
    have hsup : span {x 0} ⊔ J = span (Set.range x) := by
      rw [hJ, ← Ideal.span_union]
      congr 1
      ext s
      simp [Fin.exists_fin_succ, eq_comm]
    exact IsRegularLocalRing.of_ringEquiv (((Ideal.quotEquivOfEq hspan).trans
      (DoubleQuot.quotQuotEquivQuotSup (span {x 0}) J)).trans (Ideal.quotEquivOfEq hsup))
end RegularQuotientIndependent
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
