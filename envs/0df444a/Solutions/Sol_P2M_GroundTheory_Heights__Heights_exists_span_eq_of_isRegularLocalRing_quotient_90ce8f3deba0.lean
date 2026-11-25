-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_exists_span_eq_of_isRegularLocalRing_quotient_90ce8f3deba0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:49:05.138654+00:00
-- url     : https://prove2.me/submissions/afd5f3dc-7a8f-4fa5-a3f4-2269aa5ae8e2

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RegularQuotientGenerators
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_spanFinrank_maximalIdeal_le_quotient_of_le_sq_c23dc5f32007
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsRegularLocalRing_isDomain
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open IsLocalRing Ideal
universe u
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (n : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R] (I : Ideal R) [IsRegularLocalRing (R ⧸ I)],
      ringKrullDim R = ringKrullDim (R ⧸ I) + n →
        ∃ f : Fin n → R, (∀ j, f j ∈ I) ∧ I = Ideal.span (Set.range f) := by
  induction n with
  | zero =>
    intro R _ _ I _ hd
    refine ⟨Fin.elim0, fun j => j.elim0, ?_⟩
    rw [Set.range_eq_empty, Ideal.span_empty]
    have := GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isDomain (R := R)
    by_contra hI
    obtain ⟨y, hyI, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hy0)
    have h2 : ringKrullDim (R ⧸ I) ≤ ringKrullDim (R ⧸ Ideal.span {y}) :=
      ringKrullDim_le_of_surjective (Ideal.Quotient.factor ((Ideal.span_singleton_le_iff_mem I).mpr hyI))
        (Ideal.Quotient.factor_surjective _)
    have hR : ringKrullDim R = ((maximalIdeal R).spanFinrank : WithBot ℕ∞) :=
      ((isRegularLocalRing_iff R).mp inferInstance).symm
    rw [Nat.cast_zero, add_zero] at hd
    have h3 : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) + 1 ≤ (maximalIdeal R).spanFinrank := by
      rw [← hR]
      calc ringKrullDim R + 1 = ringKrullDim (R ⧸ I) + 1 := by rw [hd]
        _ ≤ ringKrullDim (R ⧸ Ideal.span {y}) + 1 := by gcongr
        _ ≤ ringKrullDim R := h1
    have h4 : (maximalIdeal R).spanFinrank + 1 ≤ (maximalIdeal R).spanFinrank := by exact_mod_cast h3
    omega
  | succ n ih =>
    intro R _ _ I _ hd
    have hR : ringKrullDim R = ((maximalIdeal R).spanFinrank : WithBot ℕ∞) :=
      ((isRegularLocalRing_iff R).mp inferInstance).symm
    have hRI : ringKrullDim (R ⧸ I) = ((maximalIdeal (R ⧸ I)).spanFinrank : WithBot ℕ∞) :=
      ((isRegularLocalRing_iff (R ⧸ I)).mp inferInstance).symm
    have hdd : (maximalIdeal R).spanFinrank = (maximalIdeal (R ⧸ I)).spanFinrank + (n + 1) := by
      rw [hR, hRI] at hd
      exact_mod_cast hd
    have hItop : I ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp inferInstance
    have hIm : I ≤ maximalIdeal R := le_maximalIdeal hItop
    obtain ⟨x, hxI, hx2⟩ : ∃ x ∈ I, x ∉ maximalIdeal R ^ 2 := by
      by_contra h
      push Not at h
      have := spanFinrank_maximalIdeal_le_quotient_of_le_sq (I := I) h
      omega
    have hxm : x ∈ maximalIdeal R := hIm hxI
    have hxI' : Ideal.span {x} ≤ I := (Ideal.span_singleton_le_iff_mem I).mpr hxI
    have hne : Ideal.span {x} ≠ ⊤ := fun h => hItop (top_le_iff.mp (h ▸ hxI'))
    have : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr hne
    have : IsLocalRing (R ⧸ Ideal.span {x}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    obtain ⟨hreg, hdim⟩ := GroundTheory.Arith.SchemeCoh.isRegularLocalRing_quotient hxm hx2
    have := hreg
    let e := DoubleQuot.quotQuotEquivQuotOfLE hxI'
    have : IsRegularLocalRing ((R ⧸ Ideal.span {x}) ⧸ I.map (Ideal.Quotient.mk (Ideal.span {x}))) :=
      IsRegularLocalRing.of_ringEquiv e.symm
    have hR' : ringKrullDim (R ⧸ Ideal.span {x}) =
        ((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank : WithBot ℕ∞) :=
      ((isRegularLocalRing_iff _).mp inferInstance).symm
    have hd' : ringKrullDim (R ⧸ Ideal.span {x}) =
        ringKrullDim ((R ⧸ Ideal.span {x}) ⧸ I.map (Ideal.Quotient.mk (Ideal.span {x}))) + n := by
      rw [ringKrullDim_eq_of_ringEquiv e, hRI, hR']
      rw [hR, hR'] at hdim
      have h5 : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 = (maximalIdeal R).spanFinrank := by
        exact_mod_cast hdim
      have h6 : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank = (maximalIdeal (R ⧸ I)).spanFinrank + n := by
        omega
      rw [h6]
      push_cast
      rfl
    obtain ⟨f', hf'I, hf'⟩ := ih _ _ hd'
    have hlift : ∀ j, ∃ a ∈ I, Ideal.Quotient.mk (Ideal.span {x}) a = f' j := fun j =>
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp (hf'I j)
    choose g hgI hg using hlift
    refine ⟨(Fin.cons x g : Fin (n + 1) → R), Fin.forall_fin_succ.mpr ⟨by simpa using hxI, fun i => by simpa using hgI i⟩, ?_⟩
    rw [Fin.range_cons, Ideal.span_insert]
    have hcomap : I = (I.map (Ideal.Quotient.mk (Ideal.span {x}))).comap (Ideal.Quotient.mk (Ideal.span {x})) := by
      rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_eq_left.mpr hxI']
    have hrange : Set.range f' = Ideal.Quotient.mk (Ideal.span {x}) '' Set.range g := by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext hg).symm
    rw [hcomap, hf', hrange, ← Ideal.map_span, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker, sup_comm]
end GroundTheory.Heights₂.Heights
