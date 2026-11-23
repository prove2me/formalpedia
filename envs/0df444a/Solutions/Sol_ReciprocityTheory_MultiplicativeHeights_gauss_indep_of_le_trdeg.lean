-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.gauss_indep_of_le_trdeg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:29.591803+00:00
-- url     : https://prove2.me/submissions/88b73ec5-bd43-4f19-9ad6-cee3558c1a52

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussIndepOfLeTrdeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.MultiplicativeHeights
open MvPolynomial
private theorem exists_transcendenceBasis_subset_adjoin_range {E C : Type} [Field E] [Field C] [Algebra E C] {σ : Type}
    (tb : σ → C) : ∃ t ⊆ ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))),
      IsTranscendenceBasis E (Subtype.val : t → Algebra.adjoin E (Set.range tb)) := by
  have htop : Algebra.adjoin E ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))) = ⊤ :=
    Algebra.adjoin_adjoin_coe_preimage
  haveI : FaithfulSMul E (Algebra.adjoin E (Set.range tb)) :=
    (faithfulSMul_iff_algebraMap_injective E _).mpr (algebraMap E _).injective
  haveI : Algebra.IsAlgebraic
      (Algebra.adjoin E ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))))
      (Algebra.adjoin E (Set.range tb)) := ⟨fun a => by
    have ha : a ∈ Algebra.adjoin E ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))) := by
      rw [htop]; exact Algebra.mem_top
    exact isAlgebraic_algebraMap (⟨a, ha⟩ : Algebra.adjoin E _)⟩
  exact exists_isTranscendenceBasis_subset (R := E) _
end ReciprocityTheory.MultiplicativeHeights
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MvPolynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {E C : Type} [Field E] [Field C] [Algebra E C] {σ : Type}
    [Finite σ] (tb : σ → C)
    (h : Cardinal.mk σ ≤ Algebra.trdeg E (Algebra.adjoin E (Set.range tb))) :
    AlgebraicIndependent E tb := by
  classical
  obtain ⟨t, hts, hb⟩ := exists_transcendenceBasis_subset_adjoin_range (E := E) tb
  have ht := hb.cardinalMk_eq_trdeg
  have h1 : Cardinal.mk t ≤ Cardinal.mk ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))) :=
    Cardinal.mk_le_mk_of_subset hts
  have h2 : Cardinal.mk ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))) ≤
      Cardinal.mk (Set.range tb) := Cardinal.mk_preimage_of_injective _ _ Subtype.val_injective
  have h3 : Cardinal.mk (Set.range tb) ≤ Cardinal.mk σ := Cardinal.mk_range_le
  have hσt : Cardinal.mk σ ≤ Cardinal.mk t := ht ▸ h

  have hinj : Function.Injective tb := by
    obtain ⟨e⟩ := Cardinal.eq.1 (le_antisymm h3 (hσt.trans (h1.trans h2)))
    have hr : Function.Injective (Set.rangeFactorization tb) :=
      (Finite.injective_iff_surjective_of_equiv e.symm).2 Set.rangeFactorization_surjective
    exact fun a b hab => hr (Subtype.ext hab)

  have hsf : ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))).Finite :=
    (Set.finite_range tb).preimage Subtype.val_injective.injOn
  have hle : ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))).ncard ≤ t.ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact Cardinal.toNat_le_toNat ((h2.trans h3).trans hσt) (hsf.subset hts).lt_aleph0
  rw [Set.eq_of_subset_of_ncard_le hts hle hsf] at hb
  let g : σ → Algebra.adjoin E (Set.range tb) := fun i => ⟨tb i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
  have hginj : Function.Injective g := fun a b hab => hinj (congrArg Subtype.val hab)
  have hrange : Set.range g = ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, Subtype.ext hi⟩
  have hg : AlgebraicIndependent E g := by
    rw [← algebraicIndependent_subtype_range hginj, hrange]
    exact hb.1
  exact hg.map' (f := (Algebra.adjoin E (Set.range tb)).val) Subtype.val_injective
end ReciprocityTheory.MultiplicativeHeights
