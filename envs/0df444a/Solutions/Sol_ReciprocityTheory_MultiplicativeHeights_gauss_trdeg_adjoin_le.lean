-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.gauss_trdeg_adjoin_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:25.903429+00:00
-- url     : https://prove2.me/submissions/72dc406c-a792-4120-8bb6-96eb829906e7

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
    (tb : σ → C) : Algebra.trdeg E (Algebra.adjoin E (Set.range tb)) ≤ Cardinal.mk σ := by
  obtain ⟨t, hts, hb⟩ := exists_transcendenceBasis_subset_adjoin_range (E := E) tb
  rw [← hb.cardinalMk_eq_trdeg]
  calc Cardinal.mk t ≤ Cardinal.mk ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))) :=
        Cardinal.mk_le_mk_of_subset hts
    _ ≤ Cardinal.mk (Set.range tb) := Cardinal.mk_preimage_of_injective _ _ Subtype.val_injective
    _ ≤ Cardinal.mk σ := Cardinal.mk_range_le
end ReciprocityTheory.MultiplicativeHeights
