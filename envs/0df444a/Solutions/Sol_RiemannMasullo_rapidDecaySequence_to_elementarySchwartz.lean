-- Prove2me | solution 1 for RiemannMasullo.rapidDecaySequence_to_elementarySchwartz
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T03:15:19.274818+00:00
-- url     : https://prove2.me/submissions/e7c06b7b-f6d4-4a6a-96a0-c70ab0654141

-- New supporting theorem for the identification in Appendix D, Remark D.1.3.6.
import Theorems.Thm_RiemannMasullo_lattice_monomial_sup_le_weighted_sequence_sum
import Theorems.Thm_RiemannMasullo_rapidDecaySequence_withSeminorms
import Theorems.Thm_RiemannMasullo_elementarySchwartz_withSeminorms
import Definitions.Def_RiemannMasullo_RapidDecaySequenceTopology
import Mathlib
open RiemannMasullo

theorem solution (r : ℕ) :
    ∃ L : RapidDecaySequence r →L[ℂ] ElementarySchwartz 0 0 r PUnit,
      Function.Injective L ∧ ∀ s (g : ElementaryLieGroup 0 0 r PUnit), L s g = s g.2.2.1 := by
  classical
  let S := RapidDecaySequence r
  let G := ElementaryLieGroup 0 0 r PUnit
  let hmem (s : S) : (fun g : G => s g.2.2.1) ∈ elementarySchwartzSubmodule 0 0 r PUnit := by
    constructor
    · intro a b
      change ContDiff ℝ _ (fun _ : EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin 0) => s a)
      exact contDiff_const
    · intro i
      exact (lattice_monomial_sup_le_weighted_sequence_sum r s.val i).trans_lt (s.property _)
  let L : S →ₗ[ℂ] ElementarySchwartz 0 0 r PUnit :=
    { toFun := fun s =>
        (⟨fun g : G => s g.2.2.1,hmem s⟩ : elementarySchwartzSubmodule 0 0 r PUnit)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hcont : Continuous L := by
    apply WithSeminorms.continuous_of_continuous_comp
      (elementarySchwartz_withSeminorms (m:=0) (n:=0) (r:=r) (F:=PUnit)) L
    intro i
    apply Seminorm.continuous_of_le (rapidDecaySequence_withSeminorms.continuous_seminorm (∑ k,i.2.2.2 k))
    intro s
    exact ENNReal.toReal_mono (s.property _).ne (lattice_monomial_sup_le_weighted_sequence_sum r s.val i)
  refine ⟨⟨L,hcont⟩,?_,fun _ _ => rfl⟩
  intro s t h
  apply Subtype.ext
  funext a
  exact congrArg (fun f : ElementarySchwartz 0 0 r PUnit => f (0,0,a,PUnit.unit)) h
