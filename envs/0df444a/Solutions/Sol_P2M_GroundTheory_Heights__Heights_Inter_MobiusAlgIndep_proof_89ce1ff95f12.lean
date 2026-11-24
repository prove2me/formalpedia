-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_MobiusAlgIndep_proof_89ce1ff95f12
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:45.322581+00:00
-- url     : https://prove2.me/submissions/2c5e30e0-2be9-4b4c-b9d7-0985cea1e2eb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StMobiusAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PMobiusAlgIndep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
namespace GroundTheory.Heights₂.Heights.Inter
namespace MobiusAlgIndep
theorem _root_.solution : MobiusAlgIndep.Statement := by
  intro Ω _ Φ _ _ n a p q p' q' ha hdet
  have hden : ∀ j, algebraMap Ω Φ p' + a j * algebraMap Ω Φ q' ≠ 0 := by
    intro j h
    by_cases hq' : q' = 0
    · subst hq'
      have hp' : p' = 0 := by simpa using h
      exact hdet (by simp [hp'])
    · apply ha.transcendental j
      have hq : algebraMap Ω Φ q' ≠ 0 := by simpa using hq'
      have : a j = algebraMap Ω Φ (-p' / q') := by
        rw [map_div₀, map_neg]
        field_simp
        linear_combination h
      rw [this]
      exact isAlgebraic_algebraMap _
  refine ⟨hden, ?_⟩
  set b : Fin n → Φ := fun j => (algebraMap Ω Φ p + a j * algebraMap Ω Φ q) /
    (algebraMap Ω Φ p' + a j * algebraMap Ω Φ q') with hb

  have hrel : ∀ j, (algebraMap Ω Φ q' * b j - algebraMap Ω Φ q) * a j =
      algebraMap Ω Φ p - algebraMap Ω Φ p' * b j := by
    intro j
    have hbD : b j * (algebraMap Ω Φ p' + a j * algebraMap Ω Φ q') =
        algebraMap Ω Φ p + a j * algebraMap Ω Φ q := div_mul_cancel₀ _ (hden j)
    linear_combination hbD
  have hc : ∀ j, algebraMap Ω Φ q' * b j - algebraMap Ω Φ q ≠ 0 := by
    intro j h
    have h2 := hrel j
    rw [h, zero_mul] at h2
    apply hdet
    apply (algebraMap Ω Φ).injective
    simp only [map_sub, map_mul, map_zero]
    linear_combination algebraMap Ω Φ p' * h - algebraMap Ω Φ q' * h2

  let S : Set Φ := Set.range a ∪ Set.range b
  let A := Algebra.adjoin Ω S
  let a' : Fin n → A := fun j => ⟨a j, Algebra.subset_adjoin (Or.inl ⟨j, rfl⟩)⟩
  let b' : Fin n → A := fun j => ⟨b j, Algebra.subset_adjoin (Or.inr ⟨j, rfl⟩)⟩
  have ha' : AlgebraicIndependent Ω a' := AlgebraicIndependent.of_comp A.val ha
  have halg : Algebra.IsAlgebraic (Algebra.adjoin Ω (Set.range b')) A := by
    refine ⟨fun z => ?_⟩
    have hz : z ∈ Algebra.adjoin Ω (((↑) : A → Φ) ⁻¹' S) := by
      rw [Algebra.adjoin_adjoin_coe_preimage]; trivial
    refine IsAlgebraic.adjoin_of_forall_isAlgebraic (R := Ω) (s := ((↑) : A → Φ) ⁻¹' S)
      (t := Set.range b') ?_ (isAlgebraic_algebraMap (⟨z, hz⟩ : Algebra.adjoin Ω (((↑) : A → Φ) ⁻¹' S)))
    rintro x ⟨hxS, hxb⟩
    rcases hxS with ⟨j, hj⟩ | ⟨j, hj⟩
    · have hx : x = a' j := Subtype.ext hj.symm
      subst hx
      let bj : Algebra.adjoin Ω (Set.range b') := ⟨b' j, Algebra.subset_adjoin ⟨j, rfl⟩⟩
      let c : Algebra.adjoin Ω (Set.range b') :=
        algebraMap Ω _ q' * bj - algebraMap Ω _ q
      let d : Algebra.adjoin Ω (Set.range b') :=
        algebraMap Ω _ p - algebraMap Ω _ p' * bj
      refine IsAlgebraic.of_mul (y := algebraMap _ A c) ?_ (isAlgebraic_algebraMap c) ?_
      · apply mem_nonZeroDivisors_of_ne_zero
        intro h0
        apply hc j
        have h1 := congrArg (fun w : A => (w : Φ)) h0
        exact h1
      · have h3 : algebraMap _ A c * a' j = algebraMap _ A d := by
          apply Subtype.ext
          exact hrel j
        rw [h3]
        exact isAlgebraic_algebraMap d
    · exact absurd ⟨j, Subtype.ext hj⟩ hxb
  have hn : Cardinal.mk (Fin n) ≤ Algebra.trdeg Ω A := ha'.cardinalMk_le_trdeg
  have hT := Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite Ω b' hn
  exact hT.1.map' (f := A.val) Subtype.val_injective
end MobiusAlgIndep
end GroundTheory.Heights₂.Heights.Inter
