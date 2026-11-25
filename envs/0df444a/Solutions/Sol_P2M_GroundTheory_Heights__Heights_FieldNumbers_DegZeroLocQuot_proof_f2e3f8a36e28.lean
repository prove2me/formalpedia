-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_DegZeroLocQuot_proof_f2e3f8a36e28
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:57:46.436296+00:00
-- url     : https://prove2.me/submissions/7721b45b-4437-4190-86b7-20537d882d55

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDegZeroLocQuot
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace DegZeroLocQuot
theorem _root_.solution : DegZeroLocQuot.Statement := by
  intro F _ K _ ι P _ 𝒲 h𝒲 x hx

  set φ : MRing ι F →+* FractionRing (MRing ι F ⧸ P) :=
    (algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))).comp (Ideal.Quotient.mk P) with hφ
  have hne : ∀ g : MRing ι F, g ∉ P → φ g ≠ 0 := fun g hg => by
    rw [hφ, RingHom.comp_apply, Ne, IsFractionRing.to_map_eq_zero_iff,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hg
  let Q : FractionRing (MRing ι F ⧸ P) → Prop := fun y =>
    ∃ (b : K → ℕ) (f g : MRing ι F), IsMultiHomog f b ∧ IsMultiHomog g b ∧
      g ∉ P ∧ (∀ W ∈ 𝒲, g ∉ W) ∧ y = φ f / φ g
  have key : Q x := by
    refine Algebra.adjoin_induction (p := fun y _ => Q y) ?_ ?_ ?_ ?_ hx
    · rintro y ⟨b, f, g, hf, hg, hgP, hgW, rfl⟩
      exact ⟨b, f, g, hf, hg, hgP, hgW, rfl⟩
    · intro c
      refine ⟨0, C c, 1, isWeightedHomogeneous_C _ c, isWeightedHomogeneous_one F _, ?_, ?_, ?_⟩
      · exact (Ideal.ne_top_iff_one P).mp (Ideal.IsPrime.ne_top inferInstance)
      · intro W hW
        exact (Ideal.ne_top_iff_one W).mp (h𝒲 W hW).ne_top
      · rw [map_one, div_one, hφ, RingHom.comp_apply,
          IsScalarTower.algebraMap_apply F (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))]
        rfl
    · rintro y z - - ⟨b, f, g, hf, hg, hgP, hgW, rfl⟩ ⟨b', f', g', hf', hg', hgP', hgW', rfl⟩
      refine ⟨b + b', f * g' + g * f', g * g', (hf.mul hg').add (hg.mul hf'), hg.mul hg', ?_, ?_, ?_⟩
      · exact fun h => ((Ideal.IsPrime.mem_or_mem inferInstance h).elim hgP hgP')
      · intro W hW h
        exact ((h𝒲 W hW).mem_or_mem h).elim (hgW W hW) (hgW' W hW)
      · rw [div_add_div _ _ (hne g hgP) (hne g' hgP'), map_add, map_mul, map_mul, map_mul]
    · rintro y z - - ⟨b, f, g, hf, hg, hgP, hgW, rfl⟩ ⟨b', f', g', hf', hg', hgP', hgW', rfl⟩
      refine ⟨b + b', f * f', g * g', hf.mul hf', hg.mul hg', ?_, ?_, ?_⟩
      · exact fun h => ((Ideal.IsPrime.mem_or_mem inferInstance h).elim hgP hgP')
      · intro W hW h
        exact ((h𝒲 W hW).mem_or_mem h).elim (hgW W hW) (hgW' W hW)
      · rw [div_mul_div_comm, map_mul, map_mul]
  exact key
end DegZeroLocQuot
end GroundTheory.Heights₂.Heights.FieldNumbers
