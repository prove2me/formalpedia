-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RankFracDegree_isFractionRing_of_closure_00df87cf7f7b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:14:38.434676+00:00
-- url     : https://prove2.me/submissions/e07bf1e5-771d-4a8a-9b08-01e263e83fbd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StRankFracDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRankFracDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
namespace GroundTheory.Heights₂.Heights.Inter
namespace RankFracDegree
theorem _root_.solution {F Ω A : Type} [Field F] [Field Ω] [Algebra F Ω] [CommRing A]
    (K : IntermediateField F Ω) (f : A →+* Ω) (hf : Function.Injective f) (hK : ∀ a, f a ∈ K)
    (hcl : K.toSubfield ≤ Subfield.closure (Set.range f)) :
    let _ := (f.codRestrict K hK).toAlgebra
    IsFractionRing A K := by
  intro _
  have hmap : ∀ a, ((algebraMap A K a : K) : Ω) = f a := fun _ => rfl
  have hnz : ∀ a : A, a ∈ nonZeroDivisors A → f a ≠ 0 := by
    intro a ha h0
    have h10 : (1 : A) = 0 :=
      mem_nonZeroDivisors_iff_right.mp ha 1 (by rw [one_mul]; exact hf (by rw [h0, map_zero]))
    exact one_ne_zero (by simpa using congrArg f h10 : (1 : Ω) = 0)
  show IsLocalization (nonZeroDivisors A) K
  rw [isLocalization_iff]
  refine ⟨fun y => IsUnit.mk0 _ fun h => hnz y y.2 (by rw [← hmap, h]; rfl), fun z => ?_, fun {x y} h => ?_⟩
  · obtain ⟨y, hy, w, hw, hyw⟩ := Subfield.mem_closure_iff.mp (hcl z.2)
    rw [← RingHom.coe_range, Subring.closure_eq] at hy hw
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨a', rfl⟩ := hw
    by_cases h0 : f a' = 0
    · refine ⟨(0, 1), Subtype.ext ?_⟩
      simp only [OneMemClass.coe_one, map_zero, map_one, mul_one, ZeroMemClass.coe_zero]
      rw [← hyw, h0, div_zero]
    · have ha' : a' ∈ nonZeroDivisors A :=
        mem_nonZeroDivisors_of_injective hf (mem_nonZeroDivisors_of_ne_zero h0)
      refine ⟨(a, ⟨a', ha'⟩), Subtype.ext ?_⟩
      simp only [MulMemClass.coe_mul, hmap]
      rw [← hyw, div_mul_cancel₀ _ h0]
  · refine ⟨1, ?_⟩
    have hxy : x = y := hf (by rw [← hmap x, ← hmap y, h])
    rw [hxy]
end RankFracDegree
end GroundTheory.Heights₂.Heights.Inter
