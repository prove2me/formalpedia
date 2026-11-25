-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_exists_imaginary_integer_17bb0c015b5a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:35:11.238827+00:00
-- url     : https://prove2.me/submissions/0959dd0d-7d99-4705-b3e6-a642080fb05d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StImaginaryLatticeCocompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PImaginaryLatticeCocompact
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_conj_eq_self_iff
import Theorems.Thm_GroundTheory_Automorphic_exists_not_mem_range
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj



set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
omit [IsTotallyReal F] [IsTotallyComplex E]
variable (F E)
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution : ∃ t : 𝓞 E, (t : E) ≠ 0 ∧ conj F E (t : E) = -(t : E) := by
  obtain ⟨ζ, hζ⟩ := exists_not_mem_range (F := F) (E := E)
  obtain ⟨y, hy0, hyi⟩ := (IsFractionRing.isAlgebraic_iff ℤ ℚ E |>.mpr (.of_finite ℚ ζ)).exists_integral_multiple
  have hθF : y • ζ ∉ Set.range (algebraMap F E) := by
    rintro ⟨c, hc⟩
    apply hζ
    refine ⟨(y : F)⁻¹ * c, ?_⟩
    have hy : (y : E) ≠ 0 := by exact_mod_cast hy0
    rw [map_mul, hc, map_inv₀, map_intCast, zsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hy, one_mul]
  have hcθ : IsIntegral ℤ (conj F E (y • ζ)) :=
    map_isIntegral_int ((conj F E : E ≃ₐ[F] E) : E →+* E) hyi
  refine ⟨⟨y • ζ - conj F E (y • ζ), hyi.sub hcθ⟩, ?_, ?_⟩
  · change y • ζ - conj F E (y • ζ) ≠ 0
    intro h
    apply hθF
    rw [← conj_eq_self_iff]
    exact (sub_eq_zero.mp h).symm
  · change conj F E (y • ζ - conj F E (y • ζ)) = -(y • ζ - conj F E (y • ζ))
    rw [map_sub, conj_conj]
    ring
end GroundTheory.Heights₂.Heights.FiniteCovolume
