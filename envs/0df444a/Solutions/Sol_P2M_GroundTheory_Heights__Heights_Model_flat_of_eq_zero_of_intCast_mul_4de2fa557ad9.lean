-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_flat_of_eq_zero_of_intCast_mul_4de2fa557ad9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:05:03.900694+00:00
-- url     : https://prove2.me/submissions/55181dce-fee5-4e16-bcd0-42285fc45eff

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGenericSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGenericSections

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry Opposite
noncomputable section
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution {Y : Scheme.{0}} (g : Y ⟶ SpecZ)
    (hT : ∀ (V : Y.Opens) (n : ℤ) (s : Γ(Y, V)), n ≠ 0 → (n : Γ(Y, V)) * s = 0 → s = 0) :
    Flat g := by
  have := HasRingHomProperty.HasAffineProperty @Flat
  rw [HasAffineProperty.iff_of_isAffine (P := @Flat) (Q := sourceAffineLocally RingHom.Flat)]
  intro V
  let e : ℤ ≃+* Γ(SpecZ, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of ℤ)).commRingCatIsoToRingEquiv.symm
  have hφ : (g.appLE ⊤ V le_top).hom =
      (((g.appLE ⊤ V le_top).hom).comp e.toRingHom).comp e.symm.toRingHom :=
    by ext x; simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply]
  rw [hφ]
  refine RingHom.Flat.comp (RingHom.Flat.of_bijective e.symm.bijective) ?_
  generalize ((g.appLE ⊤ V le_top).hom).comp e.toRingHom = ψ
  have hψ : ψ = algebraMap ℤ Γ(Y, V) := RingHom.ext_int _ _
  rw [hψ, RingHom.flat_algebraMap_iff]
  have : Module.IsTorsionFree ℤ Γ(Y, V) := ⟨fun r hr b c hbc => by
    have hr0 : r ≠ 0 := hr.ne_zero
    simp only [zsmul_eq_mul] at hbc
    rw [← sub_eq_zero]
    exact hT V r _ hr0 (by rw [mul_sub, hbc, sub_self])⟩
  infer_instance
end GroundTheory.Heights₂.Heights.Model
