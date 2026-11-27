-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualStdModelTransc_proof_e42ae22b6284
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:55:10.693804+00:00
-- url     : https://prove2.me/submissions/b8be784d-2aa3-498c-8fa6-b05b4b624011

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualStdModelField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdModelTransc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_transcendental_of_scale_4a059b5201ae
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_scale_inl_1f1551173b5c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_scale_inr_f74ac1b56685
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_dualLatticeCoord_eq_ca49334a53b1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_evalForm_ne_zero_eeeb6c3d9f4a


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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial
noncomputable section
open DualArithmeticVariety StandardDualModelTranscendence
namespace GroundTheory.Heights₂.Heights
namespace DualStdModelTransc
theorem _root_.solution : DualStdModelTransc.Statement := by
  intro K _ _ i T _ _ b Φ₀ _ _ hΦ _ c
  have hy : dualLatticeCoord b ⟨(), c⟩ ≠ 0 := by
    rw [dualLatticeCoord_eq]
    exact evalForm_ne_zero fun h => b.ne_zero c (Subtype.ext h)
  have hS : dualStdModelS K i ≠ 0 := by
    intro h
    have h' := IsFractionRing.injective (MvPolynomial Unit (MvPolynomial Unit (ProjField K i)))
      (dualStdModelField K i) (h.trans (map_zero _).symm)
    simp at h'
  refine transcendental_of_scale _ (mul_ne_zero ((map_ne_zero _).mpr hy) hS) fun n => ?_
  have ha : ((n : ProjField K i) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  have hΦfix : ∀ x : Φ₀, scale ha (algebraMap Φ₀ _ x) = algebraMap Φ₀ _ x := by
    intro x
    have hx : algebraMap Φ₀ (dualStdModelField K i) x ∈
        Subfield.closure (Set.range (dualStdModelPt b ∘ inrV (ι := dualBlocks T) (ι₂ := PBlk i))) :=
      hΦ ▸ RingHom.mem_fieldRange.mpr ⟨x, rfl⟩
    refine RingHom.eqOn_field_closure (g := RingHom.id _) ?_ hx
    rintro _ ⟨⟨u, j⟩, rfl⟩
    cases u
    exact scale_inr b ha j
  let σ : dualStdModelField K i →ₐ[Φ₀] dualStdModelField K i := { scale ha with commutes' := hΦfix }
  refine ⟨scale ha, fun y hyA => AlgHom.adjoin_le_equalizer σ (AlgHom.id Φ₀ _) ?_ hyA, ?_⟩
  · rintro _ ⟨t, rfl⟩
    change scale ha _ = _
    rw [map_div₀, scale_inl b ha, scale_inl b ha, mul_div_mul_left _ _ ((map_ne_zero _).mpr ha)]
    rfl
  · rw [scale_inl b ha]
    simp
end DualStdModelTransc
end GroundTheory.Heights₂.Heights
