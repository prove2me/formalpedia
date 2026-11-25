-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.kernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:01:08.333674+00:00
-- url     : https://prove2.me/submissions/65566d4f-0beb-413c-bd9b-5a39aca6f973

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ExistsDensity
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplexFourier
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_IntegrableConjPowGaussian
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_nm_pos
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_ae_unit
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_integral_scale
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_integrable_scale
import Theorems.Thm_P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf



set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped ComplexConjugate
variable {ι : Type} [Fintype ι]
namespace PositivityTheory.ThKG.Loc.Bump
theorem _root_.solution {a j : (ι → ℂ) → ℂ} (ha : AEStronglyMeasurable a volume) (hj : Integrable j) (hjm : Measurable j) {s : (ι → ℂ) → ι → ℂ}
    (hs : Measurable s) (hsU : ∀ x, (∀ w, x w ≠ 0) → ∀ w, s x w ≠ 0) (hi : Integrable fun x => a x * ((nm (s x) : ℝ) : ℂ)⁻¹) :
    Integrable (fun q : (ι → ℂ) × (ι → ℂ) => a q.1 * j (s q.1 * q.2)) (volume.prod volume) ∧
      ∫ x, ∫ y, a x * j (s x * y) = (∫ x, a x * ((nm (s x) : ℝ) : ℂ)⁻¹) * ∫ y, j y := by
  constructor
  · have hm : AEStronglyMeasurable (fun q : (ι → ℂ) × (ι → ℂ) => a q.1 * j (s q.1 * q.2)) (volume.prod volume) :=
      ha.comp_fst.mul (hjm.comp ((hs.comp measurable_fst).mul measurable_snd)).aestronglyMeasurable
    refine (integrable_prod_iff hm).2 ⟨?_, ?_⟩
    · filter_upwards [ae_unit] with x hx using (integrable_scale (hsU x hx) hj).const_mul _
    · refine (hi.norm.mul_const (∫ y, ‖j y‖)).congr ?_
      filter_upwards [ae_unit] with x hx
      simp only [norm_mul]
      rw [integral_const_mul, integral_scale (hsU x hx) (g := fun y => ‖j y‖) hj.1.norm, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg (nm_pos (hsU x hx)).le, smul_eq_mul, mul_assoc]
  · rw [← integral_mul_const]
    refine integral_congr_ae ?_
    filter_upwards [ae_unit] with x hx
    rw [integral_const_mul, integral_scale (hsU x hx) hj.1, Complex.real_smul, mul_assoc]
    push_cast; rfl
end PositivityTheory.ThKG.Loc.Bump
