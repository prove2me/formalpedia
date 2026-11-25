-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_KaehlerBound_proof_2363d5ba854f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:58:25.122933+00:00
-- url     : https://prove2.me/submissions/c96d4d19-feef-4794-8f29-69fdabb41475

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_KaehlerBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_PKaehlerBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_two_le_smooth_kb_fd6647adc872
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_regChartData_isCompact_univ_e3182ebcff2c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_levi_abs_le_global_f507302d4074
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshMean_isOpen_inter_preimage
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_isPotentialRsmul
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
import Theorems.Thm_ReciprocityTheory_AnForm_continuousOn_levi
import Theorems.Thm_ReciprocityTheory_AnForm_levi_add_smul
import Theorems.Thm_ReciprocityTheory_AnForm_levi_comp
import Theorems.Thm_ReciprocityTheory_AnForm_levi_congr
import Theorems.Thm_ReciprocityTheory_AnForm_levi_re_analytic
import Theorems.Thm_ReciprocityTheory_AnForm_levi_smul_dir
import Theorems.Thm_ReciprocityTheory_AnForm_levi_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open Filter Topology
open scoped ContDiff
open ReciprocityTheory.AnForm (levi levi_congr levi_comp levi_zero levi_smul_dir levi_add_smul
  levi_re_analytic continuousOn_levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot chartIdx)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)
noncomputable section
variable {D : ℕ} {X : Type} [TopologicalSpace X]
namespace GroundTheory.Heights₂.Heights.AnalyticLimit
namespace KaehlerBound
theorem _root_.solution : KaehlerBound.Statement := by
  intro D X _ A R
  obtain ⟨M, hM0, hM⟩ := levi_abs_le_global A (regChartData_isCompact_univ R) R.θ R.om R.θ_pot
    R.om_pot R.om_pos
  have hK : (0 : ℝ) < M + 1 := by linarith
  have hsm : ∀ P : LocPot X, IsPotential A P → ∀ x k,
      ∀ y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' P.U x,
        ContDiffAt ℝ 2 (P.φ x ∘ (A.chart k).symm) y := fun P hP x k y hy =>
    ((hP.1 x k).of_le two_le_smooth_kb).contDiffAt
      (((A.chart k).continuousOn_symm.isOpen_inter_preimage (A.chart k).open_target
        (P.isOpen_U x)).mem_nhds hy)
  have hsmul : ∀ (P : LocPot X) (a : ℝ) x k y, ContDiffAt ℝ 2 (P.φ x ∘ (A.chart k).symm) y →
      ∀ w, levi ((P.rsmul a).φ x ∘ (A.chart k).symm) y w =
        a * levi (P.φ x ∘ (A.chart k).symm) y w := by
    intro P a x k y hy w
    have h := levi_add_smul a (contDiffAt_const (c := (0 : ℝ))) hy w
    have he : (P.rsmul a).φ x ∘ (A.chart k).symm =
        fun z => (0 : ℝ) + a * (P.φ x ∘ (A.chart k).symm) z := by
      funext z
      simp [LocPot.rsmul]
    rw [he, h, levi_const, zero_add]
  have key : ∀ x k, ∀ y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' (R.θ.U x ∩ R.om.U x),
      ∀ w : Fin D → ℂ,
        levi ((thetaOmega R).φ x ∘ (A.chart k).symm) y w =
            levi (R.θ.φ x ∘ (A.chart k).symm) y w + levi (R.om.φ x ∘ (A.chart k).symm) y w ∧
          levi ((R.om.rsmul (M + 1)).φ x ∘ (A.chart k).symm) y w =
            (M + 1) * levi (R.om.φ x ∘ (A.chart k).symm) y w ∧
          |levi (R.θ.φ x ∘ (A.chart k).symm) y w| ≤
            M * levi (R.om.φ x ∘ (A.chart k).symm) y w ∧
          0 ≤ levi (R.om.φ x ∘ (A.chart k).symm) y w := by
    intro x k y hy w
    have hθs := hsm R.θ R.θ_pot x k y ⟨hy.1, hy.2.1⟩
    have homs := hsm R.om R.om_pot x k y ⟨hy.1, hy.2.2⟩
    refine ⟨?_, hsmul R.om (M + 1) x k y homs w, hM x k y hy w, ?_⟩
    · have he : (thetaOmega R).φ x ∘ (A.chart k).symm = fun z =>
          (R.θ.φ x ∘ (A.chart k).symm) z + 1 * (R.om.φ x ∘ (A.chart k).symm) z := by
        funext z
        show R.θ.φ x _ + R.om.φ x _ = _
        simp
      rw [he, levi_add_smul 1 hθs homs w, one_mul]
    · rcases eq_or_ne w 0 with h0 | h0
      · rw [h0, levi_zero]
      · exact (R.om_pos x k y ⟨hy.1, hy.2.2⟩ w h0).le
  refine ⟨⟨R.om.rsmul (M + 1), ReciprocityTheory.AnForm.M.isPotentialRsmul A (M + 1) R.om R.om_pot,
    fun x k y hy w hw => ?_⟩, ?_, ?_⟩
  · rw [hsmul R.om (M + 1) x k y (hsm R.om R.om_pot x k y hy) w]
    exact mul_pos hK (R.om_pos x k y hy w hw)
  · intro x k y hy w
    have hy' : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' (R.θ.U x ∩ R.om.U x) :=
      ⟨hy.1, hy.2.1.2.1, hy.2.1.2.2⟩
    obtain ⟨h1, h2, h3, h4⟩ := key x k y hy' w
    show 1 * levi ((thetaOmega R).φ x ∘ (A.chart k).symm) y w ≤
      1 * levi ((R.om.rsmul (M + 1)).φ x ∘ (A.chart k).symm) y w
    rw [h1, h2]
    have := abs_le.mp h3
    nlinarith
  · intro x k y hy w
    have hy' : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' (R.θ.U x ∩ R.om.U x) :=
      ⟨hy.1, hy.2.2.1, hy.2.2.2⟩
    obtain ⟨h1, h2, h3, h4⟩ := key x k y hy' w
    show -1 * levi ((R.om.rsmul (M + 1)).φ x ∘ (A.chart k).symm) y w ≤
      1 * levi ((thetaOmega R).φ x ∘ (A.chart k).symm) y w
    rw [h1, h2]
    have := abs_le.mp h3
    nlinarith
end KaehlerBound
end GroundTheory.Heights₂.Heights.AnalyticLimit
