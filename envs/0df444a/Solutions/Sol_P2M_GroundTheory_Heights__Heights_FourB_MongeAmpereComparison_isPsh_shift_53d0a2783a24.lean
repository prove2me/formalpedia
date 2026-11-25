-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_isPsh_shift_53d0a2783a24
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:55:03.125619+00:00
-- url     : https://prove2.me/submissions/2b90d52e-0ccb-4b86-b547-8842d5cd99ed

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PMongeAmpereComparison
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_hasDerivAt_cutoff_d9e21ca0833b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_contDiff_cutoff_231a9780e2e3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_levi_add_const_f7132524e540
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_levi_comp_real_46101a89c4a1
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_potSmoothAt
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
import Theorems.Thm_ReciprocityTheory_AnForm_levi_add_smul
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.FourB.MongeAmpereComparison
namespace GroundTheory.Heights₂.Heights.FourB.MongeAmpereComparison
theorem _root_.solution {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (P : LocPot X) (a b : X → ℝ) (k : ℝ) (hP : IsPotential A P) (ha : A.Smooth a)
    (hb : A.Smooth b) (hPa : IsPsh A (P + LocPot.ofFun a)) (hPb : IsPsh A (P + LocPot.ofFun b)) :
    IsPsh A ((P + LocPot.ofFun a) + LocPot.ofFun (fun x => cutoff (b x - a x + k))) := by
  intro x j y hy w
  have hyP : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x := ⟨hy.1, hy.2.1.1⟩
  have hT : (A.chart j).target ∈ 𝓝 y := (A.chart j).open_target.mem_nhds hy.1
  have sm : ∀ f : X → ℝ, A.Smooth f → ContDiffAt ℝ 2 (f ∘ (A.chart j).symm) y := fun f hf => by
    have := hf j
    rw [Set.preimage_univ, Set.inter_univ] at this
    exact (this.contDiffAt hT).of_le (WithTop.coe_le_coe.2 le_top)
  have hφ := potSmoothAt A P hP x j hyP
  have hα := sm a ha
  have hβ := sm b hb
  have ht : ContDiffAt ℝ 2 (fun z => b ((A.chart j).symm z) - a ((A.chart j).symm z) + k) y :=
    (hβ.sub hα).add contDiffAt_const
  have hsT : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition (b ((A.chart j).symm y) - a ((A.chart j).symm y) + k))
      (b ((A.chart j).symm y) - a ((A.chart j).symm y) + k) :=
    ((Real.smoothTransition.contDiffAt (n := 1)).differentiableAt (by simp)).hasDerivAt
  have hc : ContDiffAt ℝ 2 (cutoff ∘ fun z => b ((A.chart j).symm z) - a ((A.chart j).symm z) + k) y :=
    ((contDiff_cutoff.of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt).comp y ht
  have hL1 : ∀ f : X → ℝ, A.Smooth f →
      levi (fun z => P.φ x ((A.chart j).symm z) + f ((A.chart j).symm z)) y w =
        levi (P.φ x ∘ (A.chart j).symm) y w + levi (f ∘ (A.chart j).symm) y w := fun f hf => by
    have := levi_add_smul (f := P.φ x ∘ (A.chart j).symm) (g := f ∘ (A.chart j).symm) 1 hφ
      (sm f hf) w
    simpa using this
  have hPa0 : 0 ≤ levi (P.φ x ∘ (A.chart j).symm) y w + levi (a ∘ (A.chart j).symm) y w := by
    rw [← hL1 a ha]
    exact hPa x j y ⟨hy.1, hy.2.1⟩ w
  have hPb0 : 0 ≤ levi (P.φ x ∘ (A.chart j).symm) y w + levi (b ∘ (A.chart j).symm) y w := by
    rw [← hL1 b hb]
    exact hPb x j y ⟨hy.1, hy.2.1⟩ w
  have hLt : levi (fun z => b ((A.chart j).symm z) - a ((A.chart j).symm z) + k) y w =
      levi (b ∘ (A.chart j).symm) y w - levi (a ∘ (A.chart j).symm) y w := by
    rw [levi_add_const (fun z => b ((A.chart j).symm z) - a ((A.chart j).symm z)) k]
    have := levi_add_smul (f := b ∘ (A.chart j).symm) (g := a ∘ (A.chart j).symm) (-1) hβ hα w
    have e : (fun z => b ((A.chart j).symm z) - a ((A.chart j).symm z)) =
        fun z => (b ∘ (A.chart j).symm) z + -1 * (a ∘ (A.chart j).symm) z := by
      funext z; simp only [Function.comp_apply]; ring
    rw [e, this]
    ring
  have hF : ((P + LocPot.ofFun a) + LocPot.ofFun (fun x => cutoff (b x - a x + k))).φ x ∘
      (A.chart j).symm = fun z => (P.φ x ((A.chart j).symm z) + a ((A.chart j).symm z)) +
        1 * (cutoff ∘ fun z => b ((A.chart j).symm z) - a ((A.chart j).symm z) + k) z := by
    funext z
    simp only [Function.comp_apply, one_mul]
    rfl
  rw [hF, levi_add_smul (f := fun z => P.φ x ((A.chart j).symm z) + a ((A.chart j).symm z)) 1
    (hφ.add hα) hc w, hL1 a ha, levi_comp_real hasDerivAt_cutoff hsT ht w, hLt]
  have hs0 := Real.smoothTransition.nonneg (b ((A.chart j).symm y) - a ((A.chart j).symm y) + k)
  have hs1 := Real.smoothTransition.le_one (b ((A.chart j).symm y) - a ((A.chart j).symm y) + k)
  have hd : 0 ≤ deriv Real.smoothTransition (b ((A.chart j).symm y) - a ((A.chart j).symm y) + k) :=
    Real.smoothTransition.monotone.deriv_nonneg
  have hq : 0 ≤ (fderiv ℝ (fun z => b ((A.chart j).symm z) - a ((A.chart j).symm z) + k) y w) ^ 2 +
      (fderiv ℝ (fun z => b ((A.chart j).symm z) - a ((A.chart j).symm z) + k) y
        (Complex.I • w)) ^ 2 := by positivity
  nlinarith [mul_nonneg (sub_nonneg.2 hs1) hPa0, mul_nonneg hs0 hPb0, mul_nonneg hd hq]
end GroundTheory.Heights₂.Heights.FourB.MongeAmpereComparison
