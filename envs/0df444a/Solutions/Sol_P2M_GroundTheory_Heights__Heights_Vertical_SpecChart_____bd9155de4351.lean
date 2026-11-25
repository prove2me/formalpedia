-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_____bd9155de4351
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:41:58.152933+00:00
-- url     : https://prove2.me/submissions/97723e1b-fa61-49d9-976f-b3c2a71954be

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChartDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartIso
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart___X_30d1d988806a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart___C_90452924d03a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_baseToBn_toBase_2f2e4d6deddf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart___C_e65327d6784a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart___val_2c54f47722fa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_toSecB_C_52fd5bf567a3


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.Vertical.SpecChart
variable {K : Type} [Field K] [NumberField K] {n : ℕ} (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
  (j : Fin n)
variable (W : Ideal (MvPolynomial (Fin n) (𝓞 K)))
variable {I W}
variable {v : HeightOneSpectrum (𝓞 K)}
variable (𝔫 : Ideal (SecB e I v)) [𝔫.IsPrime]
variable {e j 𝔫}
namespace GroundTheory.Heights₂.Heights.Vertical.SpecChart
theorem _root_.solution (hj : toSecB e I v (X j) ∉ 𝔫) :
    (Φ hj).comp (σ e I j) = (algebraMap (SecB e I v) (Localization.AtPrime 𝔫)).comp
      ((algebraMap (ParDVR e n v) (SecB e I v)).comp (algebraMap _ (ParDVR e n v))) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply, σ_C, Φ_C, baseToBn_toBase, toSecB_C]
  · intro p
    simp only [RingHom.comp_apply, σ_X, Φ_val, parB, parY]
end GroundTheory.Heights₂.Heights.Vertical.SpecChart
