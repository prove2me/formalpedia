-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GoodChartDim_segreCone_smul_97061b6be25b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:52:53.307391+00:00
-- url     : https://prove2.me/submissions/10c89f62-7085-4e1c-a755-3bab34c334d3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StGoodChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StConeVanishingHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StConeSliceIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartDehomogPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PGoodChartZeroSet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartHomogenise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartDehomog
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PGoodChartDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodChartZeroSet_exists_segre_smul_bfffda87fde7
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
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
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar mcPts segre)
open GroundTheory.Heights₂.Heights.GoodChartDim
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.GoodChartDim
theorem _root_.solution {P : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) :
    ∀ c ∈ segreCone P σ, ∀ a : ℂ, a ≠ 0 → a • c ∈ segreCone P σ := by
  rintro _ ⟨z, hz, rfl⟩ a ha
  obtain ⟨z', hz', hseg⟩ := GoodChartZeroSet.exists_segre_smul P hP.2.1.2.1 hz ha
    (fun h => absurd hP.1 (not_nonempty_iff.2 h))
  exact ⟨z', hz', funext fun b => by simp [hseg]⟩
end GroundTheory.Heights₂.Heights.GoodChartDim
