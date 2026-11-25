-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_birational_latticeCoord_528f8b6c0df6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:39:03.31567+00:00
-- url     : https://prove2.me/submissions/68f6ddcf-87c9-49e8-9f6c-f22b7a806adb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelB
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_mem_quotField_f112b4739b83
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_isMultiHomog_iff_98f435e2c05f

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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.LatticeModel
variable {K : Type} [Field K] [NumberField K] {m N : ℕ} {L : Submodule (𝓞 K) (Fin m → K)}
variable {φ : Fin (N + 1) → Fin m → K}
variable {r : ℕ} {L : Submodule (𝓞 K) (Fin (r + 1) → K)} {φ : Fin (N + 1) → Fin (r + 1) → K}
namespace GroundTheory.Heights₂.Heights.LatticeModel
theorem _root_.solution (hL : L.FG) (hφ : IsDualBasis L φ) :
    Geo.Birational (ι := blockIdx fun _ : Unit ↦ N) (latticeCoord φ) := by
  intro s
  obtain ⟨d, g, h, hg, hh, hne, he⟩ := mem_quotField hL hφ s
  refine ⟨fun _ ↦ d, g, h, (isMultiHomog_iff g _).mpr hg, (isMultiHomog_iff h _).mpr hh, ?_, ?_⟩
  · simpa only [aeval_def, algebraMap_int_eq, yEval, coe_eval₂Hom] using hne
  · simpa only [aeval_def, algebraMap_int_eq, yEval, coe_eval₂Hom] using he
end GroundTheory.Heights₂.Heights.LatticeModel
