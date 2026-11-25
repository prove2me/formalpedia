-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupSec.symmetricMeasure_l2Norm_eq_resolutionL2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:57:19.910586+00:00
-- url     : https://prove2.me/submissions/26797090-96ef-415f-9ea0-ca1d691f345e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_SupGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ExtProof
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfRsmulRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_SupSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_PfSupSec_thetaSectionPointwiseNormSq_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupSec
open NumberField ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupSec
theorem _root_.solution (X : PT E) (s : (Fin 1 → Vsp X.dim) → ℂ) :
    X.l2 1 s = (toGT X).l2 1 (fun v => s (fun _ => v)) := by
  have hmp := MeasureTheory.volume_preserving_funUnique (Fin 1) (Vsp X.dim)
  have hfd : X.fd 1 =
      (MeasurableEquiv.funUnique (Fin 1) (Vsp X.dim)) ⁻¹' ZSpan.fundamentalDomain X.b := by
    ext v
    show (∀ k, v k ∈ ZSpan.fundamentalDomain X.b) ↔ v default ∈ ZSpan.fundamentalDomain X.b
    exact ⟨fun h => h _, fun h k => by rwa [Subsingleton.elim k default]⟩
  have hpt : ∀ v, X.ptN2 1 s v = (toGT X).ptN2 1 (fun u => s (fun _ => u))
      (MeasurableEquiv.funUnique (Fin 1) (Vsp X.dim) v) := fun v => thetaSectionPointwiseNormSq_eq X s v
  show (⨍ v in X.fd 1, X.ptN2 1 s v) =
    ⨍ v in ZSpan.fundamentalDomain X.b, (toGT X).ptN2 1 (fun u => s (fun _ => u)) v
  simp only [hpt]
  rw [hfd, MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq]
  erw [hmp.setIntegral_preimage_emb (MeasurableEquiv.measurableEmbedding _)
      ((toGT X).ptN2 1 (fun u => s (fun _ => u))) (ZSpan.fundamentalDomain X.b)]
  simp only [MeasureTheory.measureReal_def]
  erw [hmp.measure_preimage_equiv]
end ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupSec
