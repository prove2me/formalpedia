-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupSec.sec_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:55:37.298805+00:00
-- url     : https://prove2.me/submissions/3cde7829-5f0f-4491-a60a-88b7a82cf77b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_SupGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ExtProof
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfRsmulRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_SupSec

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
theorem _root_.solution (X : PT E) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) :
    (fun v : Vsp X.dim => s (fun _ => v)) ∈ (toGT X).Sec 1 := by
  obtain ⟨hd, hper⟩ := hs
  refine ⟨hd.comp (differentiable_pi.2 fun _ => differentiable_id), fun γ hγ v => ?_⟩
  have h := hper (fun _ => γ) (fun _ => hγ) (fun _ => v)
  simp only [HC, Fin.sum_univ_one, Fin.prod_univ_one, pow_one] at h
  exact h
end ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupSec
