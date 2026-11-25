-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLAux.analyticAt_compat_fun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:03:25.420263+00:00
-- url     : https://prove2.me/submissions/26c86b6b-5ff1-4056-828b-561e96bcc37a

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffHypInclAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffMulOfTsupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.M.PLAux
open MeasureTheory FinHolAtlas Filter Topology
open ReciprocityTheory.AnForm.A (hypInclAt densHypAt)
open scoped ContDiff Manifold
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
omit [T2Space X] [CompactSpace X]
namespace ReciprocityTheory.AnForm.M.PLAux
theorem _root_.solution {A : FinHolAtlas e X} {ψ : OpenPartialHomeomorph X (Fin e → ℂ)}
    (hψ : IsCompatChart A ψ) {U : Set X} {g : X → ℂ} (hg : A.HoloOn U g) {y : Fin e → ℂ}
    (hy : y ∈ ψ.target) (hyU : ψ.symm y ∈ U) : AnalyticAt ℂ (g ∘ ψ.symm) y := by
  obtain ⟨j, hj⟩ : ∃ j, ψ.symm y ∈ (A.chart j).source := A.cover (ψ.symm y)
  have h1 : AnalyticAt ℂ (⇑(A.chart j) ∘ ⇑ψ.symm) y := (hψ j).2 y ⟨hy, hj⟩
  have h2 : AnalyticAt ℂ (g ∘ ⇑(A.chart j).symm) ((⇑(A.chart j) ∘ ⇑ψ.symm) y) :=
    hg j _ ⟨(A.chart j).map_source hj, by simpa [Function.comp, (A.chart j).left_inv hj] using hyU⟩
  refine (h2.comp h1).congr ?_
  filter_upwards [ψ.continuousAt_symm hy ((A.chart j).open_source.mem_nhds hj)] with z hz
  simp [Function.comp, (A.chart j).left_inv hz]
end ReciprocityTheory.AnForm.M.PLAux
