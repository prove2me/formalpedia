-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLAux.contDiff_mul_of_tsupport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:03:29.444372+00:00
-- url     : https://prove2.me/submissions/4d761b08-83df-4d37-86b6-e44fc3602544

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
theorem _root_.solution {n : ℕ} {ρ f : (Fin n → ℂ) → ℝ} {U : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hρ : ContDiff ℝ ∞ ρ) (hρU : tsupport ρ ⊆ U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiff ℝ ∞ (fun y => ρ y * f y) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ U
  · exact hρ.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds hy))
  · have hyρ : y ∉ tsupport ρ := fun h => hy (hρU h)
    have h0 : (fun z => ρ z * f z) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hyρ] with z hz
      simp [hz]
    exact contDiffAt_const.congr_of_eventuallyEq h0
end ReciprocityTheory.AnForm.M.PLAux
