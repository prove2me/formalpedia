-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLAux.contDiffOn_compat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:32.191522+00:00
-- url     : https://prove2.me/submissions/0563558a-f7ff-4f27-a12f-6b1c83327c5c

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero

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
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M.PLAux
theorem _root_.solution {A : FinHolAtlas e X} {ψ : OpenPartialHomeomorph X (Fin e → ℂ)}
    (hψ : IsCompatChart A ψ) {U : Set X} (hU : IsOpen U) {f : X → ℝ} (hf : A.SmoothOn U f) :
    ContDiffOn ℝ ∞ (f ∘ ψ.symm) (ψ.target ∩ ψ.symm ⁻¹' U) := by
  intro y hy
  refine ContDiffAt.contDiffWithinAt ?_
  obtain ⟨a, ha⟩ := A.cover (ψ.symm y)
  have h1 : ContDiffAt ℝ ∞ (f ∘ (A.chart a).symm) (A.chart a (ψ.symm y)) := by
    have hO' : IsOpen ((A.chart a).target ∩ (A.chart a).symm ⁻¹' U) :=
      (A.chart a).continuousOn_symm.isOpen_inter_preimage (A.chart a).open_target hU
    refine (hf a).contDiffAt (hO'.mem_nhds ⟨(A.chart a).map_source ha, ?_⟩)
    simpa [(A.chart a).left_inv ha] using hy.2
  have h2 : ContDiffAt ℝ ∞ (A.chart a ∘ ψ.symm) y :=
    ((hψ a).2 y ⟨hy.1, ha⟩).contDiffAt.restrict_scalars ℝ
  refine (h1.comp y h2).congr_of_eventuallyEq ?_
  have hN : ψ.target ∩ ψ.symm ⁻¹' (A.chart a).source ∈ 𝓝 y :=
    (ψ.continuousOn_symm.isOpen_inter_preimage ψ.open_target (A.chart a).open_source).mem_nhds
      ⟨hy.1, ha⟩
  filter_upwards [hN] with y' hy'
  simp [(A.chart a).left_inv hy'.2]
end ReciprocityTheory.AnForm.M.PLAux
