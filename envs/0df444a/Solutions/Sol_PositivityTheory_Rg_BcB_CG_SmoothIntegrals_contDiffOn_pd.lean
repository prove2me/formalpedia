-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.CG.SmoothIntegrals.contDiffOn_pd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:13:12.961475+00:00
-- url     : https://prove2.me/submissions/bdef3bc7-ee9b-44c3-bccb-5cf6f08cdb8b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_HeckeFubiniCompatibility_PSmoothA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric Set
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.CG.SmoothIntegrals
variable {X M T : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup M] [NormedSpace ℝ M]
  [TopologicalSpace T] [T2Space T] [MeasurableSpace T] [OpensMeasurableSpace T]
omit [FiniteDimensional ℝ X]
namespace PositivityTheory.Rg.BcB.CG.SmoothIntegrals
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Q : X × M → V} {U : Set X} {W : Set M}
    (hU : IsOpen U) (hW : IsOpen W) (hQ : ContDiffOn ℝ ∞ Q (U ×ˢ W)) : ContDiffOn ℝ ∞ (pd Q) (U ×ˢ W) := by
  intro q hq
  have hQa : ContDiffAt ℝ ∞ Q q := hQ.contDiffAt ((hU.prod hW).mem_nhds hq)
  refine ContDiffAt.contDiffWithinAt ?_
  refine ContDiffAt.fderiv (f := fun (r : X × M) (x : X) => Q (x, r.2)) (g := fun r => r.1) ?_ contDiffAt_fst
    ENat.coe_top_add_one.le
  have e : Function.uncurry (fun (r : X × M) (x : X) => Q (x, r.2)) = Q ∘ fun z : (X × M) × X => (z.2, z.1.2) := rfl
  rw [e]
  exact ContDiffAt.comp _ hQa (contDiffAt_snd.prodMk (contDiffAt_snd.comp _ contDiffAt_fst))
end PositivityTheory.Rg.BcB.CG.SmoothIntegrals
