-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fn_sub_closure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:54:19.540918+00:00
-- url     : https://prove2.me/submissions/d126c89e-4085-4c7b-ba7c-9592d1c82d2d

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatNullB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_G_ne_iff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fn_dense


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Set
open scoped ContDiff ENNReal
noncomputable section
universe u
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) (i : ι) {O : Set (V n)}
    (hO : IsOpen O) (hOt : O ⊆ (A.chart i).target) :
    O ⊆ closure (O ∩ {u | fnG A w0 s De i u ≠ 0}) := by
  intro u hu
  rw [mem_closure_iff]
  intro W hW huW
  have hWO : IsOpen ((A.chart i).source ∩ (A.chart i) ⁻¹' (W ∩ O)) :=
    (A.chart i).continuousOn.isOpen_inter_preimage (A.chart i).open_source (hW.inter hO)
  have hut : u ∈ (A.chart i).target := hOt hu
  obtain ⟨y, ⟨hys, hyWO⟩, hyM⟩ := (fn_dense A hD hF).inter_open_nonempty _ hWO
    ⟨(A.chart i).symm u, (A.chart i).map_target hut, by
      rw [Set.mem_preimage, (A.chart i).right_inv hut]; exact ⟨huW, hu⟩⟩
  refine ⟨(A.chart i) y, hyWO.1, hyWO.2, ?_⟩
  show fnG A w0 s De i ((A.chart i) y) ≠ 0
  rw [fn_G_ne_iff A hD ((A.chart i).map_source hys), (A.chart i).left_inv hys]
  exact hyM
end ReciprocityTheory.L2DbarEstimates.Y
