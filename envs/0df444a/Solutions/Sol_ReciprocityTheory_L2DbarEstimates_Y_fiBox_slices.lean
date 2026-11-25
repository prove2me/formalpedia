-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.fiBox_slices
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:25:39.847193+00:00
-- url     : https://prove2.me/submissions/0a092075-6308-4bbc-8cd0-83d78a843a1f

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourIndep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Set
open scoped Interval
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} (i : Fin (n + 1)) (Φ : (Fin (n + 1) → ℝ) → ℂ) (hΦ : Continuous Φ) :
    ∫ x in fiBox (n + 1), Φ x = ∫ y in fiBox n, ∫ t in Set.Ioc (0 : ℝ) 1, Φ (i.insertNth t y) := by
  set e : ℝ × (Fin n → ℝ) ≃ᵐ (Fin (n + 1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i).symm
  have hem : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm _
  have hpre : e ⁻¹' fiBox (n + 1) = Set.Ioc (0 : ℝ) 1 ×ˢ fiBox n := by
    ext ⟨t, y⟩
    simp [e, fiBox, Set.mem_pi, Fin.forall_iff_succAbove i]
  have hint : IntegrableOn Φ (fiBox (n + 1)) := by
    have hc : IsCompact (Set.univ.pi (fun _ : Fin (n + 1) => Set.Icc (0 : ℝ) 1)) :=
      isCompact_univ_pi (fun _ => isCompact_Icc)
    refine (hΦ.continuousOn.integrableOn_compact hc).mono_set ?_
    exact Set.pi_mono (fun _ _ => Set.Ioc_subset_Icc_self)
  have hint' : IntegrableOn (Φ ∘ e) (Set.Ioc (0 : ℝ) 1 ×ˢ fiBox n) (volume.prod volume) := by
    rw [← hpre, ← Measure.volume_eq_prod]
    exact (hem.integrableOn_comp_preimage e.measurableEmbedding).2 hint
  rw [← hem.map_eq, setIntegral_map_equiv, hpre, Measure.volume_eq_prod]
  rw [IntegrableOn, ← Measure.prod_restrict] at hint'
  rw [← Measure.prod_restrict, integral_prod_symm (fun z => Φ (e z)) hint']
  simp [e]
  rfl
end ReciprocityTheory.L2DbarEstimates.Y
