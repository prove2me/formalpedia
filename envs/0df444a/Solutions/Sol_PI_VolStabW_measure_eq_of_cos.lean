-- Prove2me | solution 1 for PI.VolStabW.measure_eq_of_cos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:13:43.616268+00:00
-- url     : https://prove2.me/submissions/326a943b-da8b-4392-a1f6-3b46fec118dc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_CosDens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_MeasureEqOfCos
import Theorems.Thm_PI_VolStabW_isOpen_thick
import Theorems.Thm_PI_VolStabW_measure_thick_eq
import Theorems.Thm_PI_VolStabW_iInter_thick

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open MeasureTheory Topology Set Filter
variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [MeasurableSpace X] [OpensMeasurableSpace X]
namespace PI.VolStabW
theorem _root_.solution (m1 m2 : Measure X) [IsFiniteMeasure m1]
    (Λ : ℕ → AddSubgroup X) (hΛo : ∀ n, IsOpen (Λ n : Set X)) (hanti : Antitone Λ)
    (hb : ∀ N ∈ 𝓝 (0 : X), ∃ n, (Λ n : Set X) ⊆ N)
    (h : ∀ n y, m1 {z | z - y ∈ Λ n} = m2 {z | z - y ∈ Λ n})
    (S : Set X) (hS : IsCompact S) (hSc : IsClosed S) : m1 S = m2 S := by
  have hA : Antitone fun n => thick S (Λ n) := by
    intro n k hnk
    rintro x ⟨s, hs, hx⟩
    exact ⟨s, hs, hanti hnk hx⟩
  have hm : ∀ n, NullMeasurableSet (thick S (Λ n)) m1 := fun n =>
    (isOpen_thick S _ (hΛo n)).measurableSet.nullMeasurableSet
  have hm2 : ∀ n, NullMeasurableSet (thick S (Λ n)) m2 := fun n =>
    (isOpen_thick S _ (hΛo n)).measurableSet.nullMeasurableSet
  have h0 := measure_thick_eq m1 m2 (Λ 0) (hΛo 0) (h 0) S hS
  rw [← iInter_thick S hSc Λ hb, hA.measure_iInter hm ⟨0, measure_ne_top _ _⟩,
    hA.measure_iInter hm2 ⟨0, h0 ▸ measure_ne_top _ _⟩]
  exact iInf_congr fun n => measure_thick_eq m1 m2 (Λ n) (hΛo n) (h n) S hS
end PI.VolStabW
