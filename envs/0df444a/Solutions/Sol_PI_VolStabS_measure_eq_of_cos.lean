-- Prove2me | solution 1 for PI.VolStabS.measure_eq_of_cos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:58:25.395839+00:00
-- url     : https://prove2.me/submissions/2ded8b8b-1784-4047-891d-9a60b22aeacc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_CosDens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_MeasureEqOfCos
import Theorems.Thm_PI_VolStabS_isOpen_thick
import Theorems.Thm_PI_VolStabS_measure_thick_eq
import Theorems.Thm_PI_VolStabS_iInter_thick

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS
open MeasureTheory Topology Set Filter
variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [MeasurableSpace X] [OpensMeasurableSpace X]
namespace PI.VolStabS
theorem _root_.solution (m1 m2 : Measure X) [IsFiniteMeasure m1]
    (Λ : ℕ → AddSubgroup X) (hΛo : ∀ n, IsOpen (Λ n : Set X)) (hanti : Antitone Λ)
    (hb : ∀ N ∈ 𝓝 (0 : X), ∃ n, (Λ n : Set X) ⊆ N)
    (h : ∀ n y, m1 {z | z - y ∈ Λ n} = m2 {z | z - y ∈ Λ n})
    (S : Set X) (hS : IsCompact S) (hSc : IsClosed S) : m1 S = m2 S := by
  have hmono : Antitone fun n => thick S (Λ n) := by
    intro a c hac x hx
    obtain ⟨s, hs, hxs⟩ := hx
    exact ⟨s, hs, hanti hac hxs⟩
  have hnull : ∀ (μ : Measure X) n, NullMeasurableSet (thick S (Λ n)) μ := fun μ n =>
    (isOpen_thick S (Λ n) (hΛo n)).measurableSet.nullMeasurableSet
  have heq : ∀ n, m1 (thick S (Λ n)) = m2 (thick S (Λ n)) := fun n =>
    measure_thick_eq m1 m2 (Λ n) (hΛo n) (h n) S hS
  rw [← iInter_thick S hSc Λ hb, hmono.measure_iInter (hnull m1) ⟨0, measure_ne_top _ _⟩,
    hmono.measure_iInter (hnull m2) ⟨0, by rw [← heq 0]; exact measure_ne_top _ _⟩]
  simp only [heq]
end PI.VolStabS
