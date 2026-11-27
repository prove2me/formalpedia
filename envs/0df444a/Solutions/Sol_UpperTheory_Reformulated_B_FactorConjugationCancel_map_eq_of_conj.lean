-- Prove2me | solution 1 for UpperTheory.Reformulated.B.FactorConjugationCancel.map_eq_of_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:32:54.95701+00:00
-- url     : https://prove2.me/submissions/48f0edf3-d9ed-4a52-b45d-7c23f92359ac

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FactorConjugationCancel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory
private theorem UpperTheory.Reformulated.B.FactorConjugationCancel.smul_cancel {G : Type} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [MeasurableSpace G]
    [BorelSpace G] (ν : Measure G) [ν.IsAddHaarMeasure] {a b : NNReal}
    (h : a • ν = b • ν) : a = b := by
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : G)
  have h0 : ν K ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hK0).ne'
  have h1 : ν K ≠ ⊤ := hK.measure_lt_top.ne
  have h2 : (a : ENNReal) * ν K = (b : ENNReal) * ν K := by
    have := congrArg (fun μ : Measure G => μ K) h
    simpa using this
  exact_mod_cast (ENNReal.mul_left_inj h0 h1).1 h2
private theorem UpperTheory.Reformulated.B.FactorConjugationCancel.exists_factor {G : Type} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (m : G ≃ₜ+ G) (ν : Measure G) [ν.IsAddHaarMeasure] :
    ∃ a : NNReal, Measure.map (⇑m : G → G) ν = a • ν := by
  haveI : (Measure.map (⇑m : G → G) ν).IsAddHaarMeasure := m.isAddHaarMeasure_map ν
  exact ⟨_, Measure.isAddLeftInvariant_eq_smul _ ν⟩
end

set_option autoImplicit false
open MeasureTheory
namespace UpperTheory.Reformulated.B.FactorConjugationCancel
theorem _root_.solution :
    ∀ {G : Type} [inst : AddCommGroup G] [inst_1 : TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [inst_5 : MeasurableSpace G]
    [BorelSpace G] (m s : G ≃ₜ+ G) (ν : MeasureTheory.Measure G) [ν.IsAddHaarMeasure] (c : NNReal),
    (∀ (x : G), (s : G → G) ((s : G → G) x) = x) →
      MeasureTheory.Measure.map (fun (x : G) ↦ (s : G → G) ((m : G → G) ((s : G → G) ((m : G → G) x)))) ν = (c * c) • ν →
        MeasureTheory.Measure.map (⇑m : G → G) ν = c • ν := by
  intro G _ _ _ _ _ _ _ m s ν _ c hs h
  obtain ⟨a, ha⟩ := UpperTheory.Reformulated.B.FactorConjugationCancel.exists_factor m ν
  obtain ⟨b, hb⟩ := UpperTheory.Reformulated.B.FactorConjugationCancel.exists_factor s ν
  have mm : Measurable (⇑m : G → G) := m.continuous.measurable
  have ms : Measurable (⇑s : G → G) := s.continuous.measurable
  have hm' : ∀ r : NNReal, Measure.map (⇑m : G → G) (r • ν) = (r * a) • ν := by
    intro r
    rw [Measure.map_smul, ha, smul_smul]
  have hs' : ∀ r : NNReal, Measure.map (⇑s : G → G) (r • ν) = (r * b) • ν := by
    intro r
    rw [Measure.map_smul, hb, smul_smul]
  have hbb : b * b = 1 := by
    apply UpperTheory.Reformulated.B.FactorConjugationCancel.smul_cancel ν
    rw [← hs', ← hb, Measure.map_map ms ms, one_smul]
    have : (⇑s ∘ ⇑s : G → G) = id := funext hs
    rw [this, Measure.map_id]
  have hcomp : (fun (x : G) ↦ (s : G → G) ((m : G → G) ((s : G → G) ((m : G → G) x))))
      = (⇑s : G → G) ∘ ((⇑m : G → G) ∘ ((⇑s : G → G) ∘ (⇑m : G → G))) := rfl
  rw [hcomp, ← Measure.map_map ms (mm.comp (ms.comp mm)), ← Measure.map_map mm (ms.comp mm),
    ← Measure.map_map ms mm, ha, hs', hm', hs'] at h
  have h2 := UpperTheory.Reformulated.B.FactorConjugationCancel.smul_cancel ν h
  have h3 : a * a = c * c := by
    rw [← h2]
    calc a * a = a * a * (b * b) := by rw [hbb, mul_one]
      _ = _ := by ring
  have h5 : (a : ℝ) * a = (c : ℝ) * c := by rw [← NNReal.coe_mul, ← NNReal.coe_mul, h3]
  have h4 : a = c := NNReal.eq ((mul_self_inj_of_nonneg a.coe_nonneg c.coe_nonneg).1 h5)
  rw [ha, h4]
end UpperTheory.Reformulated.B.FactorConjugationCancel
