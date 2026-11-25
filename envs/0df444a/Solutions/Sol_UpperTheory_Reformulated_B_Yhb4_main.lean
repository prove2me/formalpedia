-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Yhb4.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:06:41.628987+00:00
-- url     : https://prove2.me/submissions/b5c3af60-2c3f-487a-bec8-b732b6b73e29

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmulNn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace MulEquivHaarCharEqOfProjection
open MeasureTheory
private lemma smul_nn {α : Type*} [MeasurableSpace α] (c : NNReal) (μ : Measure α) (s : Set α) :
    (c • μ) s = (c : ENNReal) * μ s := by
  rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
end MulEquivHaarCharEqOfProjection
end

set_option autoImplicit false

open MeasureTheory MeasureTheory.Measure
namespace UpperTheory.Reformulated.B.Yhb4
theorem _root_.solution :
    ∀ {H N : Type} [inst : Group H] [inst_1 : TopologicalSpace H] [inst_2 : IsTopologicalGroup H]
      [inst_3 : LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [inst_6 : MeasurableSpace H]
      [inst_7 : BorelSpace H] [inst_8 : Group N] [inst_9 : TopologicalSpace N] [inst_10 : IsTopologicalGroup N]
      [inst_11 : LocallyCompactSpace N] [SecondCountableTopology N] [T2Space N] [inst_14 : MeasurableSpace N]
      [inst_15 : BorelSpace N] (ι : N →* H),
      Continuous (⇑ι : N → H) →
        ∀ (π : H → N),
          Continuous π →
            (∀ (x : N) (p : H), π ((ι : N → H) x * p) = x * π p) →
              ∀ (φ : H ≃ₜ* H) (ψ : N ≃ₜ* N),
                (∀ (p : H), π ((φ : H → H) p) = (ψ : N → N) (π p)) →
                  (∀ (p : H), ((ι : N → H) (π ((φ : H → H) p)))⁻¹ * (φ : H → H) p = ((ι : N → H) (π p))⁻¹ * p) →
                    MeasureTheory.mulEquivHaarChar φ = MeasureTheory.mulEquivHaarChar ψ := by
  intro H N _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι hι π hπ hπι φ ψ hφψ hσ
  classical
  let σ : H → H := fun p => (ι (π p))⁻¹ * p
  have hσc : Continuous σ := ((hι.comp hπ).inv).mul continuous_id
  have hsplit : ∀ p, ι (π p) * σ p = p := by intro p; simp [σ]
  have hσmul : ∀ x p, σ (ι x * p) = σ p := by
    intro x p; simp [σ, hπι, mul_assoc]
  have hσφ : ∀ p, σ (φ p) = σ p := fun p => hσ p
  obtain ⟨C, hCc, hCn⟩ := exists_compact_mem_nhds (σ 1)
  let μH : Measure H := Measure.haar
  let μN : Measure N := Measure.haar
  let m : Measure N := Measure.map π (μH.restrict (σ ⁻¹' C))
  have hσC : MeasurableSet (σ ⁻¹' C) := (hCc.isClosed.preimage hσc).measurableSet
  have hmA : ∀ A, MeasurableSet A → m A = μH (π ⁻¹' A ∩ σ ⁻¹' C) := by
    intro A hA
    rw [Measure.map_apply hπ.measurable hA, Measure.restrict_apply (hπ.measurable hA)]
  have hinv : m.IsMulLeftInvariant := by
    refine ⟨fun x => ?_⟩
    ext A hA
    rw [Measure.map_apply (measurable_const_mul x) hA, hmA _ hA, hmA _ ((measurable_const_mul x) hA)]
    have : π ⁻¹' ((fun y => x * y) ⁻¹' A) ∩ σ ⁻¹' C
        = (fun p => ι x * p) ⁻¹' (π ⁻¹' A ∩ σ ⁻¹' C) := by
      ext p; simp [hπι, hσmul]
    rw [this, measure_preimage_mul]
  have hfin : IsFiniteMeasureOnCompacts m := by
    refine ⟨fun K hK => ?_⟩
    rw [hmA _ hK.isClosed.measurableSet]
    have hcomp : IsCompact ((fun q : N × H => ι q.1 * q.2) '' (K ×ˢ C)) :=
      (hK.prod hCc).image ((hι.comp continuous_fst).mul continuous_snd)
    refine lt_of_le_of_lt (measure_mono ?_) hcomp.measure_lt_top
    rintro p ⟨hp1, hp2⟩
    exact ⟨(π p, σ p), ⟨hp1, hp2⟩, hsplit p⟩
  have hc : m = haarScalarFactor m μN • μN := isMulLeftInvariant_eq_smul m μN
  set c := haarScalarFactor m μN with hcdef
  have hmuniv : 0 < m Set.univ := by
    rw [hmA _ MeasurableSet.univ, Set.preimage_univ, Set.univ_inter]
    have h1 : σ ⁻¹' C ∈ nhds (1 : H) := hσc.continuousAt.preimage_mem_nhds hCn
    exact measure_pos_of_nonempty_interior μH ⟨1, mem_interior_iff_mem_nhds.2 h1⟩
  have hc0 : (c : ENNReal) ≠ 0 := by
    intro h0
    rw [hc, MulEquivHaarCharEqOfProjection.smul_nn, h0, zero_mul] at hmuniv
    exact lt_irrefl _ hmuniv
  obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds (1 : N)
  let A : Set N := ψ.symm ⁻¹' K
  have hAm : MeasurableSet A := (hKc.isClosed.preimage ψ.symm.continuous).measurableSet
  have hApre : ψ ⁻¹' A = K := by ext x; simp [A]
  have hK0 : μN K ≠ 0 :=
    (measure_pos_of_nonempty_interior μN ⟨1, mem_interior_iff_mem_nhds.2 hKn⟩).ne'
  have hKt : μN K ≠ ⊤ := hKc.measure_lt_top.ne

  have e1 := mulEquivHaarChar_smul_preimage μH (X := π ⁻¹' A ∩ σ ⁻¹' C) φ
  have hpre : ⇑φ ⁻¹' (π ⁻¹' A ∩ σ ⁻¹' C) = π ⁻¹' K ∩ σ ⁻¹' C := by
    ext p; simp [A, hφψ, hσφ]
  rw [hpre, ← hmA _ hKc.isClosed.measurableSet, ← hmA _ hAm, hc, ENNReal.smul_def,
    MulEquivHaarCharEqOfProjection.smul_nn, MulEquivHaarCharEqOfProjection.smul_nn] at e1
  have e2 := mulEquivHaarChar_smul_preimage μN (X := A) ψ
  rw [hApre] at e2
  simp only [ENNReal.smul_def, smul_eq_mul] at e1 e2
  have key : ((c : ENNReal) * μN K) * (mulEquivHaarChar φ : ENNReal)
      = ((c : ENNReal) * μN K) * (mulEquivHaarChar ψ : ENNReal) := by
    calc ((c : ENNReal) * μN K) * (mulEquivHaarChar φ : ENNReal)
        = (mulEquivHaarChar φ : ENNReal) * ((c : ENNReal) * μN K) := by ring
      _ = (c : ENNReal) * μN A := e1
      _ = (c : ENNReal) * ((mulEquivHaarChar ψ : ENNReal) * μN K) := by rw [e2]
      _ = ((c : ENNReal) * μN K) * (mulEquivHaarChar ψ : ENNReal) := by ring
  rw [ENNReal.mul_right_inj (mul_ne_zero hc0 hK0) (ENNReal.mul_ne_top ENNReal.coe_ne_top hKt)] at key
  exact_mod_cast key
end UpperTheory.Reformulated.B.Yhb4
