-- Prove2me | solution 1 for VapnikChervonenkis.Entropy.necessity_step1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:24:25.768122+00:00
-- url     : https://prove2.me/submissions/46b0a596-879b-4880-9c2b-435c334803a9

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_deviation

open MeasureTheory Filter Topology

namespace VapnikChervonenkis.Entropy

lemma aux_ns1_relFreq_nonneg {X : Type*} (A : Set X) {l : ℕ} (x : Fin l → X) :
    0 ≤ Shared.relFreq A x := by
  unfold Shared.relFreq; positivity

lemma aux_ns1_relFreq_le_one {X : Type*} (A : Set X) {l : ℕ} (x : Fin l → X) :
    Shared.relFreq A x ≤ 1 := by
  unfold Shared.relFreq
  rcases Nat.eq_zero_or_pos l with h | h
  · subst h; simp
  · apply div_le_one_of_le₀ _ (by positivity)
    exact_mod_cast (Finset.card_le_univ _).trans (by simp)

lemma aux_ns1_abs_le {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (A : Set X) {l : ℕ} (x : Fin l → X) : |Shared.relFreq A x - P.real A| ≤ 1 := by
  have h1 := aux_ns1_relFreq_nonneg A x
  have h2 := aux_ns1_relFreq_le_one A x
  have h3 : 0 ≤ P.real A := measureReal_nonneg
  have h4 : P.real A ≤ 1 := measureReal_le_one
  rw [abs_le]; constructor <;> linarith

lemma aux_ns1_split {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (S : Set (Set X)) (ε : ℝ) (hε : 0 < ε) (l : ℕ) (x : Fin (l + l) → X)
    (hx : 2 * ε < Shared.semiSampleDeviation S l x) :
    ε < Shared.maxDeviation S P l (fun i => x (Fin.castAdd l i)) ∨
    ε < Shared.maxDeviation S P l (fun i => x (Fin.natAdd l i)) := by
  unfold Shared.semiSampleDeviation at hx
  rcases isEmpty_or_nonempty S with hS | hS
  · rw [Real.iSup_of_isEmpty] at hx; linarith
  obtain ⟨A, hA⟩ := exists_lt_of_lt_ciSup hx
  have hbdd : ∀ y : Fin l → X, BddAbove (Set.range fun A : S =>
      |Shared.relFreq (A : Set X) y - P.real (A : Set X)|) := by
    intro y
    refine ⟨1, ?_⟩
    rintro _ ⟨B, rfl⟩
    exact aux_ns1_abs_le P _ y
  have h1 := le_ciSup (hbdd (fun i => x (Fin.castAdd l i))) A
  have h2 := le_ciSup (hbdd (fun i => x (Fin.natAdd l i))) A
  unfold Shared.maxDeviation
  set a := Shared.relFreq (A : Set X) (fun i => x (Fin.castAdd l i))
  set b := Shared.relFreq (A : Set X) (fun i => x (Fin.natAdd l i))
  set p := P.real (A : Set X)
  have htri : |a - b| ≤ |a - p| + |b - p| := by
    have := abs_sub_le a p b
    rw [abs_sub_comm p b] at this
    exact this
  by_contra hcon
  push Not at hcon
  obtain ⟨hc1, hc2⟩ := hcon
  linarith

theorem aux_ns1_mp (l : ℕ) {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] :
    MeasurePreserving (fun x : Fin (l + l) → X =>
        ((fun i => x (Fin.castAdd l i)), (fun i => x (Fin.natAdd l i))))
      (Measure.pi (fun _ : Fin (l + l) => P))
      ((Measure.pi (fun _ : Fin l => P)).prod (Measure.pi (fun _ : Fin l => P))) := by
  have h1 := (measurePreserving_piCongrLeft (fun _ : Fin (l + l) => P) finSumFinEquiv).symm
  have h2 := measurePreserving_sumPiEquivProdPi (fun _ : Fin l ⊕ Fin l => P)
  have := h2.comp h1
  convert this using 1
  funext x
  ext i
  · simp [MeasurableEquiv.coe_sumPiEquivProdPi, Equiv.sumPiEquivProdPi, MeasurableEquiv.piCongrLeft]
  · simp [MeasurableEquiv.coe_sumPiEquivProdPi, Equiv.sumPiEquivProdPi, MeasurableEquiv.piCongrLeft]

end VapnikChervonenkis.Entropy

open VapnikChervonenkis VapnikChervonenkis.Entropy
open MeasureTheory Filter Topology

theorem solution {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (S : Set (Set X))
    (hπ : ∀ l, Measurable (Shared.maxDeviation S P l)) (ε : ℝ) (hε : 0 < ε) (l : ℕ) :
    (1 - (Measure.pi (fun _ : Fin l => P)).real {x | ε < Shared.maxDeviation S P l x}) ^ 2
      ≤ 1 - (Measure.pi (fun _ : Fin (l + l) => P)).real
          {x | 2 * ε < Shared.semiSampleDeviation S l x} := by
  set μl := Measure.pi (fun _ : Fin l => P) with hμl
  set μ2 := Measure.pi (fun _ : Fin (l + l) => P) with hμ2
  set Q := {x | ε < Shared.maxDeviation S P l x} with hQdef
  have hQ : MeasurableSet Q := measurableSet_lt measurable_const (hπ l)
  have hf := aux_ns1_mp l P
  set f := fun x : Fin (l + l) → X =>
    ((fun i => x (Fin.castAdd l i)), (fun i => x (Fin.natAdd l i))) with hfdef
  set G := f ⁻¹' (Qᶜ ×ˢ Qᶜ) with hGdef
  have hGm : MeasurableSet G := hf.measurable (hQ.compl.prod hQ.compl)
  have hG : μ2.real G = (1 - μl.real Q) ^ 2 := by
    have h : μ2 G = μl Qᶜ * μl Qᶜ := by
      rw [hf.measure_preimage (hQ.compl.prod hQ.compl).nullMeasurableSet, Measure.prod_prod]
    have h' : μ2.real G = μl.real Qᶜ * μl.real Qᶜ := by
      simp only [Measure.real, h, ENNReal.toReal_mul]
    rw [h', probReal_compl_eq_one_sub hQ]
    ring
  have hsub : {x | 2 * ε < Shared.semiSampleDeviation S l x} ⊆ Gᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff, hGdef, Set.mem_preimage, Set.mem_prod, hfdef, hQdef,
      Set.mem_ofPred_eq, not_and, not_lt]
    rcases aux_ns1_split P S ε hε l x hx with h | h
    · intro h1; linarith
    · intro _; exact not_le.mpr h
  have hGc : μ2.real Gᶜ = 1 - μ2.real G := probReal_compl_eq_one_sub hGm
  have hmono : μ2.real {x | 2 * ε < Shared.semiSampleDeviation S l x} ≤ μ2.real Gᶜ :=
    measureReal_mono hsub
  linarith
