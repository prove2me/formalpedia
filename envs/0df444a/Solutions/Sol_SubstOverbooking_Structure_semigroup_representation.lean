-- Prove2me | solution 1 for SubstOverbooking.Structure.semigroup_representation
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T07:29:41.089836+00:00
-- url     : https://prove2.me/submissions/35c1d866-4221-4fe0-b959-6d7ba1775076

import Mathlib
import Definitions.Def_SubstOverbooking_Structure_Setting

open MeasureTheory SubstOverbooking.Structure

theorem solution {n m : ℕ} (a : Fin n → Fin (m + 1) → ℝ) (c : Fin (m + 1) → ℝ)
    (P : Set ℝ) (L : Fin n → ℝ → PMF ℕ) (hL : ∀ i, IsSemigroupFamily P (L i))
    (u : Fin n → ℝ) (hu : ∀ k, u k ∈ P) (i : Fin n) (ε : ℝ) (hε : ε ∈ P) :
    ∫ z, V0 a c (fun k => (z k : ℝ)) ∂(survivalLaw L (Function.update u i (u i + ε))) =
      ∫ p : (Fin n → ℕ) × ℕ, V0 a c (fun k => ((p.1 + (Pi.single i p.2 : Fin n → ℕ)) k : ℝ))
        ∂((survivalLaw L u).prod (L i ε).toMeasure) := by
  classical
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    let μ : Fin (n + 1) → Measure ℕ := fun k => (L k (u k)).toMeasure
    let ν := (L i ε).toMeasure
    let ρ := Measure.pi (fun j : Fin n => μ (i.succAbove j))
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℕ) i
    have H1 := (measurePreserving_piFinSuccAbove μ i).prod (MeasurePreserving.id ν)
    have H2 := (measurePreserving_prodAssoc (μ i) ρ ν).comp H1
    have H3 := ((MeasurePreserving.id (μ i)).prod
      (Measure.measurePreserving_swap (μ := ρ) (ν := ν))).comp H2
    have H4 := ((measurePreserving_prodAssoc (μ i) ν ρ).symm
      MeasurableEquiv.prodAssoc).comp H3
    have hadd : MeasurePreserving (fun p : ℕ × ℕ => p.1 + p.2)
        ((μ i).prod ν) (L i (u i + ε)).toMeasure :=
      ⟨by fun_prop, (hL i).1 (u i) (hu i) ε hε |>.symm⟩
    have H5 := (hadd.prod (MeasurePreserving.id ρ)).comp H4
    have H6 := (measurePreserving_piFinSuccAbove
      (fun k => (L k (Function.update u i (u i + ε) k)).toMeasure) i).symm e
    have H6' : MeasurePreserving e.symm
        ((L i (u i + ε)).toMeasure.prod ρ)
        (survivalLaw L (Function.update u i (u i + ε))) := by
      simpa [e, ρ, μ, survivalLaw, Function.update_of_ne (Fin.succAbove_ne i _)] using H6
    have H := H6'.comp H5
    have heq : e.symm ∘ (fun p => (p.1.1 + p.1.2, p.2)) ∘
        MeasurableEquiv.prodAssoc.symm ∘ (fun p => (p.1, p.2.swap)) ∘
        MeasurableEquiv.prodAssoc ∘ (fun p => (e p.1, p.2)) =
        (fun p : (Fin (n + 1) → ℕ) × ℕ => p.1 + Pi.single i p.2) := by
      ext p k
      obtain rfl | ⟨j, rfl⟩ := i.eq_self_or_eq_succAbove k
      · simp [e, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv,
          MeasurableEquiv.prodAssoc, Fin.removeNth]
      · simp [e, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv,
          MeasurableEquiv.prodAssoc, Fin.removeNth]
    have H' : MeasurePreserving
        (fun p : (Fin (n + 1) → ℕ) × ℕ => p.1 + Pi.single i p.2)
        ((survivalLaw L u).prod (L i ε).toMeasure)
        (survivalLaw L (Function.update u i (u i + ε))) := by
      convert H using 1
      · exact heq.symm
      · rfl
    rw [← H'.map_eq]
    exact integral_map (by fun_prop)
      (measurable_of_countable (fun z : Fin (n + 1) → ℕ => V0 a c (fun k => (z k : ℝ)))).aestronglyMeasurable


#print axioms solution
