-- Prove2me | solution 1 for ProbabilityTheory.IsPoissonPointFamily.indepFun_pieceBlocks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:45:29.914126+00:00
-- url     : https://prove2.me/submissions/1a78077e-2320-45b8-a159-aec35618008f

import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E} {m : MeasureTheory.Measure E} [SigmaFinite m] [Nonempty E] {μ : MeasureTheory.Measure Ω}
private def pointFamilyBlock : ℕ ⊕ ℕ × ℕ → ℕ := Sum.elim id Prod.fst

theorem solution [MeasureTheory.IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (n : ℕ) :
    IndepFun
      (fun ω (i : {i : ℕ ⊕ ℕ × ℕ // pointFamilyBlock i ≤ n}) => pointFamilyCombined K X i.1 ω)
      (fun ω (i : {i : ℕ ⊕ ℕ × ℕ // pointFamilyBlock i = n + 1}) => pointFamilyCombined K X i.1 ω)
      μ := by
  classical
  have hmeas : ∀ i, Measurable (pointFamilyCombined K X i) := by
    intro i
    cases i with
    | inl k => exact hd.measurable_count k
    | inr p => exact hd.measurable_point p.1 p.2
  refine IndepFun.process_indepFun_process
    (fun i => hmeas i.1) (fun j => hmeas j.1) ?_
  intro I J
  let eφ : {i : ℕ ⊕ ℕ × ℕ // pointFamilyBlock i ≤ n} ↪ ℕ ⊕ ℕ × ℕ :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let eψ : {i : ℕ ⊕ ℕ × ℕ // pointFamilyBlock i = n + 1} ↪ ℕ ⊕ ℕ × ℕ :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hST : ∀ (s : {i : ℕ ⊕ ℕ × ℕ // pointFamilyBlock i ≤ n})
      (t : {i : ℕ ⊕ ℕ × ℕ // pointFamilyBlock i = n + 1}), s.1 ≠ t.1 := by
    intro s t h
    have h1 := s.2
    have h2 := t.2
    rw [h] at h1
    omega
  have hdisj : Disjoint (I.map eφ) (J.map eψ) := by
    rw [Finset.disjoint_left]
    rintro x hx1 hx2
    rw [Finset.mem_map] at hx1 hx2
    obtain ⟨a, -, rfl⟩ := hx1
    obtain ⟨c, -, hc⟩ := hx2
    exact hST a c hc.symm
  have key := hd.indep.indepFun_finset (I.map eφ) (J.map eψ) hdisj hmeas
  have hLmeas : Measurable
      (fun (g : (i : ↑(I.map eφ)) → pointFamilyIndexType E i.1) (i : I) =>
        g ⟨eφ i.1, Finset.mem_map_of_mem eφ i.2⟩) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  have hRmeas : Measurable
      (fun (g : (j : ↑(J.map eψ)) → pointFamilyIndexType E j.1) (j : J) =>
        g ⟨eψ j.1, Finset.mem_map_of_mem eψ j.2⟩) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply _
  exact key.comp hLmeas hRmeas
