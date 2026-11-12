-- Prove2me | solution 1 for StochIneqPO.Comparison.prop2_le_of_marginals_le
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T17:51:13.9952+00:00
-- url     : https://prove2.me/submissions/90acd3b9-f55b-4143-b48a-c5d8309569b5

import Mathlib
import Definitions.Def_StochIneqPO_Comparison_StochLE
import Theorems.Thm_StochIneqPO_Comparison_theorem1_tfae

open MeasureTheory ProbabilityTheory Finset StochIneqPO.Comparison

/-- The set of points lying above `g c` for some `c` in a compact set is closed. -/
lemma isClosed_above_image_compact {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Preorder Y] [OrderClosedTopology Y] {C : Set X} (hC : IsCompact C) {g : X → Y}
    (hg : Continuous g) : IsClosed {u : Y | ∃ c ∈ C, g c ≤ u} := by
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hS : IsClosed {p : C × Y | g p.1 ≤ p.2} :=
    isClosed_le (hg.comp (continuous_subtype_val.comp continuous_fst)) continuous_snd
  have himg : (Prod.snd '' {p : C × Y | g p.1 ≤ p.2}) = {u : Y | ∃ c ∈ C, g c ≤ u} := by
    ext u
    constructor
    · rintro ⟨⟨c, v⟩, hcv, rfl⟩
      exact ⟨c, c.2, hcv⟩
    · rintro ⟨c, hc, hcu⟩
      exact ⟨(⟨c, hc⟩, u), hcu, rfl⟩
  rw [← himg]
  exact isClosedMap_snd_of_compactSpace _ hS

theorem solution {E : ℕ → Type*} [∀ n, TopologicalSpace (E n)]
    [∀ n, PolishSpace (E n)] [∀ n, MeasurableSpace (E n)] [∀ n, BorelSpace (E n)]
    [∀ n, PartialOrder (E n)] [∀ n, OrderClosedTopology (E n)]
    (P Q : Measure (Π n, E n)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (h : ∀ i : ℕ, StochLE (P.map (Preorder.frestrictLe i)) (Q.map (Preorder.frestrictLe i))) :
    StochLE P Q := by
  -- (vi) ⇒ (i) of Theorem 1 on the sequence space
  refine ((theorem1_tfae P Q).out 0 5).mpr ?_
  intro B hB hBup
  -- closed increasing sets of the marginals
  have hfin : ∀ i, ∀ U : Set (Π j : Iic i, E j), IsClosed U → IsUpperSet U →
      P (Preorder.frestrictLe i ⁻¹' U) ≤ Q (Preorder.frestrictLe i ⁻¹' U) := by
    intro i U hU hUup
    have hP : IsProbabilityMeasure (P.map (Preorder.frestrictLe i)) :=
      Measure.isProbabilityMeasure_map (Preorder.measurable_frestrictLe i).aemeasurable
    have hQ : IsProbabilityMeasure (Q.map (Preorder.frestrictLe i)) :=
      Measure.isProbabilityMeasure_map (Preorder.measurable_frestrictLe i).aemeasurable
    have key := (theorem1_tfae (P.map (Preorder.frestrictLe i))
      (Q.map (Preorder.frestrictLe i))).out 0 5
    have := key.mp (h i) U hU hUup
    rwa [Measure.map_apply (Preorder.measurable_frestrictLe i) hU.measurableSet,
      Measure.map_apply (Preorder.measurable_frestrictLe i) hU.measurableSet] at this
  -- inner regularity
  rw [hB.measurableSet.measure_eq_iSup_isCompact P]
  refine iSup₂_le fun C hCB => iSup_le fun hC => ?_
  have hcont : ∀ i, Continuous (Preorder.frestrictLe (π := E) i) := fun i =>
    continuous_pi fun j => continuous_apply _
  let U : (i : ℕ) → Set (Π j : Iic i, E j) := fun i =>
    {u | ∃ c ∈ C, Preorder.frestrictLe i c ≤ u}
  have hUc : ∀ i, IsClosed (U i) := fun i => isClosed_above_image_compact hC (hcont i)
  have hUup : ∀ i, IsUpperSet (U i) := fun i u v huv ⟨c, hc, hcu⟩ => ⟨c, hc, hcu.trans huv⟩
  let A : ℕ → Set (Π n, E n) := fun i => Preorder.frestrictLe i ⁻¹' U i
  have hAm : ∀ i, MeasurableSet (A i) := fun i =>
    (hUc i).measurableSet.preimage (Preorder.measurable_frestrictLe i)
  have hCA : ∀ i, C ⊆ A i := fun i x hx => ⟨x, hx, le_rfl⟩
  have hAanti : Antitone A := by
    apply antitone_nat_of_succ_le
    intro i x ⟨c, hc, hcx⟩
    refine ⟨c, hc, fun j => ?_⟩
    have hj : (j : ℕ) ≤ i + 1 := by have := mem_Iic.1 j.2; omega
    exact hcx ⟨j, mem_Iic.2 hj⟩
  have hInter : (⋂ i, A i) ⊆ B := by
    intro x hx
    rw [Set.mem_iInter] at hx
    let D : ℕ → Set (Π n, E n) := fun i => C ∩ {c | Preorder.frestrictLe i c ≤ Preorder.frestrictLe i x}
    have hD : (⋂ i, D i).Nonempty := by
      apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed D
      · intro i c ⟨hc, hcx⟩
        refine ⟨hc, fun j => ?_⟩
        have hj : (j : ℕ) ≤ i + 1 := by have := mem_Iic.1 j.2; omega
        exact hcx ⟨j, mem_Iic.2 hj⟩
      · intro i
        obtain ⟨c, hc, hcx⟩ := hx i
        exact ⟨c, hc, hcx⟩
      · exact hC.inter_right (isClosed_le (hcont 0) continuous_const)
      · intro i
        exact hC.isClosed.inter (isClosed_le (hcont i) continuous_const)
    obtain ⟨c, hc⟩ := hD
    rw [Set.mem_iInter] at hc
    have hcC : c ∈ C := (hc 0).1
    have hcx : c ≤ x := fun n => (hc n).2 ⟨n, mem_Iic.2 le_rfl⟩
    exact hBup hcx (hCB hcC)
  have hQ : Q (⋂ i, A i) = ⨅ i, Q (A i) :=
    hAanti.measure_iInter (fun i => (hAm i).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩
  calc P C ≤ ⨅ i, Q (A i) := le_iInf fun i => (measure_mono (hCA i)).trans (hfin i _ (hUc i) (hUup i))
    _ = Q (⋂ i, A i) := hQ.symm
    _ ≤ Q B := measure_mono hInter
