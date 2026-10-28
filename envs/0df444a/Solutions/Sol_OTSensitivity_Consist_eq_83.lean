-- Prove2me | solution 1 for OTSensitivity.Consist.eq_83
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T22:47:17.512538+00:00
-- url     : https://prove2.me/submissions/1c41331d-84b3-473c-94bd-4302cc222f1b

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_OTSensitivity_Consist_Setting
import Definitions.Def_OTSensitivity_Consist_Estimation

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Aux_OTS_83

open OTSensitivity.Consist

lemma dich {𝒳 : Type*} {n : ℕ} (C : Fin n → Set 𝒳)
    (hd : Pairwise (fun h h' => Disjoint (C h) (C h'))) (S : Set 𝒳)
    (hS : MeasurableSet[cellSigma C] S) (h : Fin n) : C h ⊆ S ∨ Disjoint (C h) S := by
  induction S, hS using MeasurableSpace.generateFrom_induction with
  | hC t ht _ =>
    obtain ⟨h', rfl⟩ := ht
    by_cases hh : h = h'
    · left; rw [hh]
    · right; exact hd hh
  | empty => right; exact Set.disjoint_empty _
  | compl t _ ih =>
    rcases ih with h1 | h1
    · right; exact Set.disjoint_of_subset_left h1 disjoint_compl_right
    · left; exact Set.subset_compl_iff_disjoint_right.mpr h1
  | iUnion s _ ih =>
    by_cases hex : ∃ i, C h ⊆ s i
    · obtain ⟨i, hi⟩ := hex
      left; exact hi.trans (Set.subset_iUnion _ i)
    · push_neg at hex
      right
      exact Set.disjoint_iUnion_right.mpr (fun i => (ih i).resolve_left (hex i))

end Aux_OTS_83

open OTSensitivity.Consist Aux_OTS_83 in
theorem solution {𝒳 𝒴 : Type*}
    [TopologicalSpace 𝒳] [PolishSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳]
    [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴] [BorelSpace 𝒴]
    (k : 𝒴 → 𝒴 → ℝ≥0∞) (hk : IsCost k)
    (π : Measure (𝒳 × 𝒴)) [IsProbabilityMeasure π] {n : ℕ} (C : Fin n → Set 𝒳)
    (hC : IsFinitePartition C) (κ : Kernel 𝒳 𝒴)
    (hκ : IsCondDistrib π Prod.fst Prod.snd (cellSigma C) κ) :
    xi k π Prod.fst Prod.snd κ =
      ∑ h ∈ Finset.univ.filter (fun h => π.fst (C h) ≠ 0),
        π.fst (C h) * RWPI.SqrtLasso.transportCost k π.snd (cellLaw π (C h)) := by
  have hfst : π.map Prod.fst = π.fst := rfl
  have hsnd : π.map Prod.snd = π.snd := rfl
  have hconst : ∀ h x x', x ∈ C h → x' ∈ C h → κ x = κ x' := by
    intro h x x' hx hx'
    ext B hB
    have hm := hκ.2.1 B hB
    have hS : MeasurableSet[cellSigma C] ((fun x => κ x B) ⁻¹' {κ x B}) :=
      hm (measurableSet_singleton _)
    rcases dich C hC.2.1 _ hS h with h1 | h1
    · exact ((h1 hx') : κ x' B = κ x B).symm
    · exact absurd (rfl : κ x B = κ x B) (Set.disjoint_left.mp h1 hx)
  unfold xi
  rw [hfst, hsnd, ← setLIntegral_univ, ← hC.2.2, lintegral_iUnion hC.1 hC.2.1, tsum_fintype,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun h _ => ?_
  split_ifs with hh
  · have hne : (C h).Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne, measure_empty] at hh
      exact hh rfl
    obtain ⟨x0, hx0⟩ := hne
    have hcell : κ x0 = cellLaw π (C h) := by
      ext B hB
      have key := hκ.2.2 (C h) (MeasurableSpace.measurableSet_generateFrom ⟨h, rfl⟩) B hB
      rw [hfst, setLIntegral_congr_fun (hC.1 h)
        (fun x hx => by rw [hconst h x x0 hx hx0]), setLIntegral_const] at key
      unfold cellLaw
      rw [Measure.smul_apply, Measure.snd_apply hB,
        Measure.restrict_apply (hB.preimage measurable_snd), Set.prod_univ, Set.inter_comm, key,
        smul_eq_mul, ← mul_assoc, mul_comm _ (κ x0 B), mul_assoc,
        ENNReal.inv_mul_cancel hh (measure_ne_top _ _), mul_one]
    rw [setLIntegral_congr_fun (hC.1 h) (fun x hx => by rw [hconst h x x0 hx hx0]),
      setLIntegral_const, mul_comm, hcell]
  · push_neg at hh
    exact setLIntegral_measure_zero _ _ hh
