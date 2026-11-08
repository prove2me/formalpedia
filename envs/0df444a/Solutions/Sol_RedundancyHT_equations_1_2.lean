-- Prove2me | solution 1 for RedundancyHT.equations_1_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:27:55.415195+00:00
-- url     : https://prove2.me/submissions/de9a0a28-0dd0-47b6-86fe-015eda3f43d3

import Definitions.Def_RedundancyHT_IsCapacityMaximizer
import Definitions.Def_RedundancyHT_StabilityOne
import Definitions.Def_RedundancyHT_StabilityTwo
import Definitions.Def_RedundancyHT_lamStar

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay

open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace Aux_Q01_RedundancyHT
open RedundancyHT

theorem mem_only {n m : ℕ} (D : Model n m) (U : Finset (Fin m)) (i : Fin n) :
    i ∈ onlyClasses D.edge U ↔ ∀ j, D.compatible i j = true → j ∈ U := by
  unfold onlyClasses
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Iff.rfl

theorem mem_servers {n m : ℕ} (D : Model n m) (T : Finset (Fin n)) (j : Fin m) :
    j ∈ serversOf D T ↔ ∃ i ∈ T, D.compatible i j = true := by
  simp [serversOf]

theorem pOf_pos {n m : ℕ} (D : Model n m) (i : Fin n) : 0 < pOf D i := by
  unfold pOf
  apply div_pos (D.nominal_pos i)
  apply Finset.sum_pos (fun k _ => D.nominal_pos k)
  exact Finset.univ_nonempty_iff.mpr ⟨⟨0, D.classes_pos⟩⟩

theorem pSet_pos {n m : ℕ} (D : Model n m) (T : Finset (Fin n)) (hT : T.Nonempty) :
    0 < pSet D T :=
  Finset.sum_pos (fun i _ => pOf_pos D i) hT

theorem pSet_mono {n m : ℕ} (D : Model n m) {T T' : Finset (Fin n)} (h : T ⊆ T') :
    pSet D T ≤ pSet D T' :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun i _ _ => (pOf_pos D i).le)

theorem cap_mono {n m : ℕ} (D : Model n m) {U U' : Finset (Fin m)} (h : U ⊆ U') :
    D.capacity U ≤ D.capacity U' :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun j _ _ => (D.service_pos j).le)

theorem cap_pos {n m : ℕ} (D : Model n m) (U : Finset (Fin m)) (hU : U.Nonempty) :
    0 < D.capacity U :=
  Finset.sum_pos (fun j _ => D.service_pos j) hU

theorem servers_nonempty {n m : ℕ} (D : Model n m) (hne : ∀ i, ∃ j, D.compatible i j = true)
    (T : Finset (Fin n)) (hT : T.Nonempty) : (serversOf D T).Nonempty := by
  obtain ⟨i, hi⟩ := hT
  obtain ⟨j, hj⟩ := hne i
  exact ⟨j, (mem_servers D T j).mpr ⟨i, hi, hj⟩⟩

end Aux_Q01_RedundancyHT

open RedundancyHT Aux_Q01_RedundancyHT in
theorem solution {n m : ℕ} (D : Model n m) (hne : ∀ i, ∃ j, D.compatible i j = true)
    (T : Finset (Fin n)) (hT : IsCapacityMaximizer D T) (lam : ℝ) (hlam : 0 < lam) :
    (StabilityOne D lam ↔ StabilityTwo D lam) ∧ (StabilityOne D lam ↔ lam < lamStar D T) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast D.servers_pos
  have hml : 0 ≤ (m : ℝ) * lam := by positivity
  have h12 : StabilityOne D lam ↔ StabilityTwo D lam := by
    constructor
    · intro h1 U hU
      by_cases hT0 : (onlyClasses D.edge U).Nonempty
      · have h := h1 _ hT0
        have hsub : serversOf D (onlyClasses D.edge U) ⊆ U := by
          intro j hj
          obtain ⟨i, hi, hij⟩ := (mem_servers D _ j).mp hj
          exact (mem_only D U i).mp hi j hij
        calc (m : ℝ) * lam * pSet D (onlyClasses D.edge U) < muSet D (onlyClasses D.edge U) := h
          _ ≤ D.capacity U := cap_mono D hsub
      · rw [Finset.not_nonempty_iff_eq_empty] at hT0
        rw [hT0]
        have h0 : pSet D ∅ = 0 := by simp [pSet]
        rw [h0, mul_zero]
        exact cap_pos D U hU
    · intro h2 T' hT'
      have hU := servers_nonempty D hne T' hT'
      have h := h2 _ hU
      have hsub : T' ⊆ onlyClasses D.edge (serversOf D T') := by
        intro i hi
        exact (mem_only D _ i).mpr (fun j hij => (mem_servers D T' j).mpr ⟨i, hi, hij⟩)
      have hp := pSet_mono D hsub
      calc (m : ℝ) * lam * pSet D T' ≤
            (m : ℝ) * lam * pSet D (onlyClasses D.edge (serversOf D T')) :=
            mul_le_mul_of_nonneg_left hp hml
        _ < D.capacity (serversOf D T') := h
        _ = muSet D T' := rfl
  refine ⟨h12, ?_⟩
  obtain ⟨hTne, hTmax⟩ := hT
  have hpT := pSet_pos D T hTne
  have hμT : 0 < muSet D T := cap_pos D _ (servers_nonempty D hne T hTne)
  unfold lamStar
  constructor
  · intro h1
    have h := h1 T hTne
    rw [lt_div_iff₀ (mul_pos hm hpT)]
    linarith
  · intro hlt T' hT'
    rw [lt_div_iff₀ (mul_pos hm hpT)] at hlt
    have hμ' : 0 < muSet D T' := cap_pos D _ (servers_nonempty D hne T' hT')
    have hr := hTmax T' hT'
    unfold capacityRatio at hr
    rw [div_le_div_iff₀ hμ' hμT] at hr
    have e1 : (m : ℝ) * lam * (pSet D T' * muSet D T) ≤ (m : ℝ) * lam * (pSet D T * muSet D T') :=
      mul_le_mul_of_nonneg_left hr hml
    have e2 : (m : ℝ) * lam * pSet D T * muSet D T' < muSet D T * muSet D T' :=
      mul_lt_mul_of_pos_right (by linarith) hμ'
    have e3 : (m : ℝ) * lam * pSet D T' * muSet D T < muSet D T' * muSet D T := by
      nlinarith
    exact lt_of_mul_lt_mul_right e3 hμT.le

end
