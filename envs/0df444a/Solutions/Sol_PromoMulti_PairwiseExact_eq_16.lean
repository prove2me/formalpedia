-- Prove2me | solution 1 for PromoMulti.PairwiseExact.eq_16
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T07:31:31.875435+00:00
-- url     : https://prove2.me/submissions/f785e2fa-2b29-4985-8b28-040c5507b28e

import Mathlib
import Definitions.Def_PromoMulti_PairwiseExact_Model

namespace PromoMulti.PairwiseExact
namespace SolAux16

theorem moebius {ι : Type*} [DecidableEq ι] (S : Finset ι) :
    ∀ g : Finset ι → ℝ,
      ∑ U ∈ S.powerset, ∑ V ∈ U.powerset, (-1 : ℝ) ^ (U.card - V.card) * g V = g S := by
  induction S using Finset.induction_on with
  | empty => intro g; simp
  | @insert a S ha ih =>
    intro g
    rw [Finset.sum_powerset_insert ha, ih g]
    have key : ∀ U ∈ S.powerset,
        ∑ V ∈ (insert a U).powerset, (-1 : ℝ) ^ ((insert a U).card - V.card) * g V =
          - ∑ V ∈ U.powerset, (-1 : ℝ) ^ (U.card - V.card) * g V +
          ∑ V ∈ U.powerset, (-1 : ℝ) ^ (U.card - V.card) * g (insert a V) := by
      intro U hU
      have hUS : U ⊆ S := Finset.mem_powerset.mp hU
      have haU : a ∉ U := fun h => ha (hUS h)
      rw [Finset.sum_powerset_insert haU, Finset.card_insert_of_notMem haU, ← Finset.sum_neg_distrib]
      congr 1
      · refine Finset.sum_congr rfl (fun V hV => ?_)
        have : V.card ≤ U.card := Finset.card_le_card (Finset.mem_powerset.mp hV)
        rw [show U.card + 1 - V.card = (U.card - V.card) + 1 by omega, pow_succ]; ring
      · refine Finset.sum_congr rfl (fun V hV => ?_)
        have hVU : V ⊆ U := Finset.mem_powerset.mp hV
        have haV : a ∉ V := fun h => haU (hVU h)
        rw [Finset.card_insert_of_notMem haV, show U.card + 1 - (V.card + 1) = U.card - V.card by omega]
    rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_neg_distrib, ih g,
      ih (fun V => g (insert a V))]
    ring

variable {N T : ℕ}

theorem supp_restrict {I : Instance N T} (σ : Pattern I) (U : Finset (Fin N)) (hU : U ⊆ supp σ) :
    supp (restrict σ U) = U := by
  ext i
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [restrict]
  constructor
  · intro h; by_contra hi; exact h (if_neg hi)
  · intro hi; rw [if_pos hi]; simpa [supp] using hU hi

theorem restrict_restrict {I : Instance N T} (σ : Pattern I) (U V : Finset (Fin N)) (hV : V ⊆ U) :
    restrict (restrict σ U) V = restrict σ V := by
  funext i
  simp only [restrict]
  by_cases hi : i ∈ V
  · simp [hi, hV hi]
  · simp [hi]

theorem restrict_supp {I : Instance N T} (σ : Pattern I) : restrict σ (supp σ) = σ := by
  funext i
  simp only [restrict]
  by_cases hi : i ∈ supp σ
  · simp [hi]
  · rw [if_neg hi]; exact (by simpa [supp] using hi : σ i = 0).symm

theorem coef_restrict (I : Instance N T) (t : Fin T) (σ : Pattern I) (U : Finset (Fin N))
    (hU : U ⊆ supp σ) :
    coef I t (restrict σ U) =
      ∑ V ∈ U.powerset, (-1 : ℝ) ^ (U.card - V.card) * MPOP I (pure I t (restrict σ V)) := by
  unfold coef
  rw [supp_restrict σ U hU]
  refine Finset.sum_congr rfl (fun V hV => ?_)
  rw [restrict_restrict σ U V (Finset.mem_powerset.mp hV)]

end SolAux16
end PromoMulti.PairwiseExact

open PromoMulti.PairwiseExact

theorem solution {N T : ℕ} (I : Instance N T) (t : Fin T) (σ : Pattern I)
    (hσ : (supp σ).Nonempty) :
    coef I t σ = MPOP I (pure I t σ) - MPOP I (regular I) -
      ∑ U ∈ (supp σ).powerset.filter (fun U => U.Nonempty ∧ U ≠ supp σ),
        coef I t (restrict σ U) := by
  set S := supp σ with hSdef
  have htot : ∑ U ∈ S.powerset, coef I t (restrict σ U) = MPOP I (pure I t σ) := by
    rw [Finset.sum_congr rfl (fun U hU =>
      SolAux16.coef_restrict I t σ U (Finset.mem_powerset.mp hU)),
      SolAux16.moebius S (fun V => MPOP I (pure I t (restrict σ V))), hSdef,
      SolAux16.restrict_supp]
  have hS0 : (∅ : Finset (Fin N)) ≠ S := (Finset.nonempty_iff_ne_empty.mp hσ).symm
  have hsplit : S.powerset.filter (fun U => ¬ (U.Nonempty ∧ U ≠ S)) = {∅, S} := by
    ext U
    simp only [Finset.mem_filter, Finset.mem_powerset, not_and, not_not, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨_, h⟩
      by_cases hU : U.Nonempty
      · exact Or.inr (h hU)
      · exact Or.inl (Finset.not_nonempty_iff_eq_empty.mp hU)
    · rintro (rfl | rfl)
      · exact ⟨Finset.empty_subset _, fun h => absurd h Finset.not_nonempty_empty⟩
      · exact ⟨subset_refl _, fun _ => rfl⟩
  rw [← Finset.sum_filter_add_sum_filter_not S.powerset (fun U => U.Nonempty ∧ U ≠ S), hsplit,
    Finset.sum_pair hS0] at htot
  have h0 : coef I t (restrict σ ∅) = MPOP I (regular I) := by
    rw [SolAux16.coef_restrict I t σ ∅ (Finset.empty_subset _)]
    simp only [Finset.powerset_empty, Finset.sum_singleton, Finset.card_empty, Nat.sub_self,
      pow_zero, one_mul]
    congr 1
    funext i τ
    simp [PromoMulti.PairwiseExact.pure, restrict, regular]
  have hS : coef I t (restrict σ S) = coef I t σ := by rw [hSdef, SolAux16.restrict_supp]
  rw [h0, hS] at htot
  linarith
