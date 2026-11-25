-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.factorCasimir_ncV_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:28:59.709031+00:00
-- url     : https://prove2.me/submissions/af5065c7-0d4c-4e9a-bf0f-65f2f0191bf5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCasA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCas
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_bcas_sum_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_BigCasimir_factorAd_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_factorAd_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {F : Big n 1 M} (hF : F ∈ ncV ε V 1) :
    factorCasimir ε 1 F = (n : ℂ) • F := by
  classical
  have hz : ∀ x y : Fin n, ε x = ε y → F (fun _ => (x, y)) = 0 := by
    intro x y hxy
    unfold ncV at hF
    have h := (Submodule.mem_iInf _).1 hF (fun _ => (x, y))
    rw [Submodule.mem_comap] at h
    have hc : ¬ ∀ j : Fin 1, ε ((fun _ : Fin 1 => (x, y)) j).1 ≠ ε ((fun _ : Fin 1 => (x, y)) j).2 :=
      fun hall => hall 0 hxy
    rw [if_neg hc, Submodule.mem_bot] at h
    exact h
  have hupd : ∀ (κ : Fin 1 → Fin n × Fin n) (v : Fin n × Fin n),
      Function.update κ 0 v = fun _ => v := by
    intro κ v
    funext i
    rw [Subsingleton.elim i 0, Function.update_self]
  have hbool : ∀ x y w : Bool, x ≠ y → (y = w ↔ ¬ w = x) := by decide
  refine PiLp.ext fun κ => ?_
  obtain ⟨⟨p, q⟩, rfl⟩ : ∃ v, κ = fun _ => v :=
    ⟨κ 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  unfold factorCasimir casimirK
  simp only [LinearMap.sum_apply, bcas_sum_apply, Module.End.mul_apply, Fin.sum_univ_one,
    factorAd_apply, hupd]
  rw [PiLp.smul_apply]
  by_cases hpq : ε p = ε q
  · rw [hz p q hpq, smul_zero]
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    by_cases h1 : p = a
    · subst h1
      by_cases h2 : q = b
      · subst h2
        simp [hz _ _ hpq, fun x => hz x x rfl]
      · simp [h2, hz _ _ hpq, fun x => hz x x rfl]
    · by_cases h2 : q = b
      · subst h2
        simp [h1, hz _ _ hpq, fun x => hz x x rfl]
      · simp [h1, h2, fun x => hz x x rfl]
  · have hpq' : p ≠ q := fun h => hpq (h ▸ rfl)
    trans ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a),
      ((if p = a then F (fun _ => (p, q)) else 0) + (if q = b then F (fun _ => (p, q)) else 0))
    · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      by_cases h1 : p = a
      · subst h1
        by_cases h2 : q = b
        · subst h2
          simp [hpq', Ne.symm hpq']
        · simp [h2, hpq', Ne.symm hpq']
      · by_cases h2 : q = b
        · subst h2
          simp [h1, hpq', Ne.symm hpq']
        · simp [h1, h2]
    · simp only [Finset.sum_add_distrib]
      have h1 : ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a),
          (if p = a then F (fun _ => (p, q)) else 0) =
          (univ.filter fun b => ε b = ε p).card • F (fun _ => (p, q)) := by
        rw [Finset.sum_eq_single p (fun a _ ha => by simp [Ne.symm ha]) (by simp)]
        simp
      have h2 : ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a),
          (if q = b then F (fun _ => (p, q)) else 0) =
          (univ.filter fun a => ε q = ε a).card • F (fun _ => (p, q)) := by
        simp only [Finset.sum_ite_eq, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← Finset.sum_filter, Finset.sum_const]
      have hcard : (univ.filter fun b => ε b = ε p).card + (univ.filter fun a => ε q = ε a).card
          = n := by
        have hf : (univ.filter fun a => ε q = ε a) = univ.filter fun a => ¬ (ε a = ε p) :=
          Finset.filter_congr fun a _ => hbool _ _ _ hpq
        rw [hf]
        first
          | rw [Finset.filter_card_add_filter_neg_card_eq_card, Finset.card_univ, Fintype.card_fin]
          | rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
          | rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter_neg _ _ _),
              Finset.filter_union_filter_neg_eq, Finset.card_univ, Fintype.card_fin]
          | rw [← Finset.card_union_eq_card_add_card.2 (Finset.disjoint_filter_filter_neg _ _ _),
              Finset.filter_union_filter_neg_eq, Finset.card_univ, Fintype.card_fin]
      rw [h1, h2, ← add_smul, hcard, Nat.cast_smul_eq_nsmul]
end ReciprocityTheory.ChartRestriction.DS
