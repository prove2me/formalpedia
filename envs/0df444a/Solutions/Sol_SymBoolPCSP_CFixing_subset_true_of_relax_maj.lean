-- Prove2me | solution 1 for SymBoolPCSP.CFixing.subset_true_of_relax_maj
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T19:08:35.432063+00:00
-- url     : https://prove2.me/submissions/5d5c9c21-b93c-48be-99be-e4254d6c33b5

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

namespace Aux_subset_true_of_relax_maj

theorem hw_eq_sum {k : ℕ} (x : Fin k → Bool) :
    hw x = ∑ c, (if x c = true then 1 else 0) := by
  unfold hw; rw [Finset.card_filter]

theorem hw_equiv {α : Type} [Fintype α] {k : ℕ} (e : α ≃ Fin k) (x : Fin k → Bool) :
    hw x = ∑ a, (if x (e a) = true then 1 else 0) := by
  rw [hw_eq_sum]; exact (Equiv.sum_comp e (fun c => if x c = true then 1 else 0)).symm

theorem neg_of_folded {L : ℕ} {f : (Fin L → Bool) → Bool} (hfold : IsFolded f)
    (x : Fin L → Bool) : f (neg x) = !f x := by
  have hnn : neg (neg x) = x := funext fun i => by simp [neg]
  rw [hfold (neg x), hnn]

end Aux_subset_true_of_relax_maj

open Aux_subset_true_of_relax_maj in
/-- Case 1 of BG Lemma 4.12: let `f` be a folded polymorphism of
`(Ham_{2m+1}({m+1}), Ham_{2m+1}({0, …, 2m}))` and let `Z` be an `m`-set of coordinates on each
of which `f` is somewhere-increasing. Then `f(e_Z) = 1`. -/
theorem subset_true_of_relax_maj {L m : ℕ} (f : (Fin L → Bool) → Bool) (hfold : IsFolded f)
    (hpol : PolOf (Ham (2 * m + 1) {m + 1}) (Ham (2 * m + 1) (Set.Iic (2 * m))) f)
    (Z : Finset (Fin L)) (hZ : Z.card = m)
    (hwit : ∀ j ∈ Z, ∃ Y : Finset (Fin L), j ∉ Y ∧ f (indicator Y) = false ∧
      f (indicator (insert j Y)) = true) :
    f (indicator Z) = true := by
  classical
  choose Y hY using hwit
  have hcard : Fintype.card ((Z × Bool) ⊕ Unit) = 2 * m + 1 := by
    simp [Fintype.card_sum, Fintype.card_prod, hZ]; ring
  let e := Fintype.equivFinOfCardEq hcard
  let v : (Z × Bool) ⊕ Unit → Fin L → Bool := Sum.elim
    (fun p => if p.2 then indicator (insert p.1.1 (Y p.1.1 p.1.2))
      else neg (indicator (Y p.1.1 p.1.2)))
    (fun _ => neg (indicator Z))
  have key := hpol (fun l c => v (e.symm c) l) (by
    intro l
    simp only [Ham, Set.mem_setOf_eq, Set.mem_singleton_iff]
    rw [hw_equiv e]
    simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, Fintype.sum_prod_type,
      Fintype.sum_bool, Finset.univ_unique, Finset.sum_singleton]
    have hterm : ∀ z : Z, ((if v (Sum.inl (z, true)) l = true then 1 else 0) +
        (if v (Sum.inl (z, false)) l = true then 1 else 0) : ℕ) =
        1 + (if l = (z : Fin L) then 1 else 0) := by
      intro z
      have hz := (hY z.1 z.2).1
      by_cases hl : l = (z : Fin L)
      · subst hl; simp [v, indicator, neg, hz]
      · by_cases hlY : l ∈ Y z.1 z.2 <;> simp [v, indicator, neg, hl, hlY]
    rw [Finset.sum_congr rfl (fun z _ => hterm z), Finset.sum_add_distrib]
    rw [Finset.sum_coe_sort Z (fun z => if l = z then 1 else 0), Finset.sum_ite_eq]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, hZ, smul_eq_mul, mul_one]
    by_cases hlZ : l ∈ Z <;> simp [v, indicator, neg, hlZ])
  simp only [Ham, Set.mem_setOf_eq, Set.mem_Iic] at key
  rw [hw_equiv e] at key
  simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Fintype.sum_bool, Finset.univ_unique, Finset.sum_singleton] at key
  have h1 : ∀ z : Z, f (v (Sum.inl (z, true))) = true := fun z => by
    simp only [v, Sum.elim_inl, if_true]; exact (hY z.1 z.2).2.2
  have h2 : ∀ z : Z, f (v (Sum.inl (z, false))) = true := fun z => by
    simp only [v, Sum.elim_inl, Bool.false_eq_true, if_false]
    rw [neg_of_folded hfold, (hY z.1 z.2).2.1]; rfl
  simp only [h1, h2, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_coe, hZ,
    smul_eq_mul, mul_one] at key
  have h3 : f (v (Sum.inr ())) = !f (indicator Z) := by
    simp only [v, Sum.elim_inr]; exact neg_of_folded hfold _
  rw [h3] at key
  cases hfz : f (indicator Z)
  · simp [hfz] at key; omega
  · rfl

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem solution {L m : ℕ} (f : (Fin L → Bool) → Bool) (hfold : IsFolded f)
    (hpol : PolOf (Ham (2 * m + 1) {m + 1}) (Ham (2 * m + 1) (Set.Iic (2 * m))) f)
    (Z : Finset (Fin L)) (hZ : Z.card = m)
    (hwit : ∀ j ∈ Z, ∃ Y : Finset (Fin L), j ∉ Y ∧ f (indicator Y) = false ∧
      f (indicator (insert j Y)) = true) :
    f (indicator Z) = true :=
  SymBoolPCSP.CFixing.subset_true_of_relax_maj f hfold hpol Z hZ hwit
