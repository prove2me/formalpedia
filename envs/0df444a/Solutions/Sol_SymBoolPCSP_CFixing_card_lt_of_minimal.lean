-- Prove2me | solution 1 for SymBoolPCSP.CFixing.card_lt_of_minimal
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T19:08:36.836253+00:00
-- url     : https://prove2.me/submissions/1c287967-a868-49ff-84de-8237e7d4a0b0

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic
import Theorems.Thm_FinsetParts_exists_parts_card_eq

open PCSPBLPAff.Symmetric Finset
namespace SymBoolPCSP.CFixing

namespace Aux_card_lt_of_minimal

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

end Aux_card_lt_of_minimal

open Aux_card_lt_of_minimal in
/-- Case 2 of BG Lemma 4.12: let `f` be a folded polymorphism of
`(Ham_{b+r}({1, b+r}), Ham_{b+r}({0, …, b+r} \ {b}))` with `b ≥ 1`. If `S` is minimal with
`f(e_S) = 1` (all proper subsets `T ⊂ S` have `f(e_T) = 0`), then `|S| < b`. -/
theorem card_lt_of_minimal {L b r : ℕ} (f : (Fin L → Bool) → Bool) (hfold : IsFolded f)
    (hb : 1 ≤ b)
    (hpol : PolOf (Ham (b + r) {1, b + r}) (Ham (b + r) (Set.Iic (b + r) \ {b})) f)
    (S : Finset (Fin L)) (hS : f (indicator S) = true)
    (hmin : ∀ T ⊂ S, f (indicator T) = false) :
    S.card < b := by
  classical
  by_contra h
  push_neg at h
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  let sz : Fin (b' + 1) → ℕ := Fin.cons (S.card - b') (fun _ => 1)
  have hsum : ∑ i, sz i = S.card := by
    simp only [sz, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    omega
  obtain ⟨T, hTS, hTc, hcov⟩ := FinsetParts.exists_parts_card_eq S sz hsum
  have hne : ∀ i, (T i).Nonempty := by
    intro i
    rw [← Finset.card_pos, hTc i]
    induction i using Fin.cases with
    | zero => simp only [sz, Fin.cons_zero]; omega
    | succ j => simp [sz]
  have hval : ∀ i, f (neg (indicator (S \ T i))) = true := by
    intro i
    rw [neg_of_folded hfold, hmin _ (Finset.sdiff_ssubset (hTS i) (hne i))]; rfl
  have hval2 : f (neg (indicator S)) = false := by
    rw [neg_of_folded hfold, hS]; rfl
  have hcard : Fintype.card (Fin (b' + 1) ⊕ Fin r) = b' + 1 + r := by simp
  let e := Fintype.equivFinOfCardEq hcard
  let v : Fin (b' + 1) ⊕ Fin r → Fin L → Bool :=
    Sum.elim (fun i => neg (indicator (S \ T i))) (fun _ => neg (indicator S))
  have key := hpol (fun l c => v (e.symm c) l) (by
    intro l
    simp only [Ham, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [hw_equiv e]
    simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type]
    by_cases hl : l ∈ S
    · left
      obtain ⟨i0, hi0, huniq⟩ := hcov l hl
      have hA : ∀ i, (if v (Sum.inl i) l = true then 1 else 0 : ℕ) =
          if l ∈ T i then 1 else 0 := fun i => by
        by_cases hli : l ∈ T i <;> simp [v, neg, indicator, hl, hli]
      simp only [hA]
      rw [Finset.sum_eq_single i0 (fun j _ hj => if_neg (fun h' => hj (huniq j h')))
        (by simp), if_pos hi0]
      simp [v, neg, indicator, hl]
    · right
      simp [v, neg, indicator, hl])
  simp only [Ham, Set.mem_setOf_eq, Set.mem_diff, Set.mem_Iic, Set.mem_singleton_iff] at key
  rw [hw_equiv e] at key
  simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, v, Sum.elim_inl, Sum.elim_inr,
    hval, hval2] at key
  simp at key

end SymBoolPCSP.CFixing

open SymBoolPCSP.CFixing in
theorem solution {L b r : ℕ} (f : (Fin L → Bool) → Bool) (hfold : IsFolded f)
    (hb : 1 ≤ b)
    (hpol : PolOf (Ham (b + r) {1, b + r}) (Ham (b + r) (Set.Iic (b + r) \ {b})) f)
    (S : Finset (Fin L)) (hS : f (indicator S) = true)
    (hmin : ∀ T ⊂ S, f (indicator T) = false) :
    S.card < b :=
  SymBoolPCSP.CFixing.card_lt_of_minimal f hfold hb hpol S hS hmin
