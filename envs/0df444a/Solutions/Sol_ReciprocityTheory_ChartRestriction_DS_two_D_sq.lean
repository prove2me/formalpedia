-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.two_D_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:57:25.60709+00:00
-- url     : https://prove2.me/submissions/60375288-dfac-4c50-b56f-5754a75866ee

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARSqB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CsqDdPt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_dd_add
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_dOp__sq_f46c3f4a63d1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_casimirK_diagE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_casimirK_sgE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_dOp_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
private theorem sum_sum_ne_eps_eq_plusIdx_minusIdx_add (ε : Fin n → Bool) {R : Type*} [AddCommMonoid R] (f : Fin n → Fin n → R) :
    ∑ a, ∑ b ∈ univ.filter (fun b => ¬ ε b = ε a), f a b =
      ∑ x ∈ plusIdx ε, ∑ y ∈ minusIdx ε, f x y + ∑ a ∈ minusIdx ε, ∑ b ∈ plusIdx ε, f a b := by
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun a => ε a = true)]
  have hm : univ.filter (fun a => ¬ ε a = true) = minusIdx ε := by
    ext a; simp [minusIdx]
  rw [hm]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Finset.sum_congr rfl fun a ha => ?_
    have ha' : ε a = true := (Finset.mem_filter.mp ha).2
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext b; simp [minusIdx, ha']
  · refine Finset.sum_congr rfl fun a ha => ?_
    have ha' : ε a = false := (Finset.mem_filter.mp ha).2
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext b; simp [plusIdx, ha']
end ReciprocityTheory.ChartRestriction.DS
end
end

set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E) (hC : IsCAR cp cm)
    (hEC : CommutesCAR E cp cm) (ε : Fin n → Bool) :
    (2 : ℂ) • ((dOp ε E cp + dOp' ε E cm) * (dOp ε E cp + dOp' ε E cm)) =
      -casimir E + casimirK ε (diagE ε E cp cm) -
        (2 : ℂ) • ∑ a, ((rhoHol ε a : ℝ) : ℂ) • diagE ε E cp cm a a := by
  have hsq : (dOp ε E cp + dOp' ε E cm) * (dOp ε E cp + dOp' ε E cm) =
      dOp ε E cp * dOp' ε E cm + dOp' ε E cm * dOp ε E cp := by
    rw [add_mul, mul_add, mul_add, dOp_sq hE hC hEC, dOp'_sq hE hC hEC]
    abel
  have hs : ∑ a, ∑ b ∈ univ.filter (fun b => ¬ ε b = ε a), E a b * E b a =
      ∑ x ∈ plusIdx ε, ∑ y ∈ minusIdx ε, E x y * E y x +
        ∑ a ∈ minusIdx ε, ∑ b ∈ plusIdx ε, E a b * E b a :=
    sum_sum_ne_eps_eq_plusIdx_minusIdx_add ε (fun a b => E a b * E b a)
  have hoff : casimir E = casimirK ε E +
      (∑ x ∈ plusIdx ε, ∑ y ∈ minusIdx ε, E x y * E y x +
        ∑ a ∈ minusIdx ε, ∑ b ∈ plusIdx ε, E a b * E b a) := by
    rw [← hs]
    unfold casimir casimirK
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have h1 : ∀ a i : Fin n, E a i * E i a = E i a * E a i + (E a a - E i i) := by
    intro a i
    have h := hE a i i a
    rw [if_pos rfl, if_pos rfl] at h
    rw [← h]
    abel
  have hcomm2 : ∑ a ∈ minusIdx ε, ∑ i ∈ plusIdx ε, E a i * E i a =
      ∑ x ∈ plusIdx ε, ∑ y ∈ minusIdx ε, E x y * E y x +
        (((plusIdx ε).card : ℂ) • ∑ a ∈ minusIdx ε, E a a -
          ((minusIdx ε).card : ℂ) • ∑ i ∈ plusIdx ε, E i i) := by
    rw [show ∑ a ∈ minusIdx ε, ∑ i ∈ plusIdx ε, E a i * E i a =
        ∑ a ∈ minusIdx ε, ∑ i ∈ plusIdx ε, (E i a * E a i + (E a a - E i i)) from
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => h1 a i]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    refine congrArg₂ (· + ·) Finset.sum_comm (congrArg₂ (· - ·) ?_ ?_)
    · rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_const, Nat.cast_smul_eq_nsmul]
    · rw [Finset.sum_comm, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_const, Nat.cast_smul_eq_nsmul]
  have hrho : (2 : ℂ) • ∑ a, ((rhoHol ε a : ℝ) : ℂ) • E a a =
      ((minusIdx ε).card : ℂ) • ∑ i ∈ plusIdx ε, E i i -
        ((plusIdx ε).card : ℂ) • ∑ a ∈ minusIdx ε, E a a := by
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun a => ε a = true)]
    have hm : univ.filter (fun a => ¬ ε a = true) = minusIdx ε := by
      ext a; simp [minusIdx]
    rw [hm]
    have e1 : ∑ a ∈ univ.filter (fun a => ε a = true), ((rhoHol ε a : ℝ) : ℂ) • E a a =
        (((minusIdx ε).card : ℂ) / 2) • ∑ i ∈ plusIdx ε, E i i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      have ha' : ε a = true := (Finset.mem_filter.mp ha).2
      rw [show rhoHol ε a = ((minusIdx ε).card : ℝ) / 2 by simp [rhoHol, ha', qOf, minusIdx]]
      push_cast
      rfl
    have e2 : ∑ a ∈ minusIdx ε, ((rhoHol ε a : ℝ) : ℂ) • E a a =
        (-((plusIdx ε).card : ℂ) / 2) • ∑ a ∈ minusIdx ε, E a a := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      have ha' : ε a = false := (Finset.mem_filter.mp ha).2
      rw [show rhoHol ε a = -((plusIdx ε).card : ℝ) / 2 by simp [rhoHol, ha', pOf, plusIdx]]
      push_cast
      rfl
    rw [e1, e2, smul_add, smul_smul, smul_smul, sub_eq_add_neg, ← neg_smul]
    exact congrArg₂ (· + ·) (congrArg (· • _) (by ring)) (congrArg (· • _) (by ring))
  rw [hsq, dd_add hE hC hEC, casimirK_diagE hEC, casimirK_sgE hC, hoff, hcomm2]
  simp only [diagE, smul_add, Finset.sum_add_distrib, smul_neg]
  rw [hrho, two_smul ℂ (∑ x ∈ plusIdx ε, ∑ y ∈ minusIdx ε, E x y * E y x)]
  abel
end ReciprocityTheory.ChartRestriction.DS
