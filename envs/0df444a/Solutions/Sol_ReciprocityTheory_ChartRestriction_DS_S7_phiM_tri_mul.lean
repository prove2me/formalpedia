-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.phiM_tri_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:22:44.116427+00:00
-- url     : https://prove2.me/submissions/00dc9a40-3ea1-4102-9f20-4697835e6f9b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_Minors
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_lead_tri_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
private lemma tele_range (D : ℕ → ℂ) (hD : ∀ l, D l ≠ 0) (m : ℕ → ℤ) (N : ℕ) :
    ∏ i ∈ range N, (∏ l ∈ range (i + 1), D l) ^ (-(m i - m (i + 1))) =
      (∏ l ∈ range N, D l ^ (-m l)) * (∏ l ∈ range N, D l) ^ m N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.prod_range_succ (fun i => (∏ l ∈ range (i + 1), D l) ^ (-(m i - m (i + 1)))) N, ih]
    simp only [Finset.prod_range_succ]
    have hP : (∏ l ∈ range N, D l) ≠ 0 := Finset.prod_ne_zero_iff.2 fun l _ => hD l
    have hPd : (∏ l ∈ range N, D l) * D N ≠ 0 := mul_ne_zero hP (hD N)
    have h1 : ((∏ l ∈ range N, D l) * D N) ^ (-(m N - m (N + 1))) =
        ((∏ l ∈ range N, D l) * D N) ^ (-m N) * ((∏ l ∈ range N, D l) * D N) ^ (m (N + 1)) := by
      rw [← zpow_add₀ hPd]
      congr 1
      ring
    have h2 : ((∏ l ∈ range N, D l) * D N) ^ (-m N) =
        (∏ l ∈ range N, D l) ^ (-m N) * D N ^ (-m N) := mul_zpow _ _ _
    have h3 : (∏ l ∈ range N, D l) ^ m N * (∏ l ∈ range N, D l) ^ (-m N) = 1 := by
      rw [← zpow_add₀ hP, add_neg_cancel, zpow_zero]
    rw [h1, h2]
    linear_combination ((∏ l ∈ range N, D l ^ (-m l)) * D N ^ (-m N) *
      ((∏ l ∈ range N, D l) * D N) ^ m (N + 1)) * h3
private lemma filter_prod_eq_range (d : Fin n → ℂ) (k : ℕ) (hk : k ≤ n) :
    ∏ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < k), d l =
      ∏ j ∈ range k, (if h : j < n then d ⟨j, h⟩ else 1) := by
  have hr : range k = (range n).filter (fun j => j < k) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor <;> intro h <;> omega
  rw [hr]
  simp only [Finset.prod_filter]
  rw [Finset.prod_range]
  refine Finset.prod_congr rfl fun l _ => ?_
  simp [l.2]
private lemma tele_fin (d : Fin n → ℂ) (hd : ∀ l, d l ≠ 0) (μ : Fin n → ℤ) :
    ∏ i : Fin n, (∏ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < (i : ℕ) + 1), d l) ^ (-(μ i - muNext μ i)) =
      ∏ l, d l ^ (-μ l) := by
  set D : ℕ → ℂ := fun j => if h : j < n then d ⟨j, h⟩ else 1 with hDdef
  set m : ℕ → ℤ := fun j => if h : j < n then μ ⟨j, h⟩ else 0 with hmdef
  have hD : ∀ l, D l ≠ 0 := by
    intro l
    simp only [hDdef]
    split_ifs
    · exact hd _
    · exact one_ne_zero
  have h1 : ∀ i : Fin n, (∏ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < (i : ℕ) + 1), d l) ^
      (-(μ i - muNext μ i)) = (∏ l ∈ range ((i : ℕ) + 1), D l) ^ (-(m i - m ((i : ℕ) + 1))) := by
    intro i
    rw [filter_prod_eq_range d _ (by have := i.2; omega)]
    congr 1
    all_goals first | rfl | simp [hmdef, muNext, i.2]
  rw [Finset.prod_congr rfl (fun i _ => h1 i),
    Fin.prod_univ_eq_prod_range (fun i => (∏ l ∈ range (i + 1), D l) ^ (-(m i - m (i + 1)))) n,
    tele_range D hD m n]
  have hmn : m n = 0 := by simp [hmdef]
  rw [hmn, zpow_zero, mul_one, Finset.prod_range (fun l => D l ^ (-m l))]
  refine Finset.prod_congr rfl fun l _ => ?_
  simp [hDdef, hmdef, l.2]
end ReciprocityTheory.ChartRestriction.DS.S7
end
end

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (μ : Fin n → ℤ) {c z c' : Matrix (Fin n) (Fin n) ℂ} (hc : IsLowerTri c) (hc' : IsUpperTri c')
    (hcd : ∀ l, c l l ≠ 0) (hcd' : ∀ l, c' l l ≠ 0) (hz : z ∈ OmegaSet n) :
    c * z * c' ∈ OmegaSet n ∧
      PhiM μ (c * z * c') = (∏ l, (c l l * c' l l) ^ (-μ l)) * PhiM μ z := by
  have hd : ∀ l, c l l * c' l l ≠ 0 := fun l => mul_ne_zero (hcd l) (hcd' l)
  have hlead : ∀ i : Fin n, lead ((i : ℕ) + 1) (c * z * c') =
      (∏ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < (i : ℕ) + 1), c l l * c' l l) * lead ((i : ℕ) + 1) z :=
    fun i => lead_tri_mul hc hc' _ i.isLt
  have hP : ∀ i : Fin n,
      (∏ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < (i : ℕ) + 1), c l l * c' l l) ≠ 0 :=
    fun i => prod_ne_zero_iff.mpr fun l _ => hd l
  refine ⟨fun i => by rw [hlead i]; exact mul_ne_zero (hP i) (hz i), ?_⟩
  have hterm : ∀ i : Fin n, lead ((i : ℕ) + 1) (c * z * c') ^ (-(μ i - muNext μ i)) =
      (∏ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < (i : ℕ) + 1), c l l * c' l l) ^ (-(μ i - muNext μ i)) *
        lead ((i : ℕ) + 1) z ^ (-(μ i - muNext μ i)) := fun i => by rw [hlead i, mul_zpow]
  unfold PhiM
  rw [prod_congr rfl fun i _ => hterm i, prod_mul_distrib,
    tele_fin (fun l => c l l * c' l l) hd μ]
end ReciprocityTheory.ChartRestriction.DS.S7
