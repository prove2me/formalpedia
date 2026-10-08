-- Prove2me | solution 1 for RevShareCoord.Competing.wholesale_foc_marginal_cost
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T05:58:00.154097+00:00
-- url     : https://prove2.me/submissions/02100630-8271-40f9-b7c5-abb2dfbeed37

import Mathlib
import Definitions.Def_RevShareCoord_Competing_Game
import Definitions.Def_RevShareCoord_Competing_Model



namespace RevShareCoord.Competing

open Finset

lemma rs_concave_tangent {f : ℝ → ℝ} {x d : ℝ} (hc : ConcaveOn ℝ (Set.Ici 0) f) (hx : 0 ≤ x)
    (hd : HasDerivAt f d x) (y : ℝ) (hy : 0 ≤ y) : f y ≤ f x + d * (y - x) := by
  rcases lt_trichotomy y x with h | h | h
  · have := hc.le_slope_of_hasDerivAt (Set.mem_Ici.mpr hy) (Set.mem_Ici.mpr hx) h hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    linarith
  · subst h; simp
  · have := hc.slope_le_of_hasDerivAt (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr hy) h hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    linarith

lemma rs_profit_update {n : ℕ} (R : Fin n → (Fin n → ℝ) → ℝ) (φ : ℝ) (w q : Fin n → ℝ)
    (i : Fin n) (x : ℝ) :
    retailerProfit R φ w (Function.update q i x) i = φ * R i (Function.update q i x) - w i * x := by
  simp [retailerProfit]

/-- FOC at an interior Nash equilibrium. -/
lemma rs_foc_core {n : ℕ} (M : Model n) (φ : ℝ) (w : Fin n → ℝ) (qN : Fin n → ℝ)
    (hN : IsNashEquilibrium M.R φ w qN) (hpos : ∀ i, 0 < qN i) :
    ∀ i, φ * M.dR i i qN = w i := by
  intro i
  set g : ℝ → ℝ := fun t => φ * M.R i (Function.update qN i t) - w i * t with hg
  have hd : HasDerivAt g (φ * M.dR i i qN - w i * 1) (qN i) := by
    have h1 := (M.hasPartial qN hpos i i).const_mul φ
    exact h1.sub ((hasDerivAt_id (qN i)).const_mul (w i))
  have hmax : IsLocalMax g (qN i) := by
    have : Set.Ioi (0:ℝ) ∈ nhds (qN i) := Ioi_mem_nhds (hpos i)
    filter_upwards [this] with x hx
    have := hN.2 i x (le_of_lt hx)
    rw [rs_profit_update] at this
    have e : retailerProfit M.R φ w qN i = g (qN i) := by
      simp [hg, retailerProfit]
    simpa [hg, e] using this
  have := hmax.hasDerivAt_eq_zero hd
  linarith

theorem revenue_sharing_equilibrium_foc_core {n : ℕ} (M : Model n) (φ : ℝ)
    (_hφ0 : 0 ≤ φ) (_hφ1 : φ ≤ 1) (w : Fin n → ℝ) (qN : Fin n → ℝ)
    (hN : IsNashEquilibrium M.R φ w qN) (hpos : ∀ i, 0 < qN i) :
    ∀ i, φ * M.dR i i qN = w i := rs_foc_core M φ w qN hN hpos

theorem wholesale_foc_marginal_cost_core {n : ℕ} (M : Model n) :
    (∀ (w : Fin n → ℝ) (qN : Fin n → ℝ), (∀ i, 0 < w i) →
        IsNashEquilibrium M.R 1 w qN → (∀ i, 0 < qN i) → ∀ i, M.dR i i qN = w i) ∧
    (∀ qI : Fin n → ℝ, (∀ i, 0 < qI i) → M.FOC qI →
        ∀ i, ∑ j ∈ univ.erase i, M.dR i j qI < 0 →
          M.c < M.dR i i qI ∧ ¬ IsNashEquilibrium M.R 1 (fun _ => M.c) qI) := by
  refine ⟨fun w qN _ hN hpos i => by simpa using rs_foc_core M 1 w qN hN hpos i, ?_⟩
  intro qI hpos hfoc i hneg
  have h1 := hfoc i
  refine ⟨by linarith, fun hN => ?_⟩
  have := rs_foc_core M 1 _ qI hN hpos i
  simp at this
  linarith

theorem coordinating_wholesale_nash_core {n : ℕ} (M : Model n) (qI : Fin n → ℝ)
    (hpos : ∀ i, 0 < qI i) (hfoc : M.FOC qI) :
    IsNashEquilibrium M.R 1 (M.wI qI) qI := by
  refine ⟨fun i => le_of_lt (hpos i), fun i x hx => ?_⟩
  rw [rs_profit_update]
  have hc := M.concave_own i qI (fun k => le_of_lt (hpos k))
  have ht := rs_concave_tangent hc (le_of_lt (hpos i)) (M.hasPartial qI hpos i i) x hx
  have hw : M.wI qI i = M.dR i i qI := by
    have := hfoc i; simp only [Model.wI]; linarith
  have e : M.R i (Function.update qI i (qI i)) = M.R i qI := by simp
  rw [e] at ht
  simp only [retailerProfit, hw]
  nlinarith

theorem revenue_sharing_nash_coordinates_core {n : ℕ} (M : Model n) (qI : Fin n → ℝ)
    (hpos : ∀ i, 0 < qI i) (hfoc : M.FOC qI) (φ : ℝ) (hφ0 : 0 ≤ φ) (_hφ1 : φ ≤ 1) :
    IsNashEquilibrium M.R φ (fun k => φ * M.wI qI k) qI ∧
      (∀ i, retailerProfit M.R φ (fun k => φ * M.wI qI k) qI i =
        φ * retailerProfit M.R 1 (M.wI qI) qI i) ∧
      supplierProfit M.R M.c φ (fun k => φ * M.wI qI k) qI =
        (1 - φ) * systemProfit M.R M.c qI + φ * supplierProfit M.R M.c 1 (M.wI qI) qI := by
  have hN := coordinating_wholesale_nash_core M qI hpos hfoc
  refine ⟨⟨hN.1, fun i x hx => ?_⟩, fun i => ?_, ?_⟩
  · have h := hN.2 i x hx
    have e1 : retailerProfit M.R φ (fun k => φ * M.wI qI k) (Function.update qI i x) i =
        φ * retailerProfit M.R 1 (M.wI qI) (Function.update qI i x) i := by
      simp only [retailerProfit]; ring
    have e2 : retailerProfit M.R φ (fun k => φ * M.wI qI k) qI i =
        φ * retailerProfit M.R 1 (M.wI qI) qI i := by
      simp only [retailerProfit]; ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left h hφ0
  · simp only [retailerProfit]; ring
  · simp only [supplierProfit, systemProfit, sub_self, zero_mul, zero_add, Finset.sum_add_distrib]
    have e2 : ∑ x, (1 - φ) * M.R x qI = (1 - φ) * ∑ x, M.R x qI := by rw [Finset.mul_sum]
    have e3 : ∑ x, φ * M.wI qI x * qI x = φ * ∑ x, M.wI qI x * qI x := by
      rw [Finset.mul_sum]; simp only [mul_assoc]
    rw [e2, e3]
    ring

theorem wI_above_cost_core {n : ℕ} (M : Model n) (qI : Fin n → ℝ)
    (hsub : ∀ i j, j ≠ i → M.dR i j qI ≤ 0) :
    (∀ i, M.c ≤ M.wI qI i) ∧
      ∀ i, (∃ j, j ≠ i ∧ M.dR i j qI < 0) → M.c < M.wI qI i := by
  refine ⟨fun i => ?_, fun i ⟨j, hji, hj⟩ => ?_⟩
  · have : ∑ j ∈ univ.erase i, M.dR i j qI ≤ 0 :=
      Finset.sum_nonpos (fun j hj => hsub i j (Finset.ne_of_mem_erase hj))
    simp only [Model.wI]; linarith
  · have : ∑ j ∈ univ.erase i, M.dR i j qI < ∑ j ∈ univ.erase i, (0:ℝ) :=
      Finset.sum_lt_sum (fun j hj => hsub i j (Finset.ne_of_mem_erase hj))
        ⟨j, Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩, hj⟩
    simp only [Finset.sum_const_zero] at this
    simp only [Model.wI]; linarith

theorem profit_split_wI_core {n : ℕ} (M : Model n) (qI : Fin n → ℝ) :
    supplierProfit M.R M.c 1 (M.wI qI) qI =
        ∑ i, qI i * ∑ j ∈ univ.erase i, (-M.dR i j qI) ∧
      ∀ i, retailerProfit M.R 1 (M.wI qI) qI i = M.R i qI - qI i * M.wI qI i := by
  refine ⟨?_, fun i => by simp only [retailerProfit]; ring⟩
  simp only [supplierProfit, sub_self, zero_mul, zero_add, Model.wI, Finset.mul_sum,
    ← Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

theorem retailer_participation_core {n : ℕ} (M : Model n) (qI : Fin n → ℝ)
    (hpos : ∀ i, 0 < qI i) (hfoc : M.FOC qI)
    (hzero : ∀ i, 0 ≤ M.R i (Function.update qI i 0)) :
    ∀ i, 0 ≤ retailerProfit M.R 1 (M.wI qI) qI i := by
  intro i
  have h := (coordinating_wholesale_nash_core M qI hpos hfoc).2 i 0 le_rfl
  rw [rs_profit_update] at h
  have := hzero i
  linarith

end RevShareCoord.Competing

open RevShareCoord.Competing
open Finset

theorem solution {n : ℕ} (M : Model n) :
    (∀ (w : Fin n → ℝ) (qN : Fin n → ℝ), (∀ i, 0 < w i) →
        IsNashEquilibrium M.R 1 w qN → (∀ i, 0 < qN i) → ∀ i, M.dR i i qN = w i) ∧
    (∀ qI : Fin n → ℝ, (∀ i, 0 < qI i) → M.FOC qI →
        ∀ i, ∑ j ∈ univ.erase i, M.dR i j qI < 0 →
          M.c < M.dR i i qI ∧ ¬ IsNashEquilibrium M.R 1 (fun _ => M.c) qI) := by
  exact wholesale_foc_marginal_cost_core M
