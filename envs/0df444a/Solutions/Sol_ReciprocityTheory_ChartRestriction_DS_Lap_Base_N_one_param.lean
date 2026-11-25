-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.one_param
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:20:20.204911+00:00
-- url     : https://prove2.me/submissions/0d9d7034-12b1-41a0-98e7-2d3b2743ac39

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_LaplaceFoundations_OneParameterSubgroups_OneParam
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_ode_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Filter Topology
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Base ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
theorem _root_.solution {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (w : H) (hw : ‖w‖ = 1) (φ : V →ₗ[ℂ] H) (d : V →ₗ[ℂ] ℂ) (st : V → V)
    {C Cd Cs K T : ℝ} (hC : 0 ≤ C) (hCd : 0 ≤ Cd) (hCs : 0 ≤ Cs) (hK : 0 ≤ K) (hT : 1 ≤ T)
    (hd : ∀ X, ‖d X‖ ≤ Cd * ‖X‖) (hst : ∀ X, ‖st X‖ ≤ Cs * ‖X‖)
    (hstadd : ∀ X X', st (X + X') = st X + st X') (hdst : ∀ X, d (st X) = starRingEnd ℂ (d X))
    (Yl Yp Ym ρ1 : V) (ρ : ℝ → V) (him : (d Yl).re = 0)
    (hρ : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖ρ τ - Ym - (τ : ℂ) • ρ1‖ ≤ K * τ ^ 2)
    (ha : ‖φ Yp‖ ≤ C) (ha' : ‖φ (st Ym)‖ ≤ C) (hc : ‖φ Yl - ((T : ℂ) * d Yl) • w‖ ≤ C)
    (hall : ∀ X, ‖φ X - ((T : ℂ) * d X) • w‖ ≤ C * Real.sqrt T * ‖X‖)
    (u : ℝ → H →L[ℂ] H) (hu : ∀ s v, ‖u s v‖ = ‖v‖) (hu0 : u 0 w = w)
    (hder : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun s => ⟪w, u s w⟫_ℂ)
      ⟪w, u s (φ ((((Real.sqrt T)⁻¹ : ℝ) : ℂ) • (Yl + Yp + Ym)))⟫_ℂ s)
    (hmove : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ⟪w, u s (φ Ym)⟫_ℂ = ⟪φ (st (ρ (s / Real.sqrt T))), u s w⟫_ℂ) :
    ‖⟪w, u 1 w⟫_ℂ * cexp (-((Real.sqrt T : ℂ) * d Yl)) - cexp (d ρ1 / 2)‖ ≤
      (3 * C + C * Cs * ‖ρ1‖ + Cd * K + C * Cs * K) / Real.sqrt T * Real.exp ‖d ρ1‖ := by
  have hsT : 1 ≤ Real.sqrt T := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hT
  have hsT0 : 0 < Real.sqrt T := by linarith
  have hTs : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt (by linarith)
  have hw2 : ⟪w, w⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hw]; simp
  have hin : ∀ s (v : H), ‖⟪w, u s v⟫_ℂ‖ ≤ ‖v‖ := fun s v =>
    (norm_inner_le_norm _ _).trans (by rw [hu, hw, one_mul])
  have hin' : ∀ s (v : H), ‖⟪v, u s w⟫_ℂ‖ ≤ ‖v‖ := fun s v =>
    (norm_inner_le_norm _ _).trans (by rw [hu, hw, mul_one])
  have hU1 : ∀ s, ‖⟪w, u s w⟫_ℂ‖ ≤ 1 := fun s => (hin s w).trans hw.le
  refine ode_bound (δ := (3 * C + C * Cs * ‖ρ1‖ + Cd * K + C * Cs * K) / Real.sqrt T)
    (fun s => ⟪w, u s w⟫_ℂ)
    (fun s => ⟪w, u s (φ ((((Real.sqrt T)⁻¹ : ℝ) : ℂ) • (Yl + Yp + Ym)))⟫_ℂ)
    ((Real.sqrt T : ℂ) * d Yl) (d ρ1) ?_ ?_ hder ?_
  · simp [him]
  · show ⟪w, u 0 w⟫_ℂ = 1
    rw [hu0, hw2]
  intro s hs
  have hm := hmove s hs
  obtain ⟨hs0, hs1⟩ := hs
  set c : ℝ := (Real.sqrt T)⁻¹ with hc_def
  have hc0 : 0 < c := inv_pos.mpr hsT0
  have hcs : c * Real.sqrt T = 1 := inv_mul_cancel₀ hsT0.ne'
  have hτ0 : 0 ≤ s / Real.sqrt T := div_nonneg hs0 hsT0.le
  have hτ1 : s / Real.sqrt T ≤ 1 := (div_le_one hsT0).mpr (hs1.trans hsT)
  have hτc : s / Real.sqrt T = s * c := by rw [hc_def, div_eq_mul_inv]
  set τ := s / Real.sqrt T with hτ
  have he₂ := hρ τ ⟨hτ0, hτ1⟩
  set e₂ := ρ τ - Ym - (τ : ℂ) • ρ1 with he₂_def
  set X := ρ τ - Ym with hX
  have hXe : X = (τ : ℂ) • ρ1 + e₂ := by rw [he₂_def]; abel
  have hstρ : st (ρ τ) = st Ym + st X := by rw [← hstadd, hX]; congr 1; abel
  have hdX : d X = (τ : ℂ) * d ρ1 + d e₂ := by rw [hXe, map_add, map_smul, smul_eq_mul]
  have e1 : φ Yl = ((T : ℂ) * d Yl) • w + (φ Yl - ((T : ℂ) * d Yl) • w) := by abel
  have e3 : φ (st X) = ((T : ℂ) * d (st X)) • w + (φ (st X) - ((T : ℂ) * d (st X)) • w) := by abel
  have he3 := hall (st X)
  set E1 := φ Yl - ((T : ℂ) * d Yl) • w with hE1
  set E3 := φ (st X) - ((T : ℂ) * d (st X)) • w with hE3
  have h1r : c * T = Real.sqrt T := by
    calc c * T = c * (Real.sqrt T * Real.sqrt T) := by rw [hTs]
      _ = (c * Real.sqrt T) * Real.sqrt T := by ring
      _ = Real.sqrt T := by rw [hcs, one_mul]
  have h2r : c * T * τ = s := by
    rw [h1r, hτc]
    calc Real.sqrt T * (s * c) = s * (c * Real.sqrt T) := by ring
      _ = s := by rw [hcs, mul_one]
  have h1 : (c : ℂ) * (T : ℂ) = (Real.sqrt T : ℂ) := by exact_mod_cast h1r
  have h2 : (c : ℂ) * (T : ℂ) * (τ : ℂ) = (s : ℂ) := by exact_mod_cast h2r
  have hmain : ⟪w, u s (φ ((c : ℂ) • (Yl + Yp + Ym)))⟫_ℂ
      - ((Real.sqrt T : ℂ) * d Yl + (s : ℂ) * d ρ1) * ⟪w, u s w⟫_ℂ
      = (c : ℂ) * ⟪w, u s E1⟫_ℂ + (c : ℂ) * ⟪w, u s (φ Yp)⟫_ℂ + (c : ℂ) * ⟪φ (st Ym), u s w⟫_ℂ
        + (c : ℂ) * T * d e₂ * ⟪w, u s w⟫_ℂ + (c : ℂ) * ⟪E3, u s w⟫_ℂ := by
    simp only [map_smul, map_add, inner_smul_right, inner_add_right]
    rw [hm, hstρ, map_add, inner_add_left, e1, e3]
    simp only [map_add, map_smul, inner_add_right, inner_smul_right, inner_add_left, inner_smul_left,
      hdst, map_mul, Complex.conj_ofReal, Complex.conj_conj, RCLike.conj_conj, hdX]
    linear_combination (d Yl * ⟪w, u s w⟫_ℂ) * h1 + (d ρ1 * ⟪w, u s w⟫_ℂ) * h2
  rw [hmain]
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hcn : ‖(c : ℂ)‖ = c := Complex.norm_of_nonneg hc0.le
  have b1 : ‖(c : ℂ) * ⟪w, u s E1⟫_ℂ‖ ≤ c * C := by
    rw [norm_mul, hcn]; exact mul_le_mul_of_nonneg_left ((hin s E1).trans hc) hc0.le
  have b2 : ‖(c : ℂ) * ⟪w, u s (φ Yp)⟫_ℂ‖ ≤ c * C := by
    rw [norm_mul, hcn]; exact mul_le_mul_of_nonneg_left ((hin s _).trans ha) hc0.le
  have b3 : ‖(c : ℂ) * ⟪φ (st Ym), u s w⟫_ℂ‖ ≤ c * C := by
    rw [norm_mul, hcn]; exact mul_le_mul_of_nonneg_left ((hin' s _).trans ha') hc0.le
  have hτs : τ = s * c := hτc
  have hTτ : T * τ ^ 2 ≤ 1 := by
    have e : T * τ ^ 2 = s ^ 2 := by
      rw [hτs, ← hTs]
      calc Real.sqrt T * Real.sqrt T * (s * c) ^ 2 = s ^ 2 * (c * Real.sqrt T) ^ 2 := by ring
        _ = s ^ 2 := by rw [hcs, one_pow, mul_one]
    rw [e]; nlinarith
  have hde2 : ‖d e₂‖ ≤ Cd * (K * τ ^ 2) := (hd e₂).trans (mul_le_mul_of_nonneg_left he₂ hCd)
  have b4 : ‖(c : ℂ) * T * d e₂ * ⟪w, u s w⟫_ℂ‖ ≤ c * (Cd * K) := by
    rw [norm_mul, norm_mul, norm_mul, hcn, Complex.norm_of_nonneg hT0]
    calc c * T * ‖d e₂‖ * ‖⟪w, u s w⟫_ℂ‖ ≤ c * T * (Cd * (K * τ ^ 2)) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hde2 (mul_nonneg hc0.le hT0)) (hU1 s)
            (norm_nonneg _) (mul_nonneg (mul_nonneg hc0.le hT0) (mul_nonneg hCd (mul_nonneg hK (sq_nonneg τ))))
      _ = c * (Cd * K) * (T * τ ^ 2) := by ring
      _ ≤ c * (Cd * K) * 1 := mul_le_mul_of_nonneg_left hTτ (mul_nonneg hc0.le (mul_nonneg hCd hK))
      _ = c * (Cd * K) := mul_one _
  have hXb : ‖X‖ ≤ τ * ‖ρ1‖ + K * τ ^ 2 := by
    rw [hXe]
    calc ‖(τ : ℂ) • ρ1 + e₂‖ ≤ ‖(τ : ℂ) • ρ1‖ + ‖e₂‖ := norm_add_le _ _
      _ ≤ τ * ‖ρ1‖ + K * τ ^ 2 := by
        rw [norm_smul, Complex.norm_of_nonneg hτ0]; linarith
  have hc1 : c ≤ 1 := by rw [hc_def]; exact inv_le_one_of_one_le₀ hsT
  have hτc' : τ ≤ c := by rw [hτs]; nlinarith
  have hτ2 : τ ^ 2 ≤ c := by nlinarith
  have b5 : ‖(c : ℂ) * ⟪E3, u s w⟫_ℂ‖ ≤ C * Cs * (c * ‖ρ1‖ + K * c) := by
    rw [norm_mul, hcn]
    calc c * ‖⟪E3, u s w⟫_ℂ‖ ≤ c * (C * Real.sqrt T * (Cs * (τ * ‖ρ1‖ + K * τ ^ 2))) := by
          apply mul_le_mul_of_nonneg_left _ hc0.le
          refine (hin' s E3).trans (he3.trans ?_)
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hsT0.le)
          exact (hst X).trans (mul_le_mul_of_nonneg_left hXb hCs)
      _ = C * Cs * (τ * ‖ρ1‖ + K * τ ^ 2) * (c * Real.sqrt T) := by ring
      _ = C * Cs * (τ * ‖ρ1‖ + K * τ ^ 2) := by rw [hcs, mul_one]
      _ ≤ C * Cs * (c * ‖ρ1‖ + K * c) := by
          have q1 := mul_le_mul_of_nonneg_right hτc' (norm_nonneg ρ1)
          have q2 := mul_le_mul_of_nonneg_left hτ2 hK
          have q3 : τ * ‖ρ1‖ + K * τ ^ 2 ≤ c * ‖ρ1‖ + K * c := add_le_add q1 q2
          exact mul_le_mul_of_nonneg_left q3 (mul_nonneg hC hCs)
  have n4 := norm_add_le ((c : ℂ) * ⟪w, u s E1⟫_ℂ + (c : ℂ) * ⟪w, u s (φ Yp)⟫_ℂ
    + (c : ℂ) * ⟪φ (st Ym), u s w⟫_ℂ + (c : ℂ) * T * d e₂ * ⟪w, u s w⟫_ℂ) ((c : ℂ) * ⟪E3, u s w⟫_ℂ)
  have n3 := norm_add_le ((c : ℂ) * ⟪w, u s E1⟫_ℂ + (c : ℂ) * ⟪w, u s (φ Yp)⟫_ℂ
    + (c : ℂ) * ⟪φ (st Ym), u s w⟫_ℂ) ((c : ℂ) * T * d e₂ * ⟪w, u s w⟫_ℂ)
  have n2 := norm_add_le ((c : ℂ) * ⟪w, u s E1⟫_ℂ + (c : ℂ) * ⟪w, u s (φ Yp)⟫_ℂ)
    ((c : ℂ) * ⟪φ (st Ym), u s w⟫_ℂ)
  have n1 := norm_add_le ((c : ℂ) * ⟪w, u s E1⟫_ℂ) ((c : ℂ) * ⟪w, u s (φ Yp)⟫_ℂ)
  have hR : c * C + c * C + c * C + c * (Cd * K) + C * Cs * (c * ‖ρ1‖ + K * c)
      = (3 * C + C * Cs * ‖ρ1‖ + Cd * K + C * Cs * K) * c := by ring
  rw [div_eq_mul_inv, ← hc_def]
  linarith [n1, n2, n3, n4, b1, b2, b3, b4, b5, hR]
end ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
