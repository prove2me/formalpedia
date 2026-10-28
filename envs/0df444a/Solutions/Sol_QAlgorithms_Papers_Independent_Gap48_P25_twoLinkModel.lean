-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P25.twoLinkModel
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T23:24:17.367523+00:00
-- url     : https://prove2.me/submissions/b62c1246-80fc-4787-8b5a-4f38ef96aec5

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P25

open QAlgorithms.Papers.Independent.Gap48.P25
noncomputable section


open scoped BigOperators ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

/-- Eq.(B2), PDF pp.46–47: exact-footnote-mean version of the mean-cutoff toy
rate. The printed rare-success approximation for tau is replaced by the exact
footnote-75 mean, since x=1 takes one round. The separate limit preserves the
printed 3/2 approximation; the lifetime test remains a strict cutoff on the mean. -/
theorem solution (ell c t eta : ℝ) (N : ℕ) (life pM etaM : ℝ)
    (hell : 0 < ell) (hc : 0 < c) (ht : 0 < t ∧ t ≤ 1)
    (heta : 0 < eta ∧ eta ≤ 1) (hN : 0 < N) (hlife : 0 < life)
    (hpM : pM ∈ Set.Icc (0 : ℝ) 1) (hetaM : etaM ∈ Set.Icc (0 : ℝ) 1) :
    let x := modeSuccess t eta N
    let tau := cycleTime ell c t eta N
    0 < x ∧ x ≤ 1 ∧ 0 < tau ∧ tau = (ell/c)*(3-2*x)/(x*(2-x)) ∧
    (tau < life → repeaterRate ell c t eta N life pM etaM = tau⁻¹*(pM^2*etaM^2/2)) ∧
    (life ≤ tau → repeaterRate ell c t eta N life pM etaM = 0) ∧
    Tendsto (fun z : ℝ => ((ell/c)*waitingMean (1-(1-z)^N))*((N : ℝ)*z)/(ell/c))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (3/2)) := by
  intro x tau
  set u := Real.sqrt t * eta with hu
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.2 ht.1
  have hs1 : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr ht.2
  have hu0 : 0 < u := mul_pos hs0 heta.1
  have hu1 : u ≤ 1 := mul_le_one₀ hs1 heta.1.le heta.2
  have hx : x = 1 - (1-u)^N := rfl
  have hp1 : (1-u)^N < 1 := pow_lt_one₀ (by linarith) (by linarith) (by omega)
  have hp0 : 0 ≤ (1-u)^N := pow_nonneg (by linarith) _
  have hxpos : 0 < x := by rw [hx]; linarith
  have hxle : x ≤ 1 := by rw [hx]; linarith
  have htau : tau = (ell/c)*(3-2*x)/(x*(2-x)) := by
    simp only [tau, cycleTime, waitingMean]; ring
  have h3 : 0 < 3 - 2*x := by linarith
  have h2 : 0 < 2 - x := by linarith
  have htpos : 0 < tau := by
    rw [htau]; exact div_pos (mul_pos (div_pos hell hc) h3) (mul_pos hxpos h2)
  refine ⟨hxpos, hxle, htpos, htau, fun h => ?_, fun h => ?_, ?_⟩
  · unfold repeaterRate; exact if_pos h
  · unfold repeaterRate; exact if_neg (not_lt.mpr h)
  · -- limit
    set X : ℝ → ℝ := fun z => 1 - (1-z)^N with hX
    have hEq : (fun z : ℝ => ((ell/c)*waitingMean (1-(1-z)^N))*((N : ℝ)*z)/(ell/c)) =
        fun z => (3-2*X z)/(2-X z) * ((N:ℝ) / (z⁻¹ * X z)) := by
      funext z
      have hec : ell/c ≠ 0 := (div_pos hell hc).ne'
      simp only [waitingMean, X]
      have key : ∀ A y : ℝ, ell/c * A * y / (ell/c) = A*y := fun A y => by field_simp
      rw [key]
      simp only [div_eq_mul_inv]; rw [mul_inv, mul_inv, inv_inv]
      ring
    rw [hEq]
    have hX0 : X 0 = 0 := by simp [X, zero_pow (show N ≠ 0 by omega)]
    have hd : HasDerivAt X (N:ℝ) 0 := by
      have := ((hasDerivAt_id (0:ℝ)).const_sub 1).pow N
      have h2 := this.const_sub 1
      convert h2 using 1 <;> first | rfl | simp
    have hslope := (hasDerivAt_iff_tendsto_slope_zero.1 hd)
    simp only [zero_add, hX0, sub_zero, smul_eq_mul] at hslope
    have hsl' : Tendsto (fun z => z⁻¹ * X z) (nhdsWithin 0 (Set.Ioi 0)) (nhds (N:ℝ)) :=
      hslope.mono_left (nhdsWithin_mono _ (fun z hz => ne_of_gt hz))
    have hNz : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hq : Tendsto (fun z => (N:ℝ) / (z⁻¹ * X z)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
      have := (tendsto_const_nhds (x := (N:ℝ))).div hsl' hNz
      rwa [div_self hNz] at this
    have hXc : Tendsto X (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have := hd.continuousAt.tendsto; rw [hX0] at this; exact this.mono_left nhdsWithin_le_nhds
    have hr : Tendsto (fun z => (3-2*X z)/(2-X z)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (3/2)) := by
      have := ((tendsto_const_nhds (x := (3:ℝ))).sub (hXc.const_mul 2)).div
        ((tendsto_const_nhds (x := (2:ℝ))).sub hXc) (by norm_num)
      rw [show (3:ℝ)/2 = (3 - 2*0)/(2-0) by norm_num]; exact this
    have := hr.mul hq
    simpa using this




