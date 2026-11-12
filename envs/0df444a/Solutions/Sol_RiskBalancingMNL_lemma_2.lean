-- Prove2me | solution 1 for RiskBalancingMNL.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T01:38:25.57627+00:00
-- url     : https://prove2.me/submissions/66008563-4f98-4198-85ce-51b3b1153533

import Mathlib
import Definitions.Def_RiskBalancingMNL_Params

open RiskBalancingMNL

private lemma lemma_2_deriv_eq (b t wt lam D q0 : ℝ) (hb : b ≠ 0) (hD : D ≠ 0)
    (hq0 : q0 = 1 / D) (h1 : 1 - q0 - lam ≠ 0) :
    2 * t * wt * (D - 1) * (D - b * t) / D ^ 3 -
        lam * (t * wt * (2 * D - b * t) / D ^ 2) =
      (-2 * b * t * (wt / D) * q0 * (1 - q0 - lam)) *
        (t - 1 / (b * q0) + lam * t / (2 * (1 - q0 - lam))) := by
  have hLHS : 2 * t * wt * (D - 1) * (D - b * t) / D ^ 3 -
      lam * (t * wt * (2 * D - b * t) / D ^ 2) =
      (2 * t * wt * (D - 1) * (D - b * t) -
        lam * (t * wt * (2 * D - b * t)) * D) / D ^ 3 := by
    have hlam_d : lam * (t * wt * (2 * D - b * t) / D ^ 2) =
        (lam * (t * wt * (2 * D - b * t)) * D) / D ^ 3 := by
      rw [← mul_div_assoc, ← mul_div_mul_right _ (D ^ 2) hD,
        show D ^ 2 * D = D ^ 3 by ring]
    rw [hlam_d, ← sub_div]
  have h2bF : (2 * b * (1 - q0 - lam)) *
      (t - 1 / (b * q0) + lam * t / (2 * (1 - q0 - lam))) =
      2 * (1 - q0 - lam) * (b * t - 1 / q0) + b * lam * t := by
    have hb1 : b * (1 / (b * q0)) = 1 / q0 := by
      rw [← mul_div_assoc, mul_div_mul_left 1 q0 hb]
    have h1c : 2 * (1 - q0 - lam) * (lam * t / (2 * (1 - q0 - lam))) = lam * t :=
      mul_div_cancel₀ (lam * t) (mul_ne_zero two_ne_zero h1)
    calc (2 * b * (1 - q0 - lam)) * (t - 1 / (b * q0) + lam * t / (2 * (1 - q0 - lam)))
        = 2 * (1 - q0 - lam) * (b * t - b * (1 / (b * q0))) +
            b * (2 * (1 - q0 - lam) * (lam * t / (2 * (1 - q0 - lam)))) := by ring
      _ = 2 * (1 - q0 - lam) * (b * t - 1 / q0) + b * lam * t := by
            rw [hb1, h1c]
            ring
  have h1D : 1 - 1 / D - lam = (D - 1 - D * lam) / D := by
    rw [eq_div_iff hD, sub_mul, sub_mul, one_mul, div_mul_cancel₀ 1 hD]
    ring
  rw [hLHS]
  symm
  calc (-2 * b * t * (wt / D) * q0 * (1 - q0 - lam)) *
          (t - 1 / (b * q0) + lam * t / (2 * (1 - q0 - lam)))
      = (-t * (wt / D) * q0) *
          ((2 * b * (1 - q0 - lam)) *
            (t - 1 / (b * q0) + lam * t / (2 * (1 - q0 - lam)))) := by ring
    _ = (-t * (wt / D) * (1 / D)) *
          (2 * ((D - 1 - D * lam) / D) * (b * t - D) + b * lam * t) := by
          rw [h2bF, hq0, one_div_one_div, h1D]
    _ = (2 * t * wt * (D - 1) * (D - b * t) -
          lam * (t * wt * (2 * D - b * t)) * D) / D ^ 3 := by
          rw [eq_div_iff (pow_ne_zero 3 hD)]
          calc (-t * (wt / D) * (1 / D)) *
                  (2 * ((D - 1 - D * lam) / D) * (b * t - D) + b * lam * t) * D ^ 3
              = (-t * ((wt / D) * D) * ((1 / D) * D)) *
                  (2 * (((D - 1 - D * lam) / D) * D) * (b * t - D) +
                    b * lam * t * D) := by ring
            _ = (-t * wt * 1) *
                  (2 * (D - 1 - D * lam) * (b * t - D) + b * lam * t * D) := by
                  rw [div_mul_cancel₀ _ hD, div_mul_cancel₀ _ hD, div_mul_cancel₀ _ hD]
            _ = 2 * t * wt * (D - 1) * (D - b * t) -
                  lam * (t * wt * (2 * D - b * t)) * D := by ring

private lemma sq_chain_eq (t wt D b : ℝ) (hD : D ≠ 0) :
    (2 : ℝ) * ((t * wt + t * (D - 1 - wt)) / D) * (wt * (D - b * t) / D ^ 2) =
      2 * t * wt * (D - 1) * (D - b * t) / D ^ 3 := by
  rw [eq_div_iff (pow_ne_zero 3 hD)]
  calc (2 : ℝ) * ((t * wt + t * (D - 1 - wt)) / D) * (wt * (D - b * t) / D ^ 2) * D ^ 3
      = 2 * (((t * wt + t * (D - 1 - wt)) / D) * D) *
          ((wt * (D - b * t) / D ^ 2) * D ^ 2) := by ring
    _ = 2 * (t * wt + t * (D - 1 - wt)) * (wt * (D - b * t)) := by
          rw [div_mul_cancel₀ _ hD, div_mul_cancel₀ _ (pow_ne_zero 2 hD)]
    _ = 2 * t * wt * (D - 1) * (D - b * t) := by ring

theorem solution {n : ℕ} [NeZero n] (P : Params n) (lam t : ℝ) (_hlam0 : 0 ≤ lam) (_hlam1 : lam < 1)
    (ht : 0 < t) (hq : noPurchase P (constM t) ≠ 1 - lam) :
    (∀ j : Fin n,
      HasDerivAt (fun s : ℝ => objective P lam (Function.update (constM t) j s)) 0 t) ↔
    t - 1 / (P.b * noPurchase P (constM t)) +
      lam * t / (2 * (1 - noPurchase P (constM t) - lam)) = 0 := by
  let q0 : ℝ := noPurchase P (constM t)
  let F : ℝ := t - 1 / (P.b * q0) + lam * t / (2 * (1 - q0 - lam))
  have h1_ne : 1 - q0 - lam ≠ 0 := by
    intro h0
    apply hq
    change q0 = 1 - lam
    linarith
  have hattr_pos : ∀ i : Fin n, 0 < attraction P (constM t) i := fun i => Real.exp_pos _
  let D : ℝ := (∑ k, attraction P (constM t) k) + 1
  have hD_pos : 0 < D := by
    have hsum_nonneg : 0 ≤ ∑ k, attraction P (constM t) k :=
      Finset.sum_nonneg fun k _ => (hattr_pos k).le
    dsimp [D]
    linarith
  have hq0_eq : q0 = 1 / D := by
    change 1 / (1 + ∑ k, attraction P (constM t) k) = 1 / ((∑ k, attraction P (constM t) k) + 1)
    rw [add_comm]
  have hq0_pos : 0 < q0 := by
    rw [hq0_eq]
    exact div_pos zero_lt_one hD_pos
  have hderiv_all : ∀ j : Fin n,
      HasDerivAt (fun s : ℝ => objective P lam (Function.update (constM t) j s))
        ((-2 * P.b * t * share P (constM t) j * q0 * (1 - q0 - lam)) * F) t := by
    intro j
    let w : ℝ → ℝ := fun s => Real.exp (P.a j - P.b * P.c j - P.b * s)
    let R : ℝ := ∑ i ∈ Finset.univ.erase j, attraction P (constM t) i
    let Ds : ℝ → ℝ := fun s => w s + R + 1
    have hwt : w t = attraction P (constM t) j := rfl
    have hDt : Ds t = D := by
      dsimp [Ds, R, D]
      rw [hwt, Finset.add_sum_erase Finset.univ (fun i => attraction P (constM t) i)
        (Finset.mem_univ j)]
    have hfun_eq : (fun s : ℝ => objective P lam (Function.update (constM t) j s)) =
        fun s : ℝ => ((s * w s + t * R) / Ds s) ^ 2 -
          lam * ((s ^ 2 * w s + t ^ 2 * R) / Ds s) := by
      ext s
      have hattr_upd_j : attraction P (Function.update (constM t) j s) j = w s := by
        simp [attraction, w]
      have hattr_upd_ne : ∀ i ∈ Finset.univ.erase j,
          attraction P (Function.update (constM t) j s) i = attraction P (constM t) i := by
        intro i hi
        have hij : i ≠ j := Finset.ne_of_mem_erase hi
        simp [attraction, hij]
      have hsum_attr : (∑ k, attraction P (Function.update (constM t) j s) k) + 1 = Ds s := by
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j), hattr_upd_j]
        have herase : ∑ i ∈ Finset.univ.erase j,
            attraction P (Function.update (constM t) j s) i = R :=
          Finset.sum_congr rfl hattr_upd_ne
        rw [herase]
      have hπ : profit P (Function.update (constM t) j s) = (s * w s + t * R) / Ds s := by
        unfold profit share FlagshipMEA.Monopoly.logitShare
        simp_rw [hsum_attr]
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j)]
        simp only [Function.update_self, hattr_upd_j]
        have herase : ∑ i ∈ Finset.univ.erase j,
            Function.update (constM t) j s i *
              (attraction P (Function.update (constM t) j s) i / Ds s) =
            (t * R) / Ds s := by
          trans ∑ i ∈ Finset.univ.erase j, (t * attraction P (constM t) i) / Ds s
          · refine Finset.sum_congr rfl fun i hi => ?_
            have hij : i ≠ j := Finset.ne_of_mem_erase hi
            rw [Function.update_of_ne hij, hattr_upd_ne i hi, constM, mul_div_assoc]
          · rw [← Finset.sum_div, ← Finset.mul_sum]
        rw [herase, ← mul_div_assoc, add_div]
      have hg : spread P (Function.update (constM t) j s) = (s ^ 2 * w s + t ^ 2 * R) / Ds s := by
        unfold spread share FlagshipMEA.Monopoly.logitShare
        simp_rw [hsum_attr]
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j)]
        simp only [Function.update_self, hattr_upd_j]
        have herase : ∑ i ∈ Finset.univ.erase j,
            Function.update (constM t) j s i ^ 2 *
              (attraction P (Function.update (constM t) j s) i / Ds s) =
            (t ^ 2 * R) / Ds s := by
          trans ∑ i ∈ Finset.univ.erase j, (t ^ 2 * attraction P (constM t) i) / Ds s
          · refine Finset.sum_congr rfl fun i hi => ?_
            have hij : i ≠ j := Finset.ne_of_mem_erase hi
            rw [Function.update_of_ne hij, hattr_upd_ne i hi, constM, mul_div_assoc]
          · rw [← Finset.sum_div, ← Finset.mul_sum]
        rw [herase, ← mul_div_assoc, add_div]
      unfold objective
      rw [hπ, hg]
    rw [hfun_eq]
    have hw_deriv : HasDerivAt w (-P.b * w t) t := by
      have hlin : HasDerivAt (fun s : ℝ => P.a j - P.b * P.c j - P.b * s) (-P.b) t := by
        have h1 : HasDerivAt (fun s : ℝ => P.b * s) (P.b * 1) t :=
          (hasDerivAt_id t).const_mul P.b
        have h2 : HasDerivAt (fun s : ℝ => P.a j - P.b * P.c j - P.b * s) (0 - P.b * 1) t :=
          (hasDerivAt_const t (P.a j - P.b * P.c j)).fun_sub h1
        simpa using h2
      have hexp := hlin.exp
      simpa [w, mul_comm] using hexp
    have hDs_deriv : HasDerivAt Ds (-P.b * w t) t := by
      have h1 : HasDerivAt (fun s : ℝ => w s + (R + 1)) (-P.b * w t + 0) t :=
        hw_deriv.fun_add (hasDerivAt_const t (R + 1))
      simpa [Ds, add_assoc] using h1
    have hDs_ne : Ds t ≠ 0 := by
      rw [hDt]
      exact hD_pos.ne'
    have hR_eq : R = D - 1 - w t := by
      have := hDt
      dsimp [Ds] at this
      linarith
    have hb_ne : P.b ≠ 0 := P.hb.ne'
    have hD_ne : D ≠ 0 := hD_pos.ne'
    have hN1_deriv : HasDerivAt (fun s : ℝ => s * w s + t * R)
        (1 * w t + t * (-P.b * w t) + 0) t :=
      ((hasDerivAt_id t).fun_mul hw_deriv).fun_add (hasDerivAt_const t (t * R))
    have hπ_deriv : HasDerivAt (fun s : ℝ => (s * w s + t * R) / Ds s)
        (w t * (D - P.b * t) / D ^ 2) t := by
      refine (hN1_deriv.fun_div hDs_deriv hDs_ne).congr_deriv ?_
      rw [hDt, hR_eq]
      congr 1
      ring
    have hsq_id : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
      simpa using (hasDerivAt_id t).fun_pow 2
    have hN2_deriv : HasDerivAt (fun s : ℝ => s ^ 2 * w s + t ^ 2 * R)
        ((2 * t) * w t + t ^ 2 * (-P.b * w t) + 0) t :=
      (hsq_id.fun_mul hw_deriv).fun_add (hasDerivAt_const t (t ^ 2 * R))
    have hg_deriv : HasDerivAt (fun s : ℝ => (s ^ 2 * w s + t ^ 2 * R) / Ds s)
        (t * w t * (2 * D - P.b * t) / D ^ 2) t := by
      refine (hN2_deriv.fun_div hDs_deriv hDs_ne).congr_deriv ?_
      rw [hDt, hR_eq]
      congr 1
      ring
    have hπ_pow : HasDerivAt (fun s : ℝ => ((s * w s + t * R) / Ds s) ^ 2)
        (2 * t * w t * (D - 1) * (D - P.b * t) / D ^ 3) t := by
      refine (hπ_deriv.fun_pow 2).congr_deriv ?_
      rw [hDt, hR_eq, show (2 : ℕ) - 1 = 1 from rfl, pow_one, Nat.cast_ofNat]
      exact sq_chain_eq t (w t) D P.b hD_ne
    have hL_deriv := hπ_pow.fun_sub (hg_deriv.const_mul lam)
    refine hL_deriv.congr_deriv ?_
    have hqj_eq : share P (constM t) j = w t / D := by
      unfold share FlagshipMEA.Monopoly.logitShare
      rw [← hwt]
    dsimp only [F]
    rw [hqj_eq]
    exact lemma_2_deriv_eq P.b t (w t) lam D q0 hb_ne hD_ne hq0_eq h1_ne
  constructor
  · intro hall
    have h0 := (hderiv_all 0).unique (hall 0)
    have hqj_pos : 0 < share P (constM t) 0 := by
      unfold share FlagshipMEA.Monopoly.logitShare
      exact div_pos (hattr_pos 0) hD_pos
    have hpref_ne : -2 * P.b * t * share P (constM t) 0 * q0 * (1 - q0 - lam) ≠ 0 :=
      mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero
            (mul_ne_zero (mul_ne_zero (by norm_num) P.hb.ne') ht.ne')
            hqj_pos.ne')
          hq0_pos.ne')
        h1_ne
    exact (mul_eq_zero.mp h0).resolve_left hpref_ne
  · intro hF j
    have hd := hderiv_all j
    change F = 0 at hF
    rw [hF, mul_zero] at hd
    exact hd
