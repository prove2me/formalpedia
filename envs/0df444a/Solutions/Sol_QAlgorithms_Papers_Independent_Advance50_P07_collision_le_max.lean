-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P07.collision_le_max
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T11:21:46.918463+00:00
-- url     : https://prove2.me/submissions/0efdbbe2-7677-4bbd-9705-0bbb80b7a6f4

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P07
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology

open Filter

namespace QAlgorithms.Papers.Independent.Advance50.P07

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P09 (relativeD petzD)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative Density elog)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P19 (marginalRA marginalRB)

open QAlgorithms.Papers.Independent.Support50.P21 (PositiveTensorBasis)

end QAlgorithms.Papers.Independent.Advance50.P07

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)
open QAlgorithms.Papers.Independent.Dependency50.P09 (petzD logExt)
open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)
open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

lemma s109c1_sq {I : Type} [Fintype I] [DecidableEq I] (rho : Mat I) (hrho : rho.IsHermitian) :
    supportPower rho 2 = rho * rho := by
  unfold supportPower
  have hr : IsSelfAdjoint rho := hrho
  have : (fun x : ℝ => if x = 0 then 0 else Real.rpow x 2) = fun x => x * x := by
    funext x; split_ifs with h
    · simp [h]
    · show x ^ (2:ℝ) = x * x
      rw [Real.rpow_two, sq]
  rw [this, cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) rho, cfc_id' ℝ rho]

lemma s109c1_herm {I : Type} [Fintype I] [DecidableEq I] (s : Mat I) (t : ℝ) :
    (supportPower s t).IsHermitian := by
  unfold supportPower
  exact cfc_predicate (fun x : ℝ => if x = 0 then 0 else Real.rpow x t) s

lemma s109c1_sss {I : Type} [Fintype I] [DecidableEq I] (s : Mat I) (hs : s.IsHermitian) :
    supportPower s (-1) * s * supportPower s (-1) = supportPower s (-1) := by
  unfold supportPower
  have hr : IsSelfAdjoint s := hs
  set g : ℝ → ℝ := fun x => if x = 0 then 0 else Real.rpow x (-1)
  rw [show cfc g s * s * cfc g s = cfc g s * cfc (fun x : ℝ => x) s * cfc g s by rw [cfc_id' ℝ s]]
  have hfin : (spectrum ℝ s).Finite := Matrix.finite_real_spectrum (A := s)
  rw [← cfc_mul g (fun x : ℝ => x) s (hfin.continuousOn _) (hfin.continuousOn _),
    ← cfc_mul _ g s (hfin.continuousOn _) (hfin.continuousOn _)]
  congr 1
  funext x
  simp only [g]
  split_ifs with h
  · simp
  · show x ^ (-1:ℝ) * x * x ^ (-1:ℝ) = x ^ (-1:ℝ)
    rw [Real.rpow_neg_one]; field_simp

lemma s109c1_supp {I : Type} [Fintype I] [DecidableEq I] (rho sigma : Mat I)
    (hrho : rho.PosSemidef) (c : ℝ) (hc : ((c : ℂ) • sigma - rho).PosSemidef) :
    SupportIncluded rho sigma := by
  intro v hv
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  have h1 := hc.dotProduct_mulVec_nonneg v
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hv, smul_zero, zero_sub,
    dotProduct_neg] at h1
  have h2 := hrho.dotProduct_mulVec_nonneg v
  have h3 : star v ⬝ᵥ (rho *ᵥ v) = 0 := le_antisymm (by simpa using h1) h2
  exact (hrho.dotProduct_mulVec_zero_iff v).mp h3

lemma s109c1_tr {I : Type} [Fintype I] [DecidableEq I] (rho sigma : Mat I)
    (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef) (c : ℝ) (hc0 : 0 < c)
    (hc : ((c : ℂ) • sigma - rho).PosSemidef) :
    (rho * rho * supportPower sigma (-1)).trace.re ≤ c * rho.trace.re := by
  set S := supportPower sigma (-1)
  have hS : S.IsHermitian := s109c1_herm sigma (-1)
  have hSSS : S * sigma * S = S := s109c1_sss sigma hsigma.1
  set M := rho * S * rho
  have hB : (S * rho)ᴴ = rho * S := by
    rw [Matrix.conjTranspose_mul, hS.eq, hrho.1.eq]
  -- rho S rho S rho ≤ c M
  have h1 := hc.conjTranspose_mul_mul_same (S * rho)
  rw [hB] at h1
  have e1 : rho * S * ((c : ℂ) • sigma - rho) * (S * rho) =
      (c : ℂ) • M - M * S * rho := by
    simp only [M, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    · congr 1
      calc rho * S * sigma * (S * rho) = rho * (S * sigma * S) * rho := by
            simp only [Matrix.mul_assoc]
        _ = rho * S * rho := by rw [hSSS, Matrix.mul_assoc]
    · simp only [Matrix.mul_assoc]
  rw [e1] at h1
  -- (1 - a S rho)^H rho (1 - a S rho) ≥ 0 with a = 1/c
  set a : ℂ := ((1 / c : ℝ) : ℂ)
  have h2 := hrho.conjTranspose_mul_mul_same (1 - a • (S * rho))
  have hB2 : (1 - a • (S * rho))ᴴ = 1 - a • (rho * S) := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_smul, hB]
    simp [a]
  rw [hB2] at h2
  have e2 : (1 - a • (rho * S)) * rho * (1 - a • (S * rho)) =
      rho - (2 * a) • M + (a * a) • (M * S * rho) := by
    simp only [M, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_smul]
    simp only [Matrix.mul_assoc]
    rw [two_mul, add_smul]; abel
  rw [e2] at h2
  have h3 : (rho - (2 * a) • M + (a * a) • (M * S * rho) +
      (a * a) • ((c : ℂ) • M - M * S * rho)).PosSemidef :=
    h2.add (h1.smul (by
      simp only [a, ← Complex.ofReal_mul]
      exact_mod_cast mul_self_nonneg (1 / c)))
  have e3 : rho - (2 * a) • M + (a * a) • (M * S * rho) +
      (a * a) • ((c : ℂ) • M - M * S * rho) = rho - a • M := by
    have hac : a * a * (c : ℂ) = a := by
      simp only [a]; push_cast; field_simp
    rw [smul_sub, smul_smul, hac]
    rw [two_mul, add_smul]; abel
  rw [e3] at h3
  have h4 := h3.trace_nonneg
  rw [Matrix.trace_sub, Matrix.trace_smul] at h4
  have h5 := (Complex.nonneg_iff.mp h4).1
  simp only [Complex.sub_re, smul_eq_mul, Complex.mul_re, a, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at h5
  have hT : (rho * rho * S).trace = M.trace := by
    simp only [M]
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc rho S rho, Matrix.trace_mul_comm rho (S*rho)]
    simp only [Matrix.mul_assoc]
  rw [hT]
  have := mul_le_mul_of_nonneg_left (by linarith : (1/c) * M.trace.re ≤ rho.trace.re) hc0.le
  rw [← mul_assoc, mul_one_div_cancel hc0.ne', one_mul] at this
  exact this

theorem solution {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho sigma : Mat I) (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef)
    (htrace : rho.trace.re ≤ 1) : petzD 2 rho sigma ≤ maxRelative rho sigma := by
  unfold maxRelative
  refine le_sInf ?_
  rintro v ⟨l, rfl, hl⟩
  have hc0 : (0:ℝ) < 2 ^ l := Real.rpow_pos_of_pos (by norm_num) l
  have hsupp := s109c1_supp rho sigma hrho _ hl
  have htr := s109c1_tr rho sigma hrho hsigma _ hc0 hl
  have htr0 : 0 ≤ rho.trace.re := (Complex.nonneg_iff.mp hrho.trace_nonneg).1
  unfold petzD
  rw [if_neg (by tauto), s109c1_sq rho hrho.1, show (1:ℝ) - 2 = -1 by norm_num,
    show (1 / ((2:ℝ) - 1)) = 1 by norm_num, EReal.coe_one, one_mul]
  set x := (rho * rho * supportPower sigma (-1)).trace.re
  unfold logExt
  rw [if_neg (EReal.coe_ne_top x)]
  split_ifs with h
  · exact bot_le
  · have hx : 0 < x := by
      by_contra hh; exact h (by exact_mod_cast not_lt.mp hh)
    rw [EReal.toReal_coe, EReal.coe_le_coe_iff]
    have : x ≤ 2 ^ l := by nlinarith
    calc Real.logb 2 x ≤ Real.logb 2 (2 ^ l) :=
          Real.logb_le_logb_of_le (by norm_num) hx this
      _ = l := by rw [Real.logb_rpow (by norm_num) (by norm_num)]
