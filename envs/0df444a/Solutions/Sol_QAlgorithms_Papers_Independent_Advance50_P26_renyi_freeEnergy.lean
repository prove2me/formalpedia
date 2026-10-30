-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P26.renyi_freeEnergy
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T10:43:42.800418+00:00
-- url     : https://prove2.me/submissions/c156e238-f666-46b1-bd1a-2c7afff4b475

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P26
noncomputable section
open Filter
open scoped BigOperators Topology Matrix.Norms.L2Operator
open QAlgorithms.Papers.Independent.Advance50.P26
open QAlgorithms.Papers.Independent.Support50.P15 (shannonEntropyNats)
open QAlgorithms.ZeroSum (classicalGibbs)
open QAlgorithms.Papers.Independent.Dependency50.P35 (spectralPower)

lemma trace_cfc' {I : Type} [Fintype I] [DecidableEq I] {H : Matrix I I ℂ} (hH : H.IsHermitian) (f : ℝ → ℝ) :
    (cfc f H).trace = ∑ i, ((f (hH.eigenvalues i) : ℝ) : ℂ) := by
  rw [hH.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_comm]
  have : (star (hH.eigenvectorUnitary : Matrix I I ℂ)) * ((hH.eigenvectorUnitary : Matrix I I ℂ) *
      Matrix.diagonal (RCLike.ofReal ∘ f ∘ hH.eigenvalues)) = Matrix.diagonal (RCLike.ofReal ∘ f ∘ hH.eigenvalues) := by
    rw [← Matrix.mul_assoc]
    simp
  rw [this, Matrix.trace_diagonal]
  simp

lemma exp_eq_cfc' {I : Type} [Fintype I] [DecidableEq I] {H : Matrix I I ℂ} (hH : H.IsHermitian) (c : ℝ) :
    NormedSpace.exp (c • H) = cfc (fun x : ℝ => Real.exp (c * x)) H := by
  have hs : IsSelfAdjoint H := hH
  have hs' : IsSelfAdjoint (c • H) := (IsSelfAdjoint.all c).smul hs
  rw [← CFC.exp_eq_normedSpace_exp (𝕜 := ℝ) hs']
  rw [← Real.exp_eq_exp_ℝ, ← cfc_comp_smul c Real.exp H]
  rfl

lemma trace_exp' {I : Type} [Fintype I] [DecidableEq I] {H : Matrix I I ℂ} (hH : H.IsHermitian) (c : ℝ) :
    (NormedSpace.exp (c • H)).trace = ((∑ i, Real.exp (c * hH.eigenvalues i) : ℝ) : ℂ) := by
  rw [exp_eq_cfc' hH c, trace_cfc' hH]
  push_cast
  rfl

theorem solution {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (H : Matrix I I ℂ) (hH : H.IsHermitian)
    (k T0 T : ℝ) (hk : 0 < k) (hT0 : 0 < T0) (hT : 0 < T) (hneq : T ≠ T0) :
    renyiEntropyWithBoltzmann (thermalGibbs H k T0) k (T0 / T) =
      -(thermalFreeEnergy H k T - thermalFreeEnergy H k T0) / (T - T0) := by
  set q : ℝ := T0 / T with hq
  have hq0 : 0 < q := div_pos hT0 hT
  have hq1 : q ≠ 1 := by
    intro h
    rw [hq, div_eq_one_iff_eq hT.ne'] at h
    exact hneq h.symm
  set c0 : ℝ := -(k * T0)⁻¹ with hc0
  set cT : ℝ := -(k * T)⁻¹ with hcT
  have hqc : q * c0 = cT := by
    rw [hq, hc0, hcT]; field_simp
  set Z0 : ℝ := ∑ i, Real.exp (c0 * hH.eigenvalues i) with hZ0
  set ZT : ℝ := ∑ i, Real.exp (cT * hH.eigenvalues i) with hZT
  have hZ0pos : 0 < Z0 := Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  have hZTpos : 0 < ZT := Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  have hPT : thermalPartition H k T = ZT := by
    unfold thermalPartition
    rw [← hcT, trace_exp' hH cT, Complex.ofReal_re]
  have hP0 : thermalPartition H k T0 = Z0 := by
    unfold thermalPartition
    rw [← hc0, trace_exp' hH c0, Complex.ofReal_re]
  have hρ : thermalGibbs H k T0 = cfc (fun x : ℝ => Z0⁻¹ * Real.exp (c0 * x)) H := by
    unfold thermalGibbs QAlgorithms.gibbsState
    rw [← hc0, trace_exp' hH c0, exp_eq_cfc' hH c0]
    have : ∀ x : ℝ, Z0⁻¹ * Real.exp (c0 * x) = Z0⁻¹ • Real.exp (c0 * x) := fun x => rfl
    simp_rw [this]
    rw [cfc_smul Z0⁻¹ (fun x : ℝ => Real.exp (c0 * x)) H]
    rw [← hZ0, ← Complex.ofReal_inv, Complex.coe_smul]
  have hqne : q ≠ 0 := hq0.ne'
  have hsp : spectralPower (thermalGibbs H k T0) q =
      cfc (fun x : ℝ => (Z0⁻¹ * Real.exp (c0 * x)) ^ q) H := by
    unfold spectralPower
    rw [if_neg hqne, hρ]
    have hcomp := cfc_comp (fun x : ℝ => if x = 0 then 0 else x ^ q)
      (fun x : ℝ => Z0⁻¹ * Real.exp (c0 * x)) H (ha := (hH : IsSelfAdjoint H))
      (hg := by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := hx
        have hp : 0 < Z0⁻¹ * Real.exp (c0 * y) := by positivity
        apply ContinuousAt.continuousWithinAt
        have h1 : ContinuousAt (fun x : ℝ => x ^ q) (Z0⁻¹ * Real.exp (c0 * y)) :=
          Real.continuousAt_rpow_const _ _ (Or.inl hp.ne')
        refine h1.congr ?_
        filter_upwards [lt_mem_nhds hp] with z hz
        simp [hz.ne'])
      (hf := by fun_prop)
    rw [← hcomp]
    apply cfc_congr
    intro x _
    have hp : 0 < Z0⁻¹ * Real.exp (c0 * x) := by positivity
    simp [Function.comp, hp.ne']
  have htr : (spectralPower (thermalGibbs H k T0) q).trace.re = (Z0⁻¹) ^ q * ZT := by
    rw [hsp, trace_cfc' hH]
    rw [Complex.re_sum]
    simp only [Complex.ofReal_re]
    rw [hZT, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.exp_mul]
    congr 2
    rw [← hqc]; ring
  have hFT : thermalFreeEnergy H k T = -k * T * Real.log ZT := by
    unfold thermalFreeEnergy; rw [hPT]
  have hF0 : thermalFreeEnergy H k T0 = -k * T0 * Real.log Z0 := by
    unfold thermalFreeEnergy; rw [hP0]
  unfold renyiEntropyWithBoltzmann
  rw [if_neg hq1, htr, hFT, hF0]
  rw [Real.log_mul (by positivity) hZTpos.ne', Real.log_rpow (inv_pos.mpr hZ0pos), Real.log_inv]
  have h1 : (1 - q) = (T - T0) / T := by rw [hq]; field_simp
  have h2 : T - T0 ≠ 0 := sub_ne_zero.mpr hneq
  rw [h1, hq]
  field_simp
  ring
