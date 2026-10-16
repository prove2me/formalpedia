-- Prove2me | solution 1 for SoftenDataShare.Mutual.pi1_sub_piN1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T09:43:26.910309+00:00
-- url     : https://prove2.me/submissions/a36c0d4d-f978-403d-a5c5-d4076cc41a25

import Mathlib
import Definitions.Def_SoftenDataShare_Mutual_Model

open SoftenDataShare.Mutual MeasureTheory

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Chongwoo Choe, Jiajia Cong and Chengsi Wang, Monash Discussion Paper 2021-10, revised 2022-10-20.
theorem solution {F f : ℝ → ℝ} {zN : ℝ} (hF : MHRDist F f) (hzN : IsZN F f zN) :
    (∀ b : ℝ, pi1 f zN b-piN1 F f zN = 2*(b-zN)*F zN) ∧
      ∀ b : ℝ, zN < b → 0 < pi1 f zN b-piN1 F f zN := by
  have hz0 : 0 < zN := by linarith [hzN.1.1]
  have hz1 : zN < 1 := hzN.1.2
  have hcont : ContinuousOn F (Set.Icc (0 : ℝ) 1) :=
    fun x hx => (hF.hasDerivWithinAt x hx).continuousWithinAt
  have hsub : Set.Icc (0 : ℝ) zN ⊆ Set.Icc (0 : ℝ) 1 :=
    fun x hx => ⟨hx.1,hx.2.trans hz1.le⟩
  have hfcont := hF.continuousOn_density.mono hsub
  have hfi : IntervalIntegrable f volume 0 zN := hfcont.intervalIntegrable_of_Icc hz0.le
  have hint : ∫ x in (0 : ℝ)..zN, f x = F zN := by
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hz0.le (hcont.mono hsub)
      (fun x hx => (hF.hasDerivWithinAt x ⟨hx.1.le,(hx.2.trans hz1).le⟩).hasDerivAt
        (Icc_mem_nhds hx.1 (hx.2.trans hz1))) hfi
    simpa only [hF.F_zero,sub_zero] using hh
  have hmono : StrictMonoOn F (Set.Icc (0 : ℝ) 1) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 1) hcont
      (fun x hx => (hF.hasDerivWithinAt x (interior_subset hx)).mono interior_subset)
      (fun x hx => hF.density_pos x (interior_subset hx))
  have hFpos : 0 < F zN := by
    have hh := hmono (by simp : (0 : ℝ) ∈ Set.Icc 0 1) ⟨hz0.le,hz1.le⟩ hz0
    simpa only [hF.F_zero] using hh
  have hprice : pN2 F f zN = 2*zN-1 := by
    unfold pN2
    have heq := hzN.2
    simp only [div_eq_mul_inv] at heq ⊢
    linarith only [heq]
  have hweight (b : ℝ) : IntervalIntegrable (fun x => ((2*b-1)+(1-2*x))*f x) volume 0 zN := by
    apply ContinuousOn.intervalIntegrable_of_Icc hz0.le
    apply ContinuousOn.mul _ hfcont
    fun_prop
  have hid (b : ℝ) : pi1 f zN b-piN1 F f zN = 2*(b-zN)*F zN := by
    unfold pi1 piN1
    rw [hprice,← intervalIntegral.integral_sub (hweight b) (hweight zN)]
    calc
      _ = ∫ x in (0 : ℝ)..zN, (2*(b-zN))*f x := by
        apply intervalIntegral.integral_congr
        intro x _
        ring
      _ = _ := by rw [intervalIntegral.integral_const_mul,hint]
  refine ⟨hid,?_⟩
  intro b hb
  rw [hid]
  exact mul_pos (mul_pos (by norm_num) (sub_pos.mpr hb)) hFpos

#print axioms solution
