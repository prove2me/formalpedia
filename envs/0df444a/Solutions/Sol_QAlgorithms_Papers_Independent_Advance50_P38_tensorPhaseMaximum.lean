-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P38.tensorPhaseMaximum
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T10:25:13.283991+00:00
-- url     : https://prove2.me/submissions/7507ccd6-a2b8-4ba3-97b4-3b3ba0f97395

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38
open QAlgorithms.Papers.Independent.Advance50.P38

theorem solution {r : ℕ} (hr : 0 < r) (d : Fin r → ℕ)
    (hd : ∀ k, 0 < d k) (X : ArrayIndex d → ℂ) :
    (∃ v : ℝ,
      IsGreatest {v | ∃ z : (k : Fin r) → Fin (d k) → ℂ,
        unitTensorFactors z ∧ v = ‖vInner X (tensorProduct z)‖} v ∧
      IsGreatest {v | ∃ z : (k : Fin r) → Fin (d k) → ℂ,
        unitTensorFactors z ∧ v = (vInner X (tensorProduct z)).re} v) ∧
    ∀ z : (k : Fin r) → Fin (d k) → ℂ, unitTensorFactors z →
      (∀ w : (k : Fin r) → Fin (d k) → ℂ, unitTensorFactors w →
        (vInner X (tensorProduct w)).re ≤ (vInner X (tensorProduct z)).re) →
      ∀ w : (k : Fin r) → Fin (d k) → ℂ, unitTensorFactors w →
        ‖vInner X (tensorProduct w)‖ ≤ ‖vInner X (tensorProduct z)‖ := by
  set f : ((k : Fin r) → Fin (d k) → ℂ) → ℂ := fun z => vInner X (tensorProduct z) with hf
  -- phase rotation of the first factor
  have phase : ∀ z : (k : Fin r) → Fin (d k) → ℂ, unitTensorFactors z →
      ∃ z', unitTensorFactors z' ∧ (f z').re = ‖f z‖ := by
    intro z hz
    set w := f z with hw
    set u : ℂ := Complex.exp (((-Complex.arg w : ℝ) : ℂ) * Complex.I) with hu
    have hun : ‖u‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    have huw : u * w = (‖w‖ : ℂ) := by
      have h := Complex.norm_mul_exp_arg_mul_I w
      calc u * w = u * ((‖w‖ : ℂ) * Complex.exp (Complex.arg w * Complex.I)) := by rw [h]
        _ = (‖w‖ : ℂ) * (Complex.exp (((-Complex.arg w : ℝ) : ℂ) * Complex.I) *
              Complex.exp (Complex.arg w * Complex.I)) := by ring
        _ = (‖w‖ : ℂ) := by
          rw [← Complex.exp_add]
          have : ((-Complex.arg w : ℝ) : ℂ) * Complex.I + Complex.arg w * Complex.I = 0 := by
            push_cast; ring
          rw [this]; simp
    let k0 : Fin r := ⟨0, hr⟩
    let c : Fin r → ℂ := fun k => if k = k0 then u else 1
    have hc : ∀ k, ‖c k‖ = 1 := by
      intro k; by_cases h : k = k0 <;> simp [c, h, hun]
    refine ⟨fun k j => c k * z k j, ?_, ?_⟩
    · intro k
      have : ∑ j, Complex.normSq (c k * z k j) = ∑ j, Complex.normSq (z k j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul]
        have : Complex.normSq (c k) = 1 := by
          rw [Complex.normSq_eq_norm_sq, hc k]; norm_num
        rw [this, one_mul]
      rw [this]; exact hz k
    · have hT : ∀ i : ArrayIndex d, tensorProduct (fun k j => c k * z k j) i =
          u * tensorProduct z i := by
        intro i
        simp only [tensorProduct]
        rw [Finset.prod_mul_distrib]
        simp [c]
      have : f (fun k j => c k * z k j) = u * w := by
        simp only [hf, vInner, hT, hw]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [this, huw]; simp
  -- compactness
  have hcomp : IsCompact {z : (k : Fin r) → Fin (d k) → ℂ | unitTensorFactors z} := by
    have h1 : {z : (k : Fin r) → Fin (d k) → ℂ | unitTensorFactors z} =
        Set.pi Set.univ (fun k => {y : Fin (d k) → ℂ | ∑ j, Complex.normSq (y j) = 1}) := by
      ext z; simp [unitTensorFactors]
    rw [h1]
    refine isCompact_univ_pi fun k => ?_
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact isClosed_eq (continuous_finset_sum _ fun j _ =>
        Complex.continuous_normSq.comp (continuous_apply j)) continuous_const
    · refine (Metric.isBounded_closedBall (x := (0 : Fin (d k) → ℂ)) (r := 1)).subset ?_
      intro y hy
      simp only [Set.mem_setOf_eq] at hy
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      intro j
      have h2 : Complex.normSq (y j) ≤ 1 := by
        rw [← hy]
        exact Finset.single_le_sum (f := fun j => Complex.normSq (y j))
          (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
      rw [Complex.normSq_eq_norm_sq] at h2
      nlinarith [norm_nonneg (y j)]
  have hne : ({z : (k : Fin r) → Fin (d k) → ℂ | unitTensorFactors z}).Nonempty := by
    refine ⟨fun k j => if j = ⟨0, hd k⟩ then 1 else 0, fun k => ?_⟩
    simp
  have hcont : Continuous f := by
    simp only [hf, vInner, tensorProduct]
    exact continuous_finset_sum _ fun i _ => continuous_const.mul
      (continuous_finset_prod _ fun k _ => (continuous_apply (i k)).comp (continuous_apply k))
  obtain ⟨zs, hzs, hmax⟩ := hcomp.exists_isMaxOn hne (hcont.norm.continuousOn)
  have hmax' : ∀ w, unitTensorFactors w → ‖f w‖ ≤ ‖f zs‖ := fun w hw => hmax hw
  obtain ⟨zr, hzr, hre⟩ := phase zs hzs
  refine ⟨⟨‖f zs‖, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩
  · exact ⟨zs, hzs, rfl⟩
  · rintro v ⟨z, hz, rfl⟩; exact hmax' z hz
  · exact ⟨zr, hzr, hre.symm⟩
  · rintro v ⟨z, hz, rfl⟩
    exact (Complex.re_le_norm _).trans (hmax' z hz)
  · intro z hz hzmax w hw
    obtain ⟨w', hw', hwre⟩ := phase w hw
    calc ‖f w‖ = (f w').re := hwre.symm
      _ ≤ (f z).re := hzmax w' hw'
      _ ≤ ‖f z‖ := Complex.re_le_norm _
