-- Prove2me | solution 1 for TaoFivePrimes.sine_weight_high_zeros_65000
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:10:19.76817+00:00
-- url     : https://prove2.me/submissions/de997a35-a4ac-4a34-962e-7a415956d1d9

-- Uses the published partition, single-bin, tail, and total certificates.
import Theorems.Thm_TaoFivePrimes_nonnegative_weight_bin_cover_65000
import Theorems.Thm_TaoFivePrimes_sine_weight_positive_bin_bound_65000
import Theorems.Thm_TaoFivePrimes_sine_weight_tail_above_297200
import Theorems.Thm_TaoFivePrimes_sine_bin_65k_rounded_total
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_PowerQuarterWeights
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 3000000
open DusartSmoothing Complex Set

theorem solution (r : ℝ) (hr0 : (1/2151:ℝ) ≤ r) (hr1 : r ≤ (1/2149:ℝ))
    (Z : Finset ℂ) (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ)
    (hγ : ∀ ρ ∈ Z, 65000 < |ρ.im|) :
    (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) *
      ((min (4*(Real.sin (ρ.im*r/2))^2 + 8*r + 3 * |ρ.im| * r^2) 4) /
        |ρ.im|^3)) ≤ (115/10^11:ℝ) := by
  classical
  let W : ℝ → ℝ := fun t =>
    (min (4*(Real.sin (t*r/2))^2 + 8*r + 3*t*r^2) 4)/t^3
  let Wmid : ℝ → ℝ := fun t => if 65000 < t ∧ t ≤ 297200 then W t else 0
  let T : ℝ := ∑ i ∈ Finset.range 180, (TaoFivePrimes.sineBinTerm65k i:ℝ)/10^21
  have hr : 0 ≤ r := by linarith
  have hsin_abs (t : ℝ) : (Real.sin (|t| * r/2))^2 = (Real.sin (t*r/2))^2 := by
    by_cases ht : 0 ≤ t
    · rw [abs_of_nonneg ht]
    · rw [abs_of_neg (lt_of_not_ge ht)]
      have he : (-t)*r/2 = -(t*r/2) := by ring
      rw [he,Real.sin_neg,neg_sq]
  have hW (t : ℝ) (ht : 0 < t) : 0 ≤ W t := by
    dsimp [W]
    have hn : 0 ≤ min (4*(Real.sin (t*r/2))^2 + 8*r + 3*t*r^2) 4 := by
      apply le_min
      · positivity
      · norm_num
    exact div_nonneg hn (pow_nonneg ht.le _)
  have hmidpos (S : Finset ℂ)
      (hS : ∀ ρ ∈ S, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im) :
      (∑ ρ ∈ S, (RvM.zeroMult ρ : ℝ) * Wmid ρ.im) ≤ T/2 := by
    let S0 := S.filter (fun ρ => 65000 < ρ.im ∧ ρ.im ≤ 297200)
    have hS0 (ρ : ℂ) (hρ : ρ ∈ S0) :
        RvM.IsNontrivialZero ρ ∧ 65000 < ρ.im ∧ ρ.im ≤ 297200 := by
      have h := Finset.mem_filter.mp hρ
      exact ⟨(hS ρ h.1).1, h.2.1, h.2.2⟩
    have hpart := TaoFivePrimes.nonnegative_weight_bin_cover_65000 S0 Complex.im
      (fun ρ => (RvM.zeroMult ρ : ℝ)*W ρ.im)
      (by
        intro ρ hρ
        exact mul_nonneg (Nat.cast_nonneg _) (hW ρ.im (by linarith [(hS0 ρ hρ).2.1])))
      (fun ρ hρ => (hS0 ρ hρ).2.1)
      (fun ρ hρ => (hS0 ρ hρ).2.2)
    have hbins (i : ℕ) (hi : i ∈ Finset.range 180) :
        (∑ ρ ∈ S0.filter (fun ρ => 65000+1290*(i:ℝ) < ρ.im ∧
            ρ.im ≤ 65000+1290*((i:ℝ)+1)), (RvM.zeroMult ρ : ℝ)*W ρ.im) ≤
          (TaoFivePrimes.sineBinTerm65k i:ℝ)/(2*10^21) := by
      let j : Fin 180 := ⟨i, Finset.mem_range.mp hi⟩
      let F := S0.filter (fun ρ => 65000+1290*(i:ℝ) < ρ.im ∧
        ρ.im ≤ 65000+1290*((i:ℝ)+1))
      have hF : ∀ ρ ∈ F, RvM.IsNontrivialZero ρ ∧
          65000+1290*(j.val:ℝ) < ρ.im ∧ ρ.im ≤ 65000+1290*(j.val:ℝ)+1290 := by
        intro ρ hρ
        obtain ⟨hρ0, hl, hu⟩ := Finset.mem_filter.mp hρ
        refine ⟨(hS0 ρ hρ0).1, ?_, ?_⟩
        · simpa [j] using hl
        · dsimp [j] at *
          linarith
      have hh := TaoFivePrimes.sine_weight_positive_bin_bound_65000 j r hr0 hr1 F hF
      simpa [W,F,j] using hh
    have hsum := Finset.sum_le_sum hbins
    have hdiv : (∑ i ∈ Finset.range 180, (TaoFivePrimes.sineBinTerm65k i:ℝ)/(2*10^21)) = T/2 := by
      dsimp [T]
      simp only [Finset.sum_div]
      ring
    have hfiltered : (∑ ρ ∈ S, (RvM.zeroMult ρ : ℝ)*Wmid ρ.im) =
        ∑ ρ ∈ S0, (RvM.zeroMult ρ : ℝ)*W ρ.im := by
      simp [S0,Wmid,Finset.sum_filter,mul_ite]
    rw [hfiltered]
    rw [hdiv] at hsum
    exact hpart.trans hsum
  let M := Z.filter (fun ρ => |ρ.im| ≤ 297200)
  let E := Z.filter (fun ρ => ¬ |ρ.im| ≤ 297200)
  have hMZ : ∀ ρ ∈ M, RvM.IsNontrivialZero ρ := by
    intro ρ hρ
    exact hZ ρ (Finset.mem_filter.mp hρ).1
  have hEZ : ∀ ρ ∈ E, RvM.IsNontrivialZero ρ := by
    intro ρ hρ
    exact hZ ρ (Finset.mem_filter.mp hρ).1
  have hEγ : ∀ ρ ∈ E, 297200 < |ρ.im| := by
    intro ρ hρ
    exact lt_of_not_ge (Finset.mem_filter.mp hρ).2
  have hm := ExplicitPNT.DusartTable1.Modules.PowerQuarterWeights.1 Wmid (T/2) hmidpos M hMZ
  have hm_eq : (∑ ρ ∈ M, (RvM.zeroMult ρ : ℝ)*Wmid |ρ.im|) =
      ∑ ρ ∈ M, (RvM.zeroMult ρ : ℝ)*W |ρ.im| := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    have hz := (Finset.mem_filter.mp hρ).1
    have hh := (Finset.mem_filter.mp hρ).2
    simp [Wmid,hγ ρ hz,hh]
  rw [hm_eq] at hm
  have hm' : (∑ ρ ∈ M, (RvM.zeroMult ρ : ℝ)*W |ρ.im|) ≤ T := by linarith
  have ht := TaoFivePrimes.sine_weight_tail_above_297200 E hEZ hEγ
  have he' : (∑ ρ ∈ E, (RvM.zeroMult ρ : ℝ)*W |ρ.im|) ≤ (81609874820/10^21:ℝ) := by
    calc
      _ ≤ ∑ ρ ∈ E, (RvM.zeroMult ρ : ℝ)*(4/|ρ.im|^3) := by
        apply Finset.sum_le_sum
        intro ρ hρ
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        dsimp [W]
        exact div_le_div_of_nonneg_right (min_le_right _ _) (pow_nonneg (abs_nonneg _) _)
      _ ≤ _ := ht
  have hsplit := Finset.sum_filter_add_sum_filter_not Z
    (fun ρ : ℂ => |ρ.im| ≤ 297200)
    (fun ρ => (RvM.zeroMult ρ : ℝ)*W |ρ.im|)
  change (∑ ρ ∈ M, _) + (∑ ρ ∈ E, _) = _ at hsplit
  have htotal := TaoFivePrimes.sine_bin_65k_rounded_total
  change T + (81609874820:ℝ)/10^21 ≤ (115/10^11:ℝ) at htotal
  have hgoal_eq : (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ)*W |ρ.im|) =
      ∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) *
        ((min (4*(Real.sin (ρ.im*r/2))^2 + 8*r + 3 * |ρ.im| * r^2) 4) /
          |ρ.im|^3) := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    dsimp [W]
    rw [hsin_abs]
  rw [←hgoal_eq]
  linarith only [hm',he',hsplit,htotal]
