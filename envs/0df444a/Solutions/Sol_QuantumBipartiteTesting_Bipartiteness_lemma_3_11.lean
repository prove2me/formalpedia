-- Prove2me | solution 1 for QuantumBipartiteTesting.Bipartiteness.lemma_3_11
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T12:32:11.268989+00:00
-- url     : https://prove2.me/submissions/f21ee31a-d5a6-494e-aa5a-87873beb5f66

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
namespace QuantumBipartiteTesting.Bipartiteness
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

private def blockCount {N l : ℕ} (b : Fin N → Fin l) (j : Fin l) : ℕ :=
  (univ.filter fun v => b v = j).card

private lemma block_mgf (N l : ℕ) (j : Fin l) (t : ℝ) :
    (∑ b : Fin N → Fin l, Real.exp (t * blockCount b j)) =
      ((l : ℝ)-1+Real.exp t)^N := by
  have hb (b : Fin N → Fin l) : Real.exp (t * blockCount b j) =
      ∏ v : Fin N, if b v = j then Real.exp t else 1 := by
    rw [mul_comm, Real.exp_nat_mul]
    simp [blockCount, Finset.prod_ite]
  have hj : (∑ a : Fin l, if a = j then Real.exp t else 1) =
      (l : ℝ)-1+Real.exp t := by
    have hpoint (a : Fin l) : (if a = j then Real.exp t else 1) =
        1 + (if a = j then Real.exp t-1 else 0) := by split_ifs <;> ring
    simp_rw [hpoint]
    simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [sum_ite_eq']
    simp only [mem_univ, ite_true]
    ring
  simp_rw [hb]
  rw [← Fintype.prod_sum (fun (_ : Fin N) (a : Fin l) => if a = j then Real.exp t else 1)]
  simp only [hj, prod_const, card_univ, Fintype.card_fin]

private lemma block_mgf_bound (N l : ℕ) (hl : 0 < l) (j : Fin l) (t : ℝ) (ht : 0 ≤ t) :
    Average univ (fun b : Fin N → Fin l => Real.exp (t * blockCount b j)) ≤
      Real.exp (N * ((Real.exp t-1)/l)) := by
  have hlr : (0 : ℝ) < l := Nat.cast_pos.mpr hl
  rw [Average, block_mgf]
  simp only [card_univ, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  rw [← div_pow]
  have he : ((l : ℝ)-1+Real.exp t)/l = 1+(Real.exp t-1)/l := by field_simp; ring
  rw [he]
  have hpos : 0 ≤ (Real.exp t-1)/l := div_nonneg (sub_nonneg.mpr
    (Real.one_le_exp_iff.mpr ht)) hlr.le
  calc
    _ ≤ (Real.exp ((Real.exp t-1)/l))^N :=
      pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp ((Real.exp t-1)/l)]) N
    _ = _ := (Real.exp_nat_mul _ _).symm

private lemma overflow_mgf (N M l : ℕ) (hl : 0 < l) (t : ℝ) (ht : 0 < t) :
    OverflowProbability N M l ≤ (l : ℝ) *
      Real.exp (-t*(M/l : ℕ) + N*((Real.exp t-1)/l)) := by
  let f := fun (b : Fin N → Fin l) (j : Fin l) =>
    Real.exp (t*((blockCount b j : ℝ)-(M/l : ℕ)))
  have hp (b : Fin N → Fin l) : (if NoOverflow N M l b then (0 : ℝ) else 1) ≤ ∑ j, f b j := by
    by_cases hb : NoOverflow N M l b
    · simp only [if_pos hb]
      exact sum_nonneg (fun _ _ => (Real.exp_pos _).le)
    · simp only [if_neg hb]
      have hex : ∃ j : Fin l, M/l < blockCount b j := by
        simpa only [NoOverflow, not_forall, not_le, blockCount] using hb
      obtain ⟨j,hj⟩ := hex
      calc
        (1 : ℝ) ≤ f b j := by
          apply Real.one_le_exp_iff.mpr
          apply mul_nonneg ht.le
          have : (M/l : ℕ) ≤ blockCount b j := hj.le
          exact sub_nonneg.mpr (by exact_mod_cast this)
        _ ≤ _ := single_le_sum (f := fun j : Fin l => f b j)
          (fun _ _ => (Real.exp_pos _).le) (mem_univ j)
  have hb (j : Fin l) : Average univ (fun b : Fin N → Fin l => f b j) ≤
      Real.exp (-t*(M/l : ℕ)) * Real.exp (N*((Real.exp t-1)/l)) := by
    have heq (b : Fin N → Fin l) : f b j =
        Real.exp (-t*(M/l : ℕ)) * Real.exp (t * blockCount b j) := by
      dsimp [f]
      rw [← Real.exp_add]
      congr 1
      ring
    simp_rw [heq]
    simp only [Average, ← mul_sum, mul_div_assoc]
    apply mul_le_mul_of_nonneg_left (block_mgf_bound N l hl j t ht.le) (Real.exp_pos _).le
  calc
    _ ≤ Average univ (fun b : Fin N → Fin l => ∑ j, f b j) := by
      unfold OverflowProbability Average
      apply div_le_div_of_nonneg_right (sum_le_sum (fun b _ => hp b)) (Nat.cast_nonneg _)
    _ = ∑ j : Fin l, Average univ (fun b : Fin N → Fin l => f b j) := by
      unfold Average
      rw [sum_comm, sum_div]
    _ ≤ ∑ j : Fin l, Real.exp (-t*(M/l : ℕ)) * Real.exp (N*((Real.exp t-1)/l)) :=
      sum_le_sum (fun j _ => hb j)
    _ = _ := by
      rw [← Real.exp_add]
      simp

private lemma overflow_chernoff (N M l : ℕ) (hl : 0 < l) (hdiv : l ∣ M)
    (hM : (109/100 : ℝ)*N ≤ M) :
    OverflowProbability N M l ≤ (l : ℝ) * Real.exp (-(N : ℝ)/(2000*l)) := by
  have hlr : (0 : ℝ) < l := Nat.cast_pos.mpr hl
  have hexp : Real.exp (1/100 : ℝ) ≤ 100/99 := by
    have := Real.exp_bound_div_one_sub_of_interval (by norm_num : (0 : ℝ) ≤ 1/100)
      (by norm_num : (1/100 : ℝ) < 1)
    norm_num at this ⊢
    exact this
  apply (overflow_mgf N M l hl (1/100) (by norm_num)).trans
  apply mul_le_mul_of_nonneg_left _ hlr.le
  apply Real.exp_le_exp.mpr
  rw [Nat.cast_div_charZero hdiv]
  have heq : -(1/100 : ℝ)*((M : ℝ)/l) + (N : ℝ)*((Real.exp (1/100 : ℝ)-1)/l) =
      (-(1/100 : ℝ)*M + N*(Real.exp (1/100 : ℝ)-1))/l := by ring
  rw [heq, show -(N : ℝ)/(2000*l) = (-(N : ℝ)/2000)/l by ring]
  apply div_le_div_of_nonneg_right _ hlr.le
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hprod : (N : ℝ)*(Real.exp (1/100 : ℝ)-1) ≤ N*(100/99-1) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_right hexp 1) hN
  nlinarith

private lemma radius_bound (N : ℕ) : (Radius N : ℝ) ≤ (N : ℝ)^(2/3 : ℝ)/100 := by
  exact Nat.floor_le (by positivity)

private lemma radius_power_bound (N : ℕ) : (Radius N : ℝ)^(3/2 : ℝ) ≤ N/100 := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have h100 : (100 : ℝ) ≤ (100 : ℝ)^(3/2 : ℝ) := by
    calc
      (100 : ℝ) = (100 : ℝ)^(1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  calc
    _ ≤ ((N : ℝ)^(2/3 : ℝ)/100)^(3/2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (radius_bound N) (by norm_num)
    _ = (N : ℝ)/(100 : ℝ)^(3/2 : ℝ) := by
      rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hN]
      norm_num
    _ ≤ _ := div_le_div_of_nonneg_left hN (by norm_num) h100


private lemma grid_lower_bound {N M l : ℕ} (h : Grid N M l) : (109/100 : ℝ)*N ≤ M := by
  have hc := Nat.le_ceil ((11*N : ℝ)/40)
  have hC : (11/10 : ℝ)*N ≤ Center N := by
    unfold Center
    push_cast
    linarith
  have hw := radius_power_bound N
  have hgrid := (abs_le.mp h.2.2.1).1
  linarith

private lemma grid_valid {N M l : ℕ} (h : Grid N M l) : ValidParameters N M l := by
  refine ⟨by have := h.1; omega, ?_, h.2.2.2⟩
  have hM := grid_lower_bound h
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have : (N : ℝ) ≤ M := by nlinarith
  exact_mod_cast this

private lemma grid_tail {N M l : ℕ} (hN : 0 < N) (h : Grid N M l) :
    OverflowProbability N M l ≤ (N : ℝ)*Real.exp (-(N : ℝ)^(1/3 : ℝ)/20) := by
  have hl : 0 < l := by have := h.1; omega
  have hlr : (0 : ℝ) < l := Nat.cast_pos.mpr hl
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hR := radius_bound N
  have hlR : (l : ℝ) ≤ (N : ℝ)^(2/3 : ℝ)/100 :=
    (show (l : ℝ) ≤ Radius N by exact_mod_cast h.2.1).trans hR
  have hpow : (N : ℝ)^(1/3 : ℝ) * (N : ℝ)^(2/3 : ℝ) = N := by
    rw [← Real.rpow_add hNr]
    norm_num
  have hscale : (N : ℝ)^(1/3 : ℝ)/20 ≤ (N : ℝ)/(2000*l) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2000*l)).mpr
    have hprod := mul_le_mul_of_nonneg_left hlR
      (Real.rpow_nonneg hNr.le (1/3 : ℝ))
    nlinarith
  have hpow' : (N : ℝ)^(2/3 : ℝ) ≤ N := by
    calc
      _ ≤ (N : ℝ)^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast hN) (by norm_num)
      _ = _ := Real.rpow_one _
  have hlN : (l : ℝ) ≤ N := by nlinarith
  have hdiv : l ∣ M := dvd_trans (dvd_mul_left l 2) h.2.2.2
  apply (overflow_chernoff N M l hl hdiv (grid_lower_bound h)).trans
  apply mul_le_mul hlN _ (Real.exp_pos _).le hNr.le
  exact Real.exp_le_exp.mpr (by simpa only [neg_div] using neg_le_neg hscale)

end
end QuantumBipartiteTesting.Bipartiteness

open QuantumBipartiteTesting.Bipartiteness

theorem solution : ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ,
    ∀ N ≥ N₀, ∀ M l : ℕ, Grid N M l →
      ValidParameters N M l ∧ OverflowProbability N M l ≤ Real.exp (-c * (N : ℝ) ^ (1/3 : ℝ)) := by
  have ho : Asymptotics.IsLittleO Filter.atTop (fun N : ℕ => Real.log (N : ℝ))
      (fun N : ℕ => (N : ℝ)^(1/3 : ℝ)) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/3)).comp_tendsto
      tendsto_natCast_atTop_atTop
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp (ho.bound (by norm_num : (0 : ℝ) < 1/40))
  refine ⟨1/40,by norm_num,max N₀ 1,?_⟩
  intro N hN M l hgrid
  refine ⟨grid_valid hgrid, ?_⟩
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  have hlog := hN₀ N (le_trans (le_max_left _ _) hN)
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hNr.le (1/3 : ℝ))] at hlog
  have hlog' : Real.log (N : ℝ) ≤ (N : ℝ)^(1/3 : ℝ)/40 := by
    have := le_abs_self (Real.log (N : ℝ))
    linarith
  apply (grid_tail hNpos hgrid).trans
  calc
    _ = Real.exp (Real.log (N : ℝ) - (N : ℝ)^(1/3 : ℝ)/20) := by
      rw [show Real.log (N : ℝ) - (N : ℝ)^(1/3 : ℝ)/20 =
        Real.log (N : ℝ) + (-(N : ℝ)^(1/3 : ℝ)/20) by ring,
        Real.exp_add, Real.exp_log hNr]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
