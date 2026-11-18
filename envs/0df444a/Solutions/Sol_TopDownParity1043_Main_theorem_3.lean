-- Prove2me | solution 1 for TopDownParity1043.Main.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T16:43:19.689077+00:00
-- url     : https://prove2.me/submissions/c177ca2e-e1cd-4fed-9d27-96d45a721ace

import Mathlib
import Theorems.Thm_TopDownParity1043_Main_parity_finite_obstruction
import Theorems.Thm_TopDownParity1043_Main_circuit_to_protocol

set_option autoImplicit false
open TopDownParity1043.Main

private theorem power_budget (t n : ℕ) (ht : 1 ≤ t) (hn : 0 < n)
    (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ (n : ℝ)^((t : ℝ)⁻¹)/4) :
    a^t*(2/(n : ℝ)) ≤ 1/2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hp := pow_le_pow_left₀ ha0 ha t
  have hr : ((n : ℝ)^((t : ℝ)⁻¹))^t = n :=
    Real.rpow_inv_natCast_pow (Nat.cast_nonneg n) (by omega)
  have hquarter : (1/4 : ℝ)^t ≤ 1/4 := by
    cases t with
    | zero => omega
    | succ t =>
      rw [pow_succ]
      have hh : (1/4 : ℝ)^t ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith
  calc
    a^t*(2/(n : ℝ)) ≤ ((n : ℝ)^((t : ℝ)⁻¹)/4)^t*(2/(n : ℝ)) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = (1/4 : ℝ)^t*2 := by
      rw [div_pow,hr,div_pow,one_pow]
      field_simp
    _ ≤ 1/2 := by linarith

private theorem fanIn_le_wires {V : Type} (C : ParityBarrier563.Trilinear.Circuit V) :
    maxFanIn C ≤ wires C := by
  apply Finset.sup_le
  intro i hi
  change (C.inputs i).length ≤ ∑ j : Fin C.size, (C.inputs j).length
  exact Finset.single_le_sum (fun j hj => Nat.zero_le (C.inputs j).length) (Finset.mem_univ i)

theorem solution (d : ℕ) (hd : 2 ≤ d) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∀ m : ℕ, (m : ℝ) ≤ ε * (n : ℝ) ^ (1 / ((d : ℝ) - 1)) →
        ¬ HasKWProtocol (parity n) d m) ∧
      (∀ C : ParityBarrier563.Trilinear.Circuit (Fin n),
        C.depth ≤ d → C.Computes (parity n) →
        (2 : ℝ) ^ (ε * (n : ℝ) ^ (1 / ((d : ℝ) - 1))) < (wires C : ℝ)) := by
  let t := d-1
  have ht : 1 ≤ t := by dsimp [t]; omega
  have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have htcast : (t : ℝ) = (d : ℝ)-1 := by
    dsimp [t]
    rw [Nat.cast_sub (by omega),Nat.cast_one]
  have hexp : 1/((d : ℝ)-1) = (t : ℝ)⁻¹ := by rw [← htcast,one_div]
  let A : ℝ := 32768*(196 : ℝ)^t
  have hA : 0 < A := by dsimp [A]; positivity
  let ε : ℝ := (16*A)⁻¹
  have hε : 0 < ε := by dsimp [ε]; positivity
  let N := ⌈(16*A)^t⌉₊ + 4
  refine ⟨ε,hε,N,?_⟩
  intro n hn
  rw [hexp]
  have hn4 : 4 ≤ n := by dsimp [N] at hn; omega
  have hn0 : 0 < n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hN : (16*A)^t ≤ (n : ℝ) := by
    apply (Nat.le_ceil _).trans
    exact_mod_cast (show ⌈(16*A)^t⌉₊ ≤ n by dsimp [N] at hn; omega)
  let b : ℝ := (n : ℝ)^((t : ℝ)⁻¹)
  have hb : 0 < b := by dsimp [b]; positivity
  have hroot : 16*A ≤ b := by
    apply (Real.le_rpow_inv_iff_of_pos (by positivity) (Nat.cast_nonneg n) htpos).mpr
    rw [Real.rpow_natCast]
    exact hN
  have hεA : ε*(16*A) = 1 := by dsimp [ε]; field_simp
  have hscale : 1 ≤ ε*b := by nlinarith
  have hprotocol : ∀ m : ℕ, (m : ℝ) ≤ 2*(ε*b) → ¬HasKWProtocol (parity n) d m := by
    intro m hm
    let p : Bias := ⟨2/(n : ℝ),⟨by positivity,by
      apply (div_le_one hnpos).mpr
      exact_mod_cast (show 2 ≤ n by omega)⟩⟩
    have hp : 0 < (p : ℝ) := by dsimp [p]; positivity
    have hnp : 2 ≤ (n : ℝ)*(p : ℝ) := by dsimp [p]; field_simp; norm_num
    have ham : 0 ≤ A*((m : ℝ)+1) := mul_nonneg hA.le (by positivity)
    have ham' : A*((m : ℝ)+1) ≤ b/4 := by
      have hm' : (m : ℝ)+1 ≤ 4*(ε*b) := by linarith
      have hh := mul_le_mul_of_nonneg_left hm' hA.le
      have heq : A*(4*(ε*b)) = b/4 := by
        dsimp [ε]
        field_simp
        ring
      rwa [heq] at hh
    apply parity_finite_obstruction n d m hn0 (by omega) p hp hnp
    exact power_budget t n ht hn0 (A*((m : ℝ)+1)) ham ham'
  constructor
  · intro m hm
    exact hprotocol m (hm.trans (by nlinarith))
  · intro C hdepth hcomp
    by_contra hnot
    have hw : (wires C : ℝ) ≤ (2 : ℝ)^(ε*b) := le_of_not_gt hnot
    let m := ⌈ε*b⌉₊
    have hm : (m : ℝ) ≤ 2*(ε*b) := by
      have hh := Nat.ceil_lt_add_one (show 0 ≤ ε*b by positivity)
      dsimp [m]
      linarith
    apply hprotocol m hm
    have hpow : (2 : ℝ)^(ε*b) ≤ (2 : ℝ)^m := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
    have hwNat : wires C ≤ 2^m := by exact_mod_cast hw.trans hpow
    apply TopDownParity1043.Main.circuit_to_protocol n d m (parity n)
    exact ⟨C,hdepth,(fanIn_le_wires C).trans hwNat,hcomp⟩
