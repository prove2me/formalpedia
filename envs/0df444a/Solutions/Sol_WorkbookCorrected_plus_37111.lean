-- Prove2me | solution 1 for WorkbookCorrected.plus_37111
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T15:00:48.296814+00:00
-- url     : https://prove2.me/submissions/4b2a2c74-d929-40dc-921d-e8529e8345bc

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
private lemma step (e t : ℝ) (ht : 4 ≤ t) (he0 : 0 ≤ e) (he : e ≤ 2/t) :
    0 ≤ e-e^2/2 ∧ e-e^2/2 ≤ 2/(t+1) := by
  have ht0 : 0 < t := by linarith
  have hb : 0 ≤ 2/t := by positivity
  have hb1 : 2/t ≤ 1/2 := (div_le_iff₀ ht0).mpr (by linarith)
  have he1 : e ≤ 1/2 := le_trans he hb1
  have hp := mul_nonneg he0 (show 0 ≤ 2-e by linarith)
  have hm := mul_nonneg (sub_nonneg.mpr he) (show 0 ≤ 2-2/t-e by linarith)
  have hid : 2/(t+1)-(2/t-(2/t)^2/2)=2/(t^2*(t+1)) := by
    field_simp
    ring
  have hpos : 0 ≤ 2/(t^2*(t+1)) := by positivity
  constructor
  · nlinarith only [hp]
  · nlinarith only [hm,hid,hpos]

theorem solution (a : ℕ → ℝ) (h1 : a 1=1/2)
    (h : ∀ n : ℕ, 1 ≤ n → a (n+1)=(a n^2+1)/2) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |a n-1| < ε := by
  have hb : ∀ n : ℕ, 0 ≤ 1-a (n+1) ∧ 1-a (n+1) ≤ 2/((n:ℝ)+4) := by
    intro n
    induction n with
    | zero => rw [h1]; norm_num
    | succ n ih =>
      have hh := step (1-a (n+1)) ((n:ℝ)+4) (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith) ih.1 ih.2
      rw [show n+1+1=(n+1)+1 by omega,h (n+1) (by omega)]
      push_cast
      rw [show (n:ℝ)+1+4=(n:ℝ)+4+1 by ring]
      constructor <;> nlinarith only [hh.1,hh.2]
  intro ε hε
  obtain ⟨K,hK⟩ := exists_nat_gt (2/ε)
  refine ⟨K+1,?_⟩
  intro n hn
  obtain ⟨m,rfl⟩ : ∃ m : ℕ, n=m+1 := ⟨n-1,by omega⟩
  have hKm : (K:ℝ) ≤ m := by exact_mod_cast (show K ≤ m by omega)
  have heps : 2/ε < (m:ℝ)+4 := by linarith
  have ht : 0 < (m:ℝ)+4 := by positivity
  have hlt : 2/((m:ℝ)+4) < ε := by
    apply (div_lt_iff₀ ht).mpr
    have hh := (div_lt_iff₀ hε).mp heps
    nlinarith only [hh]
  rw [abs_of_nonpos (by linarith [(hb m).1] : a (m+1)-1 ≤ 0)]
  have hh := lt_of_le_of_lt (hb m).2 hlt
  linarith only [hh]
example : (∀ (a : ℕ → ℝ) (h1 : a 1=1/2)
    (h : ∀ n : ℕ, 1 ≤ n → a (n+1)=(a n^2+1)/2),
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |a n-1| < ε) := @solution
#print axioms solution
