-- Prove2me | solution 1 for WorkbookCorrected.plus_42198
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T15:06:14.136774+00:00
-- url     : https://prove2.me/submissions/eed9f9c3-dc55-45cc-8969-fdb45bbd2fa9

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem solution (a : ℕ → ℝ)
    (h : ∀ n : ℕ, 1 ≤ n → a (n+1)=(1-1/(n:ℝ))^2*a n+1/(n:ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |a n-1/2| < ε := by
  have hf : ∀ n : ℕ, a (n+2)=((n:ℝ)+2)/(2*((n:ℝ)+1)) := by
    intro n
    induction n with
    | zero => have hh := h 1 (by omega); norm_num at hh ⊢; exact hh
    | succ n ih =>
      rw [show n+1+2=(n+2)+1 by omega,h (n+2) (by omega),ih]
      push_cast
      have hp : (0:ℝ) < (n:ℝ)+1 := by positivity
      have hp2 : (0:ℝ) < (n:ℝ)+2 := by positivity
      field_simp
      ring
  have he : ∀ n : ℕ, a (n+2)-1/2=1/(2*((n:ℝ)+1)) := by
    intro n
    rw [hf n]
    have hp : (0:ℝ) < (n:ℝ)+1 := by positivity
    field_simp
    ring
  intro ε hε
  obtain ⟨K,hK⟩ := exists_nat_gt (1/ε)
  refine ⟨K+2,?_⟩
  intro n hn
  obtain ⟨m,rfl⟩ : ∃ m : ℕ, n=m+2 := ⟨n-2,by omega⟩
  have hKm : (K:ℝ) ≤ m := by exact_mod_cast (show K ≤ m by omega)
  rw [he m,abs_of_pos (by positivity)]
  apply (div_lt_iff₀ (by positivity : (0:ℝ) < 2*((m:ℝ)+1))).mpr
  have hh := (div_lt_iff₀ hε).mp (lt_of_lt_of_le hK hKm)
  have hmε := mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (le_of_lt hε)
  nlinarith only [hh,hmε,hε]
example : (∀ (a : ℕ → ℝ)
    (h : ∀ n : ℕ, 1 ≤ n → a (n+1)=(1-1/(n:ℝ))^2*a n+1/(n:ℝ)),
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |a n-1/2| < ε) := @solution
#print axioms solution
