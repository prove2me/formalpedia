-- Prove2me | solution 1 for WorkbookCorrected.plus_56310
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T15:24:46.24699+00:00
-- url     : https://prove2.me/submissions/0d10834d-5609-4186-b88d-4e91bbb27dcd

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem solution (x : ℕ → ℝ) (h1 : x 1=603) (h2 : x 2=102)
    (h : ∀ n : ℕ, 1 ≤ n → x (n+2)=x (n+1)+x n+2*Real.sqrt (x n*x (n+1)-2)) :
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℤ, x n=(k:ℝ) := by
  have hb : ∀ n : ℕ, ∃ m k r : ℕ,
      x (n+1)=(m:ℝ) ∧ x (n+2)=(k:ℝ) ∧ m*k=r^2+2 := by
    intro n
    induction n with
    | zero => exact ⟨603,102,248,by simpa using h1,by simpa using h2,by norm_num⟩
    | succ n ih =>
      obtain ⟨m,k,r,hm,hk,hr⟩ := ih
      have hrR : (m:ℝ)*(k:ℝ)=(r:ℝ)^2+2 := by exact_mod_cast hr
      have hs : Real.sqrt ((m:ℝ)*(k:ℝ)-2)=(r:ℝ) := by
        rw [show (m:ℝ)*(k:ℝ)-2=(r:ℝ)^2 by linarith only [hrR],Real.sqrt_sq (Nat.cast_nonneg r)]
      refine ⟨k,k+m+2*r,k+r,?_,?_,?_⟩
      · simpa only [Nat.add_assoc] using hk
      · rw [show n+1+2=(n+1)+2 by omega,h (n+1) (by omega),show n+1+1=n+2 by omega,hk,hm,hs]
        push_cast
        ring
      · nlinarith only [hr]
  intro n hn
  obtain ⟨t,rfl⟩ : ∃ t : ℕ, n=t+1 := ⟨n-1,by omega⟩
  obtain ⟨m,k,r,hm,hk,hr⟩ := hb t
  refine ⟨(m:ℤ),?_⟩
  simpa using hm
example : (∀ (x : ℕ → ℝ) (h1 : x 1=603) (h2 : x 2=102)
    (h : ∀ n : ℕ, 1 ≤ n → x (n+2)=x (n+1)+x n+2*Real.sqrt (x n*x (n+1)-2)),
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℤ, x n=(k:ℝ)) := @solution
#print axioms solution
