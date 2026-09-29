-- Prove2me | solution 1 for WorkbookCorrected.plus_40328
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T15:02:37.125905+00:00
-- url     : https://prove2.me/submissions/5acb8b97-60fc-461e-b444-246c9449fd65

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem solution (a : ℕ → ℝ) (h1 : a 1=1)
    (h : ∀ n : ℕ, 1 ≤ n → a (n+1)=2*a n+Real.sqrt (3*a n^2+1)) :
    ∀ n : ℕ, 1 ≤ n → a n = (⌊a n⌋ : ℤ) := by
  have hb : ∀ n : ℕ, ∃ m k : ℕ, a (n+1)=(m:ℝ) ∧ k^2=3*m^2+1 := by
    intro n
    induction n with
    | zero => exact ⟨1,2,by simpa using h1,by norm_num⟩
    | succ n ih =>
      obtain ⟨m,k,hm,hk⟩ := ih
      have hkR : (k:ℝ)^2=3*(m:ℝ)^2+1 := by exact_mod_cast hk
      have hs : Real.sqrt (3*(m:ℝ)^2+1)=(k:ℝ) := by
        rw [← hkR,Real.sqrt_sq (Nat.cast_nonneg k)]
      refine ⟨2*m+k,3*m+2*k,?_,?_⟩
      · rw [show n+1+1=(n+1)+1 by omega,h (n+1) (by omega),hm,hs]
        push_cast
        ring
      · nlinarith only [hk]
  intro n hn
  obtain ⟨t,rfl⟩ : ∃ t : ℕ, n=t+1 := ⟨n-1,by omega⟩
  obtain ⟨m,k,hm,hk⟩ := hb t
  rw [hm]
  simp
example : (∀ (a : ℕ → ℝ) (h1 : a 1=1)
    (h : ∀ n : ℕ, 1 ≤ n → a (n+1)=2*a n+Real.sqrt (3*a n^2+1)),
    ∀ n : ℕ, 1 ≤ n → a n = (⌊a n⌋ : ℤ)) := @solution
#print axioms solution
