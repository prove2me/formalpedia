-- Prove2me | solution 1 for WorkbookCorrected.plus_23173
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T13:12:56.642933+00:00
-- url     : https://prove2.me/submissions/39c07adf-d181-45d4-bb50-e5f99ce0c400

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x : ℝ) :
    (∃ u v w : ℝ, u^3=x+7 ∧ v^3=2*x-1 ∧ w^3=x ∧ u-v=w) ↔ x=1 := by
  constructor
  · rintro ⟨u,v,w,hu,hv,hw,hs⟩
    have he : u=v+w := by linarith only [hs]
    have hp : 3*u*v*w=8-2*x := by
      rw [he] at hu ⊢
      nlinarith only [hu,hv,hw]
    have hc := congrArg (fun t : ℝ => t^3) hp
    have hi : (u*v*w)^3=(x+7)*(2*x-1)*x := by
      simp only [mul_pow,hu,hv,hw]
    have hf : (x-1)*(62*x^2+317*x+512)=0 := by
      nlinarith only [hc,hi]
    have hq : 0 < 62*x^2+317*x+512 := by
      nlinarith only [sq_nonneg (124*x+317)]
    rcases mul_eq_zero.mp hf with h | h
    · linarith only [h]
    · exact False.elim ((ne_of_gt hq) h)
  · intro hx
    subst x
    exact ⟨2,1,1,by norm_num,by norm_num,by norm_num,by norm_num⟩
example : (∀ (x : ℝ),
    (∃ u v w : ℝ, u^3=x+7 ∧ v^3=2*x-1 ∧ w^3=x ∧ u-v=w) ↔ x=1) := @solution
#print axioms solution
