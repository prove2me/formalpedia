-- Prove2me | solution 1 for RobustSDP.Uniqueness.h3a_R_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T22:29:59.822901+00:00
-- url     : https://prove2.me/submissions/83972eb9-a2ee-495b-b545-de50c3aed045

import Mathlib
import Definitions.Def_RobustSDP_Uniqueness_Model
import Definitions.Def_RobustSDP_Uniqueness_Hypotheses

open Matrix RobustSDP.Uniqueness

theorem solution {m n p q : ℕ} (D : SDPData m n p q) (h3a : D.H3a) (x : Fin m → ℝ) :
    D.R x ≠ 0 := by
  obtain ⟨N, hNtop, hker⟩ := h3a
  intro hR0
  -- `R(x)` is the pencil at `λ = 1`, so H3(a) pins its kernel down to `N ≠ ⊤`
  have hpencil : D.pencil 1 x = D.R x := by
    simp only [SDPData.pencil, SDPData.R, one_smul]
  have hN := hker 1 x (Or.inl one_ne_zero)
  rw [hpencil, hR0] at hN
  have htop : LinearMap.ker (Matrix.toLin' (0 : Matrix (Fin q) (Fin n) ℝ)) = ⊤ := by
    rw [LinearMap.ker_eq_top]
    ext v
    simp [Matrix.toLin'_apply]
  rw [htop] at hN
  exact hNtop hN.symm
