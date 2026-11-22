-- Prove2me | solution 1 for PolyDiagonalJetRigidity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:15:12.334107+00:00
-- url     : https://prove2.me/submissions/6115b146-998d-4e6d-addb-09824e52784e

import Definitions.Def_PHigherOrder_IteratedDerivAlongRay
import Definitions.Def_PHigherOrder_PolyDiagonalJetRigidity
import Theorems.Thm_IteratedDerivAlongRay


set_option autoImplicit false

theorem _root_.solution (k : ℕ) (S : Plane → ℝ) (hS : ContDiff ℝ (⊤ : ℕ∞) S)
    (htop : ∀ w : Plane, iteratedFDeriv ℝ (k + 1) S w = 0)
    (hjets : ∀ j : ℕ, j ≤ k → ∀ w : Plane, iteratedFDeriv ℝ j S 0 (fun _ => w) = 0) :
    S = 0 := by
  funext x
  show S x = 0
  -- the ray `s ↦ 0 + s • x`, and the restriction of `S` to it
  have haff : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => (0 : Plane) + s • x) :=
    contDiff_const.add ((ContinuousLinearMap.id ℝ ℝ).smulRight x).contDiff
  have hphi : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => S ((0 : Plane) + s • x)) := hS.comp haff
  -- every one-variable derivative along the ray is a diagonal evaluation
  have hray : ∀ (j : ℕ) (t : ℝ),
      iteratedDeriv j (fun s : ℝ => S ((0 : Plane) + s • x)) t
        = iteratedFDeriv ℝ j S ((0 : Plane) + t • x) (fun _ => x) := by
    intro j t
    exact IteratedDerivAlongRay Set.univ isOpen_univ S j
      (hS.contDiffOn.of_le (by exact_mod_cast le_top)) 0 x t (Set.mem_univ _)
  -- the degree-`k` Taylor polynomial at `0` collapses, every term killed by `hjets`
  have hpoly : taylorWithinEval (fun s : ℝ => S ((0 : Plane) + s • x)) k (Set.uIcc 0 1) 0 1
      = 0 := by
    rw [taylor_within_apply]
    refine Finset.sum_eq_zero ?_
    intro j hj
    have hjk : j ≤ k := by
      have := Finset.mem_range.mp hj
      omega
    have hzero : iteratedDerivWithin j (fun s : ℝ => S ((0 : Plane) + s • x))
        (Set.uIcc 0 1) 0 = 0 := by
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (by norm_num))
          (hphi.contDiffAt.of_le (by exact_mod_cast le_top)) Set.left_mem_uIcc,
        hray j 0, zero_smul, add_zero]
      exact hjets j hjk x
    rw [hzero, smul_zero]
  -- Taylor with Lagrange remainder on `[0,1]`;  the remainder is a diagonal evaluation of
  -- `D^{k+1} S`, which vanishes identically
  obtain ⟨ξ, hξ, hTay⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (f := fun s : ℝ => S ((0 : Plane) + s • x)) (x₀ := (0 : ℝ)) (x := (1 : ℝ)) (n := k)
      (by norm_num) (hphi.contDiffOn.of_le (by exact_mod_cast le_top))
  rw [hpoly, hray (k + 1) ξ, htop ((0 : Plane) + ξ • x)] at hTay
  simpa using hTay
