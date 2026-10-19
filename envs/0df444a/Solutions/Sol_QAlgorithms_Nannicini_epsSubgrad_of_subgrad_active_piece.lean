-- Prove2me | solution 1 for QAlgorithms.Nannicini.epsSubgrad_of_subgrad_active_piece
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T10:22:01.165739+00:00
-- url     : https://prove2.me/submissions/a11f8649-3812-40a5-aebd-4fbfc72e5ff9

import Definitions.Def_QAlgorithms_Defs_SDP
import Definitions.Def_QAlgorithms_Nannicini_Ch08b_Model
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open QAlgorithms QAlgorithms.SDP

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (h : Fin m → E → ℝ) (hLip : ∀ i, LipschitzWith 1 (h i))
    (_hconv : ∀ i, ConvexOn ℝ Set.univ (h i)) (ε : ℝ) (xbar xhat : E)
    (hdist : ‖xbar - xhat‖ ≤ ε * 4⁻¹) (j : Fin m) (hj : ∀ i, h i xhat ≤ h j xhat)
    (g : E →L[ℝ] ℝ) (hg : IsEpsSubgradOn Set.univ (h j) 0 xhat g.toLinearMap) :
    IsEpsSubgradOn Set.univ
      (fun x => Finset.univ.sup' ⟨j, Finset.mem_univ j⟩ fun i => h i x)
      (ε * 4⁻¹ * (‖g‖ + 1)) xbar g.toLinearMap := by
  classical
  have hmax :
      (Finset.univ.sup' ⟨j, Finset.mem_univ j⟩ fun i => h i xbar) ≤
        h j xhat + ε * 4⁻¹ := by
    apply Finset.sup'_le
    intro i hi
    have hiLip := (hLip i).dist_le_mul xbar xhat
    have hiDiff : h i xbar - h i xhat ≤ ‖xbar - xhat‖ := by
      exact (le_abs_self _).trans (by simpa [Real.dist_eq, dist_eq_norm] using hiLip)
    linarith [hj i]
  intro x hx
  have hsub := hg x (Set.mem_univ x)
  have hpiece : h j x ≤ Finset.univ.sup' ⟨j, Finset.mem_univ j⟩ (fun i => h i x) :=
    Finset.le_sup' (fun i => h i x) (Finset.mem_univ j)
  have hdual : -g (xbar - xhat) ≤ ‖g‖ * (ε * 4⁻¹) := by
    calc
      -g (xbar - xhat) ≤ ‖g (xbar - xhat)‖ := neg_le_abs _
      _ ≤ ‖g‖ * ‖xbar - xhat‖ := g.le_opNorm _
      _ ≤ ‖g‖ * (ε * 4⁻¹) := mul_le_mul_of_nonneg_left hdist (norm_nonneg g)
  have hlin : g (x - xbar) = g (x - xhat) - g (xbar - xhat) := by
    rw [← map_sub]
    congr 1
    abel
  change h j xhat + g (x - xhat) - 0 ≤ h j x at hsub
  change (Finset.univ.sup' ⟨j, Finset.mem_univ j⟩ fun i => h i xbar) +
    g (x - xbar) - ε * 4⁻¹ * (‖g‖ + 1) ≤ _
  rw [hlin]
  nlinarith
