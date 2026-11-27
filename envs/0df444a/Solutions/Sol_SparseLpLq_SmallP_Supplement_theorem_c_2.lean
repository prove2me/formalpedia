-- Prove2me | solution 1 for SparseLpLq.SmallP.Supplement.theorem_c_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:40:32.794814+00:00
-- url     : https://prove2.me/submissions/3737806c-d856-4d1a-b4f6-ddf880ee470a

import Mathlib
import Definitions.Def_SparseLpLq_SmallP_Setting
import Definitions.Def_SparseLpLq_SmallP_Supplement_Penalty

open scoped ENNReal Matrix Topology

open SparseLpLq
open SparseLpLq.SmallP
open SparseLpLq.SmallP.Supplement

open SparseLpLq.SmallP
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ : ℝ)
    (hσ : 0 ≤ σ) (hfeas : (FEA A b σ 1).Nonempty) (hb : σ < qNorm 1 b)
    (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (x : Fin n → ℝ) (hx : x ∈ SOL A b σ p 1) :
    ∀ ε : ℝ, 0 < ε → ∃ lamε : ℝ, 0 < lamε ∧
      ∀ lam : ℝ, lamε ≤ lam → IsEpsMinPen A b σ p lam ε x := by
        classical
        have hp0 : 0 < p := hp.1
        have hpne : p ≠ 0 := ne_of_gt hp0
        have hnonneg : ∀ y : Fin n → ℝ, 0 ≤ lpObj p y := by
          intro y
          simp only [lpObj, if_neg hpne]
          exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _
        have hobj : Continuous (lpObj p : (Fin n → ℝ) → ℝ) := by
          change Continuous (fun y : Fin n → ℝ => lpObj p y)
          simp only [lpObj, if_neg hpne]
          apply continuous_finsetSum
          intro i hi
          exact (continuous_apply i).abs.rpow_const (fun _ => Or.inr hp0.le)
        have hres : Continuous (fun y : Fin n → ℝ => qNorm 1 (A *ᵥ y - b)) := by
          unfold qNorm
          apply Continuous.norm
          apply (PiLp.continuous_toLp 1 (fun _ : Fin m => ℝ)).comp
          apply continuous_pi
          intro i
          simp only [Pi.sub_apply, Matrix.mulVec, dotProduct]
          exact (continuous_finsetSum _ fun j _ =>
            continuous_const.mul (continuous_apply j)).sub continuous_const
        have hx' : x ∈ FEA A b σ 1 ∧
            ∀ y ∈ FEA A b σ 1, lpObj p x ≤ lpObj p y := hx
        intro ε hε
        let c : ℝ := lpObj p x
        have hc : 0 ≤ c := hnonneg x
        let R : ℝ := c ^ p⁻¹
        let S : Set (Fin n → ℝ) := {y | lpObj p y ≤ c - ε}
        have hSclosed : IsClosed S := isClosed_le hobj continuous_const
        have hSbounded : S ⊆ Set.Icc (fun _ => -R) (fun _ => R) := by
          intro y hy
          have hy' : lpObj p y ≤ c - ε := hy
          have hcoord : ∀ i, |y i| ≤ R := by
            intro i
            have hi : |y i| ^ p ≤ c := by
              calc
                |y i| ^ p ≤ ∑ j : Fin n, |y j| ^ p :=
                  Finset.single_le_sum (fun j _ => Real.rpow_nonneg (abs_nonneg _) _)
                    (Finset.mem_univ i)
                _ = lpObj p y := by simp only [lpObj, if_neg hpne]
                _ ≤ c := by linarith
            have hi' := Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg (y i)) p)
              hi (inv_nonneg.mpr hp0.le)
            simpa only [Real.rpow_rpow_inv (abs_nonneg (y i)) hpne] using hi'
          exact ⟨fun i => (abs_le.mp (hcoord i)).1, fun i => (abs_le.mp (hcoord i)).2⟩
        have hScompact : IsCompact S := isCompact_Icc.of_isClosed_subset hSclosed hSbounded
        have hSres : ∀ y ∈ S, σ < qNorm 1 (A *ᵥ y - b) := by
          intro y hy
          by_contra h
          have hyfeas : y ∈ FEA A b σ 1 := le_of_not_gt h
          have hopt := hx'.2 y hyfeas
          have hy' : lpObj p y ≤ c - ε := hy
          dsimp [c] at hy'
          linarith
        obtain ⟨r, hr, hrlower⟩ := hScompact.exists_forall_le' hres.continuousOn hSres
        have hd : 0 < r - σ := sub_pos.mpr hr
        let L : ℝ := (c + 1) / (r - σ)
        have hL : 0 < L := div_pos (by linarith) hd
        refine ⟨L, hL, ?_⟩
        intro lam hlam
        have hlam0 : 0 ≤ lam := le_trans hL.le hlam
        have hFx : Fpen A b σ p lam x = c := by
          have hxf : qNorm 1 (A *ᵥ x - b) ≤ σ := hx'.1
          simp only [Fpen, max_eq_right (sub_nonpos.mpr hxf), mul_zero, add_zero]
          rfl
        intro y
        rw [hFx]
        by_cases hy : c ≤ lpObj p y + ε
        · have hpen : 0 ≤ lam * max (qNorm 1 (A *ᵥ y - b) - σ) 0 :=
            mul_nonneg hlam0 (le_max_right _ _)
          unfold Fpen
          linarith
        · have hyS : y ∈ S := by
            change lpObj p y ≤ c - ε
            linarith
          have hresy := hrlower y hyS
          have hdy : r - σ ≤ max (qNorm 1 (A *ᵥ y - b) - σ) 0 := by
            exact le_trans (sub_le_sub_right hresy σ) (le_max_left _ _)
          have hprod : c + 1 ≤ lam * max (qNorm 1 (A *ᵥ y - b) - σ) 0 := by
            calc
              c + 1 = L * (r - σ) := by
                dsimp [L]
                exact (div_mul_cancel₀ (c + 1) (ne_of_gt hd)).symm
              _ ≤ lam * (r - σ) := mul_le_mul_of_nonneg_right hlam hd.le
              _ ≤ lam * max (qNorm 1 (A *ᵥ y - b) - σ) 0 :=
                mul_le_mul_of_nonneg_left hdy hlam0
          have hny := hnonneg y
          unfold Fpen
          linarith
