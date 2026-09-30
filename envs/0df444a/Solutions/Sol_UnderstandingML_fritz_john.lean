-- Prove2me | solution 1 for UnderstandingML.fritz_john
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T18:16:36.179636+00:00
-- url     : https://prove2.me/submissions/7d020c41-5fc6-4c34-bf24-1898982cd826

import Definitions.Def_UnderstandingML_SVM
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

open MeasureTheory Filter Topology
open scoped InnerProductSpace
open UnderstandingML

namespace FritzJohnAux

/-- Along a direction of negative directional derivative, a differentiable function strictly
decreases for small positive steps. -/
theorem eventually_lt_of_inner_gradient_neg {d : ℕ} (φ : Vec d → ℝ) (w δ : Vec d)
    (hφ : DifferentiableAt ℝ φ w) (h : ⟪gradient φ w, δ⟫_ℝ < 0) :
    ∀ᶠ t in 𝓝[>] (0:ℝ), φ (w + t • δ) < φ w := by
  have hline : HasDerivAt (fun t : ℝ => w + t • δ) δ 0 := by
    simpa using HasDerivAt.const_add w (HasDerivAt.smul_const (hasDerivAt_id (0:ℝ)) δ)
  have hcomp : HasDerivAt (fun t : ℝ => φ (w + t • δ)) (fderiv ℝ φ w δ) 0 := by
    have hφ' : HasFDerivAt φ (fderiv ℝ φ w) ((fun t : ℝ => w + t • δ) 0) := by
      simpa using hφ.hasFDerivAt
    exact HasFDerivAt.comp_hasDerivAt (0:ℝ) hφ' hline
  have hval : fderiv ℝ φ w δ = ⟪gradient φ w, δ⟫_ℝ := by
    rw [gradient, InnerProductSpace.toDual_symm_apply]
  rw [hval] at hcomp
  have hslope := HasDerivAt.tendsto_slope_zero_right hcomp
  have hev := hslope.eventually (eventually_lt_nhds h)
  filter_upwards [hev, self_mem_nhdsWithin] with t ht htpos
  have htpos' : (0:ℝ) < t := htpos
  simp only [zero_add, zero_smul, add_zero, smul_eq_mul] at ht
  have : φ (w + t • δ) - φ w < 0 := by
    have h2 : t⁻¹ * (φ (w + t • δ) - φ w) < 0 := ht
    rcases lt_or_ge (φ (w + t • δ) - φ w) 0 with h3 | h3
    · exact h3
    · exact absurd h2 (not_lt.mpr (mul_nonneg (inv_nonneg.mpr htpos'.le) h3))
  linarith

end FritzJohnAux

open FritzJohnAux in
theorem solution {d m : ℕ} (f : Vec d → ℝ) (g : Fin m → Vec d → ℝ) (hf : Differentiable ℝ f)
    (hg : ∀ i, Differentiable ℝ (g i)) (wstar : Vec d) (hfeas : ∀ i, g i wstar ≤ 0)
    (hmin : ∀ w, (∀ i, g i w ≤ 0) → f wstar ≤ f w) :
    ∃ (α₀ : ℝ) (α : Fin m → ℝ), 0 ≤ α₀ ∧ (∀ i, 0 ≤ α i) ∧ (α₀ ≠ 0 ∨ ∃ i, α i ≠ 0) ∧
      (∀ i, g i wstar ≠ 0 → α i = 0) ∧
      α₀ • gradient f wstar + ∑ i, α i • gradient (g i) wstar = 0 := by
  classical
  set v : Option (Fin m) → Vec d := fun j => match j with
    | none => gradient f wstar
    | some i => if g i wstar = 0 then gradient (g i) wstar else gradient f wstar with hv
  by_cases h0 : (0 : Vec d) ∈ convexHull ℝ (Set.range v)
  · rw [convexHull_range_eq_exists_affineCombination] at h0
    obtain ⟨s, μ', hμ'0, hμ'1, hμ'v⟩ := h0
    rw [Finset.affineCombination_eq_linear_combination s v μ' hμ'1] at hμ'v
    set μ : Option (Fin m) → ℝ := fun j => if j ∈ s then μ' j else 0 with hμ
    have hμ0 : ∀ j, 0 ≤ μ j := by
      intro j; simp only [hμ]; split_ifs with hj
      · exact hμ'0 j hj
      · exact le_refl 0
    have hμ1 : ∑ j, μ j = 1 := by
      rw [← hμ'1, ← Finset.sum_subset (Finset.subset_univ s)]
      · exact Finset.sum_congr rfl fun j hj => by simp [hμ, hj]
      · intro j _ hj; simp [hμ, hj]
    have hμv : ∑ j, μ j • v j = 0 := by
      rw [← hμ'v, ← Finset.sum_subset (Finset.subset_univ s)]
      · exact Finset.sum_congr rfl fun j hj => by simp [hμ, hj]
      · intro j _ hj; simp [hμ, hj]
    set r : Fin m → ℝ := fun i => if g i wstar = 0 then 0 else μ (some i) with hr
    refine ⟨μ none + ∑ i, r i, fun i => if g i wstar = 0 then μ (some i) else 0, ?_, ?_, ?_, ?_, ?_⟩
    · exact add_nonneg (hμ0 none) (Finset.sum_nonneg fun i _ => by
        simp only [hr]; split_ifs
        · exact le_refl 0
        · exact hμ0 _)
    · intro i; simp only; split_ifs
      · exact hμ0 _
      · exact le_refl 0
    · by_contra hcon
      push Not at hcon
      obtain ⟨hα₀, hα⟩ := hcon
      have : ∑ j, μ j = μ none + ∑ i, r i + ∑ i, (if g i wstar = 0 then μ (some i) else 0) := by
        rw [Fintype.sum_option, add_assoc, ← Finset.sum_add_distrib]
        congr 1
        exact Finset.sum_congr rfl fun i _ => by simp only [hr]; split_ifs <;> ring
      rw [hμ1, hα₀, zero_add, Finset.sum_eq_zero fun i _ => hα i] at this
      norm_num at this
    · intro i hi; simp [hi]
    · rw [Fintype.sum_option] at hμv
      rw [← hμv, add_smul, add_assoc, Finset.sum_smul, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hv, hr]
      split_ifs <;> simp
  · exfalso
    have hclosed : IsClosed (convexHull ℝ (Set.range v)) :=
      ((Set.finite_range v).isCompact_convexHull ℝ).isClosed
    obtain ⟨φ, u, hφu, hu0⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ _)
      hclosed h0
    rw [map_zero] at hu0
    set δ : Vec d := (InnerProductSpace.toDual ℝ (Vec d)).symm φ with hδ
    have hneg : ∀ j, ⟪v j, δ⟫_ℝ < 0 := by
      intro j
      rw [real_inner_comm, hδ, InnerProductSpace.toDual_symm_apply]
      exact lt_trans (hφu _ (subset_convexHull ℝ _ ⟨j, rfl⟩)) hu0
    have hfd : ⟪gradient f wstar, δ⟫_ℝ < 0 := hneg none
    have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), f (wstar + t • δ) < f wstar ∧
        ∀ i, g i (wstar + t • δ) ≤ 0 := by
      refine (eventually_lt_of_inner_gradient_neg f wstar δ (hf _) hfd).and ?_
      rw [Filter.eventually_all]
      intro i
      by_cases hi : g i wstar = 0
      · have hgi : ⟪gradient (g i) wstar, δ⟫_ℝ < 0 := by
          have := hneg (some i); simpa [hv, hi] using this
        filter_upwards [eventually_lt_of_inner_gradient_neg (g i) wstar δ (hg i _) hgi]
          with t ht
        linarith
      · have hlt : g i wstar < 0 := lt_of_le_of_ne (hfeas i) hi
        have hc : Continuous (fun t : ℝ => g i (wstar + t • δ)) :=
          (hg i).continuous.comp (by fun_prop)
        have := (hc.tendsto 0).eventually (eventually_lt_nhds (by simpa using hlt))
        exact nhdsWithin_le_nhds (this.mono fun t ht => ht.le)
    obtain ⟨t, ht1, ht2⟩ := hev.exists
    exact absurd (hmin _ ht2) (not_le.mpr ht1)
