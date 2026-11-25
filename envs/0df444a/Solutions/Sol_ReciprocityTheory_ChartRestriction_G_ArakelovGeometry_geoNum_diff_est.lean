-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.geoNum_diff_est
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:05:16.91981+00:00
-- url     : https://prove2.me/submissions/c714aacc-eb4f-481c-bebb-1ad7aa94e8df

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SupportSubsetMonoBox
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AbsProdSubProdSubLinLe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_abs_prod_sub_prod_sub_lin_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_prod_update_split
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_abs_le_nrm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_nrm_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_geoNum_expand_real
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_geoNum_update_eq_snoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (m : ℕ) (V : Ideal (MRing ι)) (hS : SymmAt (m + 1) V) (x : K → ℤ) (b : K) :
    |(geoNum (m + 1) V (fun _ => x) : ℝ) - geoNum (m + 1) V (fun _ => x - uv b) -
        (m + 1) * geoNum (m + 1) V (Fin.snoc (fun _ => x) (uv b))| ≤
      coefB (m + 1) V * ((m + 1) * m * (nrm x + 2) ^ (m + 1 - 2)) := by
  have hlin : ((m + 1 : ℕ) : ℝ) * geoNum (m + 1) V (Fin.snoc (fun _ => x) (uv b)) =
      ∑ i : Fin (m + 1), (geoNum (m + 1) V (Function.update (fun _ => x) i (uv b)) : ℝ) := by
    have h : ∀ i : Fin (m + 1), (geoNum (m + 1) V (Function.update (fun _ => x) i (uv b)) : ℝ) =
        geoNum (m + 1) V (Fin.snoc (fun _ => x) (uv b)) := fun i => by
      rw [geoNum_update_eq_snoc m V hS x (uv b) i]
    rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  push_cast at hlin
  rw [hlin, geoNum_expand_real (m + 1) V hS (fun _ => x),
    geoNum_expand_real (m + 1) V hS (fun _ => x - uv b),
    Finset.sum_congr rfl fun i _ => geoNum_expand_real (m + 1) V hS (Function.update (fun _ => x) i (uv b))]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, coefB, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [← Finset.sum_mul, ← sub_mul, ← sub_mul, abs_mul, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have := abs_prod_sub_prod_sub_lin_le (Finset.univ : Finset (Fin (m + 1))) (fun i => (x (r i) : ℝ))
    (fun i => (uv b (r i) : ℝ)) (Y := nrm x + 1) (E := 1) (by linarith [nrm_nonneg x]) zero_le_one
    (fun i _ => (abs_le_nrm x _).trans (by linarith))
    (fun i _ => by simp only [uv, Pi.single_apply]; split_ifs <;> simp)
  simp only [Finset.card_univ, Fintype.card_fin, one_pow, mul_one] at this
  rw [show nrm x + 1 + 1 = nrm x + 2 by ring] at this
  have e1 : (∏ i, (((x - uv b) (r i) : ℤ) : ℝ)) = ∏ i, ((x (r i) : ℝ) - (uv b (r i) : ℝ)) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [Pi.sub_apply]
  have e2 : ∀ i, (∏ j, ((Function.update (fun _ => x) i (uv b) j (r j) : ℤ) : ℝ)) =
      (uv b (r i) : ℝ) * (∏ j with j < i, (x (r j) : ℝ)) * ∏ j with i < j, (x (r j) : ℝ) := by
    intro i
    rw [← prod_update_split]
    refine Finset.prod_congr rfl fun j _ => ?_
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  rw [e1, Finset.sum_congr rfl fun i _ => e2 i]
  push_cast at this
  exact this
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
