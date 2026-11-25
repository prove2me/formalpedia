-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.sum_minorWeights_indicator_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:18:08.525414+00:00
-- url     : https://prove2.me/submissions/bd2f5b03-daa5-44bf-ba15-7c4e7a2e554a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CBinet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecMomentsA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dm_sum_castLE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dm_entry
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dm_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dm_one_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dm_mass
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_sum_minorWeights_indicator
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_lead_unitary_diag


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) {i : ℕ} (hi : i ≤ n)
    (k l : Fin n) (hkl : k ≠ l) :
    ∑ J : {J : Finset (Fin n) // J.card = i}, ((dmW U hi J : ℝ) : ℂ) * (dmInd J.1 k * dmInd J.1 l) =
      dmK U i k k * dmK U i l l - dmK U i k l * dmK U i l k := by
  have h := lead_unitary_diag (U := U)
    (fun j => (if j = k then (2 : ℂ) else 1) * (if j = l then (2 : ℂ) else 1)) i hi
  have hprod : ∀ J : Finset (Fin n),
      ∏ j ∈ J, ((if j = k then (2 : ℂ) else 1) * (if j = l then (2 : ℂ) else 1)) =
        1 + dmInd J k + dmInd J l + dmInd J k * dmInd J l := by
    intro J
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']
    unfold dmInd; split_ifs <;> norm_num
  simp only [hprod, mul_add, mul_one, Finset.sum_add_distrib] at h
  have hm := dm_mass hU hi
  have h1 := sum_minorWeights_indicator hU hi k
  have h2 := sum_minorWeights_indicator hU hi l
  simp only [dmW] at hm h1 h2 ⊢
  rw [hm, h1, h2] at h
  let W : Matrix (Fin i) (Fin 2) ℂ :=
    Matrix.of fun a c => if c = 0 then U (Fin.castLE hi a) k else U (Fin.castLE hi a) l
  have hsub : (U * Matrix.diagonal (fun j => (if j = k then (2 : ℂ) else 1) * (if j = l then (2 : ℂ) else 1))
      * Uᴴ).submatrix (Fin.castLE hi) (Fin.castLE hi) = 1 + W * Wᴴ := by
    ext a b
    rw [Matrix.submatrix_apply, dm_entry]
    have hj : ∀ j, U (Fin.castLE hi a) j * ((if j = k then (2 : ℂ) else 1) * (if j = l then (2 : ℂ) else 1))
        * star (U (Fin.castLE hi b) j)
        = U (Fin.castLE hi a) j * star (U (Fin.castLE hi b) j) +
          ((if k = j then U (Fin.castLE hi a) k * star (U (Fin.castLE hi b) k) else 0) +
          (if l = j then U (Fin.castLE hi a) l * star (U (Fin.castLE hi b) l) else 0)) := by
      intro j
      by_cases hjk : j = k
      · have hjl : j ≠ l := hjk ▸ hkl
        rw [if_pos hjk, if_neg hjl, if_pos hjk.symm, if_neg (Ne.symm hjl), hjk]; ring
      · by_cases hjl : j = l
        · rw [if_neg hjk, if_pos hjl, if_neg (Ne.symm hjk), if_pos hjl.symm, hjl]; ring
        · rw [if_neg hjk, if_neg hjl, if_neg (Ne.symm hjk), if_neg (Ne.symm hjl)]; ring
    simp only [hj, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, dm_unit hU,
      dm_one_sub]
    simp [Matrix.mul_apply, W, Fin.sum_univ_two]
  have hK : ∀ c c' : Fin 2, (Wᴴ * W) c c' = dmK U i (![k, l] c) (![k, l] c') := by
    intro c c'
    rw [Matrix.mul_apply, dmK, ← dm_sum_castLE hi (fun a => star (U a (![k, l] c)) * U a (![k, l] c'))]
    refine Finset.sum_congr rfl fun a _ => ?_
    fin_cases c <;> fin_cases c' <;> simp [W]
  rw [lead, dif_pos hi, hsub, Matrix.det_one_add_mul_comm, Matrix.det_fin_two] at h
  simp only [Matrix.add_apply, hK, Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), Matrix.cons_val_zero, Matrix.cons_val_one,
    zero_add] at h
  linear_combination -h
end ReciprocityTheory.ChartRestriction.DS.S7
