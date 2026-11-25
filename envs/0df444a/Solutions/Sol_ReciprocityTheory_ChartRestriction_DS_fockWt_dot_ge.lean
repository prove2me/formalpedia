-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.fockWt_dot_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:21:56.876253+00:00
-- url     : https://prove2.me/submissions/d694118c-de80-462f-a4fe-eb8ba2125941

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_cfa_rho_coord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) {lam : Fin n → ℝ} (hlam : StrictAnti lam)
    (s : Finset (Fin (n * n))) : dot (rhoHol ε - rhoN ε) lam ≤ dot (fockWt ε s) lam := by
  have h1 : dot (rhoHol ε - rhoN ε) lam = ∑ x : Fin n × Fin n, cfaM ε lam x := by
    simp only [dot, cfa_rho_coord, cfaM, Fintype.sum_prod_type, Finset.sum_mul, sub_mul,
      Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
    congr 1
    exact Finset.sum_comm
  have hroot : ∀ x : Fin n × Fin n, dot (modeWt ε x) lam =
      if ε x.1 = true ∧ ε x.2 = false then lam x.1 - lam x.2 else 0 := by
    intro x
    unfold modeWt
    split_ifs
    · simp [dot, root, sub_mul, Finset.sum_sub_distrib, Pi.single_apply]
    · simp [dot]
  have h2 : ∀ x, cfaM ε lam x ≤ 0 ∧ cfaM ε lam x ≤ dot (modeWt ε x) lam := by
    intro x
    rw [hroot]
    unfold cfaM
    by_cases hx : ε x.1 = true ∧ ε x.2 = false
    · by_cases hlt : x.2 < x.1
      · have := hlam hlt
        have hp : ε x.1 = true ∧ ε x.2 = false ∧ x.2 < x.1 := ⟨hx.1, hx.2, hlt⟩
        rw [if_pos hp, if_pos hp, if_pos hx]
        constructor <;> linarith
      · have := hlam.antitone (not_lt.1 hlt)
        have hn : ¬ (ε x.1 = true ∧ ε x.2 = false ∧ x.2 < x.1) := fun h => hlt h.2.2
        rw [if_neg hn, if_neg hn, if_pos hx, sub_self]
        constructor <;> linarith
    · have : ¬ (ε x.1 = true ∧ ε x.2 = false ∧ x.2 < x.1) := fun h => hx ⟨h.1, h.2.1⟩
      simp [hx, this]
  have h3 : dot (fockWt ε s) lam = ∑ k ∈ s, dot (modeWt ε (finProdFinEquiv.symm k)) lam := by
    simp only [dot, fockWt, Finset.sum_apply, Finset.sum_mul]
    exact Finset.sum_comm
  rw [h1, h3, ← Equiv.sum_comp finProdFinEquiv.symm (cfaM ε lam)]
  calc ∑ k, cfaM ε lam (finProdFinEquiv.symm k)
      ≤ ∑ k ∈ s, cfaM ε lam (finProdFinEquiv.symm k) := by
        rw [← Finset.sum_sdiff (Finset.subset_univ s)]
        have := Finset.sum_nonpos (s := univ \ s) fun k _ => (h2 (finProdFinEquiv.symm k)).1
        linarith
    _ ≤ _ := Finset.sum_le_sum fun k _ => (h2 _).2
end ReciprocityTheory.ChartRestriction.DS
