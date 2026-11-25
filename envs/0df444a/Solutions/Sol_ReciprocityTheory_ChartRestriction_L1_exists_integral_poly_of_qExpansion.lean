-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.exists_integral_poly_of_qExpansion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:06:03.983006+00:00
-- url     : https://prove2.me/submissions/56471cd9-542c-4f49-88c8-a0df401fe5b5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEisInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDeltaInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_analytic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_qExp_AA_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_aC_coeff_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_div_DD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_coeffIn_of_dC_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_low_of_dC_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_DD_ne_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_congr_weight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_const_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_IsMF_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_isMF_AA


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (R : Subring ℂ) (N : ℕ) : ∀ f : ℍ → ℂ, IsMF (12 * (N : ℤ)) f →
    CoeffIn R (qExpansion 1 f) →
    ∃ P : Polynomial ℂ, (∀ i, P.coeff i ∈ R) ∧ P.natDegree ≤ N ∧
      (∀ τ, f τ = DD τ ^ N * P.eval (jT τ)) ∧
      ∀ (n0 : ℕ) (u : ℂ), u ≠ 0 → (∀ n < n0, PowerSeries.coeff n (qExpansion 1 f) = 0) →
        PowerSeries.coeff n0 (qExpansion 1 f) = u → P.leadingCoeff = u := by
  induction N with
  | zero =>
    intro f hf hR
    obtain ⟨g, hg⟩ := hf.congr_weight (k' := 0) (by simp)
    obtain ⟨c, hc⟩ := levelOne_weight_zero_const g
    have hfc : f = c • (1 : ℍ → ℂ) := by
      funext τ; rw [← hg τ, hc]; simp
    have hq : qExpansion 1 f = c • (1 : PowerSeries ℂ) := by
      have h1 : AnalyticAt ℂ (cuspFunction 1 (1 : ℍ → ℂ)) 0 := by
        have : IsMF 0 (1 : ℍ → ℂ) := ⟨1, fun τ => by simp⟩
        exact this.analytic
      rw [hfc, qExpansion_smul h1, qExpansion_one]
    refine ⟨Polynomial.C c, fun i => ?_, by simp, fun τ => ?_, fun n0 u hu h0 h1 => ?_⟩
    · have := hR 0
      rw [hq] at this
      rw [Polynomial.coeff_C]
      split_ifs
      · simpa using this
      · exact R.zero_mem
    · rw [hfc]; simp
    · rw [hq] at h1
      rw [Polynomial.leadingCoeff_C]
      cases n0 with
      | zero => simpa using h1
      | succ k =>
        exfalso; apply hu; rw [← h1]
        simp [PowerSeries.coeff_one]
  | succ N ih =>
    intro f hf hR
    set a0 : ℂ := PowerSeries.coeff 0 (qExpansion 1 f) with ha0
    have hA : IsMF (12 * ((N + 1 : ℕ) : ℤ)) (fun τ => AA τ ^ (N + 1)) :=
      (isMF_AA.pow (N + 1)).congr_weight (by ring)
    have hcA : IsMF (12 * ((N + 1 : ℕ) : ℤ)) (fun τ => a0 * AA τ ^ (N + 1)) := hA.const_mul a0
    have hg : IsMF (12 * ((N + 1 : ℕ) : ℤ)) (fun τ => f τ - a0 * AA τ ^ (N + 1)) := hf.sub hcA
    have hqg : qExpansion 1 (fun τ => f τ - a0 * AA τ ^ (N + 1)) =
        qExpansion 1 f - a0 • aC ^ (N + 1) := by
      have e1 : (fun τ => f τ - a0 * AA τ ^ (N + 1)) = f - a0 • (fun τ => AA τ ^ (N + 1)) := by
        funext τ; simp
      have e2 : (fun τ => a0 * AA τ ^ (N + 1)) = a0 • (fun τ => AA τ ^ (N + 1)) := by
        funext τ; simp
      rw [e1, qExpansion_sub hf.analytic (e2 ▸ hcA.analytic), qExpansion_smul hA.analytic,
        qExp_AA_pow]
    have haR : a0 ∈ R := hR 0
    have hac : ∀ n, PowerSeries.coeff n (aC ^ (N + 1)) ∈ R := by
      intro n
      have : aC ^ (N + 1) = (aZ ^ (N + 1)).map (Int.castRingHom ℂ) := by rw [map_pow]; rfl
      rw [this, PowerSeries.coeff_map]
      exact intCast_mem R _
    have hac0 : PowerSeries.coeff 0 (aC ^ (N + 1)) = 1 := by
      have := aC_coeff_zero
      simp only [PowerSeries.coeff_zero_eq_constantCoeff] at this ⊢
      rw [map_pow, this, one_pow]
    have hg0 : PowerSeries.coeff 0 (qExpansion 1 (fun τ => f τ - a0 * AA τ ^ (N + 1))) = 0 := by
      rw [hqg, map_sub, PowerSeries.coeff_smul, hac0]; simp [ha0]
    obtain ⟨h, hh, hfh, hqh⟩ := hg.div_DD hg0
    have hh' : IsMF (12 * (N : ℤ)) h := hh.congr_weight (by push_cast; ring)
    have hRh : CoeffIn R (qExpansion 1 h) := by
      apply coeffIn_of_dC_mul
      rw [← hqh, hqg]
      intro n
      rw [map_sub, PowerSeries.coeff_smul]
      exact R.sub_mem (hR n) (R.mul_mem haR (hac n))
    obtain ⟨P', hP1, hP2, hP3, hP4⟩ := ih h hh' hRh
    refine ⟨Polynomial.C a0 * Polynomial.X ^ (N + 1) + P', fun i => ?_, ?_, fun τ => ?_,
      fun n0 u hu h0 h1 => ?_⟩
    · rw [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
      refine R.add_mem ?_ (hP1 i)
      split_ifs
      · exact haR
      · exact R.zero_mem
    · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ (by omega))
      exact Polynomial.natDegree_C_mul_X_pow_le _ _
    · have hD := DD_ne_zero τ
      have e := hfh τ
      rw [hP3 τ] at e
      have : f τ = a0 * AA τ ^ (N + 1) + DD τ * (DD τ ^ N * P'.eval (jT τ)) := by
        rw [← e]; ring
      rw [this]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X]
      have hj : DD τ ^ (N + 1) * jT τ ^ (N + 1) = AA τ ^ (N + 1) := by
        rw [← mul_pow, jT, mul_div_cancel₀ _ hD]
      rw [← hj]; ring
    · by_cases hz : a0 = 0
      · have hq' : qExpansion 1 f = dC * qExpansion 1 h := by
          rw [← hqh, hqg, hz]; simp
        rw [hq'] at h0 h1
        obtain ⟨k, -, hk0, hk1⟩ := low_of_dC_mul _ n0 u hu h0 h1
        rw [hz]; simp only [map_zero, zero_mul, zero_add]
        exact hP4 k u hu hk0 hk1
      · have hn0 : n0 = 0 := by
          by_contra hne
          exact hz (h0 0 (Nat.pos_of_ne_zero hne))
        subst hn0
        rw [Polynomial.leadingCoeff_add_of_degree_lt', Polynomial.leadingCoeff_mul_X_pow,
          Polynomial.leadingCoeff_C]
        · exact h1
        · rw [Polynomial.degree_C_mul_X_pow _ hz]
          refine lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le hP2) ?_
          exact_mod_cast Nat.lt_succ_self N
end ReciprocityTheory.ChartRestriction.L1
