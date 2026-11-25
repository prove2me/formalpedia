-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.HCols.colAlg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:46:13.379196+00:00
-- url     : https://prove2.me/submissions/d4348b01-54a8-4c28-b9fb-dfb42b4b7b18

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GermSCCols
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnOperator
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LemmaH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LemmaHCols
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_HCols_Mf_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_HCols_Mf_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_HCols_Mf_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_HCols_combine_colM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_HCols_prodQ_monomial
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_HCols_Mf_prodQ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_HCols_degree_colM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_HCols_totalDegree_monomial_one_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_HCols_iter_linear
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_HCols_iter_zero__6c5105cab79c
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_nablaL_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_DegreeTruncationOperator_cS_univ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_DegreeTruncationOperator_exp_cols
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_DegreeTruncationOperator_exp_opA_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_SecondColumnDegree_so_iter_eq_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.TB.SCPf.nablaL_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.HCols
variable {k : Type} [CommRing k] {ι : Type} [Fintype ι] {n : ℕ}
variable (mu : Fin n → MvPolynomial ι k →ₗ[k] k)
variable [Algebra ℚ k]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.HCols
theorem _root_.solution (κ : ι → ι → k) (lam : Fin n → (ι →₀ ℕ) → k)
    (hlm : ∀ b α, lam b α = ∑ i ∈ Finset.range ((monomial α (1 : k)).totalDegree + 1),
        mu b (((i.factorial : ℚ)⁻¹) • (secondOrder k κ)^[i] (monomial α 1)))
    (P : MvPolynomial (ι × Fin n) k)
    (hP : secondOrder k (fun p q : ι × Fin n => if p.2 = q.2 then κ p.1 q.1 else 0) P = 0) :
    ∑ mo ∈ P.support, P.coeff mo * ∏ b, lam b (colM mo b) = Mf mu P := by
  classical
  set N := P.totalDegree with hN
  set cc : ι × Fin n → ι × Fin n → k := cS κ (Finset.univ : Finset (Fin n)) with hcc
  have hccu : cc = fun p q : ι × Fin n => if p.2 = q.2 then κ p.1 q.1 else 0 := cS_univ κ
  have hE : ∀ b α, (monomial α (1 : k)).totalDegree ≤ N →
      lam b α = mu b (E1 κ 1 N (monomial α 1)) := by
    intro b α hα
    rw [hlm, E1, map_sum]
    refine Finset.sum_subset (Finset.range_subset_range.2 (Nat.succ_le_succ hα)) (fun i hi hi' => ?_) |>.trans ?_
    · rw [so_iter_eq_zero κ i _ (by simp only [Finset.mem_range] at hi'; omega), smul_zero, map_zero]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [one_pow, mul_one, ← algebraMap_smul k ((i.factorial : ℚ)⁻¹)]
  have hmo : ∀ mo ∈ P.support, ∏ b, lam b (colM mo b) =
      ∑ i ∈ Finset.range (N + 1), (algebraMap ℚ k ((i.factorial : ℚ)⁻¹) * 1 ^ i) *
        Mf mu ((secondOrder k cc)^[i] (monomial mo 1)) := by
    intro mo hmo
    have hdeg : mo.degree ≤ N := by
      have := le_totalDegree hmo
      exact le_of_eq_of_le (by rfl) this
    have hD : ∀ b, (monomial (colM mo b) (1 : k)).totalDegree ≤ (colM mo b).degree :=
      fun b => totalDegree_monomial_one_le _
    have hsum : ∑ b, (colM mo b).degree ≤ N := (degree_colM mo).le.trans hdeg
    have hb : ∀ b, (monomial (colM mo b) (1 : k)).totalDegree ≤ N := fun b =>
      (hD b).trans ((Finset.single_le_sum (fun b _ => Nat.zero_le _) (Finset.mem_univ b)).trans hsum)
    rw [Finset.prod_congr rfl (fun b _ => hE b (colM mo b) (hb b)), ← Mf_prodQ]
    have hx := exp_cols κ 1 N (fun b => (colM mo b).degree) hsum Finset.univ
      (fun b => monomial (colM mo b) 1) hD
    simp only [Finset.mem_univ, if_true] at hx
    rw [← hx, prodQ_monomial, Finset.prod_const_one, combine_colM,
      exp_opA_apply _ _ _ _ ((totalDegree_monomial_one_le mo).trans hdeg), Mf_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Mf_smul]
  rw [Finset.sum_congr rfl fun mo hmo' => by rw [hmo mo hmo']]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hlin : ∀ i, ∑ mo ∈ P.support, P.coeff mo * ((algebraMap ℚ k ((i.factorial : ℚ)⁻¹) * 1 ^ i) *
      Mf mu ((secondOrder k cc)^[i] (monomial mo 1))) =
      (algebraMap ℚ k ((i.factorial : ℚ)⁻¹) * 1 ^ i) * Mf mu ((secondOrder k cc)^[i] P) := by
    intro i
    conv_rhs => rw [as_sum P]
    rw [iter_linear, map_sum, Mf_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun mo _ => ?_
    rw [show monomial mo (P.coeff mo) = P.coeff mo • monomial mo (1 : k) by
      rw [smul_monomial, smul_eq_mul, mul_one], map_smul, Mf_smul, ← iter_linear]
    ring
  rw [Finset.sum_congr rfl fun i _ => hlin i, Finset.sum_range_succ', Finset.sum_eq_zero]
  · simp
  · intro i _
    rw [Function.iterate_succ_apply, hccu, hP, iter_zero', Mf_zero, mul_zero]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.HCols
