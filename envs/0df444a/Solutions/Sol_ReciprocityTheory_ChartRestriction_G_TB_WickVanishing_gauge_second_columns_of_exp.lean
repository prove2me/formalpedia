-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gauge_second_columns_of_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:44:20.344383+00:00
-- url     : https://prove2.me/submissions/be614bf9-b596-4bcb-aa0d-f4c036a2ba2b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnOperator
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TruncatedExpSecondEqFull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_lamL_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_nabVal_eq_lam
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_glue_colM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_prodQ_monomial
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_lam_prodQ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_truncated_exp_second_eq_full
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_TL_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_DegreeTruncationOperator_cS_univ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_DegreeTruncationOperator_exp_cols
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_DegreeTruncationOperator_exp_opA_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_SecondColumnDegree_so_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open SecondColumnDegree DegreeTruncationOperator
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution (hG : GaugeExpSt) : GaugeIndependenceColumns := by
  intro R _ d O _ _ _ _ _ k _ _ _ B h h' hh hh' w0 mm n ι _ u P hP f
  rcases subsingleton_or_nontrivial k with hk | hk
  · exact Subsingleton.elim _ _
  classical
  set c : ι → ι → k := fun l l' =>
    dotProduct (u l) ((bilinPart k (h' - h)).mulVec ((dAct k B w0).mulVec (u l'))) +
      dotProduct (u l') ((bilinPart k (h' - h)).mulVec ((dAct k B w0).mulVec (u l))) with hc
  set cD : ι × Fin n → ι × Fin n → k := fun p q => if p.2 = q.2 then c p.1 q.1 else 0 with hcD
  have hP' : secondOrder k cD P = 0 := hP
  set t : k := (mm : k) * algebraMap ℚ k (1 / 2) with ht
  set N := P.totalDegree with hN
  set V : Fin n → (ι →₀ ℕ) → k := fun b e => B.nabVal k h w0 mm (f b) u (monomial e 1) with hV
  set W : (ι × Fin n →₀ ℕ) → k := fun mo => ∏ b, V b (colM mo b) with hW
  have hLHS : (∑ mo ∈ P.support, P.coeff mo *
      ∏ b, B.nabVal k h w0 mm (f b) u (monomial (colM mo b) 1)) = lam W P := rfl
  rw [hLHS]
  have hcol : ∀ (mo : (ι × Fin n) →₀ ℕ) (b : Fin n) (l : ι), colM mo b l = mo (l, b) := by
    intro mo b l
    simp [colM]
  have hsum : ∀ mo ∈ P.support, ∑ b, (monomial (colM mo b) (1 : k)).totalDegree ≤ N := by
    intro mo hmo
    have h1 := le_totalDegree hmo
    have h2 : ∀ b, (monomial (colM mo b) (1 : k)).totalDegree = ∑ l, mo (l, b) := by
      intro b
      rw [totalDegree_monomial _ one_ne_zero, Finsupp.sum_fintype _ _ (fun _ => rfl)]
      exact sum_congr rfl fun l _ => hcol mo b l
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_prod_type] at h1
    simp only [h2]
    rw [sum_comm]
    exact h1
  have key : ∀ mo ∈ P.support, ∏ b, B.nabVal k h' w0 mm (f b) u (monomial (colM mo b) 1) =
      lam W (TL cD t N (monomial mo 1)) := by
    intro mo hmo
    have hbN : ∀ b, (monomial (colM mo b) (1 : k)).totalDegree ≤ N := fun b =>
      (single_le_sum (f := fun b => (monomial (colM mo b) (1 : k)).totalDegree) (fun _ _ => Nat.zero_le _)
        (mem_univ b)).trans (hsum mo hmo)
    have h1 : ∀ b, B.nabVal k h' w0 mm (f b) u (monomial (colM mo b) 1) =
        lam (V b) (E1 c t N (monomial (colM mo b) 1)) := by
      intro b
      rw [hG R d O k B h h' hh hh' w0 mm u _ (f b), nabVal_eq_lam,
        truncated_exp_second_eq_full c t _ N (hbN b) _ le_rfl]
    rw [prod_congr rfl fun b _ => h1 b, ← lam_prodQ V (fun b => E1 c t N (monomial (colM mo b) 1))]
    have hE := exp_cols c t N (fun b => (monomial (colM mo b) (1 : k)).totalDegree) (hsum mo hmo) univ
      (fun b => monomial (colM mo b) 1) (fun _ => le_rfl)
    simp only [mem_univ, if_true] at hE
    have hmoN : (monomial mo (1 : k)).totalDegree ≤ N :=
      (totalDegree_monomial_le _ _).trans (le_totalDegree hmo)
    rw [← hE, cS_univ, prodQ_monomial, glue_colM, exp_opA_apply _ _ _ _ hmoN, TL_apply]
  have hRHS : (∑ mo ∈ P.support, P.coeff mo *
      ∏ b, B.nabVal k h' w0 mm (f b) u (monomial (colM mo b) 1)) = lam W (TL cD t N P) := by
    rw [sum_congr rfl fun mo hmo => by rw [key mo hmo]]
    conv_rhs => rw [as_sum P]
    rw [map_sum, ← lamL_apply, map_sum]
    refine sum_congr rfl fun mo _ => ?_
    rw [show (monomial mo (P.coeff mo) : MvPolynomial (ι × Fin n) k) = P.coeff mo • monomial mo 1 by
      rw [smul_monomial, smul_eq_mul, mul_one], map_smul, map_smul, lamL_apply, smul_eq_mul]
  have hTP : TL cD t N P = P := by
    rw [TL_apply, sum_eq_single 0]
    · simp
    · intro i _ hi
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
      rw [Function.iterate_succ_apply, hP', Function.iterate_fixed (so_zero _) j, smul_zero]
    · intro h0
      simp at h0
  rw [hRHS, hTP]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
