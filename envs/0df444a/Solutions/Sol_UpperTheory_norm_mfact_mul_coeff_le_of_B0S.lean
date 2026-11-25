-- Prove2me | solution 1 for UpperTheory.norm_mfact_mul_coeff_le_of_B0S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:13:07.803201+00:00
-- url     : https://prove2.me/submissions/6eb220bc-2bf3-4e59-9cd5-5afed2615143

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_ColDefs
import Definitions.Def_Formalism_GaussJetBounds_OneLetterRadius
import Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_BeSConstantCoeffEqZeroAndWtGe
import Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_NormMfactMulCoeffLeOfB0S
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmR_dot_fintype
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmR_dot_nonneg
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmR_monoWtGe_rad
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_exponential_weight_le
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_generalized_log_inverse
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_generalized_log_weight
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_monoWtGe_iff
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_multiplicative_weight_le
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_natCast_eq_pow_padicValNat
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_substitution_weight_bound
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_key
import Theorems.Thm_Formalism_IncomingBounds_padicValFactorialBounds
import Theorems.Thm_UpperTheory_beS_constantCoeff_eq_zero_and_wtGe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped BigOperators
open Formalism.DworkPowerSeriesWeights Formalism.IncomingBounds UpperTheory.G2
private theorem factA {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} (hl : l.Prime)
    (hlt : ‖(l : K)‖ < 1) {ι : Type} [Fintype ι] (κ : ι →₀ ℕ) (A : ℝ) (hA : 1 ≤ A) (hκ : ∀ v, (κ v : ℝ) ≤ A) :
    ‖((mfact κ : ℕ) : K)‖ ≤ ‖(l : K)‖ ^ ((∑ i, (κ i : ℝ) / ((l : ℝ) - 1)) -
        (Fintype.card ι : ℝ) * (Real.logb l A + 1)) := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hπ0 : 0 < ‖(l : K)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hl.ne_zero)
  have hπ1 : ‖(l : K)‖ ≤ 1 := hlt.le
  have hlogA : 0 ≤ Real.logb l A := Real.logb_nonneg hl1 hA
  have key : ∀ N : ℕ, (N : ℝ) ≤ A →
      ‖((N.factorial : ℕ) : K)‖ ≤ ‖(l : K)‖ ^ ((N : ℝ) / ((l : ℝ) - 1) - (Real.logb l A + 1)) := by
    intro N hN
    rcases Nat.eq_zero_or_pos N with rfl | hNpos
    · simp only [Nat.factorial_zero, Nat.cast_one, norm_one, Nat.cast_zero, zero_div, zero_sub]
      exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hπ0 hπ1 (by linarith)
    · rw [norm_natCast_eq_pow_padicValNat hl hlt (Nat.factorial_ne_zero N), ← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_ge hπ0 hπ1
      have hb := (padicValFactorialBounds l hl N hNpos).1
      have hNA : Real.logb l N ≤ Real.logb l A :=
        Real.logb_le_logb_of_le hl1 (by exact_mod_cast hNpos) hN
      linarith
  have hm : ((mfact κ : ℕ) : K) = ∏ i, (((κ i).factorial : ℕ) : K) := by
    unfold mfact
    rw [Finsupp.prod_fintype _ _ (by simp), Nat.cast_prod]
  rw [hm, norm_prod]
  calc ∏ i, ‖(((κ i).factorial : ℕ) : K)‖
      ≤ ∏ i, ‖(l : K)‖ ^ ((κ i : ℝ) / ((l : ℝ) - 1) - (Real.logb l A + 1)) :=
        Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => key _ (hκ i))
    _ = ‖(l : K)‖ ^ ((∑ i, (κ i : ℝ) / ((l : ℝ) - 1)) -
          (Fintype.card ι : ℝ) * (Real.logb l A + 1)) := by
        rw [← Real.rpow_sum_of_pos hπ0, Finset.sum_sub_distrib, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul]
private theorem genLog_cc {K : Type} [Field K] {τ : Type} [DecidableEq τ] {l : ℕ} (p : τ → τ) (x : τ) :
    MvPowerSeries.constantCoeff (genLog (K := K) l p x) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_apply]
  simp [genLog]
  intro h
  have := DFunLike.congr_fun h x
  simp at this
private theorem unshape {K : Type} [Field K] {τ : Type} [Finite τ] (z g : τ → MvPowerSeries τ K)
    (hz : ∀ x, MvPowerSeries.constantCoeff (z x) = 0) (hg : ∀ x, MvPowerSeries.constantCoeff (g x) = 0)
    (hzg : ∀ x, MvPowerSeries.subst g (z x) = MvPowerSeries.X x) (ep : K) (Th U E : MvPowerSeries τ K)
    (h : MvPowerSeries.subst (fun v => MvPowerSeries.C ep * z v) Th = U * MvPowerSeries.subst z E) :
    MvPowerSeries.rescale (fun _ => ep) Th = MvPowerSeries.subst g U * E := by
  have hzs : MvPowerSeries.HasSubst z := MvPowerSeries.hasSubst_of_constantCoeff_zero hz
  have hgs : MvPowerSeries.HasSubst g := MvPowerSeries.hasSubst_of_constantCoeff_zero hg
  have hcz : MvPowerSeries.HasSubst (fun v => MvPowerSeries.C ep * z v) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun v => by simp [hz v])
  have e := congrArg (MvPowerSeries.subst g) h
  rw [MvPowerSeries.subst_comp_subst_apply hcz hgs, MvPowerSeries.subst_mul hgs,
    MvPowerSeries.subst_comp_subst_apply hzs hgs] at e
  simp only [MvPowerSeries.subst_mul hgs, MvPowerSeries.subst_C, hzg] at e
  have e1 : (fun v => MvPowerSeries.C ep * MvPowerSeries.X v) =
      (fun _ : τ => ep) • (MvPowerSeries.X : τ → MvPowerSeries τ K) := by
    funext v
    simp [MvPowerSeries.smul_eq_C_mul]
  rw [MvPowerSeries.rescale_eq_subst, ← e1, e, MvPowerSeries.subst_self]
  rfl
end

set_option autoImplicit false
open scoped BigOperators
open Formalism.DworkPowerSeriesWeights Formalism.IncomingBounds UpperTheory.G2
namespace UpperTheory
theorem _root_.solution :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l i : ℕ) [NeZero i], l.Prime → Odd l → ‖(l : K)‖ < 1 →
    ∀ (Lt β : Type) [Fintype Lt] [Fintype β] [DecidableEq Lt] [DecidableEq β] (pos : Lt → ℕ → Lt), IsPos i pos →
    ∀ Th : MvPowerSeries (Lt × β) K, HasThetaProductForm l i pos Th → ∀ sig : Lt → ℝ, IsRadii l pos sig →
    ∀ (κ : Lt × β →₀ ℕ) (A : ℝ), 1 ≤ A → (∀ v, (κ v : ℝ) ≤ A) →
    ‖((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ Th‖ ≤
      ‖(l : K)‖ ^ ((∑ v, (κ v : ℝ) * (gam l - sig v.1)) - (Fintype.card (Lt × β) : ℝ) * (Real.logb l A + 1)) := by
  intro K _ _ _ l i _ hl hodd hlt Lt β _ _ _ _ pos hpos Th hB sig hsig κ A hA hκ
  obtain ⟨K0, ζ, R, ep, sg, be, hK0, hζ, hep, hsg, hbe, U, hU, hsh⟩ := hB
  have hπ0 : 0 < ‖(l : K)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hl.ne_zero)
  have hπ1 : ‖(l : K)‖ ≤ 1 := hlt.le
  obtain ⟨g, hg0, hg1, -⟩ := generalized_log_inverse K l hl (Lt × β)
    (fun y => (pos y.1 (2 * (i - 1)), y.2))
  have hz0 : ∀ v : Lt × β, MvPowerSeries.constantCoeff (logS (K := K) (β := β) l i pos v) = 0 :=
    fun v => genLog_cc _ _
  have hres := unshape (logS l i pos) g hz0 hg0 hg1 ep Th U _ hsh
  obtain ⟨hbc, hbw⟩ := UpperTheory.beS_constantCoeff_eq_zero_and_wtGe K l i hl hodd hlt K0 hK0 ζ hζ Lt β pos hpos sig hsig R sg be
    hsg hbe
  have hexp := exponential_weight_le K l hl hlt (Lt × β) (fun v => rho l + sig v.1) κ _ hbc
    (fun n _ => hbw n)
  have hgl := generalized_log_weight K l hl hlt (Lt × β) (fun y => (pos y.1 (2 * (i - 1)), y.2))
    g hg0 hg1
  have hgw : ∀ x, WtGe ‖(l : K)‖ (fun v : Lt × β => rho l + sig v.1) (rho l) (g x) :=
    fun x n => asmR_monoWtGe_rad hπ0 hπ1 (fun v => by linarith [hsig.1 v.1]) (hgl x n)
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
  have hUw : WtGe ‖(l : K)‖ (fun _ : Lt × β => rho l) 0 U := by
    intro n
    rw [monoWtGe_iff]
    refine (hU n).trans (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hπ0 hπ1 ?_)
    have hrho : 0 ≤ rho l := by
      unfold rho
      have : (1 : ℝ) < (l : ℝ) ^ 2 := by nlinarith
      exact div_nonneg zero_le_one (by linarith)
    have := asmR_dot_nonneg n (r := fun _ : Lt × β => rho l) (fun _ => hrho)
    linarith
  have hsu := substitution_weight_bound K ‖(l : K)‖ hπ0 hlt (Lt × β) (Lt × β) g (fun _ => rho l)
    (fun v => rho l + sig v.1) 0 U hg0 hgw hUw
  have hprod := multiplicative_weight_le K ‖(l : K)‖ hπ0 (Lt × β) (fun v => rho l + sig v.1) 0 0 κ _ _
    (fun n _ => hsu n) hexp
  have hk := hprod κ le_rfl
  rw [monoWtGe_iff, ← hres, MvPowerSeries.coeff_rescale, norm_mul] at hk
  have hone : ‖κ.prod fun _ m => ep ^ m‖ = 1 := by
    rw [Finsupp.prod, norm_prod]
    simp [hep]
  rw [hone, one_mul] at hk
  have hfact := factA hl hlt κ A hA hκ
  have hc : 1 / ((l : ℝ) - 1) - rho l = gam l := by
    unfold rho gam
    have h1 : (l : ℝ) - 1 ≠ 0 := by linarith
    have h2 : (l : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    field_simp
    ring
  have hg : ∀ v : Lt × β, (κ v : ℝ) / ((l : ℝ) - 1) - (κ v : ℝ) * (rho l + sig v.1) =
      (κ v : ℝ) * (gam l - sig v.1) := by
    intro v
    have : (κ v : ℝ) / ((l : ℝ) - 1) = (κ v : ℝ) * (1 / ((l : ℝ) - 1)) := by ring
    rw [this]
    linear_combination (κ v : ℝ) * hc
  rw [norm_mul]
  calc ‖((mfact κ : ℕ) : K)‖ * ‖MvPowerSeries.coeff κ Th‖
      ≤ ‖(l : K)‖ ^ ((∑ v, (κ v : ℝ) / ((l : ℝ) - 1)) -
          (Fintype.card (Lt × β) : ℝ) * (Real.logb l A + 1)) *
        ‖(l : K)‖ ^ (0 + 0 - dot κ (fun v : Lt × β => rho l + sig v.1)) :=
        mul_le_mul hfact hk (norm_nonneg _) (Real.rpow_nonneg hπ0.le _)
    _ = _ := by
        rw [← Real.rpow_add hπ0]
        congr 1
        rw [asmR_dot_fintype, ← Finset.sum_congr rfl (fun v _ => hg v), Finset.sum_sub_distrib]
        ring
end UpperTheory
