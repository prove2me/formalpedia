-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_hessC_chartPot_eb4505fa5cb5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:38:24.960871+00:00
-- url     : https://prove2.me/submissions/d5c47a34-cf2b-4a0d-95a5-c76a2b419ce8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjPotDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotDensLevi
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotDens
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_affLift_analyticAt_1c5c7977c09d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_blockCLM_apply_a12544bdf5b0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_levi_fsMultiPot_e06421934b30
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_lift_analyticAt_64b6a8ed765d
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessC_add_log_norm
import Theorems.Thm_ReciprocityTheory_AnForm_M_hessCGerm
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_Targets_ProjPotDens_blockCLM_apply_a12544bdf5b0
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology
open GroundTheory.Heights₂.Heights.Targets.ProjPotDens
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
  {n : ℕ} {R : AnLogRes P J (n + 1)} {V : Set R.X} {BV : FinHolAtlas n V}
namespace GroundTheory.Heights₂.Heights.Targets.ProjPotDens
theorem _root_.solution (hB : HoloMap BV R.A Subtype.val) (x : V) {j : Fin BV.n}
    (hx : x ∈ (BV.chart j).source) (p : (k : K) → ι k)
    (hp : ∀ k, R.lift x.1 x.1 ⟨k, p k⟩ ≠ 0) :
    ReciprocityTheory.AnForm.hessC (fun u => (multiprojPot R V).φ x ((BV.chart j).symm u)) (BV.chart j x) =
      ReciprocityTheory.AnForm.hessC
        (fsMultiPot ∘ fun u => affCoord p (R.lift x.1 ((BV.chart j).symm u).1)) (BV.chart j x) := by
  obtain ⟨hτa, hev⟩ := affLift_analyticAt hB x hx p hp
  have hsx : (BV.chart j).symm (BV.chart j x) = x := (BV.chart j).left_inv hx
  set G : (Fin n → ℂ) → (Σ k, ι k) → ℂ := fun u => R.lift x.1 ((BV.chart j).symm u).1 with hG
  set τ : (Fin n → ℂ) → (Σ k, ι k) → ℂ := fun u => affCoord p (G u) with hτ
  have hGa : ∀ q, AnalyticAt ℂ (fun u => G u q) (BV.chart j x) :=
    fun q => analyticAt_pi_iff.1 (ProjRegular.lift_analyticAt hB x hx).1 q
  have hp' : ∀ k, G (BV.chart j x) ⟨k, p k⟩ ≠ 0 := by
    intro k; simp only [hG, hsx]; exact hp k
  have hτ1 : ∀ u, (∀ k, G u ⟨k, p k⟩ ≠ 0) → ∀ k, τ u ⟨k, p k⟩ = 1 :=
    fun u hu k => div_self (hu k)
  let g : (Fin n → ℂ) → ℂ := fun u => ∏ k, G u ⟨k, p k⟩ ^ 2
  have hga : AnalyticAt ℂ g (BV.chart j x) :=
    Finset.univ.analyticAt_fun_prod fun k _ => (hGa ⟨k, p k⟩).pow 2
  have hg0 : g (BV.chart j x) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero 2 (hp' k)
  have hC : ContDiffAt ℝ 2 fsMultiPot (τ (BV.chart j x)) :=
    (levi_fsMultiPot p (fun k => by rw [hτ1 _ hp' k]; exact one_ne_zero) 0).1
  have hgerm : (fun u => (multiprojPot R V).φ x ((BV.chart j).symm u)) =ᶠ[𝓝 (BV.chart j x)]
      fun u => (fsMultiPot ∘ τ) u + Real.log ‖g u‖ := by
    filter_upwards [hev] with u hu
    show ∑ k, Real.log (∑ i, ‖G u ⟨k, i⟩‖ ^ 2) =
      ∑ k, Real.log (∑ i, ‖τ u ⟨k, i⟩‖ ^ 2) + Real.log ‖∏ k, G u ⟨k, p k⟩ ^ 2‖
    have hs : ∀ k, ∑ i, ‖G u ⟨k, i⟩‖ ^ 2 = ‖G u ⟨k, p k⟩‖ ^ 2 * ∑ i, ‖τ u ⟨k, i⟩‖ ^ 2 := by
      intro k
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hn : ‖G u ⟨k, p k⟩‖ ≠ 0 := norm_ne_zero_iff.2 (hu k)
      simp only [hτ, affCoord, norm_div, div_pow]
      field_simp
    have hpos : ∀ k, 0 < ∑ i, ‖τ u ⟨k, i⟩‖ ^ 2 := fun k =>
      lt_of_lt_of_le (by rw [hτ1 u hu k]; norm_num)
        (Finset.single_le_sum (f := fun i => ‖τ u ⟨k, i⟩‖ ^ 2) (fun i _ => sq_nonneg _)
          (Finset.mem_univ (p k)))
    have hne : ∀ k ∈ (Finset.univ : Finset K), ‖G u ⟨k, p k⟩ ^ 2‖ ≠ 0 := fun k _ => by
      rw [norm_pow]; exact pow_ne_zero 2 (norm_ne_zero_iff.2 (hu k))
    rw [norm_prod, Real.log_prod hne, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hs k, norm_pow, Real.log_mul (pow_ne_zero 2 (norm_ne_zero_iff.2 (hu k))) (hpos k).ne',
      add_comm]
  rw [hessCGerm _ _ _ hgerm]
  exact ReciprocityTheory.AnForm.A.hessC_add_log_norm _ g _
    (hC.comp _ (hτa.contDiffAt.restrict_scalars ℝ)) hga hg0
end GroundTheory.Heights₂.Heights.Targets.ProjPotDens
