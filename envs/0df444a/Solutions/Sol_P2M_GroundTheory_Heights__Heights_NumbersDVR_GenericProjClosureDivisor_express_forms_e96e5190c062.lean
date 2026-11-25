-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_express_forms_e96e5190c062
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:28:59.089804+00:00
-- url     : https://prove2.me/submissions/9b982c24-c03b-40da-bbf1-65a40eed8feb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsGenericProjClosureDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensExpress
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDivisor
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_vdeg_add_4f8428746a98
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_chartMonoZ_homog_94b18e153b90
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_genVal_sum_smul_e5decc0eb856
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_genVal_smul_134973ce4a1e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_aeval_chartMonoZ_7388c339ad0d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_chart_forms_uniform_bdb7ff8351a1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
  {N M M' : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]
  {Φ : Type} [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor
theorem _root_.solution (y : (Σ k, ι k) → Ω) (e : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E) (t : Fin N → Φ) (c : ∀ k, ι k)
    (hc : segreVec y c ≠ 0) (ϖ : O) {L : ℕ} (ψ : Fin L → Module.Dual Ω E) (χ : Module.Dual Ω E)
    (a a' : K → ℤ) (n : ℕ) (r : Fin L → Ω) (hr : ∀ l, r l ∈ chartRing O (segreVec y) c)
    (h : algebraMap O Ω ϖ ^ n • χ = ∑ l, (r l * ∏ k, y ⟨k, c k⟩ ^ (a' k - a k)) • ψ l) :
    ∃ (bG bH : K → ℕ) (G : Fin L → MRing (bundleIdx (bundleIdx ι M) M') O),
      (∀ l, IsMultiHomog (G l) (vdeg bG)) ∧ (∀ k, (bG k : ℤ) - bH k = a' k - a k) ∧
      aeval (pairProjCoord y e φ φ' t) (C (ϖ ^ n) * chartMonoZ O M M' c bH) * genVal e t χ =
        ∑ l, aeval (pairProjCoord y e φ φ' t) (G l) * genVal e t (ψ l) := by
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 => hc (Finset.prod_eq_zero (Finset.mem_univ k) h0)
  obtain ⟨n₀, U, hU⟩ := chart_forms_uniform (O := O) (M := M) (M' := M') y e φ φ' t c hc r hr
  let A : K → ℕ := fun k => (a' k - a k).toNat
  let B : K → ℕ := fun k => (a k - a' k).toNat
  have hAB : ∀ k, ((n₀ + B k : ℕ) : ℤ) + (a' k - a k) = (n₀ : ℤ) + (A k : ℤ) := by
    intro k
    simp only [A, B]
    omega
  refine ⟨fun k => n₀ + A k, fun k => n₀ + B k, fun l => U l * chartMonoZ O M M' c A, fun l => ?_,
    fun k => ?_, ?_⟩
  · have hv : vdeg (K := K) (fun k => n₀ + A k) = vdeg (fun _ => n₀) + vdeg A := vdeg_add _ _
    rw [hv]
    exact IsWeightedHomogeneous.mul (hU l).1 (chartMonoZ_homog c A)
  · have := hAB k
    push_cast at this ⊢
    linarith
  · have hk : ∀ k, y ⟨k, c k⟩ ^ (n₀ + B k) * y ⟨k, c k⟩ ^ (a' k - a k) =
        y ⟨k, c k⟩ ^ n₀ * y ⟨k, c k⟩ ^ A k := by
      intro k
      rw [← zpow_natCast (y _) (n₀ + B k), ← zpow_add₀ (hy k), hAB k, zpow_add₀ (hy k), zpow_natCast,
        zpow_natCast]
    have key : (algebraMap O Ω ϖ ^ n * ∏ k, y ⟨k, c k⟩ ^ (n₀ + B k)) • χ =
        ∑ l, (r l * segreVec y c ^ n₀ * ∏ k, y ⟨k, c k⟩ ^ A k) • ψ l := by
      rw [mul_comm, ← smul_smul, h, Finset.smul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [smul_smul]
      congr 1
      calc (∏ k, y ⟨k, c k⟩ ^ (n₀ + B k)) * (r l * ∏ k, y ⟨k, c k⟩ ^ (a' k - a k))
          = r l * ∏ k, (y ⟨k, c k⟩ ^ (n₀ + B k) * y ⟨k, c k⟩ ^ (a' k - a k)) := by
            rw [Finset.prod_mul_distrib]
            ring
        _ = r l * segreVec y c ^ n₀ * ∏ k, y ⟨k, c k⟩ ^ A k := by
            simp_rw [hk]
            rw [Finset.prod_mul_distrib, Finset.prod_pow, show ∏ k, y ⟨k, c k⟩ = segreVec y c from rfl]
            ring
    have hval := congrArg (genVal e t) key
    rw [genVal_smul, genVal_sum_smul] at hval
    rw [map_mul, aeval_C, aeval_chartMonoZ, map_pow, IsScalarTower.algebraMap_apply O Ω Φ, ← map_pow,
      ← map_mul, hval]
    refine Finset.sum_congr rfl fun l _ => ?_
    show _ = aeval _ (U l * chartMonoZ O M M' c A) * _
    rw [map_mul (aeval (pairProjCoord y e φ φ' t)) (U l), (hU l).2, aeval_chartMonoZ,
      map_mul (algebraMap Ω Φ) (r l * segreVec y c ^ n₀)]
end GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor
