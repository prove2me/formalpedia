-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_chart_forms_uniform_bdb7ff8351a1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:24:32.029793+00:00
-- url     : https://prove2.me/submissions/5206e3c9-c627-4746-84f3-164b5342e68f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsGenericProjClosureDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensExpress
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDivisor
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_vdeg_add_4f8428746a98
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_chartMonoZ_homog_94b18e153b90
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_aeval_chartMonoZ_7388c339ad0d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_chart_form_7a9a4f7ad469

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
    (hc : segreVec y c ≠ 0) {L : ℕ} (r : Fin L → Ω) (hr : ∀ l, r l ∈ chartRing O (segreVec y) c) :
    ∃ (n : ℕ) (U : Fin L → MRing (bundleIdx (bundleIdx ι M) M') O), ∀ l,
      IsMultiHomog (U l) (vdeg fun _ => n) ∧
        aeval (pairProjCoord y e φ φ' t) (U l) = algebraMap Ω Φ (r l * segreVec y c ^ n) := by
  choose n U hU hUe using fun l => chart_form (O := O) (M := M) (M' := M') y e φ φ' t c hc (hr l)
  refine ⟨∑ l, n l, fun l => U l * chartMonoZ O M M' c (fun _ => ∑ j, n j - n l), fun l => ⟨?_, ?_⟩⟩
  · have hle : n l ≤ ∑ j, n j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
    have h : vdeg (K := K) (fun _ => ∑ j, n j) = vdeg (fun _ => n l) + vdeg (fun _ => ∑ j, n j - n l) := by
      rw [← vdeg_add]
      congr 1
      funext k
      simp only [Pi.add_apply]
      omega
    rw [h]
    exact IsWeightedHomogeneous.mul (hU l) (chartMonoZ_homog c _)
  · have hle : n l ≤ ∑ j, n j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
    rw [map_mul, hUe l, aeval_chartMonoZ, Finset.prod_pow, ← map_mul]
    congr 1
    rw [mul_assoc, show ∏ k, y ⟨k, c k⟩ = segreVec y c from rfl, ← pow_add, Nat.add_sub_cancel' hle]
end GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor
