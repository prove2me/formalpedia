-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_exists_lift_cf8724f91cea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:35:41.653722+00:00
-- url     : https://prove2.me/submissions/ec400a46-3021-47b8-8676-50644a6a9bff

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_OneNotMemOfIsPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsLocalizationConeVarMap
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_coe_algebraMap_cone_190c0cf09fd0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_locRing_algebraMap_cone_coe_cb5a4a87300e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_homog_X_910d45ab2133


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo IsLocalRing
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime]
variable {P W}
namespace GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
theorem _root_.solution (hPW : P ≤ W) {v : ∀ k, ι k} (hv : ∀ k, (X ⟨k, v k⟩ : MRing ι) ∉ W) (f : MRing ι) :
    ∃ F, coneVarMap P W hPW v F =
      algebraMap (MRing ι ⧸ P) (coneLocRing P W hPW) (Ideal.Quotient.mk P f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C c =>
    refine ⟨(c : MvPolynomial K (locRing P W)), ?_⟩
    rw [map_intCast, eq_intCast (MvPolynomial.C) c, map_intCast, map_intCast]
  | add p q hp hq =>
    obtain ⟨F, hF⟩ := hp
    obtain ⟨G, hG⟩ := hq
    exact ⟨F + G, by rw [map_add, hF, hG, map_add, map_add]⟩
  | mul_X p n hp =>
    obtain ⟨F, hF⟩ := hp
    obtain ⟨k, i⟩ := n
    have hX0 : fracHom P (X ⟨k, v k⟩) ≠ 0 := by
      rw [Ne, fracHom_eq_zero_iff]
      exact fun h => hv k (hPW h)
    have hr : fracHom P (X ⟨k, i⟩) / fracHom P (X ⟨k, v k⟩) ∈ locRing P W :=
      div_mem_locRing hPW (homog_X k i) (homog_X k (v k)) (hv k)
    refine ⟨F * (MvPolynomial.C (⟨_, hr⟩ : locRing P W) * X k), ?_⟩
    have hX : coneVarMap P W hPW v (X k) =
        algebraMap (MRing ι ⧸ P) (coneLocRing P W hPW) (Ideal.Quotient.mk P (X ⟨k, v k⟩)) :=
      aeval_X _ _
    rw [map_mul, map_mul, hF, algHom_C, hX]
    apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_mul, coe_algebraMap_cone, coe_algebraMap_cone, coe_algebraMap_cone,
      locRing.algebraMap_cone_coe, ← fracHom_apply, ← fracHom_apply, ← fracHom_apply, map_mul]
    rw [div_mul_cancel₀ _ hX0]
end GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
