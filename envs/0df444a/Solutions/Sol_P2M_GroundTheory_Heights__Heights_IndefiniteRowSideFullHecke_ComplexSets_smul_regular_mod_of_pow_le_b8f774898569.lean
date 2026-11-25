-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_smul_regular_mod_of_pow_le_b8f774898569
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:10:03.831206+00:00
-- url     : https://prove2.me/submissions/1afa85f1-2cbe-48c0-b0a8-ed4318e5b3a3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatLocalRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFlatLocalRegularElement
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_mem_colon_smul_top_of_flat_e37665e62fd4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_not_mem_forall_mul_mem_91389b1b572a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_smul_mem_smul_top_of_mem_42c739f56100

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open IsLocalRing TensorProduct
open scoped Pointwise
variable {A B M : Type} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
variable [IsNoetherianRing A] [IsLocalRing A] [Module.Flat A M]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution (y : B)
    (h0 : ∀ u : M, y • u ∈ maximalIdeal A • (⊤ : Submodule A M) →
      u ∈ maximalIdeal A • (⊤ : Submodule A M)) (J : Ideal A) :
    (∃ n, maximalIdeal A ^ n ≤ J) →
      ∀ z : M, y • z ∈ J • (⊤ : Submodule A M) → z ∈ J • (⊤ : Submodule A M) := by
  induction J using WellFoundedGT.induction with
  | _ J ih =>
  intro hpow z hz
  by_cases hJ : J = ⊤
  · subst hJ
    rw [Submodule.top_smul]
    exact Submodule.mem_top
  obtain ⟨a, haJ, hma⟩ := exists_not_mem_forall_mul_mem (maximalIdeal A) J hJ hpow
  have hlt : J < J ⊔ Ideal.span {a} :=
    lt_of_le_of_ne le_sup_left fun h =>
      haJ (h ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a))
  have hz' := ih _ hlt (hpow.imp fun n hn => hn.trans le_sup_left) z
    (Submodule.smul_mono_left le_sup_left hz)
  rw [Submodule.sup_smul, Submodule.mem_sup] at hz'
  obtain ⟨w, hw, v, hv, rfl⟩ := hz'
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hv
  obtain ⟨u, -, rfl⟩ := hv
  have hyw := smul_mem_smul_top_of_mem J y hw
  have hau : a • (y • u) ∈ J • (⊤ : Submodule A M) := by
    rw [smul_comm]
    have : y • (a • u) = y • (w + a • u) - y • w := by rw [smul_add]; abel
    rw [this]
    exact sub_mem hz hyw
  have hK : LinearMap.ker (J.mkQ ∘ₗ LinearMap.mulRight A a) ≤ maximalIdeal A := by
    intro r hr
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.mulRight_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hr
    by_contra hrm
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hrm
    obtain ⟨r', rfl⟩ := hrm
    apply haJ
    have := J.mul_mem_left (↑r'⁻¹ : A) hr
    rwa [← mul_assoc, Units.inv_mul, one_mul] at this
  have hu := h0 u (Submodule.smul_mono_left hK (mem_colon_smul_top_of_flat J a hau))
  refine add_mem hw ?_
  refine Submodule.smul_induction_on hu (fun r hr m _ => ?_) (fun x x' hx hx' => ?_)
  · rw [smul_smul, mul_comm]
    exact Submodule.smul_mem_smul (hma r hr) Submodule.mem_top
  · rw [smul_add]
    exact add_mem hx hx'
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
