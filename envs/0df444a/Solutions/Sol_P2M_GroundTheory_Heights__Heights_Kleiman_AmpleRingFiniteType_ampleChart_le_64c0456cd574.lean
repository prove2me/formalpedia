-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_AmpleRingFiniteType_ampleChart_le_64c0456cd574
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:33:28.00352+00:00
-- url     : https://prove2.me/submissions/72ededf8-6f0d-4a1b-ac4f-596e13ef68b9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AmpleRingFiniteTypeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleRingFiniteType
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleRingFiniteType_chartRing_le_ac4d9db28511
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_pow_sub_25f1e2a30df9


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.AmpleRingFiniteType
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.AmpleRingFiniteType
theorem _root_.solution (H : LineBundle S x) (D : AmpleData S x H) (j : Fin (D.r + 1))
    (h0 : D.h j ≠ 0) (J : Chart x) {a : Ω} (ha : a ∈ ampleChart H.toSubSystem D.m (D.h j) J) :
    a ∈ Algebra.adjoin S (Set.range (fun l => D.h l / D.h j) ∪ (chartGens J : Set Ω)) := by
  set L := Algebra.adjoin S (Set.range (fun l => D.h l / D.h j) ∪ (chartGens J : Set Ω))
  have hA : ∀ c ∈ chartRing S x J, c ∈ L := fun c hc =>
    Algebra.adjoin_mono Set.subset_union_right (chartRing_le J hc)
  have hP : ∀ q ∈ (H.pow D.m).sub J, q / D.h j ∈ L := by
    intro q hq
    rw [← D.generates J] at hq
    induction hq using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨l, rfl⟩ := hq
      exact Algebra.subset_adjoin (Or.inl ⟨l, rfl⟩)
    | zero => rw [zero_div]; exact zero_mem _
    | add q q' _ _ h1 h2 => rw [add_div]; exact add_mem h1 h2
    | smul c q _ h1 =>
      rw [chartRing_smul_def, mul_div_assoc]
      exact mul_mem (hA _ c.2) h1
  have hPn : ∀ n, ∀ y ∈ ((H.pow D.m).sub J) ^ n, y / D.h j ^ n ∈ L := by
    intro n
    induction n with
    | zero =>
      intro y hy
      obtain ⟨c, rfl⟩ := Submodule.mem_one.mp hy
      rw [pow_zero, div_one]
      exact hA _ c.2
    | succ n ih =>
      intro y hy
      rw [pow_succ] at hy
      refine Submodule.mul_induction_on hy (fun p hp q hq => ?_) (fun y y' h1 h2 => ?_)
      · rw [pow_succ, mul_div_mul_comm]
        exact mul_mem (ih p hp) (hP q hq)
      · rw [add_div]; exact add_mem h1 h2
  obtain ⟨n, hn⟩ := ha
  have hn' : a * D.h j ^ n ∈ ((H.pow D.m).sub J) ^ n := by
    rw [SubSystem.pow_sub, ← pow_mul, ← SubSystem.pow_sub]
    exact hn
  have := hPn n _ hn'
  rwa [mul_div_cancel_right₀ _ (pow_ne_zero _ h0)] at this
end GroundTheory.Heights₂.Heights.Kleiman.AmpleRingFiniteType
