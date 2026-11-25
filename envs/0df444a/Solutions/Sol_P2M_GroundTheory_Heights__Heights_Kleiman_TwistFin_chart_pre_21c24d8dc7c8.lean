-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_chart_pre_21c24d8dc7c8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:56:21.401827+00:00
-- url     : https://prove2.me/submissions/61cdf32c-f817-4acd-8865-7ba3f50951b5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_IsUnitPhiOfMemMonos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_CoeffPsiMulSingle
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_twist_sub_le_b74da22da760
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_gen_pre_cba970ff5a87
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_algebraMap_LA_e2e747c45c95


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
open MvPolynomial AddMonoidAlgebra
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.TwistFin
variable {Ω : Type w} [Field Ω] {N r : ℕ}
variable (x : Fin (N + 1) → Ω) (η : Fin (r + 1) → Ω) (S : Type u) [CommRing S] [Algebra S Ω]
variable (n0 : ℕ) (d0 : Fin n0 → ℤ) (g0 : Fin n0 → Ω)
variable (M0 : FinGradedSub (S := S) (x := x) Ω)
variable {n0 d0 g0}
namespace GroundTheory.Heights₂.Heights.Kleiman.TwistFin
theorem _root_.solution (G B : LineBundle S x)
    (hgen : ∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I)
    (hG : ∀ I, M0.tilde 0 I = G.sub I)
    (hspan : ∀ c, M0.piece c ≤ Submodule.span S {z | ∃ (j : Fin n0) (f : Poly S N) (e : ℕ),
      f.IsHomogeneous e ∧ (e : ℤ) + d0 j = c ∧ z = aeval x f • g0 j})
    (I : StdCell N) (hI : ∀ i ∈ I.1, x i ≠ 0) (b : ℕ) {ω : Ω}
    (hω : ω ∈ (G.twist (B.pow b)).sub (toChart x I hI)) :
    ∃ z ∈ degLoc (tgraded x η S n0 d0 g0) 0 I,
      locL x η S n0 d0 g0 I.1 hI z = (toA x η).symm (single ((0 : ℤ), (b : ℤ)) ω) := by
  have h1 := twist_sub_le x η S M0 G B hgen hG (toChart x I hI) b ω hω
  clear hω
  induction h1 using Submodule.span_induction with
  | mem z hz => exact gen_pre x η S M0 hspan I hI b hz
  | zero => exact ⟨0, zero_mem _, by rw [map_zero, single_zero, map_zero]⟩
  | add p q _ _ hp hq =>
    obtain ⟨z1, hz1, e1⟩ := hp
    obtain ⟨z2, hz2, e2⟩ := hq
    exact ⟨z1 + z2, add_mem hz1 hz2, by rw [map_add, e1, e2, single_add, map_add]⟩
  | smul s p _ hp =>
    obtain ⟨z1, hz1, e1⟩ := hp
    refine ⟨(C s : Sy S r) • z1, Submodule.smul_mem _ _ hz1, ?_⟩
    rw [LinearMap.map_smul_of_tower, e1]
    apply (toA x η).injective
    rw [toA_smulSy, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, psi, aeval_C, algebraMap_LA,
      single_mul_single, Algebra.smul_def]
    simp
end GroundTheory.Heights₂.Heights.Kleiman.TwistFin
