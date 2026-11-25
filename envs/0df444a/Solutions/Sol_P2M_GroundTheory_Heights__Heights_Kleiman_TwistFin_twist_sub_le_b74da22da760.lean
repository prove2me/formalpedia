-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_twist_sub_le_b74da22da760
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:30:48.70661+00:00
-- url     : https://prove2.me/submissions/7b34f204-721b-4943-bb21-292e6ec323e0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_IsUnitPhiOfMemMonos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_CoeffPsiMulSingle
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_pow_sub_le_4eab0f2c1500
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_chart_mul_mem_span_1b6ac5c8ed25

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
namespace GroundTheory.Heights₂.Heights.Kleiman.TwistFin
theorem _root_.solution (G B : LineBundle S x)
    (hgen : ∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I)
    (hG : ∀ I, M0.tilde 0 I = G.sub I) (I : Chart x) (b : ℕ) :
    ∀ ω ∈ (G.twist (B.pow b)).sub I, ω ∈ Submodule.span S (genSet x η S M0 I b) := by
  let W : Submodule (chartRing S x I) Ω :=
    { carrier := Submodule.span S (genSet x η S M0 I b)
      add_mem' := fun ha hb => add_mem ha hb
      zero_mem' := zero_mem _
      smul_mem' := fun c ω hω => chart_mul_mem_span x η S M0 I b c hω }
  suffices hle : (G.twist (B.pow b)).sub I ≤ W from fun ω hω => hle hω
  change Submodule.span _ _ ≤ W
  rw [Submodule.span_le]
  rintro _ ⟨q, hq, y, hy, rfl⟩
  have hq' := pow_sub_le x η S B.toSubFamily.toSubSystem hgen I b hq
  rw [← hG I] at hy
  have hmul := Submodule.mul_mem_mul hq' hy
  rw [FinGradedSub.tilde, Submodule.span_mul_span] at hmul
  rw [smul_eq_mul]
  refine (Submodule.span_le.mpr ?_) hmul
  rintro _ ⟨_, ⟨h, hh, rfl⟩, _, ⟨m, t, a, e, ht, hte, hm, hae, rfl⟩, rfl⟩
  refine Submodule.subset_span ⟨1, 0, h, m, a, t, e, isHomogeneous_one _ _, hh, hm, ht, hte, by omega, ?_⟩
  rw [map_one, one_mul, smul_eq_mul]
  field_simp
end GroundTheory.Heights₂.Heights.Kleiman.TwistFin
