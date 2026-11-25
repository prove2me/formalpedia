-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_chart_mul_mem_span_1b6ac5c8ed25
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:19:50.2966+00:00
-- url     : https://prove2.me/submissions/ba54f03a-94eb-4187-9583-1c413f4a28f9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_IsUnitPhiOfMemMonos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_CoeffPsiMulSingle

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
theorem _root_.solution (I : Chart x) (b : ℕ) (c : chartRing S x I) {ω : Ω}
    (hω : ω ∈ Submodule.span S (genSet x η S M0 I b)) :
    (c : Ω) * ω ∈ Submodule.span S (genSet x η S M0 I b) := by
  obtain ⟨f', t', e'', ht', hf', hte', hc⟩ := c.2
  induction hω using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨f, e, h, m, a, t, e', hf, hh, hm, ht, hte, hee, rfl⟩ := hz
    refine Submodule.subset_span ⟨f' * f, e'' + e, h, m, a, t' * t, e'' + e', hf'.mul hf, hh, hm,
      mul_mem ht' ht, hte'.mul hte, by push_cast; omega, ?_⟩
    rw [hc]
    have h1 := eval_ne_zero_of_mem_monos I ht'
    have h2 := eval_ne_zero_of_mem_monos I ht
    simp only [map_mul]
    field_simp
  | zero => rw [mul_zero]; exact zero_mem _
  | add p q _ _ hp hq => rw [mul_add]; exact add_mem hp hq
  | smul s p _ hp => rw [mul_smul_comm]; exact Submodule.smul_mem _ s hp
end GroundTheory.Heights₂.Heights.Kleiman.TwistFin
