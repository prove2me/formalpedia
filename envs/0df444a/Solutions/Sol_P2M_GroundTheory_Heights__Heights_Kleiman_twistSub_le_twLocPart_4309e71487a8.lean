-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_twistSub_le_twLocPart_4309e71487a8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:30:25.376851+00:00
-- url     : https://prove2.me/submissions/7ddcdf01-6af3-4e27-b4b3-f849b680f06e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistSplitObj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistSplitChart
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mul_mem_of_mem_span_3875fb0ba4e8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_pow_sub_le_span_9b5c2856005a

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
open MvPolynomial Pointwise
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {r : ℕ} (η : Fin (r + 1) → Ω)
variable {G B : SubSystem S x Ω}
variable (M₀ : FinGradedSub (S := S) (x := x) Ω)
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (hG : ∀ I, M₀.tilde 0 I = G.sub I)
    (hB : ∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I) (K : Chart x) (n : ℕ) (c : ℤ)
    {y : Ω} (hy : y ∈ ((G.twist (B.pow n)).twist (twistSys S x c)).sub K) :
    y ∈ twLocPart η M₀ n c K.1 := by
  change y ∈ twLocPartA η M₀ n c K
  revert y
  change Submodule.span _ _ ≤ twLocPartA η M₀ n c K
  rw [Submodule.span_le]
  rintro _ ⟨t, ht, y', hy', rfl⟩
  rw [smul_eq_mul, ← one_mul (t * y')]
  refine mul_mem_of_mem_span _ 1 ?_ ht hy'
  rintro u ⟨f, s, e, e', hs, hf, hse, hc, rfl⟩ v ⟨q, hq, g, hg, rfl⟩
  rw [one_mul, smul_eq_mul]
  rw [← hG K] at hg
  refine mul_mem_of_mem_span _ (aeval x f / aeval x s) ?_ (pow_sub_le_span η hB K n hq) hg
  rintro q' hq' _ ⟨m, s₁, a, e₁, hs₁, hse₁, hm, hae, rfl⟩
  refine Submodule.subset_span ⟨(aeval x f * m) * q', s * s₁, a + e', e + e₁, mul_mem hs hs₁,
    hse.mul hse₁, ?_, by push_cast; omega, ?_⟩
  · rw [twPart_of_nonneg]
    exact Submodule.subset_span (Set.mul_mem_mul (M₀.smul_mem e' a f m hf hm) hq')
  · rw [smul_eq_mul, map_mul, mul_inv, div_eq_mul_inv]
    ring
end GroundTheory.Heights₂.Heights.Kleiman
