-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_pow_sub_le_4eab0f2c1500
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:19:00.807629+00:00
-- url     : https://prove2.me/submissions/e730e891-3ca1-4606-9762-16b0f277d0d7

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
namespace GroundTheory.Heights₂.Heights.Kleiman.TwistFin
theorem _root_.solution (B : SubSystem S x Ω)
    (hgen : ∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I) (I : Chart x) (b : ℕ) :
    (B.pow b).sub I ≤ Submodule.span (chartRing S x I)
      {z | ∃ h : MvPolynomial (Fin (r + 1)) S, h.IsHomogeneous b ∧ z = aeval η h} := by
  induction b with
  | zero =>
    obtain ⟨i, hi⟩ := I.2.1
    change twistMod S x 0 I ≤ _
    rw [twistMod_eq_span 0 I hi, zpow_zero]
    exact Submodule.span_mono (Set.singleton_subset_iff.mpr ⟨1, isHomogeneous_one _ _, by simp⟩)
  | succ b ih =>
    change Submodule.span _ _ ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨q, hq, y, hy, rfl⟩
    rw [← hgen I] at hq
    have hmul : q * y ∈ Submodule.span (chartRing S x I) (Set.range η) *
        Submodule.span (chartRing S x I)
          {z | ∃ h : MvPolynomial (Fin (r + 1)) S, h.IsHomogeneous b ∧ z = aeval η h} :=
      Submodule.mul_mem_mul hq (ih hy)
    rw [Submodule.span_mul_span] at hmul
    rw [smul_eq_mul]
    refine Submodule.span_mono ?_ hmul
    rintro _ ⟨_, ⟨j, rfl⟩, _, ⟨h, hh, rfl⟩, rfl⟩
    refine ⟨X j * h, ?_, by rw [map_mul, aeval_X]⟩
    simpa [add_comm] using (isHomogeneous_X S j).mul hh
end GroundTheory.Heights₂.Heights.Kleiman.TwistFin
