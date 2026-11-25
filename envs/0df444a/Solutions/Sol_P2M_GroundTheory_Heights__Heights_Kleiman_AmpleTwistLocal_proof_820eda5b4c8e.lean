-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_proof_820eda5b4c8e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:28:45.889151+00:00
-- url     : https://prove2.me/submissions/9f509b1e-536b-4599-b8f9-ec87179d17b6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsAmple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsAmpleAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleTwistLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_pow_mem_pow_9418c8e10619
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleTwistLocal_mul_mem_twist_pow_d77a3231d657

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
open GroundTheory.Heights₂.Heights.Kleiman.AmpleTwistLocal
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.AmpleTwistLocal
theorem _root_.solution (hA : AmpleAffineGen.Statement.{u, w}) : AmpleTwistLocal.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x H A Q b j
  classical
  by_cases h0 : A.h j = 0
  · refine ⟨0, fun n _ I y _ => ⟨1, ?_⟩⟩
    rw [h0, pow_one, mul_zero]
    exact Submodule.zero_mem _
  obtain ⟨p, s, hs, hgen⟩ := hA S Ω N x H A Q b j h0
  have hhI : ∀ I : Chart x, A.h j ∈ (H.pow A.m).sub I := fun I =>
    (Submodule.mem_iInf _).mp (A.mem_secs j) I
  choose k hk using hs
  refine ⟨Finset.univ.sup fun q : Fin p × Chart x => k q.1 q.2, fun n hn I y hy => ?_⟩
  have hglob : ∀ t, s t * A.h j ^ n ∈ (Q.twist (H.pow (b + A.m * n))).secs := by
    intro t
    refine (Submodule.mem_iInf _).mpr fun I' => ?_
    have hle : k t I' ≤ n := le_trans
      (Finset.le_sup (f := fun q : Fin p × Chart x => k q.1 q.2) (Finset.mem_univ (t, I'))) hn
    have h1 := mul_mem_twist_pow Q.toSubSystem H.toSubSystem I' (hk t I')
      (pow_mem_pow H.toSubSystem I' (hhI I') (n - k t I'))
    have e1 : s t * A.h j ^ k t I' * A.h j ^ (n - k t I') = s t * A.h j ^ n := by
      rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hle]
    have e2 : b + A.m * k t I' + A.m * (n - k t I') = b + A.m * n := by
      rw [add_assoc, ← mul_add, Nat.add_sub_cancel' hle]
    rw [e1, e2] at h1
    exact h1
  have hpn : A.h j ^ n ≠ 0 := pow_ne_zero n h0
  obtain ⟨e, g, hg, hz⟩ := hgen I (y / A.h j ^ n) n (by rwa [div_mul_cancel₀ y hpn])
  refine ⟨e, ?_⟩
  have hy' : y = A.h j ^ n * ∑ t, g t * s t := by
    rw [← hz]; field_simp
  rw [hy', Finset.mul_sum, Finset.sum_mul]
  refine Submodule.sum_mem _ fun t _ => ?_
  have e3 : A.h j ^ n * (g t * s t) * A.h j ^ e = (s t * A.h j ^ n) * (g t * A.h j ^ e) := by ring
  rw [e3]
  exact Submodule.mul_mem_mul (Submodule.subset_span (hglob t)) (hg t)
end GroundTheory.Heights₂.Heights.Kleiman.AmpleTwistLocal
