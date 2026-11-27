-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_AmpleRingFinite_proof_d16d8d1a8838
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:01:43.169717+00:00
-- url     : https://prove2.me/submissions/a37157ff-a3b5-4718-bda1-8e0924320638

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AmpleRingFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AmpleRingIntegralSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AmpleRingFiniteTypeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwinEqAmple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleRingFinite

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
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace AmpleRingFinite
theorem _root_.solution (hint : AmpleRingIntegral.Statement) (hft : AmpleRingFiniteType.Statement) :
    AmpleRingFinite.Statement := by
  intro S _ N Ω _ _ x H D j hj
  have hsub : ∀ l I, D.h l ∈ (H.pow D.m).sub I := by
    intro l I
    have := D.mem_secs l
    rw [SubSystem.secs, Submodule.mem_iInf] at this
    exact this I
  let R := TranslateEq.ampleSub H.toSubSystem D.m (D.h j) (hsub j)
  have hBR : ∀ b ∈ ampleBase (S := S) D.h j, b ∈ R := by
    intro b hb
    refine (Algebra.adjoin_le (R := S) (S := R) ?_) hb
    rintro _ ⟨l, rfl⟩
    refine Set.mem_iInter.mpr fun I => ⟨1, ?_⟩
    rw [pow_one, div_mul_cancel₀ _ hj, Nat.mul_one]
    exact hsub l I
  obtain ⟨r, g, hgR, hgen⟩ := hft S N Ω x H D j hj
  have hfg : Subalgebra.toSubmodule (Algebra.adjoin (ampleBase (S := S) D.h j) (Set.range g)) |>.FG :=
    fg_adjoin_of_finite (Set.finite_range g) (by
      rintro _ ⟨l, rfl⟩
      exact hint S N Ω x H D j hj (g l) (hgR l))
  obtain ⟨n, b, hb⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  have hAR : ∀ y ∈ Algebra.adjoin (ampleBase (S := S) D.h j) (Set.range g), y ∈ R := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨l, rfl⟩ := hy
      exact hgR l
    | algebraMap c => exact hBR c c.2
    | add y z _ _ hy hz => exact R.add_mem hy hz
    | mul y z _ _ hy hz => exact R.mul_mem hy hz
  refine ⟨n, b, fun l => hAR _ ?_, fun f hf => ?_⟩
  · have hl : b l ∈ Submodule.span (ampleBase (S := S) D.h j) (Set.range b) :=
      Submodule.subset_span ⟨l, rfl⟩
    rw [hb] at hl
    exact hl
  · rw [hb]
    exact hgen hf
end AmpleRingFinite
end GroundTheory.Heights₂.Heights.Kleiman
