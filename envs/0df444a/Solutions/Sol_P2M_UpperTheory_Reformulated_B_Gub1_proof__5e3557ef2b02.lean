-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Gub1_proof__5e3557ef2b02
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:54:26.832337+00:00
-- url     : https://prove2.me/submissions/ce0355e3-26fc-4304-9d8d-42c5b26d0b0b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsLineIndex
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerExtra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Gub1.proof
theorem _root_.solution.{u_1, u_2} :
    ∀ (E : Type u_1) (W : Type u_2) [inst : Field E] [inst_1 : NumberField E] [inst_2 : AddCommGroup W]
      [inst_3 : _root_.Module E W], GroundTheory.Heights₂.Heights.FiniteCovolume.LineIndexNeZero.Statement E W := by
  intro E W _ _ _ _ La x hL _ _
  have hfg : (La ⊓ (Submodule.span E {x}).toAddSubgroup).FG :=
    (Submodule.fg_iff_addSubgroup_fg (AddSubgroup.toIntSubmodule _)).1
      (((Submodule.fg_iff_addSubgroup_fg (AddSubgroup.toIntSubmodule La)).2 hL.fg).of_le
        (AddSubgroup.toIntSubmodule.monotone inf_le_left))
  have := (AddGroup.fg_iff_addSubgroup_fg _).2 hfg
  refine @AddSubgroup.index_ne_zero_of_finite _ _ _ (AddCommGroup.finite_of_fg_isAddTorsion _ ?_)
  rintro ⟨y, hy', hy⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  obtain ⟨n, hn, hc⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
    (Algebra.IsAlgebraic.isAlgebraic c)).exists_integral_multiple
  refine isOfFinAddOrder_iff_zsmul_eq_zero.2 ⟨n, hn, (QuotientAddGroup.eq_zero_iff (n • _)).2 ?_⟩
  exact ⟨⟨n • c, hc⟩, smul_assoc n c x⟩
end UpperTheory.Reformulated.B.Gub1.proof
