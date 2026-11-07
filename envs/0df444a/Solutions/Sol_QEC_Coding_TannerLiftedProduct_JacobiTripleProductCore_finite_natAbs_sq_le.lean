-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.finite_natAbs_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:52:06.321592+00:00
-- url     : https://prove2.me/submissions/7d37a982-c975-441b-ba9a-4cd1955dac5b

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (d : ℕ) :
    {m : ℤ | m.natAbs ^ 2 ≤ d}.Finite :=
  (Set.finite_Icc (-(d : ℤ)) (d : ℤ)).subset fun m (hm : m.natAbs ^ 2 ≤ d) => by
    have habs : m.natAbs ≤ d := by nlinarith [Nat.le_self_pow (n := 2) (by omega) m.natAbs]
    constructor <;> (rcases abs_cases m with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
