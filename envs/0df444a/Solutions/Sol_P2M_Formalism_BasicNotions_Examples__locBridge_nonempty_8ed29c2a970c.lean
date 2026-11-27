-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__locBridge_nonempty_8ed29c2a970c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:50:21.17201+00:00
-- url     : https://prove2.me/submissions/f1862e8c-f851-47b4-91ab-7a9d62292921

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocC
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CovariantDegrees
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocD
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_exists_emb_1690c8e74711
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_isAlgClosureQ_74b0853cbd95


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc LB
namespace Formalism.BasicNotions.Examples₂
theorem _root_.solution (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) :
    ∃ (j : Ω →+* Om l) (_ : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1), ∀ LL : FinExt l,
      (∀ (τ : ↥(KwF (E := E) j) →ₐ[ℚ_[l]] Om l) (x : ↥(KwF (E := E) j)), τ x ∈ LL.1) →
      ∃ B : LocBridge l E Ω (Dec (F := E) A) ↥(OL LL), B.j = j ∧ B.LL = LL ∧ B.Kw.1 = KwF (E := E) j := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : IsAlgClosure ℚ Ω := isAlgClosureQ E Ω
  obtain ⟨j, hj⟩ := exists_emb (l := l) A hA
  exact ⟨j, hj, fun LL hLL => ⟨bridgeOf hj LL hLL, rfl, rfl, rfl⟩⟩
end Formalism.BasicNotions.Examples₂
