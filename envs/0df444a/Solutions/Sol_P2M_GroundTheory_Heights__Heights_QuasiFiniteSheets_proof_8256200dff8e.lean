-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_QuasiFiniteSheets_proof_8256200dff8e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:11:29.264087+00:00
-- url     : https://prove2.me/submissions/275f9b59-be54-4037-be50-cb100ea2e02b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsQuasiFiniteSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPrimeQuasiFiniteSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPrimePairMeetImage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PQuasiFiniteSheets
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_QuasiFiniteSheets_hasSheetsOff_biUnion_39b419609317

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open QuasiFiniteSheets
namespace GroundTheory.Heights₂.Heights
namespace QuasiFiniteSheets
theorem _root_.solution (h₁ : PrimeQuasiFiniteSheets.Statement)
    (h₂ : PrimePairMeetImage.Statement) : QuasiFiniteSheets.Statement := by
  intro n d I A hfin
  classical
  have hmin := I.finite_minimalPrimes_of_isNoetherianRing
  have hfinQ : ∀ Q ∈ I.minimalPrimes, ∀ y, (ComplexSets.fibre Q A y).Finite := fun Q hQ y =>
    (hfin y).subset fun x hx => ⟨fun q hq => hx.1 q (hQ.1.2 hq), hx.2⟩
  have hZ : ComplexSets.zeroSet I = ⋃ Q ∈ hmin.toFinset, ComplexSets.zeroSet Q := by
    ext x
    constructor
    · intro hx
      have hker : I ≤ RingHom.ker (eval x) := fun q hq => hx q hq
      have : (RingHom.ker (eval x : MvPolynomial (Fin n) ℂ →+* ℂ)).IsPrime := RingHom.ker_isPrime _
      obtain ⟨Q, hQ, hQle⟩ := Ideal.exists_minimalPrimes_le hker
      exact Set.mem_iUnion₂.mpr ⟨Q, hmin.mem_toFinset.mpr hQ, fun q hq => hQle hq⟩
    · intro hx
      obtain ⟨Q, hQ, hxQ⟩ := Set.mem_iUnion₂.mp hx
      exact fun q hq => hxQ q ((hmin.mem_toFinset.mp hQ).1.2 hq)
  obtain ⟨c, hc, hsh⟩ := hasSheetsOff_biUnion hmin.toFinset A
    (fun Q hQ => h₁ n d Q A (hmin.mem_toFinset.mp hQ).1.1 (hfinQ Q (hmin.mem_toFinset.mp hQ)))
    (fun Q hQ Q' hQ' hne => h₂ n d Q Q' A (hmin.mem_toFinset.mp hQ).1.1 (hmin.mem_toFinset.mp hQ').1.1 hne
      (hfinQ Q (hmin.mem_toFinset.mp hQ)) (hfinQ Q' (hmin.mem_toFinset.mp hQ')))
  rw [← hZ] at hsh
  exact ⟨c, hc, hsh⟩
end QuasiFiniteSheets
end GroundTheory.Heights₂.Heights
