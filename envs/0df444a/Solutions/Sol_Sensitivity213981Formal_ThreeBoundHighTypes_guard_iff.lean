-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundHighTypes.guard_iff
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T18:28:15.487756+00:00
-- url     : https://prove2.me/submissions/fe7ed791-0efc-4b83-a4c0-795f6004ea9d

import Definitions.Def_Sensitivity213981Formal_HighTypeCore
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fintype.Basic


namespace Sensitivity213981Formal
section
/- The finite high-head type system depends only on exact guard counts.
It covers both equal-threshold and symmetric min/max targets, through any
fixed maximum tolerance. The cases q=2 and q=3 have 8 and 11 types. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000

namespace ThreeBoundHighTypes



















theorem guard_iff (q d : ℕ) (P G : ℕ → Prop) (k : Kind q)
    (hp : ∀ b, P b → b ≤  q ∧ d=b)
    (hg : ∀ b, G b → b ≤  q ∧ d=b+1) (hk : OfKind q P G k) :
    (∃ b, G b) ↔ isGuard q k = true := by
  unfold OfKind at hk
  simp only [isGuard,decide_eq_true_eq]
  split_ifs at hk with h1 h2
  · constructor
    · rintro ⟨b,hb⟩
      obtain ⟨_,hdp⟩ := hp _ hk.1
      obtain ⟨_,hdg⟩ := hg _ hb
      rcases hk.2 with hz | hn
      · omega
      · have he : b=k.val-1 := by omega
        exact False.elim (hn (he ▸ hb))
    · omega
  · exact ⟨fun _ => by omega,fun _ => ⟨_,hk.1⟩⟩
  · exact ⟨fun _ => by omega,fun _ => ⟨_,hk.2⟩⟩



end ThreeBoundHighTypes




end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ (q d : Nat) (P G : Nat → Prop) (k : Sensitivity213981Formal.ThreeBoundHighTypes.Kind q)
  (hp : ∀ (b : Nat), P b → And (@LE.le.{0} Nat instLENat b q) (@Eq.{1} Nat d b))
  (hg :
    ∀ (b : Nat),
      G b →
        And (@LE.le.{0} Nat instLENat b q)
          (@Eq.{1} Nat d
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (hk : Sensitivity213981Formal.ThreeBoundHighTypes.OfKind q P G k),
  Iff (@Exists.{1} Nat fun (b : Nat) => G b)
    (@Eq.{1} Bool (Sensitivity213981Formal.ThreeBoundHighTypes.isGuard q k) Bool.true) := @Sensitivity213981Formal.ThreeBoundHighTypes.guard_iff
