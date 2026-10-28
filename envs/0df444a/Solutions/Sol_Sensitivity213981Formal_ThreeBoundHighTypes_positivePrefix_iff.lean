-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundHighTypes.positivePrefix_iff
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T18:29:22.098996+00:00
-- url     : https://prove2.me/submissions/958775a9-95cb-4b0b-8e9e-6d2e651f934b

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





















theorem positivePrefix_iff (q d b : ℕ) (P G : ℕ → Prop) (k : Kind q)
    (hp : ∀ c, P c → c ≤  q ∧ d=c)
    (hg : ∀ c, G c → c ≤  q ∧ d=c+1) (hk : OfKind q P G k) :
    (∃ c, c ≤  b ∧ P c) ↔ positivePrefix q b k = true := by
  unfold OfKind at hk
  simp only [positivePrefix,decide_eq_true_eq]
  split_ifs at hk with h1 h2
  · have hd := (hp _ hk.1).2
    constructor
    · rintro ⟨c,hcb,hc⟩
      have hdc := (hp _ hc).2
      exact Or.inl ⟨h1,by omega⟩
    · intro hh
      refine ⟨k.val,?_,hk.1⟩
      rcases hh with hh | hh <;> omega
  · constructor
    · rintro ⟨c,hcb,hc⟩
      have hdc := hp _ hc
      have hdg := hg _ hk.1
      rcases hk.2 with hz | hn
      · omega
      · have he : c=k.val-q := by omega
        exact False.elim (hn (he ▸ hc))
    · intro hh
      rcases hh with hh | hh <;> omega
  · have hd := (hp _ hk.1).2
    constructor
    · rintro ⟨c,hcb,hc⟩
      have hdc := (hp _ hc).2
      exact Or.inr ⟨by omega,by omega⟩
    · intro hh
      refine ⟨k.val-(2*q+1),?_,hk.1⟩
      rcases hh with hh | hh <;> omega

end ThreeBoundHighTypes




end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ (q d b : Nat) (P G : Nat → Prop) (k : Sensitivity213981Formal.ThreeBoundHighTypes.Kind q)
  (hp : ∀ (c : Nat), P c → And (@LE.le.{0} Nat instLENat c q) (@Eq.{1} Nat d c))
  (hg :
    ∀ (c : Nat),
      G c →
        And (@LE.le.{0} Nat instLENat c q)
          (@Eq.{1} Nat d
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (hk : Sensitivity213981Formal.ThreeBoundHighTypes.OfKind q P G k),
  Iff (@Exists.{1} Nat fun (c : Nat) => And (@LE.le.{0} Nat instLENat c b) (P c))
    (@Eq.{1} Bool (Sensitivity213981Formal.ThreeBoundHighTypes.positivePrefix q b k) Bool.true) := @Sensitivity213981Formal.ThreeBoundHighTypes.positivePrefix_iff
