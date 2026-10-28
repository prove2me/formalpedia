-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundNumeric.oneBit_upper
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T20:23:58.165312+00:00
-- url     : https://prove2.me/submissions/e17555a9-9fd3-4842-af6a-c553d2c98c84

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_NumericAdmissibility
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Ring


namespace Sensitivity213981Formal
section


set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ThreeBoundNumeric
open ThreeBoundProfiles ThreeBoundFullProfile





















theorem oneBit_upper {n : ℕ} (v : Profile n) (h : BasePositive v) :
    Upper (fun (_ : Fin n) (x : Unit → Bool)=>x ()) v := by
  intro coord
  cases coord with
  | a i j =>
      intro hij x hx
      exact (show (flipsTo (fun x : Unit → Bool=>x ()) true x).card≤ 1 by
        simpa using Finset.card_le_univ (flipsTo (fun x : Unit → Bool=>x ()) true x)).trans
        (h i j hij).1
  | b i j =>
      intro hij x hx
      exact (show (flipsTo (fun x : Unit → Bool=>x ()) false x).card≤ 1 by
        simpa using Finset.card_le_univ (flipsTo (fun x : Unit → Bool=>x ()) false x)).trans
        (h i j hij).2
  | m i j =>
      intro hij hn x hx hy
      change x ()=true at hx
      change x ()=false at hy
      rw [hy] at hx
      contradiction
  | p j l =>
      intro hjl x hx hy
      change x ()=true at hx
      change x ()=false at hy
      rw [hy] at hx
      contradiction
  | d i j l =>
      intro hij hjl x hx hy
      change x ()=true at hx
      change x ()=false at hy
      rw [hy] at hx
      contradiction

end ThreeBoundNumeric




end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {n : Nat} (v : Sensitivity213981Formal.ThreeBoundFullProfile.Profile n)
  (h : @Sensitivity213981Formal.ThreeBoundNumeric.BasePositive n v),
  @Sensitivity213981Formal.ThreeBoundFullProfile.Upper n Unit PUnit.fintype.{0}
    (fun (x : Fin n) (x_1 : Unit → Bool) => x_1 Unit.unit) v := @Sensitivity213981Formal.ThreeBoundNumeric.oneBit_upper
