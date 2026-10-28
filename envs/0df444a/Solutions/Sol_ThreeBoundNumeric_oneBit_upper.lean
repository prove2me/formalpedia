-- Prove2me | solution 1 for ThreeBoundNumeric.oneBit_upper
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:43:09.128996+00:00
-- url     : https://prove2.me/submissions/da09c943-5aa5-49c8-bbbb-60c11cec4b29

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Ring
import Definitions.Def_Sensitivity213303_ClosureHomogeneity
import Definitions.Def_Sensitivity213303_FlatProfiles
import Definitions.Def_Sensitivity213303_FullProfileClosure
import Definitions.Def_Sensitivity213303_NumericAdmissibility
import Definitions.Def_Sensitivity213303_NumericExpressions
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_Q2RawExpressions

namespace ThreeBoundFullProfile
end ThreeBoundFullProfile
namespace ThreeBoundProfiles
end ThreeBoundProfiles
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace ThreeBoundNumeric
end ThreeBoundNumeric
open ThreeBoundNumeric
open ThreeBoundProfiles ThreeBoundFullProfile

theorem solution {n : ℕ} (v : Profile n) (h : BasePositive v) :
    Upper (fun (_ : Fin n) (x : Unit → Bool)=>x ()) v := by
  intro coord
  cases coord with
  | a i j =>
      intro hij x hx
      exact (show (flipsTo (fun x : Unit → Bool=>x ()) true x).card≤1 by
        simpa using Finset.card_le_univ (flipsTo (fun x : Unit → Bool=>x ()) true x)).trans
        (h i j hij).1
  | b i j =>
      intro hij x hx
      exact (show (flipsTo (fun x : Unit → Bool=>x ()) false x).card≤1 by
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
end
