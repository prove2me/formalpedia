-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22VariableCache.cache1100_valid
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:41:02.21393+00:00
-- url     : https://prove2.me/submissions/ee55bccd-a90d-455b-9cb6-c6c608011b05

import Definitions.Def_Sensitivity213981Formal_Endpoint22VariableCacheData1100
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankPackedVariableCache
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto


namespace Sensitivity213981Formal
section
/- Reuse a certified variable-cost maximum across all rows with the same
packed capcode and external count.  Lookups verify both arguments exactly.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ThreeBoundEndpoint22Packed
open ThreeBoundNumeric (maximum)
open ThreeBoundRankCached ThreeBoundRankAnnotated
open ThreeBoundEndpoint22Records











theorem VariableCache.check_branch (q : ℕ) (values : CostValues) (pivot : ℕ)
    (left right : VariableCache) (hl : left.check q values=true)
    (hr : right.check q values=true) :
    (VariableCache.branch pivot left right).check q values=true := by
  simp only [VariableCache.check,hl,hr,Bool.true_and]













end ThreeBoundEndpoint22Packed



end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22VariableCache
open ThreeBoundEndpoint22Packed ThreeBoundMinmaxNumeric.Endpoint22
theorem cache1100_valid_block000 : cache1100Block000.check 3 values1100=true := by decide +kernel
end ThreeBoundEndpoint22VariableCache


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22VariableCache
open ThreeBoundEndpoint22Packed ThreeBoundMinmaxNumeric.Endpoint22
theorem cache1100_valid_block001 : cache1100Block001.check 3 values1100=true := by decide +kernel
end ThreeBoundEndpoint22VariableCache


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22VariableCache
open ThreeBoundEndpoint22Packed ThreeBoundMinmaxNumeric.Endpoint22
theorem cache1100_valid_block002 : cache1100Block002.check 3 values1100=true := by decide +kernel
end ThreeBoundEndpoint22VariableCache


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22VariableCache
open ThreeBoundEndpoint22Packed ThreeBoundMinmaxNumeric.Endpoint22
theorem cache1100_valid_block003 : cache1100Block003.check 3 values1100=true := by decide +kernel
end ThreeBoundEndpoint22VariableCache


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22VariableCache
open ThreeBoundEndpoint22Packed ThreeBoundMinmaxNumeric.Endpoint22
theorem cache1100_valid_block004 : cache1100Block004.check 3 values1100=true := by decide +kernel
end ThreeBoundEndpoint22VariableCache


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22VariableCache
open ThreeBoundEndpoint22Packed ThreeBoundMinmaxNumeric.Endpoint22
theorem cache1100_valid_block005 : cache1100Block005.check 3 values1100=true := by decide +kernel
end ThreeBoundEndpoint22VariableCache


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22VariableCache
open ThreeBoundEndpoint22Packed ThreeBoundMinmaxNumeric.Endpoint22
theorem cache1100_valid_block006 : cache1100Block006.check 3 values1100=true := by decide +kernel
end ThreeBoundEndpoint22VariableCache


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22VariableCache
open ThreeBoundEndpoint22Packed ThreeBoundMinmaxNumeric.Endpoint22
theorem cache1100_valid_block007 : cache1100Block007.check 3 values1100=true := by decide +kernel
end ThreeBoundEndpoint22VariableCache


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22VariableCache
open ThreeBoundEndpoint22Packed ThreeBoundMinmaxNumeric.Endpoint22
theorem cache1100_valid_block008 : cache1100Block008.check 3 values1100=true := by decide +kernel
end ThreeBoundEndpoint22VariableCache


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22VariableCache
open ThreeBoundEndpoint22Packed ThreeBoundMinmaxNumeric.Endpoint22
theorem cache1100_valid_block009 : cache1100Block009.check 3 values1100=true := by decide +kernel
end ThreeBoundEndpoint22VariableCache


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22VariableCache
open ThreeBoundEndpoint22Packed ThreeBoundMinmaxNumeric.Endpoint22
theorem cache1100_valid_block010 : cache1100Block010.check 3 values1100=true := by decide +kernel
end ThreeBoundEndpoint22VariableCache


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22VariableCache
open ThreeBoundEndpoint22Packed ThreeBoundMinmaxNumeric.Endpoint22
theorem cache1100_valid_block011 : cache1100Block011.check 3 values1100=true := by decide +kernel
end ThreeBoundEndpoint22VariableCache


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22VariableCache
open ThreeBoundEndpoint22Packed ThreeBoundMinmaxNumeric.Endpoint22
theorem cache1100_valid_block012 : cache1100Block012.check 3 values1100=true := by decide +kernel
end ThreeBoundEndpoint22VariableCache


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22VariableCache
open ThreeBoundEndpoint22Packed ThreeBoundMinmaxNumeric.Endpoint22
theorem cache1100_valid_block013 : cache1100Block013.check 3 values1100=true := by decide +kernel
end ThreeBoundEndpoint22VariableCache


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22VariableCache
open ThreeBoundEndpoint22Packed ThreeBoundMinmaxNumeric.Endpoint22
theorem cache1100_valid_block014 : cache1100Block014.check 3 values1100=true := by decide +kernel
end ThreeBoundEndpoint22VariableCache


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22VariableCache
open ThreeBoundEndpoint22Packed ThreeBoundMinmaxNumeric.Endpoint22
theorem cache1100_valid_block015 : cache1100Block015.check 3 values1100=true := by decide +kernel
end ThreeBoundEndpoint22VariableCache


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22VariableCache
open ThreeBoundEndpoint22Packed ThreeBoundMinmaxNumeric.Endpoint22
theorem cache1100_valid_block016 : cache1100Block016.check 3 values1100=true := by decide +kernel
end ThreeBoundEndpoint22VariableCache


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22VariableCache
open ThreeBoundEndpoint22Packed ThreeBoundMinmaxNumeric.Endpoint22
theorem cache1100_valid_block017 : cache1100Block017.check 3 values1100=true := by decide +kernel
end ThreeBoundEndpoint22VariableCache


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22VariableCache
open ThreeBoundEndpoint22Packed ThreeBoundMinmaxNumeric.Endpoint22
theorem cache1100_valid_block018 : cache1100Block018.check 3 values1100=true := by decide +kernel
end ThreeBoundEndpoint22VariableCache


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22VariableCache
open ThreeBoundEndpoint22Packed ThreeBoundMinmaxNumeric.Endpoint22
theorem cache1100_valid_block019 : cache1100Block019.check 3 values1100=true := by decide +kernel
end ThreeBoundEndpoint22VariableCache


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22VariableCache
open ThreeBoundEndpoint22Packed ThreeBoundMinmaxNumeric.Endpoint22
theorem cache1100_valid_block020 : cache1100Block020.check 3 values1100=true := by decide +kernel
end ThreeBoundEndpoint22VariableCache


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22VariableCache
open ThreeBoundEndpoint22Packed ThreeBoundMinmaxNumeric.Endpoint22
theorem cache1100_valid_block021 : cache1100Block021.check 3 values1100=true := by decide +kernel
end ThreeBoundEndpoint22VariableCache


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22VariableCache
open ThreeBoundEndpoint22Packed ThreeBoundMinmaxNumeric.Endpoint22
theorem cache1100_valid : cache1100.check 3 values1100=true := by
  unfold cache1100
  apply VariableCache.check_branch
  ·
    apply VariableCache.check_branch
    ·
      apply VariableCache.check_branch
      ·
        apply VariableCache.check_branch
        ·
          exact cache1100_valid_block000
        ·
          exact cache1100_valid_block001
      ·
        apply VariableCache.check_branch
        ·
          exact cache1100_valid_block002
        ·
          apply VariableCache.check_branch
          ·
            exact cache1100_valid_block003
          ·
            exact cache1100_valid_block004
    ·
      apply VariableCache.check_branch
      ·
        apply VariableCache.check_branch
        ·
          exact cache1100_valid_block005
        ·
          apply VariableCache.check_branch
          ·
            exact cache1100_valid_block006
          ·
            exact cache1100_valid_block007
      ·
        apply VariableCache.check_branch
        ·
          exact cache1100_valid_block008
        ·
          apply VariableCache.check_branch
          ·
            exact cache1100_valid_block009
          ·
            exact cache1100_valid_block010
  ·
    apply VariableCache.check_branch
    ·
      apply VariableCache.check_branch
      ·
        apply VariableCache.check_branch
        ·
          exact cache1100_valid_block011
        ·
          exact cache1100_valid_block012
      ·
        apply VariableCache.check_branch
        ·
          exact cache1100_valid_block013
        ·
          apply VariableCache.check_branch
          ·
            exact cache1100_valid_block014
          ·
            exact cache1100_valid_block015
    ·
      apply VariableCache.check_branch
      ·
        apply VariableCache.check_branch
        ·
          exact cache1100_valid_block016
        ·
          apply VariableCache.check_branch
          ·
            exact cache1100_valid_block017
          ·
            exact cache1100_valid_block018
      ·
        apply VariableCache.check_branch
        ·
          exact cache1100_valid_block019
        ·
          apply VariableCache.check_branch
          ·
            exact cache1100_valid_block020
          ·
            exact cache1100_valid_block021
end ThreeBoundEndpoint22VariableCache


end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
@Eq.{1} Bool
  (Sensitivity213981Formal.ThreeBoundEndpoint22Packed.VariableCache.check
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    Sensitivity213981Formal.ThreeBoundMinmaxNumeric.Endpoint22.values1100
    Sensitivity213981Formal.ThreeBoundEndpoint22VariableCache.cache1100)
  Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22VariableCache.cache1100_valid
