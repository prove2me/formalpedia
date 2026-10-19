-- Prove2me | solution 1 for PermanentFormulaLowerBound.cyclicMatchingBlock_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/18a73c0f-241c-4071-98ca-5908726a7f4d

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution {n k : ℕ}
    (hk : 0 < k) (x y : Fin n × Fin (n / k)) (hxy : x ≠ y) :
    Disjoint (cyclicMatchingBlock hk x.1 x.2)
      (cyclicMatchingBlock hk y.1 y.2) := by
  classical
  letI : NeZero n :=
    ⟨Nat.ne_of_gt ((Nat.zero_le (x.1 : ℕ)).trans_lt x.1.isLt)⟩
  apply Finset.disjoint_left.mpr
  intro z hx hy
  obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hx
  obtain ⟨r', _, hr'⟩ := Finset.mem_image.mp hy
  have hpair :
      (matchingBlockRow hk x.2 r,
        matchingBlockRow hk x.2 r + x.1) =
        (matchingBlockRow hk y.2 r',
          matchingBlockRow hk y.2 r' + y.1) :=
    hr.trans hr'.symm
  have hrow : matchingBlockRow hk x.2 r =
      matchingBlockRow hk y.2 r' := congrArg Prod.fst hpair
  have hcol :
      matchingBlockRow hk x.2 r + x.1 =
        matchingBlockRow hk y.2 r' + y.1 :=
    congrArg Prod.snd hpair
  have hoffset : x.1 = y.1 := by
    apply add_left_cancel (a := matchingBlockRow hk x.2 r)
    simpa [hrow] using hcol
  have hblock : x.2 = y.2 :=
    congrArg Prod.fst
      (matchingBlockRow_injective hk
        (a₁ := (x.2, r)) (a₂ := (y.2, r')) hrow)
  exact hxy (Prod.ext hoffset hblock)
end PermanentFormulaLowerBound
