-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allRank_fin_last_mem_span_of_weaklyRegular_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/6af00a7f-cb34-435d-94e7-409c61d25f0d

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped nonZeroDivisors Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
open scoped Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {R : Type*} [CommRing R] {n : ℕ}
    (f : Fin (n + 1) → R)
    (hregular : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn f))
    {a : R}
    (ha : f (Fin.last n) * a ∈
      Ideal.span (Set.range fun i : Fin n => f i.castSucc)) :
    a ∈ Ideal.span (Set.range fun i : Fin n => f i.castSucc) := by
  let rs : List R := List.ofFn fun i : Fin n => f i.castSucc
  have hlist : List.ofFn f = rs ++ [f (Fin.last n)] :=
    List.ofFn_succ_last
  have hregular' :
      RingTheory.Sequence.IsWeaklyRegular R
        (rs ++ [f (Fin.last n)]) := hlist ▸ hregular
  have hlast :=
    (RingTheory.Sequence.isWeaklyRegular_append_iff
      R rs [f (Fin.last n)]).mp hregular'
  have hlast' :
      IsSMulRegular
        (R ⧸ (Ideal.ofList rs • (⊤ : Submodule R R)))
        (f (Fin.last n)) :=
    (RingTheory.Sequence.isWeaklyRegular_singleton_iff
      (R ⧸ (Ideal.ofList rs • (⊤ : Submodule R R)))
      (f (Fin.last n))).mp hlast.2
  have hspan :
      Ideal.ofList rs =
        Ideal.span (Set.range fun i : Fin n => f i.castSucc) := by
    change Ideal.span {x : R | x ∈ List.ofFn
      (fun i : Fin n => f i.castSucc)} = _
    congr 1
    ext x
    simp
  have hideal :
      Ideal.ofList rs • (⊤ : Submodule R R) =
        (Ideal.span (Set.range fun i : Fin n => f i.castSucc) :
          Submodule R R) := by
    simp [hspan]
  have hmem :=
    (isSMulRegular_quotient_iff_mem_of_smul_mem
      (Ideal.ofList rs • (⊤ : Submodule R R))
      (f (Fin.last n))).mp hlast'
  change a ∈
    (Ideal.span (Set.range fun i : Fin n => f i.castSucc) :
      Submodule R R)
  rw [← hideal]
  apply hmem a
  rw [hideal]
  simpa [smul_eq_mul] using ha
end PermanentRollout
