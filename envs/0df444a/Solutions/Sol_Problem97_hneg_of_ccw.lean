-- Prove2me | solution 1 for Problem97.hneg_of_ccw
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:06:35.202975+00:00
-- url     : https://prove2.me/submissions/4b116d48-0d78-4481-8175-540d1db298bb

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.ConvexCyclicOrder.Basic:3093:3987. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_SignedAreaOangle
import Theorems.Thm_Problem97_signedArea2_sign_eq_oangle_sign

section Erdos9796CountingFragment_Erdos9796Proof_P97_ConvexCyclicOrder_Basic

open Problem97

/- Fragment from Erdos9796Proof.P97.ConvexCyclicOrder.Basic; source SHA-256 f1ec282e547e3f3ca8edca05b96111ec2591b61f6aeecd11c668396d093955a1 -/



/-!
# Convex cyclic order wrapper around `IsCcwConvexPolygon`

This module supplies a thin wrapper around the upstream predicate
`EuclideanGeometry.IsCcwConvexPolygon` (from
`FormalConjecturesForMathlib.Geometry.2d`) suited to the Nivasch–Pach–Pinchasi–Zerbib 2013
Lemma 6 sign-stability arguments consumed downstream by the CGN counting
bridge.

The key downstream consumer needs the statement "four points
`p, q, r, s` appear in this cyclic order on the convex-hull boundary
of `A`" plus an immediate algebraic API:

* `Problem97.ConvexCyclicOrder A p q r s` — the wrapper predicate.
* `oangle_sign_{pqr,qrs,pqs,prs}` — direct sign extraction for the
  four oriented angles whose central vertex is in the interior of
  the index sequence (immediate from `IsCcwConvexPolygon.sign_oangle`).
* `signedArea2_sign_stable_{pq, qr_chord}` — sign-stability of the
  `signedArea2` predicate as the third/first point varies along the
  cyclic order. Bridges via `signedArea2_sign_eq_oangle_sign` in
  `SignedAreaOangle`.

All proofs are mechanical composition of `IsCcwConvexPolygon.sign_oangle*`
with `signedArea2_sign_eq_oangle_sign`. No axioms are introduced.

## Step 1 scope

This file is the Step 1 wrapper.  It now includes the generic cyclic-shift
transport for `IsCcwConvexPolygon`, enough to change the linear cut of a
global boundary enumeration.  The higher-level
`ConvexCyclicOrder.rotate`/`ConvexCyclicOrder.reverse` wrapper API is still
deferred to Step 2.  Reversal flips chirality, so a faithful Step-2 reverse
should wrap upstream `IsConvexPolygon` (which already handles both
chiralities) rather than `IsCcwConvexPolygon`.
-/

open scoped EuclideanGeometry








theorem solution {n : ℕ} {φ : Fin n → ℝ²}
    (hinj : Function.Injective φ)
    (hccw : EuclideanGeometry.IsCcwConvexPolygon φ) :
    ∀ {i j k : Fin n}, i < j → j < k →
      signedArea2 (φ i) (φ j) (φ k) < 0 := by
  intro i j k hij hjk
  have hij_ne : φ i ≠ φ j := fun h => (ne_of_lt hij) (hinj h)
  have hkj_ne : φ k ≠ φ j := fun h => (ne_of_gt hjk) (hinj h)
  have hsign : SignType.sign (signedArea2 (φ j) (φ i) (φ k)) = 1 := by
    rw [signedArea2_sign_eq_oangle_sign (φ j) (φ i) (φ k) hij_ne hkj_ne]
    exact hccw.sign_oangle hij hjk
  have hpos : 0 < signedArea2 (φ j) (φ i) (φ k) :=
    sign_eq_one_iff.mp hsign
  have hswap :
      signedArea2 (φ j) (φ i) (φ k) =
        -signedArea2 (φ i) (φ j) (φ k) := by
    simp only [signedArea2]
    ring
  linarith













-- TODO Step 2: ConvexCyclicOrder.rotate — `ConvexCyclicOrder A p q r s
-- → ConvexCyclicOrder A q r s p`. The generic boundary-enumeration cyclic
-- shift above supplies the geometric transport; the remaining work is a
-- wrapper-level theorem that repacks the four witnesses.
--
-- TODO Step 2: ConvexCyclicOrder.reverse — reversing the cyclic order
-- flips CCW → CW. The faithful Step-2 form should be stated over
-- `IsConvexPolygon` (the chirality-agnostic predicate at
-- `FormalConjecturesForMathlib/Geometry/2d.lean`), not the CCW form.

/-! ### Direct oriented-angle sign extraction

For each triple `(x, y, z) ⊆ {p, q, r, s}` whose central vertex `y` is
in the *middle* of the cyclic index sequence, `IsCcwConvexPolygon.sign_oangle`
directly yields `(∡ x y z).sign = 1`. The four such triples are listed
below.
-/









/-! ### `signedArea2` sign-stability

Bridge the oriented-angle extraction above to the algebraic
`signedArea2` predicate via `Problem97.signedArea2_sign_eq_oangle_sign`.
Recall the convention `signedArea2 v vj vk ↔ ∡ vj v vk` (central vertex
is the *first* argument of `signedArea2`).
-/

end Erdos9796CountingFragment_Erdos9796Proof_P97_ConvexCyclicOrder_Basic
