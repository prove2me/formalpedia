-- Prove2me | solution 1 for Problem97.hneg_cyclicShift
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:05:57.501625+00:00
-- url     : https://prove2.me/submissions/16e6dd99-6ffa-4d2d-9e7a-d658c3c9cdab

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.ConvexCyclicOrder.Basic:4916:8139. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation

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
    (hneg : ∀ {i j k : Fin n}, i < j → j < k →
      signedArea2 (φ i) (φ j) (φ k) < 0)
    (cut : Fin n) :
    ∀ {i j k : Fin n}, i < j → j < k →
      signedArea2 (φ (i + cut)) (φ (j + cut)) (φ (k + cut)) < 0 := by
  have hcyc {a b c : ℝ²} : signedArea2 a b c = signedArea2 c a b := by
    simp [signedArea2]
    ring
  let bound : ℕ := n - cut.val
  have hval_nowrap {t : Fin n} (ht : (t : ℕ) < bound) :
      ((t + cut : Fin n) : ℕ) = t.val + cut.val := by
    rw [Fin.val_add_eq_ite]
    have hlt : ¬ n ≤ t.val + cut.val := by omega
    simp [hlt]
  have hval_wrap {t : Fin n} (ht : bound ≤ (t : ℕ)) :
      ((t + cut : Fin n) : ℕ) = t.val - bound := by
    rw [Fin.val_add_eq_ite]
    have hge : n ≤ t.val + cut.val := by omega
    simp [hge]
    omega
  intro i j k hij hjk
  by_cases hk : (k : ℕ) < bound
  · have hi : (i : ℕ) < bound := by omega
    have hj : (j : ℕ) < bound := by omega
    have hij' : i + cut < j + cut := by
      change (((i + cut : Fin n) : ℕ) < ((j + cut : Fin n) : ℕ))
      rw [hval_nowrap hi, hval_nowrap hj]
      omega
    have hjk' : j + cut < k + cut := by
      change (((j + cut : Fin n) : ℕ) < ((k + cut : Fin n) : ℕ))
      rw [hval_nowrap hj, hval_nowrap hk]
      omega
    exact hneg hij' hjk'
  · by_cases hj : (j : ℕ) < bound
    · have hi : (i : ℕ) < bound := by omega
      have hk' : bound ≤ (k : ℕ) := by omega
      have hki : k + cut < i + cut := by
        change (((k + cut : Fin n) : ℕ) < ((i + cut : Fin n) : ℕ))
        rw [hval_wrap hk', hval_nowrap hi]
        omega
      have hij' : i + cut < j + cut := by
        change (((i + cut : Fin n) : ℕ) < ((j + cut : Fin n) : ℕ))
        rw [hval_nowrap hi, hval_nowrap hj]
        omega
      have hneg' :
          signedArea2 (φ (k + cut)) (φ (i + cut)) (φ (j + cut)) < 0 :=
        hneg hki hij'
      simpa [hcyc] using hneg'
    · by_cases hi : (i : ℕ) < bound
      · have hj' : bound ≤ (j : ℕ) := by omega
        have hk' : bound ≤ (k : ℕ) := by omega
        have hjk'' : j + cut < k + cut := by
          change (((j + cut : Fin n) : ℕ) < ((k + cut : Fin n) : ℕ))
          rw [hval_wrap hj', hval_wrap hk']
          omega
        have hki : k + cut < i + cut := by
          change (((k + cut : Fin n) : ℕ) < ((i + cut : Fin n) : ℕ))
          rw [hval_wrap hk', hval_nowrap hi]
          omega
        have hneg' :
            signedArea2 (φ (j + cut)) (φ (k + cut)) (φ (i + cut)) < 0 :=
          hneg hjk'' hki
        simpa [hcyc] using hneg'
      · have hi' : bound ≤ (i : ℕ) := by omega
        have hj' : bound ≤ (j : ℕ) := by omega
        have hk' : bound ≤ (k : ℕ) := by omega
        have hij' : i + cut < j + cut := by
          change (((i + cut : Fin n) : ℕ) < ((j + cut : Fin n) : ℕ))
          rw [hval_wrap hi', hval_wrap hj']
          omega
        have hjk' : j + cut < k + cut := by
          change (((j + cut : Fin n) : ℕ) < ((k + cut : Fin n) : ℕ))
          rw [hval_wrap hj', hval_wrap hk']
          omega
        exact hneg hij' hjk'









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
