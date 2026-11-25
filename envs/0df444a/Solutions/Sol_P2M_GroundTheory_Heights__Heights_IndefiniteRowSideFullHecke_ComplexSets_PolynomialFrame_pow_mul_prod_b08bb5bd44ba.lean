-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialFrame_pow_mul_prod_b08bb5bd44ba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:56:17.608643+00:00
-- url     : https://prove2.me/submissions/27f13003-a6e2-471c-83d6-a3ad39acdfd3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PolynomialFrame

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolynomialFrame
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolynomialFrame
theorem _root_.solution {k : ℕ} {s : ℂ} (hs : s ≠ 0) (a b : Fin k → ℂ) (m : Fin k →₀ ℕ) {d : ℕ}
    (hm : m.degree ≤ d) :
    s ^ d * ∏ i ∈ m.support, (a i + s⁻¹ * b i) ^ m i =
      s ^ (d - m.degree) * ∏ i ∈ m.support, (s * a i + b i) ^ m i := by
  calc s ^ d * ∏ i ∈ m.support, (a i + s⁻¹ * b i) ^ m i
      = s ^ (d - m.degree) * (s ^ m.degree * ∏ i ∈ m.support, (a i + s⁻¹ * b i) ^ m i) := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hm]
    _ = s ^ (d - m.degree) * ∏ i ∈ m.support, (s * a i + b i) ^ m i := by
        congr 1
        rw [Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← mul_pow]
        congr 1
        field_simp
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolynomialFrame
