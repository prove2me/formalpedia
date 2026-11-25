-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BlockTrdeg_exists_nat_mul_mem_range_0c268acf36e9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:36:37.35925+00:00
-- url     : https://prove2.me/submissions/0636fdbe-9de9-4ef2-8f90-b4ac6e5c358a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsBlockTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PBlockTrdeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 Algebra Cardinal
open GroundTheory.Heights₂.Heights.BlockTrdeg
attribute [local instance] MvPolynomial.weightedGradedAlgebra
open scoped Classical
variable {σ : Type} {L : Type} [Field L] [Algebra ℚ L]
namespace GroundTheory.Heights₂.Heights.BlockTrdeg
theorem _root_.solution (ψ : MvPolynomial σ ℤ →+* L) {y : L}
    (hy : y ∈ adjoin ℚ (Set.range fun p ↦ ψ (X p))) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : L) * y ∈ ψ.range := by
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact ⟨1, one_ne_zero, ⟨X p, by rw [Nat.cast_one, one_mul]⟩⟩
  | algebraMap q =>
    refine ⟨q.den, q.den_nz, ⟨(q.num : MvPolynomial σ ℤ), ?_⟩⟩
    rw [map_intCast, ← map_natCast (algebraMap ℚ L), ← map_mul, Rat.den_mul_eq_num, map_intCast]
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    have e : ((n * m : ℕ) : L) * (x + y) = m * (n * x) + n * (m * y) := by push_cast; ring
    rw [e]
    exact add_mem (mul_mem (natCast_mem _ _) hnx) (mul_mem (natCast_mem _ _) hmy)
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    have e : ((n * m : ℕ) : L) * (x * y) = (n * x) * (m * y) := by push_cast; ring
    rw [e]
    exact mul_mem hnx hmy
end GroundTheory.Heights₂.Heights.BlockTrdeg
