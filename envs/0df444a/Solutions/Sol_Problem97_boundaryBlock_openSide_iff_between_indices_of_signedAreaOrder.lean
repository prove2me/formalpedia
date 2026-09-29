-- Prove2me | solution 1 for Problem97.boundaryBlock_openSide_iff_between_indices_of_signedAreaOrder
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T05:55:43.412246+00:00
-- url     : https://prove2.me/submissions/a4f72fa5-2b60-41b3-a3b0-b86f69f6f1b7

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.CGN.CGN4g:55165:58896. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_CGN_CGN
import Definitions.Def_Erdos9796Counting_CGN_CGN4g
import Definitions.Def_Erdos9796Counting_Foundation
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin

section Erdos9796CountingFragment_Erdos9796Proof_P97_CGN_CGN4g

open Problem97

/- Fragment from Erdos9796Proof.P97.CGN.CGN4g; source SHA-256 c412b95ca627805e0db3a1f0d192f80b93891249e4eb1369844d4f8206dcba79 -/


/-!
# CGN4g: ordered-cap block packaging

This file adds the closure-plan data carrier for the ordered-cap block cut out
of a global convex-boundary enumeration, together with the theorem wrappers
that are pure packaging.

The geometric producers for the block (`CGN4g1`, `CGN4g3`, `CGN4g4`) remain
separate. The declarations here are the sanctioned interfaces consumed by the
existing CGN6 / CGN7 layers.
-/

open scoped EuclideanGeometry
open scoped InnerProductSpace












variable {A C : Finset ℝ²}


















































theorem solution
    {A C : Finset ℝ²} {n m : ℕ}
    {phi : Fin n → ℝ²} {L : Problem97.CGN.OrderedCap m}
    (Block : Problem97.CGN.BoundaryCapBlock A C phi L)
    (hneg : ∀ {i j k : Fin n}, i < j → j < k →
      Problem97.signedArea2 (phi i) (phi j) (phi k) < 0)
    (_hno3 : ∀ {x y z : ℝ²}, x ∈ A → y ∈ A → z ∈ A →
      x ≠ y → y ≠ z → x ≠ z →
      Problem97.signedArea2 x y z ≠ 0) :
    ∀ {r s : Fin m}, r < s → ∀ {x : ℝ²}, x ∈ A →
      (0 < Problem97.signedArea2 (L.points r) (L.points s) x ↔
        ∃ j : Fin m, r < j ∧ j < s ∧ L.points j = x) := by
  have hcyc {a b c : ℝ²} :
      Problem97.signedArea2 a b c = Problem97.signedArea2 c a b := by
    simp [Problem97.signedArea2]
    ring
  have hswap {a b c : ℝ²} :
      Problem97.signedArea2 a b c = -Problem97.signedArea2 a c b := by
    simp [Problem97.signedArea2]
  intro r s hrs x hxA
  constructor
  · intro hpos
    have hidxrs : Block.idx r < Block.idx s := Block.idx_strict hrs
    have hxphi : x ∈ Finset.univ.image phi := by
      rw [Block.phi_image]
      exact hxA
    rcases Finset.mem_image.mp hxphi with ⟨q, -, hqeq⟩
    have hpos' : 0 < Problem97.signedArea2 (phi (Block.idx r)) (phi (Block.idx s)) (phi q) := by
      simpa [Block.points_eq, hqeq] using hpos
    rcases lt_trichotomy q (Block.idx r) with hq_lt_r | hq_eq_r | hq_gt_r
    · have hneg' : Problem97.signedArea2 (phi q) (phi (Block.idx r)) (phi (Block.idx s)) < 0 :=
        hneg hq_lt_r hidxrs
      rw [← hcyc] at hneg'
      linarith
    · subst hq_eq_r
      simp [Problem97.signedArea2] at hpos'
    · rcases lt_trichotomy q (Block.idx s) with hq_lt_s | hq_eq_s | hq_gt_s
      · have hq_bounds : Block.lo ≤ q ∧ q ≤ Block.hi := by
          constructor
          · have hlo : Block.lo ≤ Block.idx r := by
              exact ((Block.idx_range_exact (Block.idx r)).2 ⟨r, rfl⟩).1
            exact le_trans hlo hq_gt_r.le
          · have hhi : Block.idx s ≤ Block.hi := by
              exact ((Block.idx_range_exact (Block.idx s)).2 ⟨s, rfl⟩).2
            exact le_trans hq_lt_s.le hhi
        rcases (Block.idx_range_exact q).1 hq_bounds with ⟨j, hjq⟩
        refine ⟨j, ?_, ?_, ?_⟩
        · by_contra hnot
          have hle : j ≤ r := le_of_not_gt hnot
          have : Block.idx j ≤ Block.idx r := Block.idx_strict.monotone hle
          rw [hjq] at this
          exact not_le_of_gt hq_gt_r this
        · by_contra hnot
          have hle : s ≤ j := le_of_not_gt hnot
          have : Block.idx s ≤ Block.idx j := Block.idx_strict.monotone hle
          rw [hjq] at this
          exact not_le_of_gt hq_lt_s this
        · rw [Block.points_eq, hjq, hqeq]
      · subst hq_eq_s
        simp [Problem97.signedArea2] at hpos'
      · have hneg' : Problem97.signedArea2 (phi (Block.idx r)) (phi (Block.idx s)) (phi q) < 0 :=
          hneg hidxrs hq_gt_s
        linarith
  · rintro ⟨j, hrj, hjs, rfl⟩
    have hidxrj : Block.idx r < Block.idx j := Block.idx_strict hrj
    have hidxjs : Block.idx j < Block.idx s := Block.idx_strict hjs
    have hneg' :
        Problem97.signedArea2 (phi (Block.idx r)) (phi (Block.idx j)) (phi (Block.idx s)) < 0 :=
      hneg hidxrj hidxjs
    have hpos' :
        0 < Problem97.signedArea2 (phi (Block.idx r)) (phi (Block.idx s)) (phi (Block.idx j)) := by
      rw [hswap]
      linarith
    simpa [Block.points_eq] using hpos'

end Erdos9796CountingFragment_Erdos9796Proof_P97_CGN_CGN4g
