-- Prove2me | solution 1 for OneEdge.not_swapMat
-- status  : ACCEPTED   (prove)
-- author  : @darkhipo
-- created : 2026-10-29T16:22:02.770268+00:00
-- url     : https://prove2.me/submissions/caee6e12-c5bb-4fd1-b317-8a31d8df0417

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-!
# Fixed-point obstruction for a one-run edge, at arbitrary width

Waypoint for R2125607035 (2026-10-29): this file isolates the structural
obstruction from the R8 reconstruction work without importing any histogram or
`native_decide` census certificate.  A one-run edge of width `w < m` fixes the
top coordinate `w`, while the full chunk interchange has a zero diagonal there.
The parameter `529` in the original repaired-net lemma was incidental.
-/

namespace IntMul.Kappa.R6.Bit.OneEdgeObstruction

open IntMul.Kappa AModel AModelFac Matrix

/-- One contiguous reversed-bank run of width `w` on an `m`-wire chunk. -/
def singleRun (m w : ℕ) : ℕ × ℕ × ℕ := (0, m - w, w)

/-- An edge carrying exactly one reversed-bank run. -/
def singleEdge (m w : ℕ) : Edge m := ⟨1, [singleRun m w], 1⟩

theorem redQ_zero (M : ℕ) : AModelFac.redQ M 0 = 0 := by
  have hd : Nat.Coprime ((0 : ℚ).den) M := by
    rw [Rat.den_zero]
    exact Nat.coprime_one_left M
  unfold AModelFac.redQ AModelFac.toGood
  rw [dif_pos hd]
  show AModelFac.redHom M (⟨(0 : ℚ), hd⟩ : AModelFac.goodSub M) = 0
  exact (AModelFac.redHom M).map_zero

theorem redQ_one (M : ℕ) : AModelFac.redQ M 1 = 1 := by
  have hd : Nat.Coprime ((1 : ℚ).den) M := by
    rw [Rat.den_one]
    exact Nat.coprime_one_left M
  unfold AModelFac.redQ AModelFac.toGood
  rw [dif_pos hd]
  show AModelFac.redHom M (⟨(1 : ℚ), hd⟩ : AModelFac.goodSub M) = 1
  exact (AModelFac.redHom M).map_one

theorem redM_one (M m : ℕ) : redM M (1 : QMat2 m) = 1 := by
  ext i j
  simp only [redM, Matrix.map_apply]
  by_cases h : i = j
  · subst h
    simp [Matrix.one_apply_eq, redQ_one]
  · simp [Matrix.one_apply_ne h, redQ_zero]

theorem singleEdge_edgeMat (M m w : ℕ) :
    edgeMat M (singleEdge m w) =
      (((singleEdge m w).runs.flatMap (runPiv m)).map fun p => Equiv.swap p.1 p.2).prod.permMatrix
        (ZMod M) := by
  unfold edgeMat
  rw [show (singleEdge m w).E₁ = 1 from rfl, show (singleEdge m w).E₂ = 1 from rfl,
    redM_one, one_mul, mul_one]

theorem swapMat_castAdd_diag (M m w : ℕ) (hw : w < m) :
    (AModel.swapMat (Q := M) (Fin.castAdd m ⟨w, hw⟩) (Fin.castAdd m ⟨w, hw⟩)) = 0 := by
  simp only [AModel.swapMat, AModel.blk, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₁₁]
  rfl

theorem permMatrix_diag_of_fix {M m : ℕ} {σ : Equiv.Perm (Fin (m + m))}
    {x : Fin (m + m)} (h : σ x = x) : σ.permMatrix (ZMod M) x x = 1 := by
  have hmem : x ∈ Equiv.toPEquiv σ x := by
    rw [Equiv.toPEquiv_apply]
    simpa using h
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, if_pos hmem]

theorem prod_swaps_fix {m : ℕ} (x : Fin (m + m))
    (ps : List (Fin (m + m) × Fin (m + m)))
    (h : ∀ p ∈ ps, Equiv.swap p.1 p.2 x = x) :
    (ps.map fun p => Equiv.swap p.1 p.2).prod x = x := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      simp only [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply]
      rw [ih (fun q hq => h q (by simp [hq]))]
      exact h p (by simp)

theorem singleRun_pivots_fix {m w : ℕ} (hw : w < m) :
    ∀ p ∈ runPiv m (singleRun m w),
      Equiv.swap p.1 p.2 (Fin.castAdd m ⟨w, hw⟩) = Fin.castAdd m ⟨w, hw⟩ := by
  intro p hp
  obtain ⟨k, hk, hpk⟩ := List.mem_filterMap.1 hp
  simp only [singleRun] at hk
  by_cases hb : (singleRun m w).1 + k < m ∧ (singleRun m w).2.1 + k < m
  · rw [dif_pos hb] at hpk
    cases hpk
    apply Equiv.swap_apply_of_ne_of_ne
    · intro heq
      have hv : w = 0 + k := congrArg Fin.val heq
      have hk' := List.mem_range.1 hk
      omega
    · intro heq
      have hv : w = m + (m - w + k) := congrArg Fin.val heq
      omega
  · rw [dif_neg hb] at hpk
    contradiction

theorem singleEdge_prod_fix {m w : ℕ} (hw : w < m) :
    (((singleEdge m w).runs.flatMap (runPiv m)).map fun p => Equiv.swap p.1 p.2).prod
      (Fin.castAdd m ⟨w, hw⟩) = Fin.castAdd m ⟨w, hw⟩ := by
  apply prod_swaps_fix
  intro p hp
  apply singleRun_pivots_fix hw p
  simpa [singleEdge] using hp

/-- A one-run edge of width below `m` is never the full `m`-chunk interchange. -/
theorem singleEdge_ne_swapMat (m M w : ℕ) (hM : 1 < M) (hw : w < m) :
    edgeMat M (singleEdge m w) ≠ AModel.swapMat := by
  letI : Fact (1 < M) := ⟨hM⟩
  intro h
  rw [singleEdge_edgeMat] at h
  have he := congrArg (fun A : FMat m M =>
    A (Fin.castAdd m ⟨w, hw⟩) (Fin.castAdd m ⟨w, hw⟩)) h
  rw [permMatrix_diag_of_fix (singleEdge_prod_fix hw), swapMat_castAdd_diag] at he
  exact one_ne_zero he

/-- The original R8 statement is the `m = 529` instance. -/
theorem singleEdge529_ne_swapMat (M w : ℕ) (hM : 1 < M) (hw : w < 529) :
    edgeMat M (singleEdge 529 w) ≠ AModel.swapMat :=
  singleEdge_ne_swapMat 529 M w hM hw

end IntMul.Kappa.R6.Bit.OneEdgeObstruction

open IntMul.Kappa IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.OneEdgeObstruction

/-- Platform submission shape: the target uses the edge literal directly. -/
theorem solution (m M w : ℕ) (hM : 1 < M) (hw : w < m) :
    edgeMat M (⟨1, [(0, m - w, w)], 1⟩ : Edge m) ≠ AModel.swapMat := by
  exact singleEdge_ne_swapMat m M w hM hw
