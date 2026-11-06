-- Prove2me | solution 1 for QEC.Locality.daiLiCorrectedCComponentEstimate_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:21:20.207697+00:00
-- url     : https://prove2.me/submissions/85850914-c1ef-4a1d-9f64-bf73d6b050b4

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Theorems.Thm_QEC_Locality_daiLiCorrectedFamilyCount_badRectangleVertexTerm_le

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ]
namespace QEC.Locality
theorem _root_.solution
    (M totalF d k n : Nat) (ell w badQubits badRectangleVertexQubits
      gridVertexQubits : ℝ)
    (hD : 0 < d) (hK : 0 < k)
    (hCount : M * d ≤ 30 * totalF) (hTotal : 50 * totalF ≤ k)
    (hBadQubits : badQubits ≤ (k : ℝ) / 50)
    (hBadRectangleVertices :
      badRectangleVertexQubits ≤ 384 * ell ^ 2 * (M : ℝ))
    (hGridVertices :
      gridVertexQubits ≤ 16 * ell ^ 2 * (n : ℝ) / w ^ 2)
    (hBadRectangleScale :
      400 * ell ^ 2 * (k : ℝ) / (d : ℝ) ≤ (k : ℝ) / 25)
    (hGridScale : 16 * ell ^ 2 * (n : ℝ) / w ^ 2 ≤ (k : ℝ) / 100) :
    badQubits + badRectangleVertexQubits + gridVertexQubits < (k : ℝ) := by
  have hRectangleTerm := daiLiCorrectedFamilyCount_badRectangleVertexTerm_le
    M totalF d k ell hD hCount hTotal
  have hKReal : (0 : ℝ) < k := by exact_mod_cast hK
  have hBadRectangleFinal : badRectangleVertexQubits ≤ (k : ℝ) / 25 :=
    hBadRectangleVertices.trans (hRectangleTerm.trans hBadRectangleScale)
  have hGridFinal : gridVertexQubits ≤ (k : ℝ) / 100 :=
    hGridVertices.trans hGridScale
  calc
    badQubits + badRectangleVertexQubits + gridVertexQubits ≤
        (k : ℝ) / 50 + (k : ℝ) / 25 + (k : ℝ) / 100 := by
      linarith
    _ < (k : ℝ) := by linarith
end QEC.Locality
