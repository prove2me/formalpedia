-- Prove2me | solution 1 for QuantumMaxCutEnergy.agm_classical_sdp_certificate_tm2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-04T19:14:02.425571+00:00
-- url     : https://prove2.me/submissions/c1e4da24-f8cf-4b1e-bbcf-170970515083
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Theorems.Thm_QuantumMaxCutEnergy_agm_sdp_certificate_solver_poly
import Mathlib
open scoped BigOperators

namespace QMCSDPSplit

open QuantumMaxCutEnergy QMCNumericRuntime OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic OAI.MetricKMedian.Binary.Automatic.Poly
open Matrix ModernConvex.Relaxations

/-- Entry `(i,j)` of a rational matrix stored as a list of rows (zero when absent). -/
def xget (Xl : List (List ℚ)) (i j : ℕ) : ℚ := (Xl[i]?.getD [])[j]?.getD 0

/-- The SDP objective evaluated edge by edge: `Σ_{i<j} w_ij (2 - X_ij - X_ji) / 4`. -/
def objEdges (p : List NumericEdge × List (List ℚ)) : ℚ :=
  (p.1.map (fun e => e.2 * (2 - xget p.2 e.1.1 e.1.2 - xget p.2 e.1.2 e.1.1) / 4)).sum

theorem objEdges_poly : Poly objEdges := by
  unfold objEdges xget
  fun_prop

end QMCSDPSplit

namespace QMCSDPSplit

open QuantumMaxCutEnergy QMCNumericRuntime OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic OAI.MetricKMedian.Binary.Automatic.Poly
open Matrix ModernConvex.Relaxations

/-- The symmetric weight matrix of `G`. -/
def wmat (G : Input) : Matrix (Fin G.n) (Fin G.n) ℝ :=
  Matrix.of fun i j : Fin G.n =>
    if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
    else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0

/-- The real matrix read from a list of rational rows. -/
def xmat (n : ℕ) (Xl : List (List ℚ)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j : Fin n => ((xget Xl i.val j.val : ℚ) : ℝ)

lemma sum_graphEdgeList {n : ℕ} (g : Edge n → ℝ) :
    ((graphEdgeList n).map g).sum =
      ∑ i : Fin n, ∑ j : Fin n, if h : i < j then g ⟨(i, j), h⟩ else 0 := by
  unfold graphEdgeList
  simp only [List.map_flatMap, sum_flatMap, Fin.sum_univ_def]
  congr 1
  apply List.map_congr_left
  intro i _
  congr 1
  apply List.map_congr_left
  intro j _
  split_ifs <;> simp

lemma objEdges_eq (G : Input) (Xl : List (List ℚ)) :
    ((objEdges (inputEdges G, Xl) : ℚ) : ℝ) =
      maxcutRelaxationObjective (wmat G) (xmat G.n Xl) := by
  have h1 : ((objEdges (inputEdges G, Xl) : ℚ) : ℝ) =
      ((graphEdgeList G.n).map (fun e : Edge G.n =>
        (G.weights e : ℝ) * (2 - xmat G.n Xl e.1.1 e.1.2 - xmat G.n Xl e.1.2 e.1.1) / 4)).sum := by
    simp [objEdges, inputEdges, List.map_map, Rat.cast_list_sum, Function.comp_def, xmat]
  rw [h1, sum_graphEdgeList]
  unfold maxcutRelaxationObjective
  have hsplit : ∀ i j : Fin G.n, wmat G i j * (1 - xmat G.n Xl i j) =
      (if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ) * (1 - xmat G.n Xl i j) else 0) +
      (if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) * (1 - xmat G.n Xl i j) else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [wmat, h, not_lt_of_gt h]
    · subst h; simp [wmat]
    · simp [wmat, h, not_lt_of_gt h]
  simp only [hsplit, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => if h : j < i then
      (G.weights ⟨(j, i), h⟩ : ℝ) * (1 - xmat G.n Xl i j) else 0)]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- Off-diagonal entries of a unit-diagonal PSD matrix are at most `1`. -/
lemma entry_le_one {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} (hX : IsUnitDiagPSD X)
    (i j : Fin n) : X i j ≤ 1 := by
  by_cases hij : i = j
  · subst hij; simp [hX.2]
  have hsym : X j i = X i j := by simpa using hX.1.1.apply i j
  have h := hX.1.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
  simp [dotProduct, mulVec, Pi.single_apply, sub_mul, mul_sub, Finset.sum_sub_distrib,
    hX.2, hsym, Finset.sum_ite_eq'] at h
  linarith

lemma objective_nonneg (G : Input) {X : Matrix (Fin G.n) (Fin G.n) ℝ}
    (hX : IsUnitDiagPSD X) : 0 ≤ maxcutRelaxationObjective (wmat G) X := by
  unfold maxcutRelaxationObjective
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_)
  refine mul_nonneg ?_ (sub_nonneg.2 (entry_le_one hX i j))
  simp only [wmat, Matrix.of_apply]
  split_ifs <;> positivity

end QMCSDPSplit


open QMCSDPSplit in
theorem solution :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input,
        ∃ (X : Matrix (Fin G.n) (Fin G.n) ℚ) (y : Fin G.n → ℚ),
          ModernConvex.Relaxations.IsUnitDiagPSD (X.map (fun q : ℚ => (q : ℝ))) ∧
          (Matrix.diagonal (fun i => (y i : ℝ)) + (1 / 4 : ℝ) •
            (Matrix.of fun i j : Fin G.n =>
              if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
              else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0)).PosSemidef ∧
          (L G : ℝ) = ModernConvex.Relaxations.maxcutRelaxationObjective
            (Matrix.of fun i j : Fin G.n =>
              if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
              else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0)
            (X.map (fun q : ℚ => (q : ℝ))) ∧
          (1 / 4 : ℝ) * (∑ i, ∑ j, (Matrix.of fun i j : Fin G.n =>
              if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
              else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) i j) +
            ∑ i, (y i : ℝ) - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 := by
  classical
  obtain ⟨Solve, hSolve, hspec⟩ := QuantumMaxCutEnergy.agm_sdp_certificate_solver_poly
  let F : List QMCNumericRuntime.NumericEdge → ℚ := fun es => objEdges (es, (Solve es).1)
  have hF : OAI.MetricKMedian.Binary.Automatic.Poly F :=
    OAI.MetricKMedian.Binary.Automatic.Poly.comp objEdges_poly
      (OAI.MetricKMedian.Binary.Automatic.Poly.pair
        OAI.MetricKMedian.Binary.Automatic.Poly.identity
        (OAI.MetricKMedian.Binary.Automatic.Poly.comp
          OAI.MetricKMedian.Binary.Automatic.Poly.fst hSolve))
  have hval : ∀ G : QuantumMaxCutEnergy.Input,
      ((F (QMCNumericRuntime.inputEdges G) : ℚ) : ℝ) =
        ModernConvex.Relaxations.maxcutRelaxationObjective (wmat G)
          (xmat G.n (Solve (QMCNumericRuntime.inputEdges G)).1) :=
    fun G => objEdges_eq G _
  have hnn : ∀ G : QuantumMaxCutEnergy.Input, 0 ≤ F (QMCNumericRuntime.inputEdges G) := by
    intro G
    have h : 0 ≤ ModernConvex.Relaxations.maxcutRelaxationObjective (wmat G)
        (xmat G.n (Solve (QMCNumericRuntime.inputEdges G)).1) := objective_nonneg G (hspec G).1
    rw [← hval G] at h
    exact_mod_cast h
  let L : QuantumMaxCutEnergy.Input → ℚ≥0 := fun G => ⟨F (QMCNumericRuntime.inputEdges G), hnn G⟩
  have hLcast : ∀ G, (L G : ℝ) = ((F (QMCNumericRuntime.inputEdges G) : ℚ) : ℝ) := by
    intro G
    show ((⟨F (QMCNumericRuntime.inputEdges G), hnn G⟩ : ℚ≥0) : ℝ) = _
    norm_cast
  refine ⟨L, ?_, fun G => ?_⟩
  · let P0 := QMCNumericRuntime.requestEdgesProgram.comp hF.program
    let P : OAI.MetricKMedian.Binary.PolyProgram QuantumMaxCutEnergy.encodeRequest
        (fun q : ℚ≥0 => OAI.MetricKMedian.Binary.Ratio.encode (q : ℚ))
        (fun r : QuantumMaxCutEnergy.Input × List Bool => L r.1) :=
      P0.recode id (fun _ => rfl) (fun _ => rfl)
    exact ⟨(P.comp QMCNumericRuntime.nnratOutput).stock⟩
  · refine ⟨Matrix.of fun i j : Fin G.n => xget (Solve (QMCNumericRuntime.inputEdges G)).1 i j,
      fun i => (Solve (QMCNumericRuntime.inputEdges G)).2[i.val]?.getD 0, ?_, ?_, ?_, ?_⟩
    · exact (hspec G).1
    · exact (hspec G).2.1
    · rw [hLcast]; exact hval G
    · have h := (hspec G).2.2
      rw [hLcast, hval G]
      exact h
