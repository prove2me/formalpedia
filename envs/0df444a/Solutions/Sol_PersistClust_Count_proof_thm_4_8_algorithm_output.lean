-- Prove2me | solution 1 for PersistClust.Count.proof_thm_4_8_algorithm_output
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-09T09:02:44.081231+00:00
-- url     : https://prove2.me/submissions/5baa9aec-5a2c-418a-a4cc-cccee433702b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_Rips
import Definitions.Def_PersistClust_Count_Algorithm
import Definitions.Def_PersistClust_Count_AlgBarcode
import Theorems.Thm_PersistClust_Count_alg_diagram_eq_barcode
import Theorems.Thm_PersistClust_Count_alg_numclust_eq_barcode

open PersistClust.Count
open scoped ENNReal

/-!
Reduction of `proof_thm_4_8_algorithm_output` to two lemmas.

The number of clusters output by Procedure 1 with threshold `τ` (entries whose root
has value `≥ τ`) equals the total multiplicity of points of the 0-th persistence
diagram $D_0\mathcal R_\delta^g(L)$ lying in the region
$\Delta^S_\tau \cap \{b \geq \tau\}$ (death at least `τ` below birth, birth at least `τ`).

The proof is the transitivity of two facts:
1. `alg_numclust_eq_barcode` — the union-find output equals the same region-count of
   the *combinatorial barcode* `ripsBarcode g Dm δ σ`, the elder-rule pairing of the
   upper-star Rips filtration (Procedure 1 run with merge threshold $+\infty$).
2. `alg_diagram_eq_barcode` — the combinatorial barcode coincides pointwise with the
   analytic diagram `ripsDiagram Dm g δ` (defined via `mult` of the rank function).
-/

theorem solution
    (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (hDm0 : ∀ i j, 0 ≤ Dm i j)
    (δ τ : ℝ) (hδ : 0 ≤ δ) (hτ : 0 < τ)
    (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) :
    (numClusters g Dm δ τ σ : ℕ∞)
      = {q : (EReal × EReal) × ℕ | (q.2 : ℕ∞) < ripsDiagram Dm g δ q.1 ∧
          q.1.2 ≤ q.1.1 - (τ : EReal) ∧ (τ : EReal) ≤ q.1.1}.encard := by
  have hB := alg_numclust_eq_barcode n g Dm hDm hDm0 δ τ hδ hτ σ hσ
  have hA := alg_diagram_eq_barcode n g Dm hDm δ σ hσ
  rw [hB]
  simp only [hA]
