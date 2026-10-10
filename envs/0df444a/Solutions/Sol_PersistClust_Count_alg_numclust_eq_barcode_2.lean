-- Prove2me | solution 2 for PersistClust.Count.alg_numclust_eq_barcode
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-10T05:10:40.308802+00:00
-- url     : https://prove2.me/submissions/ca9b8b51-0481-42f2-bd10-48f22c9ec31b

import Mathlib
import Definitions.Def_PersistClust_Count_Algorithm
import Definitions.Def_PersistClust_Count_AlgBarcode
import Theorems.Thm_PersistClust_Count_alg_numclust_eq_barcode_forward
import Theorems.Thm_PersistClust_Count_alg_numclust_eq_barcode_reverse

open PersistClust.Count

/-!
Reduction of `alg_numclust_eq_barcode` to two lemmas.

Procedure 1 run with merge threshold `τ` outputs `numClusters` clusters (final union-find
entries whose root has value `≥ τ`).  The claim is that this equals the total multiplicity of
elder-rule barcode points `(b, d)` with `d ≤ b - τ` and `b ≥ τ`.

The reduction is the antisymmetry of two independent sub-claims:

1. `alg_numclust_eq_barcode_forward` — every output cluster injects into the copy set of the
   region: a surviving root `r` maps to its recorded barcode point (the per-root death map
   of the `τ = +∞` sweep; equal points are separated by the rank of `r`), which lies in the
   region `d ≤ b - τ`, `τ ≤ b`.
2. `alg_numclust_eq_barcode_reverse` — every copy of a barcode point in the region is realized
   by a distinct output cluster: the underlying root of the point survived the `τ`-sweep.

Both directions rest on the same combinatorial fact: the final roots of the `τ`-sweep are
exactly the immortal roots of the plain sweep together with the roots whose recorded death
prominence is at least `τ` — the `τ`-thresholded merge rules kill exactly the
non-`τ`-prominent pairs.
-/

theorem solution
    (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (hDm0 : ∀ i j, 0 ≤ Dm i j)
    (δ τ : ℝ) (hδ : 0 ≤ δ) (hτ : 0 < τ)
    (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) :
    (numClusters g Dm δ τ σ : ℕ∞)
      = {q : (EReal × EReal) × ℕ | (q.2 : ℕ∞) < ripsBarcode g Dm δ σ q.1 ∧
          q.1.2 ≤ q.1.1 - (τ : EReal) ∧ (τ : EReal) ≤ q.1.1}.encard := by
  exact le_antisymm
    (alg_numclust_eq_barcode_forward n g Dm hDm hDm0 δ τ hδ hτ σ hσ)
    (alg_numclust_eq_barcode_reverse n g Dm hDm hDm0 δ τ hδ hτ σ hσ)
