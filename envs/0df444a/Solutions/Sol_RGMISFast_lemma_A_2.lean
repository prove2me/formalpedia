-- Prove2me | solution 1 for RGMISFast.lemma_A_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @srikkanthr
-- created : 2026-11-15T22:28:32.204773+00:00
-- url     : https://prove2.me/submissions/7a610ea8-796b-4fb4-b674-25771bf99037
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_RGMISFast_root_connected_tree_code_exists
import Definitions.Def_RGMISFast_rootedTreeCode
import Definitions.Def_RGMISFast_IsRootConnected
open RGMISFast
set_option autoImplicit false

/-- Counting all traversal words over-approximates the balanced tree shapes. -/
theorem rootedTreeCode_count {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (u : V) (j : ℕ)
    (hencode : ∀ A : Finset V, IsRootConnected G u A → A.card = j+1 →
      ∃ (shape : Fin (2*j) → Bool) (labels : Fin j → Fin Δ),
        rootedTreeCode G Δ u j shape labels = A) :
    {A : Finset V | IsRootConnected G u A ∧ A.card = j+1}.ncard ≤ (4*Δ)^j := by
  classical
  let C := (Fin (2*j) → Bool) × (Fin j → Fin Δ)
  let decode : C → Finset V := fun p => rootedTreeCode G Δ u j p.1 p.2
  let F : Finset (Finset V) := Finset.univ.image decode
  have hsub : {A : Finset V | IsRootConnected G u A ∧ A.card = j+1} ⊆ (F : Set (Finset V)) := by
    intro A hA
    obtain ⟨shape,labels,he⟩ := hencode A hA.1 hA.2
    exact Finset.mem_image.mpr ⟨(shape,labels),Finset.mem_univ _,he⟩
  have hcount : Fintype.card C = (4*Δ)^j := by
    dsimp [C]
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    rw [pow_mul]
    norm_num
    rw [← mul_pow]
  calc
    _ ≤ (F : Set (Finset V)).ncard := Set.ncard_le_ncard hsub
    _ = F.card := Set.ncard_coe_finset _
    _ ≤ (Finset.univ : Finset C).card := Finset.card_image_le
    _ = (4*Δ)^j := by rw [Finset.card_univ,hcount]

open RGMISFast

/-- Lemma A.2 (Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized Greedy MIS Is Fast at Every Node*,
STOC 2027 submission (manuscript sha256 e93cdfec…), p.29): for every `j ≥ 0`, there are at most `(4∆)^j` root-connected sets with
exactly `j` vertices other than `u∗`.

**Formalization Note** `∆` is any bound on all degrees; no lower bound on `∆` is needed. The
sets are finsets `A` with `|A| = j + 1`, counted by `Set.ncard` (the family is finite). -/
theorem solution {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ)
    (hdeg : ∀ v, G.degree v ≤ Δ) (u : V) (j : ℕ) :
    {A : Finset V | IsRootConnected G u A ∧ A.card = j + 1}.ncard ≤ (4 * Δ) ^ j := by
  exact rootedTreeCode_count G Δ u j (root_connected_tree_code_exists G Δ hdeg u j)


