-- Prove2me | solution 1 for SnarkGen.OddFactors.g81_cyclicallyEdgeConnected_four
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T20:28:38.765829+00:00
-- url     : https://prove2.me/submissions/85865a8e-814b-40cf-845a-80bd4b05923d

import Mathlib
import Definitions.Def_SnarkGen_OddFactors_Snark
import Definitions.Def_SnarkGen_OddFactors_G81

open SnarkGen.OddFactors

private def v0 : Fin 26 := ⟨0, by decide⟩
private def v1 : Fin 26 := ⟨1, by decide⟩
private def v2 : Fin 26 := ⟨2, by decide⟩
private def v3 : Fin 26 := ⟨3, by decide⟩
private def v4 : Fin 26 := ⟨4, by decide⟩
private def v5 : Fin 26 := ⟨5, by decide⟩
private def v6 : Fin 26 := ⟨6, by decide⟩
private def v7 : Fin 26 := ⟨7, by decide⟩
private def v8 : Fin 26 := ⟨8, by decide⟩
private def v9 : Fin 26 := ⟨9, by decide⟩
private def v10 : Fin 26 := ⟨10, by decide⟩
private def v11 : Fin 26 := ⟨11, by decide⟩
private def v12 : Fin 26 := ⟨12, by decide⟩
private def v13 : Fin 26 := ⟨13, by decide⟩
private def v14 : Fin 26 := ⟨14, by decide⟩
private def v15 : Fin 26 := ⟨15, by decide⟩
private def v16 : Fin 26 := ⟨16, by decide⟩
private def v17 : Fin 26 := ⟨17, by decide⟩
private def v18 : Fin 26 := ⟨18, by decide⟩
private def v19 : Fin 26 := ⟨19, by decide⟩
private def v20 : Fin 26 := ⟨20, by decide⟩
private def v21 : Fin 26 := ⟨21, by decide⟩
private def v22 : Fin 26 := ⟨22, by decide⟩
private def v23 : Fin 26 := ⟨23, by decide⟩
private def v24 : Fin 26 := ⟨24, by decide⟩
private def v25 : Fin 26 := ⟨25, by decide⟩

private abbrev Path26 := Fin 26 × List (Fin 26)
private abbrev Quad26 := Path26 × Path26 × Path26 × Path26

private def memEdges (p : Fin 26 × Fin 26) : Bool :=
  G81Edges.any (fun q => p.1.val == q.1.val && p.2.val == q.2.val)

private def adjBool (a b : Fin 26) : Bool :=
  memEdges (a, b) || memEdges (b, a)

private lemma adj_of_adjBool {a b : Fin 26} (h : adjBool a b = true) : G81.Adj a b := by
  simp only [adjBool, memEdges, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
    beq_iff_eq, Fin.ext_iff] at h
  rcases h with ⟨⟨q1, q2⟩, hmem, h1, h2⟩ | ⟨⟨q1, q2⟩, hmem, h1, h2⟩
  · have hq1 : a = q1 := Fin.ext h1
    have hq2 : b = q2 := Fin.ext h2
    subst hq1 hq2; exact Or.inl hmem
  · have hq1 : b = q1 := Fin.ext h1
    have hq2 : a = q2 := Fin.ext h2
    subst hq1 hq2; exact Or.inr hmem

private def walkPairs : Fin 26 → List (Fin 26) → List (Fin 26 × Fin 26)
  | _, [] => []
  | a, b :: l => (a, b) :: walkPairs b l

private def walkEnd : Fin 26 → List (Fin 26) → Fin 26
  | a, [] => a
  | _, b :: l => walkEnd b l

private def walkValid : Fin 26 → List (Fin 26) → Bool
  | _, [] => true
  | a, b :: l => adjBool a b && walkValid b l

private def pathOk (u v ru rv : Fin 26) (w : Path26) : Bool :=
  (w.1.val == u.val || w.1.val == v.val) &&
  (walkEnd w.1 w.2 == ru || walkEnd w.1 w.2 == rv) &&
  walkValid w.1 w.2

private def pPairs (w : Path26) : List (Fin 26 × Fin 26) := walkPairs w.1 w.2

private def sameEdge (p q : Fin 26 × Fin 26) : Bool :=
  (p.1.val == q.1.val && p.2.val == q.2.val) || (p.1.val == q.2.val && p.2.val == q.1.val)

private def listDisj (l₁ l₂ : List (Fin 26 × Fin 26)) : Bool :=
  l₁.all (fun p => l₂.all (fun q => !sameEdge p q))

private def quadOk (u v ru rv : Fin 26) (q : Quad26) : Bool :=
  let (w₀, w₁, w₂, w₃) := q
  pathOk u v ru rv w₀ && pathOk u v ru rv w₁ &&
  pathOk u v ru rv w₂ && pathOk u v ru rv w₃ &&
  listDisj (pPairs w₀) (pPairs w₁) &&
  listDisj (pPairs w₀) (pPairs w₂) &&
  listDisj (pPairs w₀) (pPairs w₃) &&
  listDisj (pPairs w₁) (pPairs w₂) &&
  listDisj (pPairs w₁) (pPairs w₃) &&
  listDisj (pPairs w₂) (pPairs w₃)

private def refEdge : Fin 4 → Fin 26 × Fin 26
  | 0 => (v0, v1)
  | 1 => (v2, v6)
  | 2 => (v3, v8)
  | 3 => (v5, v7)

private def quadsList : Fin 4 → List ((Fin 26 × Fin 26) × Quad26)
  | 0 =>
    [((v0, v1), ((v0, []), (v0, []), (v0, []), (v0, []))),
     ((v0, v2), ((v0, []), (v0, []), (v0, []), (v0, []))),
     ((v0, v3), ((v0, []), (v0, []), (v0, []), (v0, []))),
     ((v1, v4), ((v1, []), (v1, []), (v1, []), (v1, []))),
     ((v1, v5), ((v1, []), (v1, []), (v1, []), (v1, []))),
     ((v2, v6), ((v2, [v7, v5, v1]), (v2, [v0]), (v6, [v10, v14, v17, v12, v8, v3, v0]), (v6, [v4, v1]))),
     ((v2, v7), ((v2, [v6, v4, v1]), (v2, [v0]), (v7, [v11, v14, v17, v12, v8, v3, v0]), (v7, [v5, v1]))),
     ((v3, v8), ((v3, [v9, v5, v1]), (v3, [v0]), (v8, [v12, v17, v14, v10, v6, v2, v0]), (v8, [v4, v1]))),
     ((v3, v9), ((v3, [v8, v4, v1]), (v3, [v0]), (v9, [v13, v17, v14, v10, v6, v2, v0]), (v9, [v5, v1]))),
     ((v4, v6), ((v4, [v8, v3, v0]), (v4, [v1]), (v6, [v10, v14, v11, v7, v5, v1]), (v6, [v2, v0]))),
     ((v4, v8), ((v4, [v6, v2, v0]), (v4, [v1]), (v8, [v12, v17, v13, v9, v5, v1]), (v8, [v3, v0]))),
     ((v5, v7), ((v5, [v9, v3, v0]), (v5, [v1]), (v7, [v11, v14, v10, v6, v4, v1]), (v7, [v2, v0]))),
     ((v5, v9), ((v5, [v7, v2, v0]), (v5, [v1]), (v9, [v13, v17, v12, v8, v4, v1]), (v9, [v3, v0]))),
     ((v6, v10), ((v6, [v4, v1]), (v6, [v2, v0]), (v10, [v15, v21, v19, v13, v9, v3, v0]), (v10, [v14, v11, v7, v5, v1]))),
     ((v7, v11), ((v7, [v5, v1]), (v7, [v2, v0]), (v11, [v16, v22, v18, v12, v8, v3, v0]), (v11, [v14, v10, v6, v4, v1]))),
     ((v8, v12), ((v8, [v4, v1]), (v8, [v3, v0]), (v12, [v18, v22, v16, v11, v7, v2, v0]), (v12, [v17, v13, v9, v5, v1]))),
     ((v9, v13), ((v9, [v5, v1]), (v9, [v3, v0]), (v13, [v19, v21, v15, v10, v6, v2, v0]), (v13, [v17, v12, v8, v4, v1]))),
     ((v10, v14), ((v10, [v15, v21, v19, v13, v9, v3, v0]), (v10, [v6, v2, v0]), (v14, [v17, v12, v8, v4, v1]), (v14, [v11, v7, v5, v1]))),
     ((v10, v15), ((v10, [v14, v11, v7, v5, v1]), (v10, [v6, v2, v0]), (v15, [v21, v19, v13, v9, v3, v0]), (v15, [v20, v16, v22, v18, v12, v8, v4, v1]))),
     ((v11, v14), ((v11, [v16, v20, v15, v21, v19, v13, v9, v5, v1]), (v11, [v7, v2, v0]), (v14, [v17, v12, v8, v3, v0]), (v14, [v10, v6, v4, v1]))),
     ((v11, v16), ((v11, [v14, v10, v6, v4, v1]), (v11, [v7, v2, v0]), (v16, [v22, v18, v12, v8, v3, v0]), (v16, [v20, v15, v21, v19, v13, v9, v5, v1]))),
     ((v12, v17), ((v12, [v18, v22, v16, v11, v7, v2, v0]), (v12, [v8, v3, v0]), (v17, [v14, v10, v6, v4, v1]), (v17, [v13, v9, v5, v1]))),
     ((v12, v18), ((v12, [v17, v13, v9, v5, v1]), (v12, [v8, v3, v0]), (v18, [v23, v19, v21, v15, v10, v6, v4, v1]), (v18, [v22, v16, v11, v7, v2, v0]))),
     ((v13, v17), ((v13, [v19, v21, v15, v10, v6, v2, v0]), (v13, [v9, v3, v0]), (v17, [v14, v11, v7, v5, v1]), (v17, [v12, v8, v4, v1]))),
     ((v13, v19), ((v13, [v17, v12, v8, v4, v1]), (v13, [v9, v3, v0]), (v19, [v23, v18, v22, v16, v11, v7, v5, v1]), (v19, [v21, v15, v10, v6, v2, v0]))),
     ((v14, v17), ((v14, [v11, v7, v5, v1]), (v14, [v10, v6, v2, v0]), (v17, [v13, v9, v3, v0]), (v17, [v12, v8, v4, v1]))),
     ((v15, v20), ((v15, [v21, v19, v13, v9, v3, v0]), (v15, [v10, v6, v2, v0]), (v20, [v24, v23, v18, v12, v8, v4, v1]), (v20, [v16, v11, v7, v5, v1]))),
     ((v15, v21), ((v15, [v20, v16, v11, v7, v5, v1]), (v15, [v10, v6, v2, v0]), (v21, [v25, v22, v18, v12, v8, v4, v1]), (v21, [v19, v13, v9, v3, v0]))),
     ((v16, v20), ((v16, [v22, v18, v12, v8, v3, v0]), (v16, [v11, v7, v2, v0]), (v20, [v24, v23, v19, v13, v9, v5, v1]), (v20, [v15, v10, v6, v4, v1]))),
     ((v16, v22), ((v16, [v20, v15, v10, v6, v4, v1]), (v16, [v11, v7, v2, v0]), (v22, [v25, v21, v19, v13, v9, v5, v1]), (v22, [v18, v12, v8, v3, v0]))),
     ((v18, v22), ((v18, [v23, v19, v13, v9, v5, v1]), (v18, [v12, v8, v3, v0]), (v22, [v25, v21, v15, v10, v6, v4, v1]), (v22, [v16, v11, v7, v2, v0]))),
     ((v18, v23), ((v18, [v22, v16, v11, v7, v2, v0]), (v18, [v12, v8, v3, v0]), (v23, [v24, v20, v15, v10, v6, v4, v1]), (v23, [v19, v13, v9, v5, v1]))),
     ((v19, v21), ((v19, [v23, v18, v12, v8, v4, v1]), (v19, [v13, v9, v3, v0]), (v21, [v25, v22, v16, v11, v7, v5, v1]), (v21, [v15, v10, v6, v2, v0]))),
     ((v19, v23), ((v19, [v21, v15, v10, v6, v2, v0]), (v19, [v13, v9, v3, v0]), (v23, [v24, v20, v16, v11, v7, v5, v1]), (v23, [v18, v12, v8, v4, v1]))),
     ((v20, v24), ((v20, [v16, v11, v7, v5, v1]), (v20, [v15, v10, v6, v2, v0]), (v24, [v25, v21, v19, v13, v9, v3, v0]), (v24, [v23, v18, v12, v8, v4, v1]))),
     ((v21, v25), ((v21, [v19, v13, v9, v3, v0]), (v21, [v15, v10, v6, v2, v0]), (v25, [v24, v23, v18, v12, v8, v4, v1]), (v25, [v22, v16, v11, v7, v5, v1]))),
     ((v22, v25), ((v22, [v18, v12, v8, v3, v0]), (v22, [v16, v11, v7, v2, v0]), (v25, [v24, v23, v19, v13, v9, v5, v1]), (v25, [v21, v15, v10, v6, v4, v1]))),
     ((v23, v24), ((v23, [v19, v13, v9, v5, v1]), (v23, [v18, v12, v8, v3, v0]), (v24, [v25, v22, v16, v11, v7, v2, v0]), (v24, [v20, v15, v10, v6, v4, v1]))),
     ((v24, v25), ((v24, [v23, v18, v12, v8, v3, v0]), (v24, [v20, v15, v10, v6, v4, v1]), (v25, [v22, v16, v11, v7, v2, v0]), (v25, [v21, v19, v13, v9, v5, v1])))]
  | 1 =>
    [((v0, v1), ((v0, [v3, v8, v12, v17, v14, v10, v6]), (v0, [v2]), (v1, [v5, v7, v2]), (v1, [v4, v6]))),
     ((v0, v2), ((v2, []), (v2, []), (v2, []), (v2, []))),
     ((v0, v3), ((v0, [v2]), (v0, [v1, v4, v6]), (v3, [v9, v5, v7, v2]), (v3, [v8, v12, v17, v14, v10, v6]))),
     ((v1, v4), ((v1, [v5, v7, v2]), (v1, [v0, v2]), (v4, [v8, v12, v17, v14, v10, v6]), (v4, [v6]))),
     ((v1, v5), ((v1, [v4, v6]), (v1, [v0, v2]), (v5, [v9, v13, v17, v14, v10, v6]), (v5, [v7, v2]))),
     ((v2, v6), ((v2, []), (v2, []), (v2, []), (v2, []))),
     ((v2, v7), ((v2, []), (v2, []), (v2, []), (v2, []))),
     ((v3, v8), ((v3, [v9, v5, v7, v2]), (v3, [v0, v2]), (v8, [v12, v17, v14, v10, v6]), (v8, [v4, v6]))),
     ((v3, v9), ((v3, [v8, v4, v6]), (v3, [v0, v2]), (v9, [v13, v17, v14, v10, v6]), (v9, [v5, v7, v2]))),
     ((v4, v6), ((v6, []), (v6, []), (v6, []), (v6, []))),
     ((v4, v8), ((v4, [v6]), (v4, [v1, v0, v2]), (v8, [v12, v17, v14, v10, v6]), (v8, [v3, v9, v5, v7, v2]))),
     ((v5, v7), ((v5, [v9, v3, v8, v4, v6]), (v5, [v1, v0, v2]), (v7, [v11, v14, v10, v6]), (v7, [v2]))),
     ((v5, v9), ((v5, [v7, v2]), (v5, [v1, v0, v2]), (v9, [v13, v17, v14, v10, v6]), (v9, [v3, v8, v4, v6]))),
     ((v6, v10), ((v6, []), (v6, []), (v6, []), (v6, []))),
     ((v7, v11), ((v7, [v5, v1, v0, v2]), (v7, [v2]), (v11, [v16, v22, v18, v12, v8, v4, v6]), (v11, [v14, v10, v6]))),
     ((v8, v12), ((v8, [v4, v6]), (v8, [v3, v0, v2]), (v12, [v18, v22, v16, v11, v7, v2]), (v12, [v17, v14, v10, v6]))),
     ((v9, v13), ((v9, [v5, v7, v2]), (v9, [v3, v0, v2]), (v13, [v19, v23, v18, v12, v8, v4, v6]), (v13, [v17, v14, v10, v6]))),
     ((v10, v14), ((v10, [v15, v21, v19, v13, v9, v3, v0, v2]), (v10, [v6]), (v14, [v17, v12, v8, v4, v6]), (v14, [v11, v7, v2]))),
     ((v10, v15), ((v10, [v14, v11, v7, v2]), (v10, [v6]), (v15, [v21, v19, v13, v9, v3, v0, v2]), (v15, [v20, v16, v22, v18, v12, v8, v4, v6]))),
     ((v11, v14), ((v11, [v16, v20, v15, v21, v19, v13, v9, v3, v0, v2]), (v11, [v7, v2]), (v14, [v17, v12, v8, v4, v6]), (v14, [v10, v6]))),
     ((v11, v16), ((v11, [v14, v10, v6]), (v11, [v7, v2]), (v16, [v22, v18, v12, v8, v4, v6]), (v16, [v20, v15, v21, v19, v13, v9, v3, v0, v2]))),
     ((v12, v17), ((v12, [v18, v22, v16, v11, v7, v2]), (v12, [v8, v4, v6]), (v17, [v14, v10, v6]), (v17, [v13, v9, v3, v0, v2]))),
     ((v12, v18), ((v12, [v17, v14, v10, v6]), (v12, [v8, v4, v6]), (v18, [v23, v19, v13, v9, v3, v0, v2]), (v18, [v22, v16, v11, v7, v2]))),
     ((v13, v17), ((v13, [v19, v21, v15, v10, v6]), (v13, [v9, v3, v0, v2]), (v17, [v14, v11, v7, v2]), (v17, [v12, v8, v4, v6]))),
     ((v13, v19), ((v13, [v17, v14, v11, v7, v2]), (v13, [v9, v3, v0, v2]), (v19, [v23, v18, v12, v8, v4, v6]), (v19, [v21, v15, v10, v6]))),
     ((v14, v17), ((v14, [v11, v7, v2]), (v14, [v10, v6]), (v17, [v13, v9, v3, v0, v2]), (v17, [v12, v8, v4, v6]))),
     ((v15, v20), ((v15, [v21, v19, v13, v9, v3, v0, v2]), (v15, [v10, v6]), (v20, [v24, v23, v18, v12, v8, v4, v6]), (v20, [v16, v11, v7, v2]))),
     ((v15, v21), ((v15, [v20, v16, v11, v7, v2]), (v15, [v10, v6]), (v21, [v25, v22, v18, v12, v8, v4, v6]), (v21, [v19, v13, v9, v3, v0, v2]))),
     ((v16, v20), ((v16, [v22, v18, v12, v8, v4, v6]), (v16, [v11, v7, v2]), (v20, [v24, v23, v19, v13, v9, v3, v0, v2]), (v20, [v15, v10, v6]))),
     ((v16, v22), ((v16, [v20, v15, v10, v6]), (v16, [v11, v7, v2]), (v22, [v25, v21, v19, v13, v9, v3, v0, v2]), (v22, [v18, v12, v8, v4, v6]))),
     ((v18, v22), ((v18, [v23, v19, v13, v9, v3, v0, v2]), (v18, [v12, v8, v4, v6]), (v22, [v25, v21, v15, v10, v6]), (v22, [v16, v11, v7, v2]))),
     ((v18, v23), ((v18, [v22, v16, v11, v7, v2]), (v18, [v12, v8, v4, v6]), (v23, [v24, v25, v21, v15, v10, v6]), (v23, [v19, v13, v9, v3, v0, v2]))),
     ((v19, v21), ((v19, [v23, v18, v12, v8, v4, v6]), (v19, [v13, v9, v3, v0, v2]), (v21, [v25, v22, v16, v11, v7, v2]), (v21, [v15, v10, v6]))),
     ((v19, v23), ((v19, [v21, v15, v10, v6]), (v19, [v13, v9, v3, v0, v2]), (v23, [v24, v20, v16, v11, v7, v2]), (v23, [v18, v12, v8, v4, v6]))),
     ((v20, v24), ((v20, [v16, v11, v7, v2]), (v20, [v15, v10, v6]), (v24, [v25, v21, v19, v13, v9, v3, v0, v2]), (v24, [v23, v18, v12, v8, v4, v6]))),
     ((v21, v25), ((v21, [v19, v13, v9, v3, v0, v2]), (v21, [v15, v10, v6]), (v25, [v24, v23, v18, v12, v8, v4, v6]), (v25, [v22, v16, v11, v7, v2]))),
     ((v22, v25), ((v22, [v18, v12, v8, v4, v6]), (v22, [v16, v11, v7, v2]), (v25, [v24, v23, v19, v13, v9, v3, v0, v2]), (v25, [v21, v15, v10, v6]))),
     ((v23, v24), ((v23, [v19, v13, v9, v3, v0, v2]), (v23, [v18, v12, v8, v4, v6]), (v24, [v25, v22, v16, v11, v7, v2]), (v24, [v20, v15, v10, v6]))),
     ((v24, v25), ((v24, [v23, v18, v12, v8, v4, v6]), (v24, [v20, v15, v10, v6]), (v25, [v22, v16, v11, v7, v2]), (v25, [v21, v19, v13, v9, v3, v0, v2])))]
  | 2 =>
    [((v0, v1), ((v0, [v3]), (v0, [v2, v6, v10, v14, v17, v12, v8]), (v1, [v5, v9, v3]), (v1, [v4, v8]))),
     ((v0, v2), ((v0, [v3]), (v0, [v1, v4, v8]), (v2, [v7, v5, v9, v3]), (v2, [v6, v10, v14, v17, v12, v8]))),
     ((v0, v3), ((v3, []), (v3, []), (v3, []), (v3, []))),
     ((v1, v4), ((v1, [v5, v9, v3]), (v1, [v0, v3]), (v4, [v8]), (v4, [v6, v10, v14, v17, v12, v8]))),
     ((v1, v5), ((v1, [v4, v8]), (v1, [v0, v3]), (v5, [v9, v3]), (v5, [v7, v11, v14, v17, v12, v8]))),
     ((v2, v6), ((v2, [v7, v5, v9, v3]), (v2, [v0, v3]), (v6, [v10, v14, v17, v12, v8]), (v6, [v4, v8]))),
     ((v2, v7), ((v2, [v6, v4, v8]), (v2, [v0, v3]), (v7, [v11, v14, v17, v12, v8]), (v7, [v5, v9, v3]))),
     ((v3, v8), ((v3, []), (v3, []), (v3, []), (v3, []))),
     ((v3, v9), ((v3, []), (v3, []), (v3, []), (v3, []))),
     ((v4, v6), ((v4, [v8]), (v4, [v1, v0, v3]), (v6, [v10, v14, v17, v12, v8]), (v6, [v2, v7, v5, v9, v3]))),
     ((v4, v8), ((v8, []), (v8, []), (v8, []), (v8, []))),
     ((v5, v7), ((v5, [v9, v3]), (v5, [v1, v0, v3]), (v7, [v11, v14, v17, v12, v8]), (v7, [v2, v6, v4, v8]))),
     ((v5, v9), ((v5, [v7, v2, v6, v4, v8]), (v5, [v1, v0, v3]), (v9, [v13, v17, v12, v8]), (v9, [v3]))),
     ((v6, v10), ((v6, [v4, v8]), (v6, [v2, v0, v3]), (v10, [v15, v21, v19, v13, v9, v3]), (v10, [v14, v17, v12, v8]))),
     ((v7, v11), ((v7, [v5, v9, v3]), (v7, [v2, v0, v3]), (v11, [v16, v20, v15, v10, v6, v4, v8]), (v11, [v14, v17, v12, v8]))),
     ((v8, v12), ((v8, []), (v8, []), (v8, []), (v8, []))),
     ((v9, v13), ((v9, [v5, v1, v0, v3]), (v9, [v3]), (v13, [v19, v21, v15, v10, v6, v4, v8]), (v13, [v17, v12, v8]))),
     ((v10, v14), ((v10, [v15, v21, v19, v13, v9, v3]), (v10, [v6, v4, v8]), (v14, [v17, v12, v8]), (v14, [v11, v7, v2, v0, v3]))),
     ((v10, v15), ((v10, [v14, v17, v12, v8]), (v10, [v6, v4, v8]), (v15, [v21, v19, v13, v9, v3]), (v15, [v20, v16, v11, v7, v2, v0, v3]))),
     ((v11, v14), ((v11, [v16, v20, v15, v21, v19, v13, v9, v3]), (v11, [v7, v2, v0, v3]), (v14, [v17, v12, v8]), (v14, [v10, v6, v4, v8]))),
     ((v11, v16), ((v11, [v14, v17, v13, v9, v3]), (v11, [v7, v2, v0, v3]), (v16, [v22, v18, v12, v8]), (v16, [v20, v15, v10, v6, v4, v8]))),
     ((v12, v17), ((v12, [v18, v22, v16, v11, v7, v2, v0, v3]), (v12, [v8]), (v17, [v14, v10, v6, v4, v8]), (v17, [v13, v9, v3]))),
     ((v12, v18), ((v12, [v17, v13, v9, v3]), (v12, [v8]), (v18, [v23, v19, v21, v15, v10, v6, v4, v8]), (v18, [v22, v16, v11, v7, v2, v0, v3]))),
     ((v13, v17), ((v13, [v19, v21, v15, v10, v6, v4, v8]), (v13, [v9, v3]), (v17, [v14, v11, v7, v2, v0, v3]), (v17, [v12, v8]))),
     ((v13, v19), ((v13, [v17, v12, v8]), (v13, [v9, v3]), (v19, [v23, v18, v22, v16, v11, v7, v2, v0, v3]), (v19, [v21, v15, v10, v6, v4, v8]))),
     ((v14, v17), ((v14, [v11, v7, v2, v0, v3]), (v14, [v10, v6, v4, v8]), (v17, [v13, v9, v3]), (v17, [v12, v8]))),
     ((v15, v20), ((v15, [v21, v19, v13, v9, v3]), (v15, [v10, v6, v4, v8]), (v20, [v24, v25, v22, v18, v12, v8]), (v20, [v16, v11, v7, v2, v0, v3]))),
     ((v15, v21), ((v15, [v20, v16, v11, v7, v2, v0, v3]), (v15, [v10, v6, v4, v8]), (v21, [v25, v22, v18, v12, v8]), (v21, [v19, v13, v9, v3]))),
     ((v16, v20), ((v16, [v22, v18, v12, v8]), (v16, [v11, v7, v2, v0, v3]), (v20, [v24, v23, v19, v13, v9, v3]), (v20, [v15, v10, v6, v4, v8]))),
     ((v16, v22), ((v16, [v20, v15, v10, v6, v4, v8]), (v16, [v11, v7, v2, v0, v3]), (v22, [v25, v21, v19, v13, v9, v3]), (v22, [v18, v12, v8]))),
     ((v18, v22), ((v18, [v23, v19, v13, v9, v3]), (v18, [v12, v8]), (v22, [v25, v21, v15, v10, v6, v4, v8]), (v22, [v16, v11, v7, v2, v0, v3]))),
     ((v18, v23), ((v18, [v22, v16, v11, v7, v2, v0, v3]), (v18, [v12, v8]), (v23, [v24, v20, v15, v10, v6, v4, v8]), (v23, [v19, v13, v9, v3]))),
     ((v19, v21), ((v19, [v23, v18, v12, v8]), (v19, [v13, v9, v3]), (v21, [v25, v22, v16, v11, v7, v2, v0, v3]), (v21, [v15, v10, v6, v4, v8]))),
     ((v19, v23), ((v19, [v21, v15, v10, v6, v4, v8]), (v19, [v13, v9, v3]), (v23, [v24, v20, v16, v11, v7, v2, v0, v3]), (v23, [v18, v12, v8]))),
     ((v20, v24), ((v20, [v16, v11, v7, v2, v0, v3]), (v20, [v15, v10, v6, v4, v8]), (v24, [v25, v21, v19, v13, v9, v3]), (v24, [v23, v18, v12, v8]))),
     ((v21, v25), ((v21, [v19, v13, v9, v3]), (v21, [v15, v10, v6, v4, v8]), (v25, [v24, v20, v16, v11, v7, v2, v0, v3]), (v25, [v22, v18, v12, v8]))),
     ((v22, v25), ((v22, [v18, v12, v8]), (v22, [v16, v11, v7, v2, v0, v3]), (v25, [v24, v20, v15, v10, v6, v4, v8]), (v25, [v21, v19, v13, v9, v3]))),
     ((v23, v24), ((v23, [v19, v13, v9, v3]), (v23, [v18, v12, v8]), (v24, [v25, v22, v16, v11, v7, v2, v0, v3]), (v24, [v20, v15, v10, v6, v4, v8]))),
     ((v24, v25), ((v24, [v23, v18, v12, v8]), (v24, [v20, v15, v10, v6, v4, v8]), (v25, [v22, v16, v11, v7, v2, v0, v3]), (v25, [v21, v19, v13, v9, v3])))]
  | 3 =>
    [((v0, v1), ((v0, [v3, v9, v5]), (v0, [v2, v7]), (v1, [v5]), (v1, [v4, v6, v10, v14, v11, v7]))),
     ((v0, v2), ((v0, [v3, v9, v5]), (v0, [v1, v5]), (v2, [v7]), (v2, [v6, v10, v14, v11, v7]))),
     ((v0, v3), ((v0, [v2, v7]), (v0, [v1, v5]), (v3, [v9, v5]), (v3, [v8, v12, v17, v14, v11, v7]))),
     ((v1, v4), ((v1, [v5]), (v1, [v0, v2, v7]), (v4, [v8, v3, v9, v5]), (v4, [v6, v10, v14, v11, v7]))),
     ((v1, v5), ((v5, []), (v5, []), (v5, []), (v5, []))),
     ((v2, v6), ((v2, [v7]), (v2, [v0, v1, v5]), (v6, [v10, v14, v11, v7]), (v6, [v4, v8, v3, v9, v5]))),
     ((v2, v7), ((v7, []), (v7, []), (v7, []), (v7, []))),
     ((v3, v8), ((v3, [v9, v5]), (v3, [v0, v1, v5]), (v8, [v12, v17, v14, v11, v7]), (v8, [v4, v6, v2, v7]))),
     ((v3, v9), ((v3, [v8, v4, v6, v2, v7]), (v3, [v0, v1, v5]), (v9, [v13, v17, v14, v11, v7]), (v9, [v5]))),
     ((v4, v6), ((v4, [v8, v3, v9, v5]), (v4, [v1, v5]), (v6, [v10, v14, v11, v7]), (v6, [v2, v7]))),
     ((v4, v8), ((v4, [v6, v2, v7]), (v4, [v1, v5]), (v8, [v12, v17, v14, v11, v7]), (v8, [v3, v9, v5]))),
     ((v5, v7), ((v5, []), (v5, []), (v5, []), (v5, []))),
     ((v5, v9), ((v5, []), (v5, []), (v5, []), (v5, []))),
     ((v6, v10), ((v6, [v4, v1, v5]), (v6, [v2, v7]), (v10, [v15, v21, v19, v13, v9, v5]), (v10, [v14, v11, v7]))),
     ((v7, v11), ((v7, []), (v7, []), (v7, []), (v7, []))),
     ((v8, v12), ((v8, [v4, v1, v5]), (v8, [v3, v9, v5]), (v12, [v18, v22, v16, v11, v7]), (v12, [v17, v14, v10, v6, v2, v7]))),
     ((v9, v13), ((v9, [v5]), (v9, [v3, v0, v1, v5]), (v13, [v19, v21, v15, v10, v6, v2, v7]), (v13, [v17, v14, v11, v7]))),
     ((v10, v14), ((v10, [v15, v20, v16, v22, v18, v12, v8, v4, v1, v5]), (v10, [v6, v2, v7]), (v14, [v17, v13, v9, v5]), (v14, [v11, v7]))),
     ((v10, v15), ((v10, [v14, v11, v7]), (v10, [v6, v2, v7]), (v15, [v21, v19, v13, v9, v5]), (v15, [v20, v16, v22, v18, v12, v8, v4, v1, v5]))),
     ((v11, v14), ((v11, [v16, v22, v18, v12, v8, v4, v1, v5]), (v11, [v7]), (v14, [v17, v13, v9, v5]), (v14, [v10, v6, v2, v7]))),
     ((v11, v16), ((v11, [v14, v10, v6, v2, v7]), (v11, [v7]), (v16, [v22, v18, v12, v8, v4, v1, v5]), (v16, [v20, v15, v21, v19, v13, v9, v5]))),
     ((v12, v17), ((v12, [v18, v22, v16, v11, v7]), (v12, [v8, v4, v1, v5]), (v17, [v14, v10, v6, v2, v7]), (v17, [v13, v9, v5]))),
     ((v12, v18), ((v12, [v17, v14, v10, v6, v2, v7]), (v12, [v8, v3, v0, v1, v5]), (v18, [v23, v19, v13, v9, v5]), (v18, [v22, v16, v11, v7]))),
     ((v13, v17), ((v13, [v19, v21, v15, v10, v6, v2, v7]), (v13, [v9, v5]), (v17, [v14, v11, v7]), (v17, [v12, v8, v4, v1, v5]))),
     ((v13, v19), ((v13, [v17, v14, v11, v7]), (v13, [v9, v5]), (v19, [v23, v18, v12, v8, v4, v1, v5]), (v19, [v21, v15, v10, v6, v2, v7]))),
     ((v14, v17), ((v14, [v11, v7]), (v14, [v10, v6, v2, v7]), (v17, [v13, v9, v5]), (v17, [v12, v8, v4, v1, v5]))),
     ((v15, v20), ((v15, [v21, v19, v13, v9, v5]), (v15, [v10, v6, v2, v7]), (v20, [v24, v23, v18, v12, v8, v4, v1, v5]), (v20, [v16, v11, v7]))),
     ((v15, v21), ((v15, [v20, v16, v11, v7]), (v15, [v10, v6, v2, v7]), (v21, [v25, v22, v18, v12, v8, v4, v1, v5]), (v21, [v19, v13, v9, v5]))),
     ((v16, v20), ((v16, [v22, v18, v12, v8, v4, v1, v5]), (v16, [v11, v7]), (v20, [v24, v23, v19, v13, v9, v5]), (v20, [v15, v10, v6, v2, v7]))),
     ((v16, v22), ((v16, [v20, v15, v10, v6, v2, v7]), (v16, [v11, v7]), (v22, [v25, v21, v19, v13, v9, v5]), (v22, [v18, v12, v8, v3, v0, v1, v5]))),
     ((v18, v22), ((v18, [v23, v19, v13, v9, v5]), (v18, [v12, v8, v3, v0, v1, v5]), (v22, [v25, v21, v15, v10, v6, v2, v7]), (v22, [v16, v11, v7]))),
     ((v18, v23), ((v18, [v22, v16, v11, v7]), (v18, [v12, v8, v4, v1, v5]), (v23, [v24, v20, v15, v10, v6, v2, v7]), (v23, [v19, v13, v9, v5]))),
     ((v19, v21), ((v19, [v23, v18, v12, v8, v4, v1, v5]), (v19, [v13, v9, v5]), (v21, [v25, v22, v16, v11, v7]), (v21, [v15, v10, v6, v2, v7]))),
     ((v19, v23), ((v19, [v21, v15, v10, v6, v2, v7]), (v19, [v13, v9, v5]), (v23, [v24, v25, v22, v16, v11, v7]), (v23, [v18, v12, v8, v4, v1, v5]))),
     ((v20, v24), ((v20, [v16, v11, v7]), (v20, [v15, v10, v6, v2, v7]), (v24, [v25, v22, v18, v12, v8, v4, v1, v5]), (v24, [v23, v19, v13, v9, v5]))),
     ((v21, v25), ((v21, [v19, v13, v9, v5]), (v21, [v15, v10, v6, v2, v7]), (v25, [v24, v23, v18, v12, v8, v4, v1, v5]), (v25, [v22, v16, v11, v7]))),
     ((v22, v25), ((v22, [v18, v12, v8, v4, v1, v5]), (v22, [v16, v11, v7]), (v25, [v24, v20, v15, v10, v6, v2, v7]), (v25, [v21, v19, v13, v9, v5]))),
     ((v23, v24), ((v23, [v19, v13, v9, v5]), (v23, [v18, v12, v8, v4, v1, v5]), (v24, [v25, v21, v15, v10, v6, v2, v7]), (v24, [v20, v16, v11, v7]))),
     ((v24, v25), ((v24, [v23, v19, v13, v9, v5]), (v24, [v20, v16, v11, v7]), (v25, [v22, v18, v12, v8, v4, v1, v5]), (v25, [v21, v15, v10, v6, v2, v7])))]

private def checkAllQuads : Bool :=
  (List.finRange 4).all (fun k =>
    ((quadsList k).map Prod.fst == G81Edges) &&
    (quadsList k).all (fun pq => quadOk pq.1.1 pq.1.2 (refEdge k).1 (refEdge k).2 pq.2))

private lemma checkAllQuads_eq_true : checkAllQuads = true := rfl

private lemma all_quads_ok (k : Fin 4) (p : Fin 26 × Fin 26) (hp : p ∈ G81Edges) :
    ∃ q : Quad26, quadOk p.1 p.2 (refEdge k).1 (refEdge k).2 q = true := by
  have hk := List.all_eq_true.mp checkAllQuads_eq_true k (List.mem_finRange k)
  simp only [Bool.and_eq_true, beq_iff_eq] at hk
  have hp' : p ∈ (quadsList k).map Prod.fst := by rw [hk.1]; exact hp
  rcases List.mem_map.mp hp' with ⟨⟨p', q⟩, hmem, rfl⟩
  exact ⟨q, List.all_eq_true.mp hk.2 (p', q) hmem⟩

private def checkRefAdj : Bool :=
  (List.finRange 4).all (fun k => adjBool (refEdge k).1 (refEdge k).2)

private lemma checkRefAdj_eq_true : checkRefAdj = true := rfl

private lemma refEdge_adj (k : Fin 4) : G81.Adj (refEdge k).1 (refEdge k).2 :=
  adj_of_adjBool (List.all_eq_true.mp checkRefAdj_eq_true k (List.mem_finRange k))

private lemma card_four_le_of_mem {α : Type*} [DecidableEq α] {S : Finset α}
    {e₀ e₁ e₂ e₃ : α} (h01 : e₀ ≠ e₁) (h02 : e₀ ≠ e₂) (h03 : e₀ ≠ e₃)
    (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃)
    (m0 : e₀ ∈ S) (m1 : e₁ ∈ S) (m2 : e₂ ∈ S) (m3 : e₃ ∈ S) : 4 ≤ S.card := by
  have hsub : ({e₀, e₁, e₂, e₃} : Finset α) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hcard : ({e₀, e₁, e₂, e₃} : Finset α).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [h23]
    · simp [h12, h13]
    · simp [h01, h02, h03]
  linarith [Finset.card_le_card hsub]

private lemma reachable_of_walkValid (S : Finset (Sym2 (Fin 26))) :
    ∀ (a : Fin 26) (l : List (Fin 26)),
      walkValid a l = true →
      (∀ p ∈ walkPairs a l, s(p.1, p.2) ∉ S) →
      (G81.deleteEdges ↑S).Reachable a (walkEnd a l)
  | a, [], _, _ => SimpleGraph.Reachable.refl a
  | a, b :: l, hval, hdisj => by
    simp only [walkValid, Bool.and_eq_true] at hval
    have hadj : (G81.deleteEdges ↑S).Adj a b := by
      rw [SimpleGraph.deleteEdges_adj]
      exact ⟨adj_of_adjBool hval.1, fun hm => hdisj (a, b) List.mem_cons_self hm⟩
    exact hadj.reachable.trans (reachable_of_walkValid S b l hval.2
      (fun p hp => hdisj p (List.mem_cons_of_mem _ hp)))

private lemma reachable_of_pathOk (S : Finset (Sym2 (Fin 26)))
    {u v ru rv : Fin 26} {w : Path26}
    (huv : (G81.deleteEdges ↑S).Adj u v)
    (hr : (G81.deleteEdges ↑S).Adj ru rv)
    (hok : pathOk u v ru rv w = true)
    (hdisj : ∀ p ∈ pPairs w, s(p.1, p.2) ∉ S) :
    (G81.deleteEdges ↑S).Reachable u ru := by
  simp only [pathOk, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, ← Fin.ext_iff] at hok
  rcases hok with ⟨⟨hstart, hend⟩, hval⟩
  have h1 : (G81.deleteEdges ↑S).Reachable u w.1 := by
    rcases hstart with h | h
    · rw [h]
    · rw [h]; exact huv.reachable
  have h2 : (G81.deleteEdges ↑S).Reachable w.1 (walkEnd w.1 w.2) :=
    reachable_of_walkValid S w.1 w.2 hval hdisj
  have h3 : (G81.deleteEdges ↑S).Reachable (walkEnd w.1 w.2) ru := by
    rcases hend with h | h
    · rw [h]
    · rw [h]; exact hr.symm.reachable
  exact h1.trans (h2.trans h3)

private lemma ne_of_listDisj {l₁ l₂ : List (Fin 26 × Fin 26)} (h : listDisj l₁ l₂ = true)
    {p₁ p₂ : Fin 26 × Fin 26} (h1 : p₁ ∈ l₁) (h2 : p₂ ∈ l₂) : s(p₁.1, p₁.2) ≠ s(p₂.1, p₂.2) := by
  have h1' := List.all_eq_true.mp h p₁ h1
  have h2' := List.all_eq_true.mp h1' p₂ h2
  simp only [Bool.not_eq_true', sameEdge, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
    beq_eq_false_iff_ne, ne_eq, ← Fin.ext_iff] at h2'
  intro heq
  rw [Sym2.eq_iff] at heq
  rcases heq with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · cases h2'.1 <;> contradiction
  · cases h2'.2 <;> contradiction

private lemma reachable_of_quadOk (S : Finset (Sym2 (Fin 26))) (hS : S.card < 4)
    {u v ru rv : Fin 26} {q : Quad26}
    (huv : (G81.deleteEdges ↑S).Adj u v)
    (hr : (G81.deleteEdges ↑S).Adj ru rv)
    (hok : quadOk u v ru rv q = true) :
    (G81.deleteEdges ↑S).Reachable u ru := by
  rcases q with ⟨w₀, w₁, w₂, w₃⟩
  simp only [quadOk, Bool.and_eq_true] at hok
  rcases hok with ⟨⟨⟨⟨⟨⟨⟨⟨⟨hp0, hp1⟩, hp2⟩, hp3⟩, d01⟩, d02⟩, d03⟩, d12⟩, d13⟩, d23⟩
  by_cases h0 : ∀ p ∈ pPairs w₀, s(p.1, p.2) ∉ S
  · exact reachable_of_pathOk S huv hr hp0 h0
  · by_cases h1 : ∀ p ∈ pPairs w₁, s(p.1, p.2) ∉ S
    · exact reachable_of_pathOk S huv hr hp1 h1
    · by_cases h2 : ∀ p ∈ pPairs w₂, s(p.1, p.2) ∉ S
      · exact reachable_of_pathOk S huv hr hp2 h2
      · by_cases h3 : ∀ p ∈ pPairs w₃, s(p.1, p.2) ∉ S
        · exact reachable_of_pathOk S huv hr hp3 h3
        · simp only [not_forall, Classical.not_not] at h0 h1 h2 h3
          rcases h0 with ⟨p₀, hp₀, m0⟩
          rcases h1 with ⟨p₁, hp₁, m1⟩
          rcases h2 with ⟨p₂, hp₂, m2⟩
          rcases h3 with ⟨p₃, hp₃, m3⟩
          have := card_four_le_of_mem
            (ne_of_listDisj d01 hp₀ hp₁) (ne_of_listDisj d02 hp₀ hp₂) (ne_of_listDisj d03 hp₀ hp₃)
            (ne_of_listDisj d12 hp₁ hp₂) (ne_of_listDisj d13 hp₁ hp₃) (ne_of_listDisj d23 hp₂ hp₃)
            m0 m1 m2 m3
          omega

private lemma reachable_ref_of_adj (S : Finset (Sym2 (Fin 26))) (hS : S.card < 4)
    (k : Fin 4) (hr : (G81.deleteEdges ↑S).Adj (refEdge k).1 (refEdge k).2)
    {u v : Fin 26} (huv : (G81.deleteEdges ↑S).Adj u v) :
    (G81.deleteEdges ↑S).Reachable u (refEdge k).1 := by
  have hadj := huv
  rw [SimpleGraph.deleteEdges_adj] at hadj
  rcases hadj.1 with hmem | hmem
  · rcases all_quads_ok k (u, v) hmem with ⟨q, hq⟩
    exact reachable_of_quadOk S hS huv hr hq
  · rcases all_quads_ok k (v, u) hmem with ⟨q, hq⟩
    exact huv.reachable.trans (reachable_of_quadOk S hS huv.symm hr hq)

private lemma exists_refEdge_adj (S : Finset (Sym2 (Fin 26))) (hS : S.card < 4) :
    ∃ k : Fin 4, (G81.deleteEdges ↑S).Adj (refEdge k).1 (refEdge k).2 := by
  by_contra H
  simp only [not_exists] at H
  have hmem : ∀ k : Fin 4, s((refEdge k).1, (refEdge k).2) ∈ S := by
    intro k
    have hk := H k
    rw [SimpleGraph.deleteEdges_adj] at hk
    by_contra hns
    exact hk ⟨refEdge_adj k, hns⟩
  have h4 := card_four_le_of_mem
    (by decide : s((refEdge 0).1, (refEdge 0).2) ≠ s((refEdge 1).1, (refEdge 1).2))
    (by decide : s((refEdge 0).1, (refEdge 0).2) ≠ s((refEdge 2).1, (refEdge 2).2))
    (by decide : s((refEdge 0).1, (refEdge 0).2) ≠ s((refEdge 3).1, (refEdge 3).2))
    (by decide : s((refEdge 1).1, (refEdge 1).2) ≠ s((refEdge 2).1, (refEdge 2).2))
    (by decide : s((refEdge 1).1, (refEdge 1).2) ≠ s((refEdge 3).1, (refEdge 3).2))
    (by decide : s((refEdge 2).1, (refEdge 2).2) ≠ s((refEdge 3).1, (refEdge 3).2))
    (hmem 0) (hmem 1) (hmem 2) (hmem 3)
  omega

theorem solution : SnarkGen.Zhang.CyclicallyEdgeConnected G81 4 := by
  intro S _ hS c₁ c₂ ⟨v₁, hv₁, p₁, hp₁⟩ ⟨v₂, hv₂, p₂, hp₂⟩
  rcases exists_refEdge_adj S hS with ⟨k, hr⟩
  have hex₁ : ∃ u₁, (G81.deleteEdges ↑S).Adj v₁ u₁ := by
    cases p₁ with
    | nil => exact absurd SimpleGraph.Walk.Nil.nil hp₁.not_nil
    | cons h _ => exact ⟨_, h⟩
  have hex₂ : ∃ u₂, (G81.deleteEdges ↑S).Adj v₂ u₂ := by
    cases p₂ with
    | nil => exact absurd SimpleGraph.Walk.Nil.nil hp₂.not_nil
    | cons h _ => exact ⟨_, h⟩
  rcases hex₁ with ⟨u₁, hu₁⟩
  rcases hex₂ with ⟨u₂, hu₂⟩
  have hr₁ := reachable_ref_of_adj S hS k hr hu₁
  have hr₂ := reachable_ref_of_adj S hS k hr hu₂
  have hreach : (G81.deleteEdges ↑S).Reachable v₁ v₂ := hr₁.trans hr₂.symm
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hv₁ hv₂
  rw [← hv₁, ← hv₂, SimpleGraph.ConnectedComponent.eq]
  exact hreach
