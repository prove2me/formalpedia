-- Prove2me | solution 1 for QAlgorithms.Childs.subadditivity_of_errors
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T07:41:03.784704+00:00
-- url     : https://prove2.me/submissions/9492b554-f025-4f67-81a6-8758857008e8

import Definitions.Def_QAlgorithms_Defs_Basic

open QAlgorithms
open scoped Matrix.Norms.L2Operator

private lemma orderedProd_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    {t : ℕ} (U : Fin t → Matrix.unitaryGroup ι ℂ) :
    orderedProd (fun i => (U i : Matrix ι ι ℂ)) ∈ Matrix.unitaryGroup ι ℂ := by
  apply Submonoid.list_prod_mem
  intro A hA
  simp only [List.mem_reverse, List.mem_ofFn] at hA
  obtain ⟨i, rfl⟩ := hA
  exact (U i).property

private lemma orderedProd_succ {ι : Type*} [Fintype ι] [DecidableEq ι]
    {t : ℕ} (U : Fin (t + 1) → Matrix ι ι ℂ) :
    orderedProd U = U (Fin.last t) * orderedProd (fun i => U i.castSucc) := by
  unfold orderedProd
  rw [List.ofFn_succ']
  simp [List.concat_eq_append]

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ℕ)
    (U V : Fin t → Matrix.unitaryGroup ι ℂ) (ε : ℝ)
    (h : ∀ i, specNorm ((U i : Matrix ι ι ℂ) - (V i : Matrix ι ι ℂ)) ≤ ε) :
    specNorm (orderedProd (fun i => (U i : Matrix ι ι ℂ)) -
      orderedProd (fun i => (V i : Matrix ι ι ℂ))) ≤ t * ε := by
  induction t with
  | zero => simp [orderedProd, specNorm]
  | succ t ih =>
    let P := orderedProd (fun i : Fin t => (U i.castSucc : Matrix ι ι ℂ))
    let Q := orderedProd (fun i : Fin t => (V i.castSucc : Matrix ι ι ℂ))
    have hi : ‖P - Q‖ ≤ (t : ℝ) * ε :=
      ih (fun i => U i.castSucc) (fun i => V i.castSucc) (fun i => h i.castSucc)
    have hQ : Q ∈ unitary (Matrix ι ι ℂ) := orderedProd_unitary (fun i => V i.castSucc)
    have hu := (U (Fin.last t)).property
    rw [orderedProd_succ, orderedProd_succ]
    change ‖(U (Fin.last t) : Matrix ι ι ℂ) * P - (V (Fin.last t) : Matrix ι ι ℂ) * Q‖ ≤ _
    calc
      _ = ‖(U (Fin.last t) : Matrix ι ι ℂ) * (P - Q) +
          ((U (Fin.last t) : Matrix ι ι ℂ) - (V (Fin.last t) : Matrix ι ι ℂ)) * Q‖ := by
        congr 1
        noncomm_ring
      _ ≤ ‖(U (Fin.last t) : Matrix ι ι ℂ) * (P - Q)‖ +
          ‖((U (Fin.last t) : Matrix ι ι ℂ) - (V (Fin.last t) : Matrix ι ι ℂ)) * Q‖ := norm_add_le _ _
      _ = ‖P - Q‖ + ‖(U (Fin.last t) : Matrix ι ι ℂ) - (V (Fin.last t) : Matrix ι ι ℂ)‖ := by
        rw [CStarRing.norm_mul_mem_unitary _ hQ, CStarRing.norm_mem_unitary_mul _ hu]
      _ ≤ (t : ℝ) * ε + ε := add_le_add hi (h (Fin.last t))
      _ = (↑(t + 1) : ℝ) * ε := by push_cast; ring
