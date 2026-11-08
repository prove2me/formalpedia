-- Prove2me | solution 1 for RankOneBTF.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T04:54:25.233577+00:00
-- url     : https://prove2.me/submissions/b960f645-308f-4c00-ab5f-d57f640fe1a0

import Mathlib
import Definitions.Def_RankOneBTF_lpObjective

open RankOneBTF in
theorem solution {n m l : ℕ} {V : Type*} (R : Set V)
    (Wof : V → Fin n → Fin m → Fin l → ℝ)
    (hbox : ∀ v ∈ R, ∀ i j k, 0 ≤ Wof v i j k ∧ Wof v i j k ≤ 1)
    (xb : Fin n → Bool) (yb : Fin m → Bool) (zb : Fin l → Bool) (vbar : V)
    (hvbar : Wof vbar = realTensor (groundTruth xb yb zb))
    (G G' : BTensor n m l)
    (hmod : ∀ i j k, G' i j k = G i j k ∨ G' i j k = groundTruth xb yb zb i j k)
    (hrec : IsUniqueOptimalOn R (fun v => objW G (Wof v)) vbar) :
    IsUniqueOptimalOn R (fun v => objW G' (Wof v)) vbar := by
  have entry : ∀ v ∈ R, ∀ i j k,
      ((if G' i j k then 1 - Wof vbar i j k else Wof vbar i j k) -
        (if G i j k then 1 - Wof vbar i j k else Wof vbar i j k)) ≤
      ((if G' i j k then 1 - Wof v i j k else Wof v i j k) -
        (if G i j k then 1 - Wof v i j k else Wof v i j k)) := by
    intro v hv i j k
    obtain ⟨h0, h1⟩ := hbox v hv i j k
    rw [hvbar]
    unfold realTensor
    rcases hmod i j k with h | h <;> rw [h]
    · simp
    · cases hT : groundTruth xb yb zb i j k <;> cases hG : G i j k <;> simp <;> linarith
  have hdiff : ∀ v ∈ R, objW G' (Wof vbar) - objW G (Wof vbar) ≤
      objW G' (Wof v) - objW G (Wof v) := by
    intro v hv
    unfold objW
    simp only [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      Finset.sum_le_sum fun k _ => entry v hv i j k
  refine ⟨hrec.1, fun v hv hle => hrec.2 v hv ?_⟩
  have := hdiff v hv
  simp only at hle ⊢
  linarith
