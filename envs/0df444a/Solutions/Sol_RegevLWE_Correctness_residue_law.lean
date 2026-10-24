-- Prove2me | solution 1 for RegevLWE.Correctness.residue_law
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T14:01:59.120525+00:00
-- url     : https://prove2.me/submissions/205a4ce5-015d-46e7-951a-d295ec5480bc

import Mathlib
import Definitions.Def_RegevLWE_Correctness_Cryptosystem
open scoped BigOperators
open RegevLWE.Correctness
namespace LWEWork
lemma iid_succ {p m : ℕ} [NeZero p] (χ : PMF (ZMod p)) :
    iidPMF χ (m+1) = χ.bind (fun x => (iidPMF χ m).map (Fin.cons x)) := by
  classical
  apply PMF.ext
  intro e
  have heq (x : ZMod p) (t : Fin m → ZMod p) :
      e = Fin.cons x t ↔ x = e 0 ∧ t = Fin.tail e := by
    constructor
    · intro h
      subst e
      simp
    · rintro ⟨rfl, rfl⟩
      simp
  simp only [iidPMF, PMF.ofFintype_apply, PMF.bind_apply, PMF.map_apply, heq]
  simp [Fin.prod_univ_succ, Fin.tail, ite_and]

lemma convPow_succ_left {p : ℕ} [NeZero p] (χ : PMF (ZMod p)) (k : ℕ) :
    convPow χ (k+1) = χ.bind (fun y => (convPow χ k).map (fun x => y+x)) := by
  simp only [convPow, PMF.map, Function.comp_def]
  rw [PMF.bind_comm]
  simp only [add_comm]

lemma sum_cons_subset {p m : ℕ} [NeZero p] (S : Finset (Fin (m+1)))
    (x : ZMod p) (t : Fin m → ZMod p) :
    (∑ i ∈ S, Fin.cons x t i) = (if 0 ∈ S then x else 0) +
      ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.succ ∈ S), t i := by
  classical
  calc
    _ = ∑ i : Fin (m+1), if i ∈ S then Fin.cons x t i else 0 := by simp
    _ = _ := by rw [Fin.sum_univ_succ]; simp [Finset.sum_filter]

lemma card_subset_succ {m : ℕ} (S : Finset (Fin (m+1))) :
    S.card = (if 0 ∈ S then 1 else 0) +
      (Finset.univ.filter (fun i : Fin m => i.succ ∈ S)).card := by
  classical
  calc
    _ = ∑ i : Fin (m+1), if i ∈ S then 1 else 0 := by simp
    _ = _ := by rw [Fin.sum_univ_succ]; simp
end LWEWork

theorem solution {p : ℕ} [NeZero p] {m : ℕ} (χ : PMF (ZMod p))
    (S : Finset (Fin m)) :
    (iidPMF χ m).map (fun e => ∑ i ∈ S, e i) = convPow χ S.card := by
  classical
  induction m with
  | zero =>
    have hS : S = ∅ := Subsingleton.elim _ _
    subst S
    simpa [convPow, Function.const_def] using
      (PMF.map_const (iidPMF χ 0) (0 : ZMod p))
  | succ m ih =>
    let T : Finset (Fin m) := Finset.univ.filter (fun i => i.succ ∈ S)
    have hs (x : ZMod p) :
        (fun e => ∑ i ∈ S, Fin.cons x e i) =
        (fun y => (if 0 ∈ S then x else 0) + y) ∘ (fun e => ∑ i ∈ T, e i) := by
      funext e
      exact LWEWork.sum_cons_subset S x e
    rw [LWEWork.iid_succ, PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def]
    change (χ.bind (fun x => (iidPMF χ m).map (fun e => ∑ i ∈ S, Fin.cons x e i))) = _
    simp_rw [hs, ← PMF.map_comp, ih T]
    have hc := LWEWork.card_subset_succ S
    change S.card = (if 0 ∈ S then 1 else 0) + T.card at hc
    by_cases h0 : (0 : Fin (m+1)) ∈ S
    · simp only [h0, ↓reduceIte] at hc ⊢
      rw [hc, Nat.add_comm, LWEWork.convPow_succ_left]
    · simp only [h0, ↓reduceIte, zero_add] at hc ⊢
      rw [PMF.bind_const, hc]
      exact PMF.map_id _
