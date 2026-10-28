-- Prove2me | solution 1 for QMaxCutBeyond.TwoQubit.eq_26
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T22:12:18.214631+00:00
-- url     : https://prove2.me/submissions/95ea1d29-3f56-45fd-a47d-896725dfc42e

import Mathlib
import Definitions.Def_QMaxCutBeyond_TwoQubit_Setting

open Matrix QMaxCutBeyond.TwoQubit

namespace QMB26Aux

lemma onSite_mul_diag {n : ℕ} (i j : Fin n) (hij : i ≠ j) (σ τ : Matrix (Fin 2) (Fin 2) ℂ)
    (s : Config n) : (onSite i σ * onSite j τ) s s = σ (s i) (s i) * τ (s j) (s j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single s]
  · simp [onSite]
  · intro y _ hy
    obtain ⟨k, hk⟩ : ∃ k, y k ≠ s k := by
      by_contra h; push_neg at h; exact hy (funext h)
    simp only [onSite]
    by_cases hki : k = i
    · subst hki
      have : ¬ ∀ l, l ≠ j → y l = s l := fun h => hk (h k hij)
      rw [if_neg this]; simp
    · have : ¬ ∀ l, l ≠ i → s l = y l := fun h => hk (h k hki).symm
      rw [if_neg this]; simp
  · simp

lemma edgeTerm_diag {n : ℕ} (i j : Fin n) (hij : i ≠ j) (s : Config n) :
    edgeTerm i j s s = if s i = s j then 0 else 1 := by
  simp only [edgeTerm, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply_eq,
    onSite_mul_diag i j hij, smul_eq_mul]
  simp only [pauliX, pauliY, pauliZ]
  generalize s i = a
  generalize s j = b
  fin_cases a <;> fin_cases b <;> norm_num

end QMB26Aux

open QMB26Aux

theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) (hw : ∀ e, 0 ≤ w e)
    (F : Finset (Sym2 (Fin n))) (hFG : F ⊆ G.edgeFinset)
    (hF : (SimpleGraph.fromEdgeSet (F : Set (Sym2 (Fin n)))).IsAcyclic) :
    ∃ s : Config n, ∑ e ∈ F, w e ≤ energy (hamiltonian G w) (basisState s) := by
  obtain ⟨C⟩ := hF.colorable_two
  refine ⟨fun i => C i, ?_⟩
  set s : Config n := fun i => C i
  have hcut : ∀ a b, s(a, b) ∈ F → a ≠ b → s a ≠ s b := by
    intro a b hab hne
    exact C.valid (by simp [SimpleGraph.fromEdgeSet_adj, hab, hne])
  have hE : energy (hamiltonian G w) (basisState s) =
      ∑ p : Fin n × Fin n, if p.1 < p.2 ∧ G.Adj p.1 p.2 then
        w s(p.1, p.2) * (if s p.1 = s p.2 then 0 else 1) else 0 := by
    have hb : star (basisState s) ⬝ᵥ (hamiltonian G w *ᵥ basisState s) =
        hamiltonian G w s s := by
      simp [basisState, dotProduct, mulVec]
    rw [energy, hb, Fintype.sum_prod_type]
    simp only [hamiltonian, Matrix.sum_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h : i < j ∧ G.Adj i j
    · rw [if_pos h, if_pos h, Matrix.smul_apply, edgeTerm_diag i j (ne_of_lt h.1)]
      by_cases hs : s i = s j
      · rw [if_pos hs, if_pos hs]; simp
      · rw [if_neg hs, if_neg hs]; simp
    · rw [if_neg h, if_neg h]; simp [Matrix.zero_apply]
  rw [hE]
  set P := Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ s(p.1, p.2) ∈ F)
  have hFP : ∑ e ∈ F, w e = ∑ p ∈ P, w s(p.1, p.2) := by
    symm
    refine Finset.sum_bij (fun p _ => s(p.1, p.2)) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro p hp; simp only [P, Finset.mem_filter] at hp; exact hp.2.2
    · rintro ⟨a, b⟩ hp ⟨c, d⟩ hq h
      simp only [P, Finset.mem_filter] at hp hq
      rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only at h1 h2; rw [h1, h2]
      · simp only at h1 h2 hp hq; subst h1 h2; exact absurd (hp.2.1.trans hq.2.1) (lt_irrefl _)
    · intro e he
      induction e using Sym2.ind with
      | _ a b =>
        have hab : a ≠ b := by
          have := hFG he
          rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this
          exact this.ne
        rcases lt_or_gt_of_ne hab with h | h
        · exact ⟨(a, b), by simp [P, h, he], rfl⟩
        · exact ⟨(b, a), by simp [P, h, Sym2.eq_swap, he], Sym2.eq_swap⟩
  rw [hFP]
  calc ∑ p ∈ P, w s(p.1, p.2)
      = ∑ p ∈ P, (if p.1 < p.2 ∧ G.Adj p.1 p.2 then
          w s(p.1, p.2) * (if s p.1 = s p.2 then 0 else 1) else 0) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        simp only [P, Finset.mem_filter] at hp
        have hadj : G.Adj p.1 p.2 := by
          have := hFG hp.2.2
          rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this
        rw [if_pos ⟨hp.2.1, hadj⟩, if_neg (hcut _ _ hp.2.2 (ne_of_lt hp.2.1)), mul_one]
    _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro p _ _
        split_ifs <;> simp [hw]
