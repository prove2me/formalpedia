-- Prove2me | solution 1 for SDDPConv.Doasa.monotonicity
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T02:16:29.598061+00:00
-- url     : https://prove2.me/submissions/877a613c-040f-493b-8ce2-1dbceff8edff

import Mathlib
import Definitions.Def_SDDPConv_Doasa_Model
import Definitions.Def_SDDPConv_Doasa_Cuts
import Definitions.Def_SDDPConv_Doasa_Run

open SDDPConv.Doasa Matrix

private theorem ap_mono (I : Instance) (t : ℕ) (h : Fin (I.m t) → ℝ)
    (C E : Set (Cut I t)) (hCE : C ⊆ E) (hC : C.Nonempty) (hE : E.Finite)
    (hf : (Feas I t h).Nonempty) (hb : Bornology.IsBounded (Feas I t h)) :
    apVal I t C h ≤ apVal I t E h := by
  classical
  have hclosed : IsClosed (Feas I t h) := by
    exact (isClosed_le continuous_const continuous_id).inter
      (isClosed_eq (by fun_prop) continuous_const)
  have hcompact : IsCompact (Feas I t h) :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨hclosed, hb⟩
  obtain ⟨a, ha⟩ := hC
  have hcont : Continuous (fun y : Fin (I.n t) → ℝ => I.c t ⬝ᵥ y + a.eval I y) := by
    unfold Cut.eval
    fun_prop
  obtain ⟨b, hbl⟩ := hcompact.bddBelow_image hcont.continuousOn
  have lower : BddBelow {v | ∃ y ∈ Feas I t h, ∃ θ : ℝ,
      (∀ a ∈ C, a.eval I y ≤ θ) ∧ v = I.c t ⬝ᵥ y + θ} := by
    refine ⟨b, ?_⟩
    rintro v ⟨y, hy, θ, hθ, rfl⟩
    exact le_trans (hbl ⟨y, hy, rfl⟩) (add_le_add_right (hθ a ha) _)
  have nonempty : {v | ∃ y ∈ Feas I t h, ∃ θ : ℝ,
      (∀ a ∈ E, a.eval I y ≤ θ) ∧ v = I.c t ⬝ᵥ y + θ}.Nonempty := by
    obtain ⟨y, hy⟩ := hf
    obtain ⟨θ, hθ⟩ := (hE.image (fun a => a.eval I y)).bddAbove
    exact ⟨_, y, hy, θ, (fun a ha => hθ ⟨a, ha, rfl⟩), rfl⟩
  exact csInf_le_csInf lower nonempty (by
    rintro v ⟨y, hy, θ, hθ, hv⟩
    exact ⟨y, hy, θ, (fun a ha => hθ a (hCE ha)), hv⟩)



/-- §2, p. 4: since cuts are only added, the optimal values of the approximate problems are
nondecreasing from one iteration to the next, at every reachable state and outcome. -/
theorem solution (I : Instance) (hA4 : A4 I) (L : ℕ → ℝ) (sol : Oracle I)
    (F : ℕ → List (Scen I)) (S : ℕ → Scen I → (t : ℕ) → Finset (Fin (I.q t)))
    (cuts : ℕ → (t : ℕ) → List (Cut I t)) (D : ℕ → (t : ℕ) → Set (Dual I t))
    (hrun : IsBatchRun I L sol F S cuts D) (k : ℕ) :
    apVal I 1 (cutset I cuts k 1) I.b₁ ≤ apVal I 1 (cutset I cuts (k + 1) 1) I.b₁ ∧
      ∀ s, 1 ≤ s → s + 1 ≤ I.T → ∀ x ∈ Reach I s, ∀ i : Fin (I.q (s + 1)),
        apVal I (s + 1) (cutset I cuts k (s + 1)) (rhs I s x i) ≤
          apVal I (s + 1) (cutset I cuts (k + 1) (s + 1)) (rhs I s x i) := by
  classical
  have hsub : ∀ k t, cutset I cuts k t ⊆ cutset I cuts (k+1) t := by
    intro k t a ha
    have hstep := hrun.2.2.2 k t
    by_cases ht : 1 ≤ t ∧ t+1 ≤ I.T
    · rw [if_pos ht] at hstep
      rcases hstep.2 with h | h
      · simpa [cutset, h.2] using ha
      · obtain ⟨d, hd, he⟩ := h.2
        simp only [cutset, Set.mem_setOf_eq] at ha ⊢
        rw [he]
        exact List.mem_append_left _ ha
    · rw [if_neg ht] at hstep
      simpa [cutset, hstep.2] using ha
  have hinit : ∀ k t, initCut I L t ∈ cutset I cuts k t := by
    intro k t
    induction k with
    | zero => simp [cutset, hrun.1 t]
    | succ k ih => exact hsub k t ih
  have hfinite : ∀ k t, (cutset I cuts k t).Finite := by
    intro k t
    exact List.finite_toSet _
  constructor
  · exact ap_mono I 1 I.b₁ _ _ (hsub k 1) ⟨_, hinit k 1⟩ (hfinite _ _)
      hA4.1 hA4.2.1
  · intro s hs hsT x hx i
    obtain ⟨hne, hb⟩ := hA4.2.2 s hs hsT x hx i
    exact ap_mono I (s+1) (rhs I s x i) _ _ (hsub k (s+1))
      ⟨_, hinit k (s+1)⟩ (hfinite _ _) hne hb




#print axioms solution
