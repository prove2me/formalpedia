-- Prove2me | solution 1 for VolunteerNotify.exAnte_feasible
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-18T20:07:47.399196+00:00
-- url     : https://prove2.me/submissions/6f5ebedf-510c-4272-b6be-53c7b78619ca

import Mathlib
import Definitions.Def_VolunteerNotify_IsExAnte

open VolunteerNotify

/-- The left-hand side of constraint (2) for row `v` at period `t`, linear in `x`. -/
private noncomputable def load {V S T : ℕ} (I : Instance V S T) (x : Decision V S T) (v : Fin V)
    (t : Fin T) : ℝ :=
  ∑ τ ∈ Finset.Iic t, ∑ s, I.lam s τ * x v s τ * (1 - cdf I.g ((t : ℕ) - (τ : ℕ)))

private lemma load_step {V S T : ℕ} (I : Instance V S T) (x y : Decision V S T) (c : ℝ)
    (v : Fin V) (t : Fin T) : load I (x + c • y) v t = load I x v t + c * load I y v t := by
  unfold load
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem solution {V S T : ℕ} (I : Instance V S T) :
    (∀ x, IsLPSolution I x → x ∈ feasibleSet I) ∧
    (∀ (m : ℕ) (x : Decision V S T), 1 ≤ m → IsFrankWolfeOutput I m x → x ∈ feasibleSet I) ∧
    (∀ x, IsSQSolution I x → x ∈ feasibleSet I) ∧
    (∀ x, IsExAnte I x → x ∈ feasibleSet I) := by
  have hLP : ∀ x, IsLPSolution I x → x ∈ feasibleSet I := fun x hx => hx.1
  have hSQ : ∀ x, IsSQSolution I x → x ∈ feasibleSet I := fun x hx v => (hx v).1
  have hAA : ∀ (m : ℕ) (x : Decision V S T), 1 ≤ m → IsFrankWolfeOutput I m x →
      x ∈ feasibleSet I := by
    intro m x hm ⟨xs, ys, h0, hstep, hxm⟩
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    -- Invariant: after `i ≤ m` steps, every entry lies in `[0, i/m]` and every load is `≤ i/m`.
    have inv : ∀ i ≤ m, (∀ v s t, 0 ≤ xs i v s t ∧ xs i v s t ≤ (i : ℝ) / m) ∧
        ∀ v t, load I (xs i) v t ≤ (i : ℝ) / m := by
      intro i
      induction i with
      | zero =>
        intro _
        refine ⟨fun v s t => ?_, fun v t => ?_⟩
        · simp [h0]
        · simp [load, h0]
      | succ i ih =>
        intro hi
        obtain ⟨hy, -, hxs⟩ := hstep i (by omega)
        obtain ⟨ih1, ih2⟩ := ih (by omega)
        have hc : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
        have hcast : ((i + 1 : ℕ) : ℝ) / m = (i : ℝ) / m + 1 / m := by push_cast; ring
        rw [hxs, hcast]
        refine ⟨fun v s t => ?_, fun v t => ?_⟩
        · obtain ⟨a1, a2⟩ := ih1 v s t
          obtain ⟨b1, b2⟩ := (hy v).1 s t
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          constructor
          · positivity
          · have : 1 / (m : ℝ) * ys (i + 1) v s t ≤ 1 / m * 1 := mul_le_mul_of_nonneg_left b2 hc
            linarith
        · rw [load_step]
          have h1 := ih2 v t
          have h2 : load I (ys (i + 1)) v t ≤ 1 := (hy v).2 t
          have : 1 / (m : ℝ) * load I (ys (i + 1)) v t ≤ 1 / m * 1 :=
            mul_le_mul_of_nonneg_left h2 hc
          linarith
    obtain ⟨h1, h2⟩ := inv m le_rfl
    have hmm : (m : ℝ) / m = 1 := div_self hmpos.ne'
    rw [hmm] at h1 h2
    subst hxm
    exact fun v => ⟨fun s t => h1 v s t, fun t => h2 v t⟩
  refine ⟨hLP, hAA, hSQ, ?_⟩
  rintro x ⟨xLP, xAA, xSQ, m, hm, hl, ha, hs, hx, -⟩
  rcases hx with rfl | rfl | rfl
  · exact hLP _ hl
  · exact hAA m _ hm ha
  · exact hSQ _ hs
