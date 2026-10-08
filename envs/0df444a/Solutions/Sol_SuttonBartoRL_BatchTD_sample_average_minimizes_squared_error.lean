-- Prove2me | solution 1 for SuttonBartoRL.BatchTD.sample_average_minimizes_squared_error
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:28:13.382809+00:00
-- url     : https://prove2.me/submissions/75f55327-cd43-48af-ba96-ab03f9e4640d

import Mathlib
import Definitions.Def_SuttonBartoRL_BatchTD_Episodes
import Definitions.Def_SuttonBartoRL_BatchTD_BatchUpdating

set_option autoImplicit false

namespace Pa2a98871
open SuttonBartoRL.BatchTD

lemma visitSum_zero {S : Type} [Fintype S] [DecidableEq S] (b : Batch S) (s : S)
    (f : Episode S → ℕ → ℝ) (h : visitCount b s = 0) : visitSum b s f = 0 := by
  unfold visitSum
  unfold visitCount at h
  induction b with
  | nil => simp
  | cons e b ih =>
    simp only [List.map_cons, List.sum_cons] at h ⊢
    have h1 := (Nat.add_eq_zero_iff.mp h).1
    have h2 := (Nat.add_eq_zero_iff.mp h).2
    rw [ih h2, ← Finset.sum_filter, Finset.card_eq_zero.mp h1]
    simp

lemma ep_expand {S : Type} [DecidableEq S] (e : Episode S) (s : S) (g : ℕ → ℝ) (c m : ℝ) :
    (∑ t ∈ Finset.range e.length, if stateAt e t = some s then (g t - c) ^ 2 else 0)
      = (∑ t ∈ Finset.range e.length, if stateAt e t = some s then (g t - m) ^ 2 else 0)
        + 2 * (m - c) * ((∑ t ∈ Finset.range e.length, if stateAt e t = some s then g t else 0)
            - m * (((Finset.range e.length).filter fun t => stateAt e t = some s).card : ℝ))
        + (m - c) ^ 2 * (((Finset.range e.length).filter fun t => stateAt e t = some s).card : ℝ) := by
  rw [← Finset.sum_filter, ← Finset.sum_filter, ← Finset.sum_filter]
  set F := (Finset.range e.length).filter fun t => stateAt e t = some s
  have h : ∀ t ∈ F, (g t - c) ^ 2 = (g t - m) ^ 2 + (2 * (m - c)) * g t
      + (-(2 * (m - c) * m) + (m - c) ^ 2) := by
    intro t _; ring
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  ring

lemma sq_expand {S : Type} [Fintype S] [DecidableEq S] (b : Batch S) (s : S)
    (g : Episode S → ℕ → ℝ) (c m : ℝ) :
    visitSum b s (fun e t => (g e t - c) ^ 2)
      = visitSum b s (fun e t => (g e t - m) ^ 2)
        + 2 * (m - c) * (visitSum b s g - m * (visitCount b s : ℝ))
        + (m - c) ^ 2 * (visitCount b s : ℝ) := by
  unfold visitSum visitCount
  induction b with
  | nil => simp
  | cons e b ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add]
    rw [ih, ep_expand e s (g e) c m]
    ring

lemma stateAt_some {S : Type} (e : Episode S) (t : ℕ) (ht : t < e.length) :
    stateAt e t = some (e[t].1) := by
  simp [stateAt, List.getElem?_eq_getElem ht]

lemma decomp {S : Type} [Fintype S] [DecidableEq S] (γ : ℝ) (b : Batch S) (V : S → ℝ) :
    mcSquaredError γ b V = ∑ s, visitSum b s (fun e t => (ret γ e t - V s) ^ 2) := by
  unfold mcSquaredError visitSum
  induction b with
  | nil => simp
  | cons e b ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro t ht
    rw [stateAt_some e t (Finset.mem_range.mp ht)]
    simp [extV]

end Pa2a98871

open SuttonBartoRL.BatchTD in
theorem solution {S : Type} [Fintype S] [DecidableEq S]
    (b : Batch S) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (V : S → ℝ) :
    mcSquaredError γ b (mcAverage γ b) ≤ mcSquaredError γ b V := by
  rw [Pa2a98871.decomp, Pa2a98871.decomp]
  refine Finset.sum_le_sum ?_
  intro s _
  rw [Pa2a98871.sq_expand b s (fun e t => ret γ e t) (V s) (mcAverage γ b s)]
  have hcross : visitSum b s (fun e t => ret γ e t) - mcAverage γ b s * (visitCount b s : ℝ) = 0 := by
    by_cases hn : visitCount b s = 0
    · rw [Pa2a98871.visitSum_zero b s _ hn, hn]; simp
    · have hn' : (visitCount b s : ℝ) ≠ 0 := by exact_mod_cast hn
      unfold mcAverage
      field_simp
      ring
  rw [hcross]
  have : 0 ≤ (mcAverage γ b s - V s) ^ 2 * (visitCount b s : ℝ) := by positivity
  linarith
