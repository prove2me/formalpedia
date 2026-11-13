-- Prove2me | solution 1 for RestrictedAP.Counting.claim_5_14
-- status  : ACCEPTED   (disprove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:09:01.310916+00:00
-- url     : https://prove2.me/submissions/17075d94-219c-43b6-888b-1d1a610cdbc1

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions
import Definitions.Def_RestrictedAP_Counting_Resilience

section
namespace RestrictedAP.Counting.Dev.C514

/-- uniform distribution on `Bool^3`. -/
noncomputable def mu8 : Bool × Bool × Bool → ℝ := fun _ => 1 / 8

noncomputable def nuH : Bool → ℝ := fun _ => 1 / 2

theorem sum_fun1 {X : Type} [Fintype X] (F : (Fin 1 → X) → ℝ) :
    ∑ x : Fin 1 → X, F x = ∑ b : X, F (fun _ => b) := by
  apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) X)
  intro x
  congr 1
  funext i
  simp [Fin.fin_one_eq_zero i]

theorem mu8_isDist : IsDist mu8 := by
  refine ⟨fun _ => by simp [mu8], ?_⟩
  simp [mu8]

theorem mu8_marg (i : Fin 3) : marginal mu8 i = nuH := by
  funext a
  fin_cases i <;> simp [marginal, coord3, mu8, nuH, Fintype.sum_prod_type]
  all_goals (cases a <;> norm_num)

theorem mu8_noemb : ¬ DistHasEmbedding ℤ mu8 := by
  rintro ⟨σ, γ, φ, hnc, h⟩
  have h' : ∀ x y z, σ x + γ y + φ z = 0 := fun x y z => h (x, y, z) (by simp [supp, mu8])
  apply hnc
  refine ⟨fun a a' => ?_, fun b b' => ?_, fun c c' => ?_⟩
  · have := h' a true true; have := h' a' true true; linarith
  · have := h' true b true; have := h' true b' true; linarith
  · have := h' true true c; have := h' true true c'; linarith

theorem delta1_mu8 (g : (Fin 1 → Bool) → ℝ) :
    Delta1 mu8 g = (1 / 8) * (g (fun _ => false) + g (fun _ => true)) ^ 3 := by
  unfold Delta1 tensorPow
  rw [sum_fun1]
  simp [mu8, Fintype.sum_prod_type]
  ring

theorem expect_nuH (g : (Fin 1 → Bool) → ℝ) :
    expect (tensorPow nuH 1) g = (g (fun _ => false) + g (fun _ => true)) / 2 := by
  unfold expect tensorPow
  rw [sum_fun1]
  simp [nuH]
  ring


noncomputable def dlt : ℕ → ℝ → ℝ := fun _ η => if η = 0 then 0 else if η = 1 then 1 else 2 * 8 ^ 32

theorem resilient_const (g : (Fin 1 → Bool) → ℝ) (h01 : ∀ x, g x = 0 ∨ g x = 1)
    (hr : Resilient nuH 1 (1 / 2) g) : g (fun _ => false) = g (fun _ => true) := by
  have key : ∀ v x : Fin 1 → Bool,
      (fun i => if i ∈ ({0} : Finset (Fin 1)) then v i else x i) = v := by
    intro v x; funext i; simp [Fin.fin_one_eq_zero i]
  have h1 := hr {0} (by simp) (fun _ => false)
  have h2 := hr {0} (by simp) (fun _ => true)
  simp only [key, expect_nuH] at h1 h2
  have e1 := h01 (fun _ => false)
  have e2 := h01 (fun _ => true)
  rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2
  · rw [e1, e2]
  · rw [e1, e2] at h1 h2; first | (norm_num at h1; done) | (norm_num at h2; done)
  · rw [e1, e2] at h1 h2; first | (norm_num at h1; done) | (norm_num at h2; done)
  · rw [e1, e2]

theorem claim_5_14_false : ¬ (∀ (Sig : Type) [Fintype Sig] [DecidableEq Sig]
    (μ : Sig × Sig × Sig → ℝ) (ν : Sig → ℝ) (_hμ : IsDist μ)
    (_hmarg : ∀ i : Fin 3, marginal μ i = ν) (_hdiag : ∀ x : Sig, μ (x, x, x) ≠ 0)
    (_hemb : ¬ DistHasEmbedding ℤ μ) (α : ℝ) (_hα : IsMinAtom μ α)
    (n B : ℕ) (δ' : ℕ → ℝ → ℝ)
    (_hyp : ∀ g : (Fin n → Sig) → ℝ, (∀ x, g x = 0 ∨ g x = 1) → Resilient ν B (1 / 2) g →
      δ' B (expect (tensorPow ν n) g) ≤ Delta1 μ g)
    (f : (Fin n → Sig) → ℝ) (_hf : ∀ x, f x = 0 ∨ f x = 1)
    (_hδ : 0 < expect (tensorPow ν n) f),
    α ^ (2 * (B : ℝ) / (expect (tensorPow ν n) f * α ^ B)) *
        δ' B (expect (tensorPow ν n) f) ≤ Delta1 μ f) := by
  intro H
  have hα : IsMinAtom mu8 (1 / 8) :=
    ⟨by norm_num, fun x _ => by simp [mu8], ⟨(true, true, true), by simp [mu8]⟩⟩
  have hyp : ∀ g : (Fin 1 → Bool) → ℝ, (∀ x, g x = 0 ∨ g x = 1) → Resilient nuH 1 (1 / 2) g →
      dlt 1 (expect (tensorPow nuH 1) g) ≤ Delta1 mu8 g := by
    intro g h01 hr
    have hc := resilient_const g h01 hr
    rw [expect_nuH, delta1_mu8, ← hc]
    rcases h01 (fun _ => false) with e | e <;> rw [e] <;> simp [dlt] <;> norm_num
  set f : (Fin 1 → Bool) → ℝ := fun x => if x 0 = false then 1 else 0 with hf
  have hef : expect (tensorPow nuH 1) f = 1 / 2 := by
    rw [expect_nuH]; simp [hf]
  have := H Bool mu8 nuH mu8_isDist mu8_marg (fun x => by simp [mu8]) mu8_noemb (1 / 8) hα 1 1 dlt
    hyp f (fun x => by simp only [hf]; split_ifs <;> simp) (by rw [hef]; norm_num)
  rw [hef, delta1_mu8] at this
  have h32 : (2 * ((1 : ℕ) : ℝ) / (1 / 2 * (1 / 8 : ℝ) ^ (1 : ℕ))) = (32 : ℕ) := by norm_num
  rw [h32, Real.rpow_natCast] at this
  simp [hf, dlt] at this
  norm_num at this

end RestrictedAP.Counting.Dev.C514
end
theorem solution : type_of% @RestrictedAP.Counting.Dev.C514.claim_5_14_false := @RestrictedAP.Counting.Dev.C514.claim_5_14_false
