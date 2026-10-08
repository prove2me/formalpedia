-- Prove2me | solution 1 for TwiceRegMDP.RobustReg.robust_counterpart
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T12:32:57.835841+00:00
-- url     : https://prove2.me/submissions/31dbe35b-8ee7-484c-ba25-d8965652ce3d

import Mathlib
import Definitions.Def_TwiceRegMDP_RobustReg_MDP
import Definitions.Def_TwiceRegMDP_RobustReg_Robust

set_option autoImplicit false

namespace A889RC

open TwiceRegMDP.RobustReg

/-- On a nonempty compact set the support function is attained and is an upper bound. -/
theorem supportFn_attained {ι : Type} [Fintype ι] (C : Set (ι → ℝ)) (hne : C.Nonempty)
    (hc : IsCompact C) (y : ι → ℝ) :
    ∃ a ∈ C, (∑ i, a i * y i) = supportFn C y ∧ ∀ b ∈ C, (∑ i, b i * y i) ≤ supportFn C y := by
  have hcont : Continuous (fun a : ι → ℝ => ∑ i, a i * y i) := by fun_prop
  obtain ⟨a, ha, hmax⟩ := hc.exists_isMaxOn hne hcont.continuousOn
  have hG : IsGreatest ((fun a : ι → ℝ => ∑ i, a i * y i) '' C) (∑ i, a i * y i) := by
    refine ⟨⟨a, ha, rfl⟩, ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    exact hmax hb
  have hs : supportFn C y = ∑ i, a i * y i := hG.csSup_eq
  refine ⟨a, ha, hs.symm, ?_⟩
  intro b hb
  rw [hs]; exact hmax hb

theorem value_eq {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (γ : ℝ) (P₀ : S → A → S → ℝ) (r₀ : S → A → ℝ)
    (π : S → A → ℝ) (v : S → ℝ) (s : S) (Pp : S → S × A → ℝ) (rp : S → A → ℝ) :
    v s - rewardPi π (fun s a => r₀ s a + rp s a) s
        - γ * transPi π (fun s a s' => P₀ s a s' + Pp s (s', a)) v s
      = (∑ x, Pp s x * (-(γ • vDotPi v π s)) x) + (∑ a, rp s a * (-(π s)) a)
        + v s - evalOp γ P₀ r₀ π v s := by
  simp only [rewardPi, transPi, evalOp, vDotPi,
    FoundationsML.ReinforcementLearning.InducedTransition, Pi.neg_apply, Pi.smul_apply,
    smul_eq_mul, Fintype.sum_prod_type]
  simp only [mul_add, add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun x y => Pp s (x, y) * -(γ * (v x * π s y)))]
  have h1 : ∀ x : S, ∀ a : A, Pp s (x, a) * -(γ * (v x * π s a))
      = -(γ * (π s a * Pp s (x, a) * v x)) := fun x a => by ring
  simp only [h1, Finset.sum_neg_distrib]
  have h2 : ∀ a : A, rp s a * -π s a = -(π s a * rp s a) := fun a => by ring
  simp only [h2, Finset.sum_neg_distrib]
  rw [Finset.sum_comm (f := fun x y => γ * (π s y * Pp s (x, y) * v x))]
  ring

end A889RC

open TwiceRegMDP.RobustReg in
theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (γ : ℝ) (P₀ : S → A → S → ℝ) (r₀ : S → A → ℝ)
    (Pset : S → Set (S × A → ℝ)) (hPne : ∀ s, (Pset s).Nonempty) (hPc : ∀ s, IsCompact (Pset s))
    (Rset : S → Set (A → ℝ)) (hRne : ∀ s, (Rset s).Nonempty) (hRc : ∀ s, IsCompact (Rset s))
    (π : S → A → ℝ) (v : S → ℝ) (s : S) :
    IsGreatest
      ((fun m : (S → A → S → ℝ) × (S → A → ℝ) =>
          v s - rewardPi π m.2 s - γ * transPi π m.1 v s) '' rectUncertainty P₀ r₀ Pset Rset)
      (supportFn (Pset s) (-(γ • vDotPi v π s)) + supportFn (Rset s) (-(π s))
        + v s - evalOp γ P₀ r₀ π v s) := by
  obtain ⟨p, hp, hpeq, hpmax⟩ := A889RC.supportFn_attained (Pset s) (hPne s) (hPc s)
    (-(γ • vDotPi v π s))
  obtain ⟨q, hq, hqeq, hqmax⟩ := A889RC.supportFn_attained (Rset s) (hRne s) (hRc s) (-(π s))
  refine ⟨?_, ?_⟩
  · let Pp : S → S × A → ℝ := fun t => if t = s then p else (hPne t).some
    let rp : S → A → ℝ := fun t => if t = s then q else (hRne t).some
    refine ⟨(fun s a s' => P₀ s a s' + Pp s (s', a), fun s a => r₀ s a + rp s a), ?_, ?_⟩
    · refine ⟨Pp, rp, fun t => ?_, rfl⟩
      by_cases ht : t = s
      · subst ht; simp [Pp, rp, hp, hq]
      · simp only [Pp, rp, if_neg ht]; exact ⟨(hPne t).some_mem, (hRne t).some_mem⟩
    · show v s - rewardPi π (fun s a => r₀ s a + rp s a) s
        - γ * transPi π (fun s a s' => P₀ s a s' + Pp s (s', a)) v s = _
      rw [A889RC.value_eq]
      simp only [Pp, rp, if_pos rfl]
      rw [hpeq, hqeq]
  · rintro _ ⟨m, ⟨Pp, rp, hmem, rfl⟩, rfl⟩
    show v s - rewardPi π (fun s a => r₀ s a + rp s a) s
        - γ * transPi π (fun s a s' => P₀ s a s' + Pp s (s', a)) v s ≤ _
    rw [A889RC.value_eq]
    have h1 := hpmax (Pp s) (hmem s).1
    have h2 := hqmax (rp s) (hmem s).2
    linarith
