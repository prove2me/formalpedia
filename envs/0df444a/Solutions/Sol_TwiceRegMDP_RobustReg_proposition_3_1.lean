-- Prove2me | solution 1 for TwiceRegMDP.RobustReg.proposition_3_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T11:04:14.872524+00:00
-- url     : https://prove2.me/submissions/0b690cb6-c58d-4196-9364-a2ec76b81d11

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_TwiceRegMDP_RobustReg_MDP
import Definitions.Def_TwiceRegMDP_RobustReg_Robust



namespace TwiceRegMDP.RobustReg

open FoundationsML.ReinforcementLearning

theorem trr_abstract_cmp {S : Type} [Fintype S] (T : (S → ℝ) → (S → ℝ)) (γ : ℝ) (hγ1 : γ < 1)
    (hmono : Monotone T)
    (hshift : ∀ v : S → ℝ, ∀ c : ℝ, 0 ≤ c → T (fun s => v s + c) ≤ fun s => T v s + γ * c)
    (v w : S → ℝ) (hv : T v = v) (hw : w ≤ T w) : w ≤ v := by
  rcases isEmpty_or_nonempty S with hS | hS
  · intro s; exact (IsEmpty.false s).elim
  obtain ⟨s0, hs0⟩ := Finite.exists_max (fun s => w s - v s)
  by_contra hcon
  have hd : 0 < w s0 - v s0 := by
    by_contra h
    push_neg at h
    apply hcon
    intro s
    have := hs0 s
    skip
    linarith
  have h1 : w ≤ fun s => v s + (w s0 - v s0) := by
    intro s; have := hs0 s; linarith
  have h2 := le_trans hw (le_trans (hmono h1) (hshift v _ hd.le))
  have h3 := h2 s0
  simp only [hv] at h3
  nlinarith

theorem trr_abstract_exists {S : Type} [Fintype S] (T : (S → ℝ) → (S → ℝ)) (γ : ℝ) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (hmono : Monotone T)
    (hshift : ∀ v : S → ℝ, ∀ c : ℝ, 0 ≤ c → T (fun s => v s + c) ≤ fun s => T v s + γ * c) :
    ∃ v, T v = v := by
  have hlip : ∀ x y : S → ℝ, dist (T x) (T y) ≤ γ * dist x y := by
    intro x y
    have hd := dist_nonneg (x := x) (y := y)
    have hxy : x ≤ fun s => y s + dist x y := by
      intro s
      have := dist_le_pi_dist x y s
      rw [Real.dist_eq] at this
      linarith [le_abs_self (x s - y s)]
    have hyx : y ≤ fun s => x s + dist x y := by
      intro s
      have := dist_le_pi_dist x y s
      rw [Real.dist_eq] at this
      linarith [neg_abs_le (x s - y s)]
    have h1 := le_trans (hmono hxy) (hshift y _ hd)
    have h2 := le_trans (hmono hyx) (hshift x _ hd)
    refine (dist_pi_le_iff (mul_nonneg hγ0 hd)).2 (fun s => ?_)
    rw [Real.dist_eq, abs_le]
    have e1 := h1 s
    have e2 := h2 s
    simp only at e1 e2
    constructor <;> linarith
  let K : NNReal := ⟨γ, hγ0⟩
  have hK : K < 1 := by
    rw [← NNReal.coe_lt_coe]
    exact hγ1
  have hc : ContractingWith K T :=
    ⟨hK, LipschitzWith.of_dist_le_mul (fun x y => by exact hlip x y)⟩
  exact ⟨ContractingWith.fixedPoint T hc, hc.fixedPoint_isFixedPt⟩

theorem trr_abstract_opt {S : Type} [Fintype S] (T : (S → ℝ) → (S → ℝ)) (γ : ℝ) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (hmono : Monotone T)
    (hshift : ∀ v : S → ℝ, ∀ c : ℝ, 0 ≤ c → T (fun s => v s + c) ≤ fun s => T v s + γ * c)
    (μ₀ : S → ℝ) (hμ₀pos : ∀ s, 0 < μ₀ s) (F : Set (S → ℝ))
    (hF1 : ∀ v, T v = v → v ∈ F) (hF2 : ∀ w ∈ F, w ≤ T w) :
    (∃! v, T v = v) ∧ ∀ v, T v = v → IsOptimalSolution μ₀ F v := by
  have cmp := trr_abstract_cmp T γ hγ1 hmono hshift
  refine ⟨?_, ?_⟩
  · obtain ⟨v, hv⟩ := trr_abstract_exists T γ hγ0 hγ1 hmono hshift
    exact ⟨v, hv, fun u hu =>
      le_antisymm (cmp v u hv (le_of_eq hu.symm)) (cmp u v hu (le_of_eq hv.symm))⟩
  · intro v hv
    refine ⟨hF1 v hv, fun w hw => ?_, fun w hw heq => ?_⟩
    · have := cmp v w hv (hF2 w hw)
      unfold pairing
      exact Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_right (this s) (hμ₀pos s).le)
    · have hle := cmp v w hv (hF2 w hw)
      unfold pairing at heq
      have h0 : ∑ s, (v s - w s) * μ₀ s = 0 := by
        simp only [sub_mul, Finset.sum_sub_distrib]; linarith
      rw [Finset.sum_eq_zero_iff_of_nonneg
        (fun s _ => mul_nonneg (sub_nonneg.2 (hle s)) (hμ₀pos s).le)] at h0
      funext s
      have := h0 s (Finset.mem_univ _)
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · exact absurd h (hμ₀pos s).ne'

theorem trr_IT_nonneg {S A : Type} [Fintype S] [Fintype A] (π : S → A → ℝ) (hπ : IsPolicy π)
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (s s' : S) :
    0 ≤ InducedTransition π P s s' :=
  Finset.sum_nonneg (fun a _ => mul_nonneg ((hπ s).1 a) ((hP s a).1 s'))

theorem trr_IT_sum {S A : Type} [Fintype S] [Fintype A] (π : S → A → ℝ) (hπ : IsPolicy π)
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (s : S) :
    ∑ s', InducedTransition π P s s' = 1 := by
  unfold InducedTransition
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, (hP s _).2, mul_one]
  exact (hπ s).2

theorem trr_eval_shift {S A : Type} [Fintype S] [Fintype A] (γ : ℝ) (π : S → A → ℝ)
    (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (r : S → A → ℝ)
    (v : S → ℝ) (c : ℝ) (s : S) :
    evalOp γ P r π (fun s => v s + c) s = evalOp γ P r π v s + γ * c := by
  unfold evalOp transPi
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, trr_IT_sum π hπ P hP s]
  ring

theorem trr_eval_mono {S A : Type} [Fintype S] [Fintype A] (γ : ℝ) (hγ0 : 0 ≤ γ) (π : S → A → ℝ)
    (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (r : S → A → ℝ)
    (u w : S → ℝ) (h : u ≤ w) (s : S) :
    evalOp γ P r π u s ≤ evalOp γ P r π w s := by
  unfold evalOp transPi
  have := Finset.sum_le_sum (fun s' (_ : s' ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (h s') (trr_IT_nonneg π hπ P hP s s'))
  nlinarith

theorem trr_eval_lb {S A : Type} [Fintype S] [Fintype A] (γ : ℝ) (hγ0 : 0 ≤ γ) (π : S → A → ℝ)
    (hπ : IsPolicy π) (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (r : S → A → ℝ)
    (v : S → ℝ) (s : S) (B : ℝ) (hB : ∀ a, -B ≤ r s a) :
    -B - γ * ∑ s', |v s'| ≤ evalOp γ P r π v s := by
  unfold evalOp transPi rewardPi
  have h1 : -B ≤ ∑ a, π s a * r s a := by
    have : ∑ a, π s a * (-B) ≤ ∑ a, π s a * r s a :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hB a) ((hπ s).1 a))
    rw [← Finset.sum_mul, (hπ s).2, one_mul] at this
    exact this
  have h2 : -(∑ s', |v s'|) ≤ ∑ s', InducedTransition π P s s' * v s' := by
    have : ∑ s', InducedTransition π P s s' * (-(∑ s', |v s'|)) ≤
        ∑ s', InducedTransition π P s s' * v s' := by
      refine Finset.sum_le_sum (fun s' _ => mul_le_mul_of_nonneg_left ?_
        (trr_IT_nonneg π hπ P hP s s'))
      have := Finset.single_le_sum (f := fun x => |v x|) (fun x _ => abs_nonneg _)
        (Finset.mem_univ s')
      skip
      linarith [neg_abs_le (v s')]
    rw [← Finset.sum_mul, trr_IT_sum π hπ P hP s, one_mul] at this
    exact this
  nlinarith

theorem trr_robust_props {S A : Type} [Fintype S] [Fintype A] (γ : ℝ) (hγ0 : 0 ≤ γ)
    (U : Set ((S → A → S → ℝ) × (S → A → ℝ))) (π : S → A → ℝ) (hπ : IsPolicy π)
    (hne : U.Nonempty) (hker : ∀ m ∈ U, IsTransitionKernel m.1)
    (hb : ∀ s, ∃ B, ∀ m ∈ U, ∀ a, -B ≤ m.2 s a) :
    (∀ v s, BddBelow ((fun m : (S → A → S → ℝ) × (S → A → ℝ) => evalOp γ m.1 m.2 π v s) '' U)) ∧
    Monotone (robustOp γ U π) ∧
    (∀ v : S → ℝ, ∀ c : ℝ, 0 ≤ c →
      robustOp γ U π (fun s => v s + c) ≤ fun s => robustOp γ U π v s + γ * c) := by
  have bdd : ∀ v s, BddBelow
      ((fun m : (S → A → S → ℝ) × (S → A → ℝ) => evalOp γ m.1 m.2 π v s) '' U) := by
    intro v s
    obtain ⟨B, hB⟩ := hb s
    refine ⟨-B - γ * ∑ s', |v s'|, ?_⟩
    rintro _ ⟨m, hm, rfl⟩
    exact trr_eval_lb γ hγ0 π hπ m.1 (hker m hm) m.2 v s B (hB m hm)
  refine ⟨bdd, ?_, ?_⟩
  · intro u w huw s
    unfold robustOp
    apply le_csInf (hne.image _)
    rintro _ ⟨m, hm, rfl⟩
    exact le_trans (csInf_le (bdd u s) ⟨m, hm, rfl⟩)
      (trr_eval_mono γ hγ0 π hπ m.1 (hker m hm) m.2 u w huw s)
  · intro v c hc s
    show robustOp γ U π (fun s => v s + c) s ≤ robustOp γ U π v s + γ * c
    unfold robustOp
    rw [← sub_le_iff_le_add]
    apply le_csInf (hne.image _)
    rintro _ ⟨m, hm, rfl⟩
    rw [sub_le_iff_le_add]
    calc _ ≤ evalOp γ m.1 m.2 π (fun s => v s + c) s := csInf_le (bdd _ s) ⟨m, hm, rfl⟩
      _ = _ := trr_eval_shift γ π hπ m.1 (hker m hm) m.2 v c s

theorem prop31_core {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    [Nonempty A]
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (μ₀ : S → ℝ) (hμ₀ : μ₀ ∈ stdSimplex ℝ S) (hμ₀pos : ∀ s, 0 < μ₀ s)
    (Pset : Set (S → A → S → ℝ)) (hPne : Pset.Nonempty) (hPc : IsCompact Pset)
    (hPker : ∀ P ∈ Pset, FoundationsML.ReinforcementLearning.IsTransitionKernel P)
    (Rset : Set (S → A → ℝ)) (hRne : Rset.Nonempty) (hRc : IsCompact Rset)
    (π : S → A → ℝ) (hπ : IsPolicy π) :
    (∃! v : S → ℝ, robustOp γ (Pset ×ˢ Rset) π v = v) ∧
    ∀ v : S → ℝ, robustOp γ (Pset ×ˢ Rset) π v = v →
      IsOptimalSolution μ₀ {w : S → ℝ | ∀ m ∈ Pset ×ˢ Rset, w ≤ evalOp γ m.1 m.2 π w} v := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hRc.isBounded
  have hb : ∀ s, ∃ B, ∀ m ∈ Pset ×ˢ Rset, ∀ a, -B ≤ m.2 s a := by
    intro s
    refine ⟨C, fun m hm a => ?_⟩
    have := (norm_le_pi_norm (m.2 s) a).trans ((norm_le_pi_norm m.2 s).trans (hC _ hm.2))
    rw [Real.norm_eq_abs] at this
    linarith [neg_abs_le (m.2 s a)]
  obtain ⟨bdd, hmono, hshift⟩ := trr_robust_props γ hγ0.le (Pset ×ˢ Rset) π hπ
    (hPne.prod hRne) (fun m hm => hPker m.1 hm.1) hb
  refine trr_abstract_opt _ γ hγ0.le hγ1 hmono hshift μ₀ hμ₀pos _ ?_ ?_
  · intro v hv m hm s
    calc v s = robustOp γ (Pset ×ˢ Rset) π v s := by rw [hv]
      _ ≤ _ := csInf_le (bdd v s) ⟨m, hm, rfl⟩
  · intro w hw s
    apply le_csInf ((hPne.prod hRne).image _)
    rintro _ ⟨m, hm, rfl⟩
    exact hw m hm s

end TwiceRegMDP.RobustReg

open TwiceRegMDP.RobustReg


theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    [Nonempty A]
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (μ₀ : S → ℝ) (hμ₀ : μ₀ ∈ stdSimplex ℝ S) (hμ₀pos : ∀ s, 0 < μ₀ s)
    (Pset : Set (S → A → S → ℝ)) (hPne : Pset.Nonempty) (hPc : IsCompact Pset)
    (hPker : ∀ P ∈ Pset, FoundationsML.ReinforcementLearning.IsTransitionKernel P)
    (Rset : Set (S → A → ℝ)) (hRne : Rset.Nonempty) (hRc : IsCompact Rset)
    (π : S → A → ℝ) (hπ : IsPolicy π) :
    (∃! v : S → ℝ, robustOp γ (Pset ×ˢ Rset) π v = v) ∧
    ∀ v : S → ℝ, robustOp γ (Pset ×ˢ Rset) π v = v →
      IsOptimalSolution μ₀ {w : S → ℝ | ∀ m ∈ Pset ×ˢ Rset, w ≤ evalOp γ m.1 m.2 π w} v := by
  exact prop31_core γ hγ0 hγ1 μ₀ hμ₀ hμ₀pos Pset hPne hPc hPker Rset hRne hRc π hπ
