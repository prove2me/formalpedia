-- Prove2me | solution 1 for RobustAgentsCausal.domain_dependence_consequences
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T17:53:47.435452+00:00
-- url     : https://prove2.me/submissions/e0b116a5-3e3e-4fcf-89a5-3b0a837a6693

import Mathlib
import Definitions.Def_RobustAgentsCausal_Basic

open MeasureTheory

namespace RobustAgentsCausal

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ι → ℕ} {A : Type*} [Fintype A] [DecidableEq A]

lemma dd_nonneg (pa : ι → Finset ι) (P : (i : ι) → Cfg k → Fin (k i) → ℝ) (hP : IsCPD pa P) :
    ∀ c, 0 ≤ jointProb P c := fun c =>
  Finset.prod_nonneg fun i _ => (hP i).1 c (c i)

/-- a policy that puts all its mass on a pointwise maximiser is optimal under any nonneg weights -/
lemma dd_opt (S : Finset ι) (μ : Cfg k → ℝ) (hμ : ∀ c, 0 ≤ μ c) (u : A → Cfg k → ℝ)
    (b : Cfg k → A) (hb : ∀ c d, u d c ≤ u (b c) c) (hbS : DependsOnlyOn S b) :
    IsOptimal S μ u (fun c d => if d = b c then 1 else 0) := by
  refine ⟨⟨fun c d => by dsimp only; split_ifs <;> norm_num, fun c => by simp, fun c c' h => ?_⟩, ?_⟩
  · funext d; dsimp only; rw [hbS c c' h]
  · intro π' hπ'
    unfold expUtil
    rw [add_zero]
    refine Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left ?_ (hμ c)
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    calc ∑ d, π' c d * u d c ≤ ∑ d, π' c d * u (b c) c :=
          Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_left (hb c d) (hπ'.1 c d)
      _ = u (b c) c := by rw [← Finset.sum_mul, hπ'.2.1 c, one_mul]

end RobustAgentsCausal

open RobustAgentsCausal in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ι → ℕ)
    (hk : ∀ i, 0 < k i) {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (pa : ι → Finset ι) (hpa : IsAcyclic pa) (paD paU : Finset ι) (uθ : UParam k A paU)
    (hdd : DomainDependent pa paD (utilOf paU uθ)) :
    (¬ ∃ d : A, ∀ c : Cfg k, ∀ d' : A, utilOf paU uθ d' c ≤ utilOf paU uθ d c) ∧
    ((↑paD : Set ι) ⊂ ancU pa paD paU) ∧
    (∃ (c : Cfg k) (d d' : A), utilOf paU uθ d c ≠ utilOf paU uθ d' c) := by
  obtain ⟨P, P', hP, hP', hno⟩ := hdd
  have contra : ∀ b : Cfg k → A, (∀ c d, utilOf paU uθ d c ≤ utilOf paU uθ (b c) c) →
      DependsOnlyOn paD b → False := fun b hb hbS =>
    hno _ (dd_opt paD _ (dd_nonneg pa P hP) _ b hb hbS) (dd_opt paD _ (dd_nonneg pa P' hP') _ b hb hbS)
  have h1 : ¬ ∃ d : A, ∀ c : Cfg k, ∀ d' : A, utilOf paU uθ d' c ≤ utilOf paU uθ d c := by
    rintro ⟨d, hd⟩
    exact contra (fun _ => d) (fun c d' => hd c d') (fun _ _ _ => rfl)
  refine ⟨h1, ?_, ?_⟩
  · rw [Set.ssubset_def]
    refine ⟨fun j hj => ⟨j, Finset.mem_union_right _ hj, Or.inl rfl⟩, fun hsub => ?_⟩
    have hU : ∀ j ∈ paU, j ∈ paD := fun j hj => by
      have := hsub ⟨j, Finset.mem_union_left _ hj, Or.inl rfl⟩
      simpa using this
    have hex : ∀ f : A → ℝ, ∃ d, ∀ d', f d' ≤ f d := fun f => by
      obtain ⟨d, _, hd⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
      exact ⟨d, fun d' => hd d' (Finset.mem_univ _)⟩
    let best : (A → ℝ) → A := fun f => Classical.choose (hex f)
    refine contra (fun c => best (fun d => utilOf paU uθ d c))
      (fun c d => Classical.choose_spec (hex (fun d => utilOf paU uθ d c)) d) ?_
    intro c c' hcc
    have : (fun d => utilOf paU uθ d c) = fun d => utilOf paU uθ d c' := by
      funext d
      simp only [utilOf]
      congr 1
      funext j
      exact hcc j.1 (hU j.1 j.2)
    simp only [this]
  · by_contra hne
    push Not at hne
    obtain ⟨d0⟩ := ‹Nonempty A›
    exact h1 ⟨d0, fun c d' => (hne c d' d0).le⟩
