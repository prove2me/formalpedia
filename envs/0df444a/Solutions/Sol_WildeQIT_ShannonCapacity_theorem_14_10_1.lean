-- Prove2me | solution 1 for WildeQIT.ShannonCapacity.theorem_14_10_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-13T16:11:18.908762+00:00
-- url     : https://prove2.me/submissions/000708d4-7b86-47b7-ad45-f66b5bbc8524

import Mathlib
import Definitions.Def_WildeQIT_channelCode
import Theorems.Thm_WildeQIT_ShannonCapacity_theorem_14_10_1_direct
import Theorems.Thm_WildeQIT_ShannonCapacity_theorem_14_10_1_converse

set_option autoImplicit false

namespace WildeQIT.ShannonCapacity.Red9e3c6433

open WildeQIT

/-- `t ↦ t log₂ t`. -/
noncomputable def xl (t : ℝ) : ℝ := t * Real.logb 2 t

lemma continuous_xl : Continuous xl := by
  have h : xl = fun t : ℝ => (t * Real.log t) / Real.log 2 := by
    funext t
    simp only [xl, Real.logb, mul_div_assoc]
  rw [h]
  exact Real.continuous_mul_log.div_const _

variable {α β : Type} [Fintype α] [Fintype β]

/-- Conditional entropy as `H(X|Y) = -∑ q log q + ∑ q_Y log q_Y`. -/
lemma condEntropy_eq (q : FinDist (α × β)) :
    condEntropy q = -(∑ x, ∑ y, xl (q.prob (x, y))) + ∑ y, xl (q.snd.prob y) := by
  have hterm : ∀ x y, q.prob (x, y) * Real.logb 2 (q.prob (x, y) / q.snd.prob y)
      = xl (q.prob (x, y)) - q.prob (x, y) * Real.logb 2 (q.snd.prob y) := by
    intro x y
    by_cases h : q.prob (x, y) = 0
    · simp [xl, h]
    · have hpos : 0 < q.prob (x, y) := lt_of_le_of_ne (q.nonneg _) (Ne.symm h)
      have hle : q.prob (x, y) ≤ q.snd.prob y := by
        rw [FinDist.snd_prob]
        exact Finset.single_le_sum (f := fun x' => q.prob (x', y))
          (fun x' _ => q.nonneg (x', y)) (Finset.mem_univ x)
      have hs : q.snd.prob y ≠ 0 := (lt_of_lt_of_le hpos hle).ne'
      rw [Real.logb_div h hs, xl]
      ring
  have hswap : ∑ x, ∑ y, q.prob (x, y) * Real.logb 2 (q.snd.prob y)
      = ∑ y, xl (q.snd.prob y) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_mul, xl, FinDist.snd_prob]
  unfold condEntropy
  simp_rw [hterm, Finset.sum_sub_distrib]
  rw [hswap]
  ring

/-- The mutual information of `p_X N` as an explicit continuous function of `p_X`. -/
noncomputable def F (N : Channel α β) (f : α → ℝ) : ℝ :=
  -(∑ x, xl (f x)) + ∑ x, ∑ y, xl (f x * (N x).prob y) - ∑ y, xl (∑ x, f x * (N x).prob y)

lemma mutualInfo_joint_eq (N : Channel α β) (p : FinDist α) :
    mutualInfo (N.joint p) = F N p.prob := by
  have hfst : (N.joint p).fst.prob = p.prob := by
    funext x
    simp only [FinDist.fst_prob, Channel.joint_prob]
    rw [← Finset.mul_sum, (N x).sum_eq_one, mul_one]
  unfold mutualInfo entropy
  rw [condEntropy_eq]
  simp only [hfst, F, xl, FinDist.snd_prob, Channel.joint_prob]
  ring

lemma continuous_F (N : Channel α β) : Continuous (F N) := by
  unfold F
  have hg := continuous_xl
  refine ((continuous_finset_sum _ fun x _ => hg.comp (continuous_apply x)).neg.add
    (continuous_finset_sum _ fun x _ => continuous_finset_sum _ fun y _ =>
      hg.comp ((continuous_apply x).mul continuous_const))).sub
    (continuous_finset_sum _ fun y _ => hg.comp
      (continuous_finset_sum _ fun x _ => (continuous_apply x).mul continuous_const))

/-- The probability simplex on `α`. -/
def simplex (α : Type) [Fintype α] : Set (α → ℝ) := {f | (∀ x, 0 ≤ f x) ∧ ∑ x, f x = 1}

lemma isCompact_simplex : IsCompact (simplex α) := by
  have hcl : IsClosed (simplex α) := by
    have h1 : IsClosed {f : α → ℝ | ∀ x, 0 ≤ f x} := by
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun x => isClosed_le continuous_const (continuous_apply x)
    have h2 : IsClosed {f : α → ℝ | ∑ x, f x = 1} :=
      isClosed_eq (continuous_finset_sum _ fun x _ => continuous_apply x) continuous_const
    exact h1.inter h2
  refine (isCompact_Icc (a := (0 : α → ℝ)) (b := 1)).of_isClosed_subset hcl ?_
  intro f hf
  refine ⟨fun x => hf.1 x, fun x => ?_⟩
  have := Finset.single_le_sum (f := f) (fun y _ => hf.1 y) (Finset.mem_univ x)
  simpa [hf.2] using this

lemma simplex_nonempty [Nonempty α] : (simplex α).Nonempty := by
  refine ⟨fun _ => 1 / (Fintype.card α : ℝ), fun _ => by positivity, ?_⟩
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- Part 2: the supremum defining `I(𝒩)` is attained. -/
lemma attained [Nonempty α] (N : Channel α β) :
    ∃ p : FinDist α, mutualInfo (N.joint p) = channelMaxMutualInfo N := by
  obtain ⟨f0, hf0, hmax⟩ :=
    isCompact_simplex.exists_isMaxOn simplex_nonempty (continuous_F N).continuousOn
  let p0 : FinDist α := ⟨f0, hf0.1, hf0.2⟩
  refine ⟨p0, ?_⟩
  have hG : IsGreatest {I : ℝ | ∃ p : FinDist α, I = mutualInfo (N.joint p)}
      (mutualInfo (N.joint p0)) := by
    refine ⟨⟨p0, rfl⟩, ?_⟩
    rintro I ⟨p, rfl⟩
    rw [mutualInfo_joint_eq, mutualInfo_joint_eq]
    exact hmax ⟨p.nonneg, p.sum_eq_one⟩
  unfold channelMaxMutualInfo
  exact hG.csSup_eq.symm

end WildeQIT.ShannonCapacity.Red9e3c6433

open WildeQIT WildeQIT.ShannonCapacity in
theorem solution {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [DecidableEq β]
    (N : Channel α β) :
    channelCapacity N = channelMaxMutualInfo N ∧
      ∃ p : FinDist α, mutualInfo (N.joint p) = channelMaxMutualInfo N := by
  refine ⟨?_, WildeQIT.ShannonCapacity.Red9e3c6433.attained N⟩
  unfold channelCapacity
  exact IsGreatest.csSup_eq
    ⟨theorem_14_10_1_direct N, fun R hR => theorem_14_10_1_converse N R hR⟩
