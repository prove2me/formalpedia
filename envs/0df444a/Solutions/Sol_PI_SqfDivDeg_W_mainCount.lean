-- Prove2me | solution 1 for PI.SqfDivDeg.W.mainCount
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:28:48.139904+00:00
-- url     : https://prove2.me/submissions/672042f4-2235-4f1e-9523-92be87202a61

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_MonicFintype
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_FibreNonempty
import Theorems.Thm_PI_SqfDivDeg_W_second_pair
import Theorems.Thm_PI_SqfDivDeg_W_fibre_nonempty
import Theorems.Thm_PI_SqfDivDeg_W_card_Mon
import Theorems.Thm_PI_SqfDivDeg_W_mem_Mon


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Finset
noncomputable section
open PI PI.SqfDivDeg PI.SqfDivDeg.W
namespace PI.SqfDivDeg.W
theorem _root_.solution : MainCount := by
  intro g r _ a har T hT
  classical
  let P := Mon g a ×ˢ Mon g (r - a)
  let F : (ZMod g)[X] → Finset ((ZMod g)[X] × (ZMod g)[X]) :=
    fun f => P.filter (fun p => p.1 * p.2 = f)
  let G : (ZMod g)[X] × (ZMod g)[X] → Prop :=
    fun p => (∃ x : ZMod g, p.1.IsRoot x) ∧ (∃ y : ZMod g, p.2.IsRoot y)
  let b : (ZMod g)[X] × (ZMod g)[X] → ℝ := fun p => if G p then 1 / 2 else 1
  have bnn : ∀ p, 0 ≤ b p := fun p => by simp only [b]; split_ifs <;> norm_num
  have key : ∀ f ∈ T, (1 : ℝ) ≤ ∑ p ∈ F f, b p := by
    intro f hf
    obtain ⟨q, h, hq, hh, hqh⟩ := fibre_nonempty har (hT f hf)
    have hpq : (q, h) ∈ F f := by simp [F, P, hq, hh, hqh]
    by_cases hG : G (q, h)
    · obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hG
      have hs : Squarefree (q * h) := hqh ▸ (hT f hf).2.1
      obtain ⟨m1, m2, d1, d2, e, ne⟩ :=
        second_pair (mem_Mon.mp hq).1 (mem_Mon.mp hh).1 hs hx hy
      have hp' : ((X - C y) * (q /ₘ (X - C x)), (X - C x) * (h /ₘ (X - C y))) ∈ F f := by
        simp only [F, P, mem_filter, mem_product, mem_Mon]
        exact ⟨⟨⟨m1, d1.trans (mem_Mon.mp hq).2⟩, ⟨m2, d2.trans (mem_Mon.mp hh).2⟩⟩,
          e.trans hqh⟩
      have hG' : G ((X - C y) * (q /ₘ (X - C x)), (X - C x) * (h /ₘ (X - C y))) :=
        ⟨⟨y, by simp⟩, ⟨x, by simp⟩⟩
      have hG0 : G (q, h) := ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      have hne : ((X - C y) * (q /ₘ (X - C x)), (X - C x) * (h /ₘ (X - C y))) ≠ (q, h) :=
        fun h' => ne (congrArg Prod.fst h')
      have hsub : ∑ p ∈ ({((X - C y) * (q /ₘ (X - C x)), (X - C x) * (h /ₘ (X - C y))),
          (q, h)} : Finset _), b p ≤ ∑ p ∈ F f, b p := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          rw [mem_insert, mem_singleton] at hp
          rcases hp with rfl | rfl
          · exact hp'
          · exact hpq
        · intro p _ _; exact bnn p
      rw [sum_pair hne] at hsub
      simp only [b, if_pos hG', if_pos hG0] at hsub
      linarith
    · have : b (q, h) ≤ ∑ p ∈ F f, b p :=
        single_le_sum (f := b) (fun p _ => bnn p) hpq
      simp only [b, if_neg hG] at this
      exact this
  have hdisj : Set.PairwiseDisjoint (↑T) F := by
    intro f _ f' _ hff'
    rw [Function.onFun, Finset.disjoint_left]
    intro p hp hp'
    simp only [F, mem_filter] at hp hp'
    exact hff' (hp.2.symm.trans hp'.2)
  have h1 : (T.card : ℝ) ≤ ∑ p ∈ T.biUnion F, b p := by
    rw [sum_biUnion hdisj]
    calc (T.card : ℝ) = ∑ f ∈ T, (1 : ℝ) := by simp
      _ ≤ _ := sum_le_sum key
  have h2 : ∑ p ∈ T.biUnion F, b p ≤ ∑ p ∈ P, b p := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨f, -, hpf⟩ := mem_biUnion.mp hp
      exact (mem_filter.mp hpf).1
    · intro p _ _; exact bnn p
  have h3 : ∑ p ∈ P, b p = (P.card : ℝ) - ((P.filter G).card : ℝ) / 2 := by
    simp only [b]
    rw [sum_ite]
    simp only [sum_const, nsmul_eq_mul]
    have hc := card_filter_add_card_filter_not (s := P) (fun p => G p)
    have h' : ((P.filter G).card : ℝ) + ((P.filter (fun p => ¬ G p)).card : ℝ) = P.card := by
      exact_mod_cast hc
    linarith
  have h4 : P.filter G = Rt g a ×ˢ Rt g (r - a) := by
    ext ⟨q, h⟩
    simp only [P, G, Rt, mem_filter, mem_product]
    tauto
  have h5 : (P.card : ℝ) = (g : ℝ) ^ r := by
    simp only [P, card_product, card_Mon]
    push_cast
    rw [← pow_add]
    congr 1
    omega
  rw [h4, h5, card_product] at h3
  push_cast at h3
  linarith
end PI.SqfDivDeg.W
