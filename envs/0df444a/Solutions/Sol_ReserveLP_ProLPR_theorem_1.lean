-- Prove2me | solution 1 for ReserveLP.ProLPR.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T09:04:11.548601+00:00
-- url     : https://prove2.me/submissions/da9d273a-cb2e-4764-83e4-3417b92d4f8f

import Mathlib
import Definitions.Def_ReserveLP_ProLPR_Model
import Theorems.Thm_ReserveLP_ProLPR_lemma_5_1
import Theorems.Thm_ReserveLP_ProLPR_lemma_5_2
import Theorems.Thm_ReserveLP_ProLPR_lemma_5_3
import Theorems.Thm_ReserveLP_ProLPR_opt_bound

open ReserveLP.ProLPR Finset

theorem lp_exists {A B : Type} [Fintype A] [Fintype B] [DecidableEq B] (D : DataSet A B) :
    ∃ s q, LPOptimal D s q := by
  classical
  let K : Set ((A → Profile B → ℝ) × (B → ℝ → ℝ)) := (Set.univ.pi fun _ : A => Set.univ.pi fun _ : Profile B => Set.Icc (0:ℝ) 1) ×ˢ
    (Set.univ.pi fun _ : B => Set.univ.pi fun _ : ℝ => Set.Icc (0:ℝ) 1)
  have hK : IsCompact K := by
    apply IsCompact.prod
    · exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
    · exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  let F : Set ((A → Profile B → ℝ) × (B → ℝ → ℝ)) := {x | LPFeasible D x.1 x.2}
  have hF : IsClosed F := by
    simp only [F, LPFeasible, Set.ofPred_and, Set.ofPred_forall]
    repeat' apply IsClosed.inter
    all_goals
      repeat' (apply isClosed_iInter; intro)
    all_goals first
      | exact isClosed_le (by fun_prop) (by fun_prop)
      | exact isClosed_eq (by fun_prop) (by fun_prop)
  have hS : IsCompact (K ∩ F) := hK.inter_right hF
  have h0 : (0 : ℝ) ∈ reserves D := by simp [reserves]
  let x0 : (A → Profile B → ℝ) × (B → ℝ → ℝ) := (fun _ _ => 0, fun _ r => if r = 0 then 1 else 0)
  have hx0 : x0 ∈ K ∩ F := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro a _ p _; simp [x0]
    · intro b _ r _; simp only [x0]; split_ifs <;> simp
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro a p _; simp [x0]
      · intro a; simp [x0]
      · intro a b r _; simp only [x0, sum_const_zero]; split_ifs <;> simp
      · intro b; simp [x0, Finset.sum_ite_eq', h0]
      · intro b r _; simp only [x0]; split_ifs <;> simp
  have hcont : ContinuousOn (fun x : (A → Profile B → ℝ) × (B → ℝ → ℝ) => LPObj D x.1) (K ∩ F) := by
    apply Continuous.continuousOn
    unfold LPObj
    fun_prop
  obtain ⟨x, hxS, hxmax⟩ := hS.exists_isMaxOn ⟨x0, hx0⟩ hcont
  refine ⟨x.1, x.2, hxS.2, ?_⟩
  intro s' q' hfeas
  obtain ⟨hs0, hs1, hQ, hq1, hq0⟩ := hfeas
  let y : (A → Profile B → ℝ) × (B → ℝ → ℝ) := (fun a p => if p ∈ validProfiles D a then s' a p else 0,
    fun b r => if r ∈ reserves D then q' b r else 0)
  have hQsub : ∀ a b r, Qset D a b r ⊆ validProfiles D a := fun a b r => filter_subset _ _
  have hyF : y ∈ F := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a p hp; simp only [y, if_pos hp]; exact hs0 a p hp
    · intro a
      rw [sum_congr rfl (fun p hp => if_pos hp)]; exact hs1 a
    · intro a b r hr
      simp only [y, if_pos hr]
      rw [sum_congr rfl (fun p hp => if_pos (hQsub a b r hp))]; exact hQ a b r hr
    · intro b
      simp only [y]
      rw [sum_congr rfl (fun r hr => if_pos hr)]; exact hq1 b
    · intro b r hr; simp only [y, if_pos hr]; exact hq0 b r hr
  have hyK : y ∈ K := by
    refine ⟨?_, ?_⟩
    · intro a _ p _
      simp only [y]
      split_ifs with hp
      · refine ⟨hs0 a p hp, le_trans ?_ (hs1 a)⟩
        exact single_le_sum (fun p hp => hs0 a p hp) hp
      · simp
    · intro b _ r _
      simp only [y]
      split_ifs with hr
      · refine ⟨hq0 b r hr, ?_⟩
        rw [← hq1 b]
        exact single_le_sum (fun r hr => hq0 b r hr) hr
      · simp
  have := hxmax ⟨hyK, hyF⟩
  simp only [Set.mem_ofPred_eq] at this
  have heq : LPObj D y.1 = LPObj D s' := by
    unfold LPObj
    refine sum_congr rfl fun a _ => sum_congr rfl fun p hp => ?_
    simp only [y, if_pos hp]
  rw [← heq]; exact this

theorem cStar_pos : 0 < cStar := by
  unfold cStar
  have : 1 < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have := Real.exp_pos (Real.sqrt 2 - 2)
  positivity

theorem cOPT_le_cStar {A B : Type} [Fintype A] [Fintype B] [DecidableEq B] (D : DataSet A B) :
    cOPT (Fintype.card B) ≤ cStar := by
  have hn : 2 ≤ Fintype.card B := Fintype.one_lt_card_iff.mpr ⟨D.b0, D.b00, D.b0_ne_b00⟩
  unfold cOPT
  apply csSup_le
  · exact ⟨_, Set.mem_image_of_mem _ (Set.left_mem_Icc.mpr zero_le_one)⟩
  · rintro _ ⟨θ, hθ, rfl⟩
    exact opt_bound _ hn θ hθ

theorem solution {A B : Type} [Fintype A] [Fintype B] [DecidableEq B] (D : DataSet A B) :
    (∃ s q, LPOptimal D s q) ∧
      ∀ s q, LPOptimal D s q → ∀ r : B → ℝ, (∀ b, 0 ≤ r b) →
        (1 + cStar)⁻¹ * rev D r ≤ expRevOut D q := by
  refine ⟨lp_exists D, ?_⟩
  intro s q hopt
  apply lemma_5_1 D s q hopt cStar cStar_pos
  · intro a t _ ht
    exact lemma_5_2 D s q hopt a t ht
  · intro a t _ ht
    exact (lemma_5_3 D s q hopt a t ht).trans (cOPT_le_cStar D)
