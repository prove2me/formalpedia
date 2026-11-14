-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.lemma_5_6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:28:09.290068+00:00
-- url     : https://prove2.me/submissions/13652b62-2783-4d96-a251-f5af5eede43c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_ZeroFreeRRG_Hardcore_RevealOverlap
import Theorems.Thm_ZeroFreeRRG_Hardcore_reveal_overlap_miss_concentration
import Theorems.Thm_ZeroFreeRRG_Hardcore_reveal_overlap_prior_concentration
import Theorems.Thm_ZeroFreeRRG_Hardcore_planted_reveal_change_measure
import Theorems.Thm_ZeroFreeRRG_Hardcore_replica_likelihood_tail
import Theorems.Thm_ZeroFreeRRG_Hardcore_reveal_weights_sum_one
import Theorems.Thm_ZeroFreeRRG_Hardcore_matching_nonempty_even
import Theorems.Thm_ZeroFreeRRG_Hardcore_planted_graph_conditional_gibbs
import Theorems.Thm_ZeroFreeRRG_Hardcore_planted_weights_sum_one
import Theorems.Thm_ZeroFreeRRG_Hardcore_planted_replica_reveal_weight_nonnegative
import Theorems.Thm_ZeroFreeRRG_Hardcore_gibbs_weights_sum_one
import Theorems.Thm_ZeroFreeRRG_Hardcore_overlap_three_exponential_errors
import Mathlib
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) (t : ℝ) (ht : m.PosParam t)
    (hC1 : Condition1 m d t) :
    ∀ η : ℝ, 0 < η → ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N, Even (n * d) →
      plantedE m t d n (fun M _ => replicaProb m t M (fun σ σ' =>
          ∃ ab : m.Spin × m.Spin, η < |overlap σ σ' ab - m.pi t ab.1 * m.pi t ab.2|))
        ≤ Real.exp (-c * n) := by
  classical
  intro η hη
  let ε := min η 1
  have hε : 0 < ε := lt_min hη (by norm_num)
  have hε1 : ε ≤ 1 := min_le_right _ _
  have hεη : ε ≤ η := min_le_left _ _
  obtain ⟨s,hs,hs1,c₀,hc₀,N₀,htail⟩ := replica_likelihood_tail m hm d hd t ht hC1 ε hε
  let b := s*ε^2/12
  have hb : 0 < b := by dsimp [b]; positivity
  have hcoef : 0 ≤ 2*(Fintype.card m.Spin : ℝ)^2 := by positivity
  obtain ⟨c,hc,Nexp,hexp⟩ := overlap_three_exponential_errors 2
    (2*(Fintype.card m.Spin : ℝ)^2) 2 b (b/2) c₀ (by norm_num) hcoef (by norm_num) hb (by linarith) hc₀
  refine ⟨c,hc,max N₀ Nexp,?_⟩
  intro n hn heven
  letI : Nonempty (Matching n d) := matching_nonempty_even n d heven
  let a₀ : m.Spin := by
    cases m with
    | hardcore => exact (0 : Fin 2)
    | potts q =>
      change 2 ≤ q at hm
      exact ⟨0,by omega⟩
  let D : (Fin n → m.Spin) → (Fin n → m.Spin) → Prop := fun σ σ' => fullOverlapDeviation m t η σ σ'
  let H : ∀ U : Finset (Fin n), ({v : Fin n // v ∈ U} → m.Spin) →
      ({v : Fin n // v ∈ U} → m.Spin) → Prop := fun U => revealedOverlapH m t s ε U
  let Good : Matching n d → (Fin n → m.Spin) → (Fin n → m.Spin) → Finset (Fin n) → Prop :=
    fun M σ σ' U => pinnedLL m t M σ U + pinnedLL m t M σ' U ≤ (b/2)*n
  let W : Matching n d → (Fin n → m.Spin) → (Fin n → m.Spin) → Finset (Fin n) → ℝ :=
    fun M σ σ' U => planted m t M σ * gibbs m t M σ' * revealProb s U
  have hW : ∀ M σ σ' U, 0 ≤ W M σ σ' U := planted_replica_reveal_weight_nonnegative m hm t s ht hs.le hs1.le d n
  have hpairnorm : (∑ M : Matching n d, ∑ σ : Fin n → m.Spin, ∑ σ' : Fin n → m.Spin,
      planted m t M σ * gibbs m t M σ') = 1 := by
    simp only [← Finset.mul_sum,gibbs_weights_sum_one m hm t ht d n, mul_one]
    exact planted_weights_sum_one m hm t ht d n
  have htarget : plantedE m t d n (fun M _ => replicaProb m t M (fun σ σ' =>
          ∃ ab : m.Spin × m.Spin, η < |overlap σ σ' ab - m.pi t ab.1 * m.pi t ab.2|)) =
      ∑ M : Matching n d, ∑ σ : Fin n → m.Spin, ∑ σ' : Fin n → m.Spin, ∑ U : Finset (Fin n),
        if D σ σ' then W M σ σ' U else 0 := by
    unfold plantedE
    apply Finset.sum_congr rfl
    intro M hM
    have hcond : ∀ σ : Fin n → m.Spin, planted m t M σ =
        (∑ τ : Fin n → m.Spin, planted m t M τ) * gibbs m t M σ :=
      planted_graph_conditional_gibbs m hm t ht d n M
    rw [← Finset.sum_mul]
    unfold replicaProb
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ hσ
    apply Finset.sum_congr rfl
    intro σ' hσ'
    by_cases hh : D σ σ'
    · have hh' : ∃ ab : m.Spin × m.Spin, η < |overlap σ σ' ab - m.pi t ab.1 * m.pi t ab.2| := hh
      simp only [hh,hh', ↓reduceIte]
      dsimp [W]
      rw [← Finset.mul_sum, reveal_weights_sum_one n s, mul_one]
      rw [hcond σ]
      ring
    · have hh' : ¬(∃ ab : m.Spin × m.Spin, η < |overlap σ σ' ab - m.pi t ab.1 * m.pi t ab.2|) := hh
      simp only [hh,hh', ↓reduceIte, mul_zero, Finset.sum_const_zero]
  have hpieces : (∑ M : Matching n d, ∑ σ : Fin n → m.Spin, ∑ σ' : Fin n → m.Spin, ∑ U : Finset (Fin n),
        if D σ σ' then W M σ σ' U else 0) ≤
      (∑ M : Matching n d, ∑ σ : Fin n → m.Spin, ∑ σ' : Fin n → m.Spin, ∑ U : Finset (Fin n),
        if D σ σ' ∧ ¬ H U (fun v => σ v.1) (fun v => σ' v.1) then W M σ σ' U else 0) +
      (∑ M : Matching n d, ∑ σ : Fin n → m.Spin, ∑ σ' : Fin n → m.Spin, ∑ U : Finset (Fin n),
        if H U (fun v => σ v.1) (fun v => σ' v.1) ∧ Good M σ σ' U then W M σ σ' U else 0) +
      (∑ M : Matching n d, ∑ σ : Fin n → m.Spin, ∑ σ' : Fin n → m.Spin, ∑ U : Finset (Fin n),
        if ¬ Good M σ σ' U then W M σ σ' U else 0) := by
    have hpnt (M : Matching n d) (σ σ' : Fin n → m.Spin) (U : Finset (Fin n)) :
        (if D σ σ' then W M σ σ' U else 0) ≤
        (if D σ σ' ∧ ¬ H U (fun v => σ v.1) (fun v => σ' v.1) then W M σ σ' U else 0) +
        (if H U (fun v => σ v.1) (fun v => σ' v.1) ∧ Good M σ σ' U then W M σ σ' U else 0) +
        (if ¬ Good M σ σ' U then W M σ σ' U else 0) := by
      by_cases hD : D σ σ' <;> by_cases hH : H U (fun v => σ v.1) (fun v => σ' v.1) <;>
        by_cases hG : Good M σ σ' U <;> simp [hD,hH,hG] <;> linarith [hW M σ σ' U]
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Matching n d))) (fun M _ =>
      Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n → m.Spin))) (fun σ _ =>
        Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n → m.Spin))) (fun σ' _ =>
          Finset.sum_le_sum (s := (Finset.univ : Finset (Finset (Fin n)))) (fun U _ => hpnt M σ σ' U))))
    simpa only [Finset.sum_add_distrib] using hh
  have hpair (M : Matching n d) (σ σ' : Fin n → m.Spin) :
      0 ≤ planted m t M σ * gibbs m t M σ' := by
    have hh : 0 ≤ ∑ U : Finset (Fin n), W M σ σ' U := Finset.sum_nonneg fun U hU => hW M σ σ' U
    simpa only [W,← Finset.mul_sum,reveal_weights_sum_one,mul_one] using hh
  have hmiss : (∑ M : Matching n d, ∑ σ : Fin n → m.Spin, ∑ σ' : Fin n → m.Spin, ∑ U : Finset (Fin n),
        if D σ σ' ∧ ¬ H U (fun v => σ v.1) (fun v => σ' v.1) then W M σ σ' U else 0)
      ≤ 2 * Real.exp (-b*n) := by
    calc
      _ ≤ ∑ M : Matching n d, ∑ σ : Fin n → m.Spin, ∑ σ' : Fin n → m.Spin,
          (planted m t M σ * gibbs m t M σ') * (2*Real.exp (-b*n)) := by
        apply Finset.sum_le_sum
        intro M hM
        apply Finset.sum_le_sum
        intro σ hσ
        apply Finset.sum_le_sum
        intro σ' hσ'
        by_cases hD : D σ σ'
        · have hdev : fullOverlapDeviation m t ε σ σ' := by
            obtain ⟨ab,hab⟩ := hD
            exact ⟨ab,lt_of_le_of_lt hεη hab⟩
          have hh := reveal_overlap_miss_concentration m hm t s ε ht hs hs1.le hε hε1 n σ σ' hdev
          change (∑ U : Finset (Fin n), revealProb s U *
            (if ¬ H U (fun v => σ v.1) (fun v => σ' v.1) then 1 else 0)) ≤ 2*Real.exp (-b*n) at hh
          have heq : (∑ U : Finset (Fin n),
              if D σ σ' ∧ ¬ H U (fun v => σ v.1) (fun v => σ' v.1) then W M σ σ' U else 0) =
              (planted m t M σ * gibbs m t M σ') *
                (∑ U : Finset (Fin n), revealProb s U *
                  (if ¬ H U (fun v => σ v.1) (fun v => σ' v.1) then 1 else 0)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro U hU
            dsimp [W]
            simp only [hD,true_and]
            split_ifs <;> ring
          rw [heq]
          exact mul_le_mul_of_nonneg_left hh (hpair M σ σ')
        · simp only [hD,false_and, ↓reduceIte, Finset.sum_const_zero]
          exact mul_nonneg (hpair M σ σ') (mul_nonneg (by norm_num) (Real.exp_pos _).le)
      _ = 2*Real.exp (-b*n) := by
        simp only [← Finset.sum_mul,hpairnorm,one_mul]
  have href := reveal_overlap_prior_concentration m hm t s ε ht hs hs1.le hε hε1 n
  have hgood0 := planted_reveal_change_measure m hm t s ht hs.le hs1.le d n a₀ ((b/2)*n)
    (2*(Fintype.card m.Spin : ℝ)^2*Real.exp (-b*n)) H href
  have hgood : (∑ M : Matching n d, ∑ σ : Fin n → m.Spin, ∑ σ' : Fin n → m.Spin, ∑ U : Finset (Fin n),
        if H U (fun v => σ v.1) (fun v => σ' v.1) ∧ Good M σ σ' U then W M σ σ' U else 0)
      ≤ 2*(Fintype.card m.Spin : ℝ)^2*Real.exp (-(b/2)*n) := by
    have heq : Real.exp ((b/2)*n) * (2*(Fintype.card m.Spin : ℝ)^2*Real.exp (-b*n)) =
        2*(Fintype.card m.Spin : ℝ)^2*Real.exp (-(b/2)*n) := by
      rw [mul_left_comm,← Real.exp_add]
      congr 2
      ring
    rw [← heq]
    convert hgood0 using 1
    apply Finset.sum_congr rfl
    intro M hM
    apply Finset.sum_congr rfl
    intro σ hσ
    apply Finset.sum_congr rfl
    intro σ' hσ'
    apply Finset.sum_congr rfl
    intro U hU
    dsimp [W,Good]
    split_ifs <;> ring
  have hbad0 := htail n (le_trans (le_max_left _ _) hn) heven
  have hbad : (∑ M : Matching n d, ∑ σ : Fin n → m.Spin, ∑ σ' : Fin n → m.Spin, ∑ U : Finset (Fin n),
        if ¬ Good M σ σ' U then W M σ σ' U else 0) ≤ 2*Real.exp (-c₀*n) := by
    have heq : (b/2)*n = (s*ε^2/24)*n := by dsimp [b]; ring
    convert hbad0 using 1
    apply Finset.sum_congr rfl
    intro M hM
    apply Finset.sum_congr rfl
    intro σ hσ
    apply Finset.sum_congr rfl
    intro σ' hσ'
    apply Finset.sum_congr rfl
    intro U hU
    dsimp [W,Good]
    simp only [heq,not_le]
    split_ifs <;> ring
  rw [htarget]
  exact hpieces.trans ((add_le_add (add_le_add hmiss hgood) hbad).trans
    (hexp n (le_trans (le_max_right _ _) hn)))
