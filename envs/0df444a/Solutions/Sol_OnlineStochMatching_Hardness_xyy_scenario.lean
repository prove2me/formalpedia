-- Prove2me | solution 1 for OnlineStochMatching.Hardness.xyy_scenario
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T05:43:57.14772+00:00
-- url     : https://prove2.me/submissions/6be2ba34-b4a9-4804-b71f-2afbbe7df902

import Mathlib
import Definitions.Def_OnlineStochMatching_Hardness_Model
import Definitions.Def_OnlineStochMatching_Hardness_SixCycle



namespace OnlineStochMatching.Hardness

section gen
variable {A I : Type} {n : ℕ} [DecidableEq A]

lemma matchedAfter_subset_aux (G : A → I → Prop) [DecidableRel G] (alg : OnlineAlg A I n)
    (ω : Fin n → I) (T : Finset A)
    (h : ∀ t : Fin n, ∀ a, alg t (prefixOf ω t) (ω t) = some a → G a (ω t) → a ∈ T) :
    ∀ k, matchedAfter G alg ω k ⊆ T := by
  intro k
  induction k with
  | zero => simp [matchedAfter]
  | succ k ih =>
    simp only [matchedAfter]
    split_ifs with hk
    · intro x hx
      unfold step at hx
      generalize hs : alg ⟨k, hk⟩ (prefixOf ω ⟨k, hk⟩) (ω ⟨k, hk⟩) = r at hx
      cases r with
      | none => exact ih hx
      | some a =>
        simp only at hx
        split_ifs at hx with hc
        · rcases Finset.mem_insert.1 hx with rfl | hx
          · exact h _ _ hs hc.1
          · exact ih hx
        · exact ih hx
    · exact ih

lemma exists_matching (G : A → I → Prop) [DecidableRel G] (alg : OnlineAlg A I n)
    (ω : Fin n → I) : ∀ k, ∃ M : Fin n → Option A, IsRealizationMatching G ω M ∧
      (∀ t a, M t = some a → a ∈ matchedAfter G alg ω k) ∧
      (∀ t : Fin n, k ≤ t.val → M t = none) ∧
      matchingSize M = (matchedAfter G alg ω k).card := by
  intro k
  induction k with
  | zero =>
    refine ⟨fun _ => none, ⟨by simp, by simp⟩, by simp, by simp, ?_⟩
    simp [matchingSize, matchedAfter]
  | succ k ih =>
    obtain ⟨M, ⟨hM1, hM2⟩, hM3, hM4, hM5⟩ := ih
    simp only [matchedAfter]
    split_ifs with hk
    · unfold step
      generalize hs : alg ⟨k, hk⟩ (prefixOf ω ⟨k, hk⟩) (ω ⟨k, hk⟩) = r
      cases r with
      | none =>
        refine ⟨M, ⟨hM1, hM2⟩, hM3, ?_, hM5⟩
        intro t ht
        exact hM4 t (by omega)
      | some a =>
        simp only
        split_ifs with hc
        · have hMt : M ⟨k, hk⟩ = none := hM4 _ le_rfl
          refine ⟨Function.update M ⟨k, hk⟩ (some a), ⟨?_, ?_⟩, ?_, ?_, ?_⟩
          · intro t b hb
            by_cases ht : t = ⟨k, hk⟩
            · subst ht
              simp at hb
              subst hb
              exact hc.1
            · rw [Function.update_of_ne ht] at hb
              exact hM1 t b hb
          · intro s t b hs ht
            by_cases hs' : s = ⟨k, hk⟩ <;> by_cases ht' : t = ⟨k, hk⟩
            · rw [hs', ht']
            · exfalso
              subst hs'
              rw [Function.update_of_ne ht'] at ht
              simp at hs
              subst hs
              exact hc.2 (hM3 _ _ ht)
            · exfalso
              subst ht'
              rw [Function.update_of_ne hs'] at hs
              simp at ht
              subst ht
              exact hc.2 (hM3 _ _ hs)
            · rw [Function.update_of_ne hs'] at hs
              rw [Function.update_of_ne ht'] at ht
              exact hM2 s t b hs ht
          · intro t b hb
            by_cases ht : t = ⟨k, hk⟩
            · subst ht
              simp at hb
              subst hb
              exact Finset.mem_insert_self _ _
            · rw [Function.update_of_ne ht] at hb
              exact Finset.mem_insert_of_mem (hM3 t b hb)
          · intro t ht
            have : t ≠ ⟨k, hk⟩ := by
              intro h; subst h; simp at ht
            rw [Function.update_of_ne this]
            exact hM4 t (by
              have : t.val ≠ k := fun h' => this (Fin.ext h')
              omega)
          · have : (Finset.univ.filter fun t => (Function.update M ⟨k, hk⟩ (some a) t).isSome) =
                insert ⟨k, hk⟩ (Finset.univ.filter fun t => (M t).isSome) := by
              ext s
              by_cases hs : s = ⟨k, hk⟩
              · subst hs; simp
              · simp [Function.update_of_ne hs, hs]
            unfold matchingSize
            rw [this, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem hc.2]
            · exact congrArg Nat.succ hM5
            · simp [hMt]
        · refine ⟨M, ⟨hM1, hM2⟩, hM3, ?_, hM5⟩
          intro t ht
          exact hM4 t (by omega)
    · exact ⟨M, ⟨hM1, hM2⟩, hM3, fun t ht => hM4 t (by omega), hM5⟩

lemma ALG_le_OPT [Fintype A] (G : A → I → Prop) [DecidableRel G] (alg : OnlineAlg A I n)
    (ω : Fin n → I) : ALG G alg ω ≤ OPT G ω := by
  classical
  obtain ⟨M, hM, -, -, h⟩ := exists_matching G alg ω n
  unfold ALG
  rw [← h]
  unfold OPT
  exact Finset.le_sup (f := matchingSize) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hM⟩)

end gen

lemma cycle_key : ∀ u v : Imp, u ≠ v → ∃ M : Fin 3 → Option Adv,
    IsRealizationMatching cycleEdge ![u, v, v] M ∧ matchingSize M = 3 := by
  unfold IsRealizationMatching
  decide +kernel

lemma cycle_OPT_three (u v : Imp) (h : u ≠ v) : OPT cycleEdge ![u, v, v] = 3 := by
  classical
  apply le_antisymm
  · unfold OPT
    apply Finset.sup_le
    intro M _
    unfold matchingSize
    calc _ ≤ (Finset.univ : Finset (Fin 3)).card := Finset.card_filter_le _ _
      _ = 3 := by simp
  · obtain ⟨M, hM, h3⟩ := cycle_key u v h
    rw [← h3]
    unfold OPT
    exact Finset.le_sup (f := matchingSize) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hM⟩)


lemma cycle_choice : ∀ (u : Imp) (s : Option Adv), ∃ v : Imp, v ≠ u ∧
    ∀ a, s = some a → cycleEdge a u → cycleEdge a v := by
  unfold cycleEdge cycleEdges
  decide

lemma cycle_nbr_card : ∀ v : Imp,
    (Finset.univ.filter fun a : Adv => cycleEdge a v).card = 2 := by
  unfold cycleEdge cycleEdges
  decide

lemma xyy_core (alg : OnlineAlg Adv Imp 3) (u : Imp) :
    ∃ v : Imp, ALG cycleEdge alg ![u, v, v] ≤ 2 ∧ OPT cycleEdge ![u, v, v] = 3 := by
  obtain ⟨v, hvu, hv⟩ := cycle_choice u (alg ⟨0, by norm_num⟩ (prefixOf ![u, u, u] ⟨0, by norm_num⟩) u)
  refine ⟨v, ?_, cycle_OPT_three u v (Ne.symm hvu)⟩
  have hsub := matchedAfter_subset_aux cycleEdge alg ![u, v, v]
    (Finset.univ.filter fun a : Adv => cycleEdge a v) (by
      intro t a hta hG
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      fin_cases t
      · have hpre : prefixOf ![u, v, v] ⟨0, by norm_num⟩ = prefixOf ![u, u, u] ⟨0, by norm_num⟩ :=
          Subsingleton.elim _ _
        simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero] at hta hG
        have hta' : alg ⟨0, by norm_num⟩ (prefixOf ![u, u, u] ⟨0, by norm_num⟩) u = some a := by
          rw [← hpre]; exact hta
        exact hv a hta' hG
      · simpa using hG
      · simpa using hG) 3
  unfold ALG
  calc _ ≤ (Finset.univ.filter fun a : Adv => cycleEdge a v).card := Finset.card_le_card hsub
    _ = 2 := cycle_nbr_card v

lemma ratio_le_one (alg : OnlineAlg Adv Imp 3) (ω : Fin 3 → Imp) :
    (ALG cycleEdge alg ω : ℝ) / (OPT cycleEdge ω : ℝ) ≤ 1 := by
  have h := ALG_le_OPT cycleEdge alg ω
  rcases Nat.eq_zero_or_pos (OPT cycleEdge ω) with h0 | h0
  · rw [h0]; simp
  · rw [div_le_one (by exact_mod_cast h0)]
    exact_mod_cast h

lemma det_bound (alg : OnlineAlg Adv Imp 3) : expectedRatio cycleEdge alg ≤ 26 / 27 := by
  choose v hv using xyy_core alg
  classical
  set W : Finset (Fin 3 → Imp) := Finset.univ.image (fun u => ![u, v u, v u]) with hW
  have hinj : Function.Injective (fun u => (![u, v u, v u] : Fin 3 → Imp)) := by
    intro a b h
    have := congrFun h 0
    simpa using this
  have hWc : W.card = 3 := by
    rw [hW, Finset.card_image_of_injective _ hinj]
    decide
  have hbound : ∀ ω : Fin 3 → Imp, (ALG cycleEdge alg ω : ℝ) / (OPT cycleEdge ω : ℝ) ≤
      1 - (if ω ∈ W then (1 / 3 : ℝ) else 0) := by
    intro ω
    by_cases hω : ω ∈ W
    · obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hω
      rw [if_pos hω]
      obtain ⟨h1, h2⟩ := hv u
      rw [h2]
      have : (ALG cycleEdge alg ![u, v u, v u] : ℝ) ≤ 2 := by exact_mod_cast h1
      push_cast
      linarith
    · rw [if_neg hω]
      have := ratio_le_one alg ω
      linarith
  have hsum : ∑ ω : Fin 3 → Imp, (ALG cycleEdge alg ω : ℝ) / (OPT cycleEdge ω : ℝ) ≤ 26 := by
    calc _ ≤ ∑ ω : Fin 3 → Imp, (1 - (if ω ∈ W then (1 / 3 : ℝ) else 0)) :=
          Finset.sum_le_sum (fun ω _ => hbound ω)
      _ = 26 := by
        rw [Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.univ_inter]
        simp only [Finset.sum_const, Finset.card_univ, hWc, nsmul_eq_mul, Fintype.card_fun]
        have : Fintype.card Imp = 3 := by decide
        rw [this]
        norm_num
  unfold expectedRatio
  have hc : (Fintype.card Imp : ℝ) ^ 3 = 27 := by
    have : Fintype.card Imp = 3 := by decide
    rw [this]; norm_num
  rw [hc, div_le_div_iff_of_pos_right (by norm_num)]
  exact hsum

theorem xyy_scenario_core (alg : OnlineAlg Adv Imp 3) (u : Imp) :
    ∃ v : Imp, ALG cycleEdge alg ![u, v, v] ≤ 2 ∧ OPT cycleEdge ![u, v, v] = 3 :=
  xyy_core alg u

theorem single_cycle_core (P : PMF (OnlineAlg Adv Imp 3)) :
    randExpectedRatio cycleEdge P ≤ 26 / 27 := by
  unfold randExpectedRatio
  have hsum1 : ∑ alg : OnlineAlg Adv Imp 3, (P alg).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top P a)]
    have := P.tsum_coe
    rw [tsum_fintype] at this
    rw [this]; simp
  calc _ ≤ ∑ alg : OnlineAlg Adv Imp 3, (P alg).toReal * (26 / 27 : ℝ) :=
        Finset.sum_le_sum (fun alg _ =>
          mul_le_mul_of_nonneg_left (det_bound alg) ENNReal.toReal_nonneg)
    _ = 26 / 27 := by rw [← Finset.sum_mul, hsum1, one_mul]

end OnlineStochMatching.Hardness

open OnlineStochMatching.Hardness


theorem solution (alg : OnlineAlg Adv Imp 3) (u : Imp) :
    ∃ v : Imp, ALG cycleEdge alg ![u, v, v] ≤ 2 ∧ OPT cycleEdge ![u, v, v] = 3 := by
  exact xyy_scenario_core alg u
