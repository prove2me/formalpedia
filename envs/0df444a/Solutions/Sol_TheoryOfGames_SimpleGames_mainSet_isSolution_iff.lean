-- Prove2me | solution 1 for TheoryOfGames.SimpleGames.mainSet_isSolution_iff
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T17:47:17.352868+00:00
-- url     : https://prove2.me/submissions/31cdf8e3-8c6b-46ce-afdc-afa5ec01d155

import Mathlib
import Definitions.Def_TheoryOfGames_SimpleGames_Majority



namespace TheoryOfGames.SimpleGames

open Classical

lemma sg_n_pos {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : IsCharFunction v) (hs : IsSimple v) :
    0 < n := by
  by_contra h
  have h0 : n = 0 := by omega
  subst h0
  apply hs.1
  intro S
  have : S = ∅ := Finset.eq_empty_of_forall_notMem (fun i => i.elim0)
  subst this
  simp [reducedForm, hv.1]

lemma sg_v_ge {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : IsCharFunction v)
    (hred : ∀ i : Fin n, v {i} = -1) (Q : Finset (Fin n)) : -(Q.card : ℝ) ≤ v Q := by
  induction Q using Finset.induction_on with
  | empty => simp [hv.1]
  | insert a Q ha ih =>
    have h1 := hv.2.2 {a} Q (Finset.disjoint_singleton_left.mpr ha)
    rw [← Finset.insert_eq] at h1
    rw [Finset.card_insert_of_notMem ha, hred a] at *
    push_cast
    linarith

lemma sg_lose_val {n : ℕ} (v : Finset (Fin n) → ℝ) (hred : ∀ i : Fin n, v {i} = -1)
    (S : Finset (Fin n)) (h : S ∈ losingSets v) : v S = -(S.card : ℝ) := by
  have h' : v S = ∑ k ∈ S, v {k} := h
  rw [h']
  simp [hred]

lemma sg_win_val {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : IsCharFunction v)
    (hred : ∀ i : Fin n, v {i} = -1)
    (S : Finset (Fin n)) (h : S ∈ winningSets v) : v S = (n : ℝ) - (S.card : ℝ) := by
  have h1 : v Sᶜ = -(Sᶜ.card : ℝ) := sg_lose_val v hred Sᶜ h
  have h2 := hv.2.1 Sᶜ
  rw [compl_compl] at h2
  have h3 : (Sᶜ.card : ℝ) + S.card = n := by
    have := Finset.card_compl_add_card S
    simp only [Fintype.card_fin] at this
    exact_mod_cast this
  linarith

lemma sg_le_of_sub_losing {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : IsCharFunction v)
    (hred : ∀ i : Fin n, v {i} = -1) (L P : Finset (Fin n)) (hL : L ∈ losingSets v)
    (hP : P ⊆ L) : v P ≤ -(P.card : ℝ) := by
  have h1 := hv.2.2 P (L \ P) Finset.disjoint_sdiff
  rw [Finset.union_sdiff_of_subset hP, sg_lose_val v hred L hL] at h1
  have h2 := sg_v_ge v hv hred (L \ P)
  have h3 : ((L \ P).card : ℝ) + P.card = L.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hP
  linarith

lemma sg_sum_alpha {n : ℕ} (x : Fin n → ℝ) (S P : Finset (Fin n)) (hP : P ⊆ S) :
    ∑ i ∈ P, alphaS x S i = -(P.card : ℝ) + ∑ i ∈ P, x i := by
  rw [Finset.sum_congr rfl (g := fun i => -1 + x i)]
  · simp [Finset.sum_add_distrib]
  · intro i hi
    simp [alphaS, hP hi]

lemma sg_alpha_eq {n : ℕ} (x : Fin n → ℝ) (S : Finset (Fin n)) (i : Fin n) :
    alphaS x S i = -1 + (if i ∈ S then x i else 0) := by
  unfold alphaS; split_ifs <;> simp

lemma sg_sum_symm {n : ℕ} (x : Fin n → ℝ) (T S : Finset (Fin n))
    (h : ∀ i ∈ symmDiff T S, x i = 0) : ∑ i ∈ T, x i = ∑ i ∈ S, x i := by
  rw [← Finset.sum_inter_add_sum_sdiff T S x, ← Finset.sum_inter_add_sum_sdiff S T x,
    Finset.inter_comm]
  rw [Finset.sum_eq_zero (s := T \ S), Finset.sum_eq_zero (s := S \ T)]
  · intro i hi
    rw [Finset.mem_sdiff] at hi
    exact h i (Finset.mem_symmDiff.mpr (Or.inr hi))
  · intro i hi
    rw [Finset.mem_sdiff] at hi
    exact h i (Finset.mem_symmDiff.mpr (Or.inl hi))

lemma sg_exists_minimal {n : ℕ} (W : Set (Finset (Fin n))) (S : Finset (Fin n)) (hS : S ∈ W) :
    ∃ S₀ ⊆ S, S₀ ∈ minimalSets W := by
  obtain ⟨S₀, hS₀, hmin⟩ := (S.powerset.filter (fun T => T ∈ W)).exists_min_image Finset.card
    ⟨S, by simp [hS]⟩
  simp only [Finset.mem_filter, Finset.mem_powerset] at hS₀ hmin
  refine ⟨S₀, hS₀.1, hS₀.2, fun T hT hTW => ?_⟩
  have := hmin T ⟨hT.1.trans hS₀.1, hTW⟩
  have := Finset.card_lt_card hT
  omega

theorem mainSet_core {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : IsCharFunction v)
    (hs : IsSimple v) (hred : ∀ i : Fin n, v {i} = -1)
    (U : Set (Finset (Fin n))) (hU : U ⊆ minimalSets (winningSets v))
    (x : Fin n → ℝ) (hx7 : ∀ i, 0 ≤ x i) (hx8 : ∀ S ∈ U, ∑ i ∈ S, x i = (n : ℝ)) :
    IsSolution v (mainSet U x) ↔
      ((∀ T : Finset (Fin n), (∃ S ∈ U, ∀ i ∈ symmDiff T S, x i = 0) →
          ∑ i ∈ T, x i = (n : ℝ)) ∧
        (∀ T ∈ uPlus U, (¬ ∃ S ∈ U, ∀ i ∈ symmDiff T S, x i = 0) →
          (n : ℝ) < ∑ i ∈ T, x i)) := by
  have hn := sg_n_pos v hv hs
  have hA : ∀ T : Finset (Fin n), (∃ S ∈ U, ∀ i ∈ symmDiff T S, x i = 0) →
      ∑ i ∈ T, x i = (n : ℝ) := by
    rintro T ⟨S, hS, h⟩
    rw [sg_sum_symm x T S h, hx8 S hS]
  constructor
  · intro sol
    refine ⟨hA, ?_⟩
    intro T hT hTn
    by_contra hle
    push_neg at hle
    have hTmeet : ∀ S ∈ U, ∃ j ∈ S, j ∈ T := by
      intro S hS
      by_contra hc
      push_neg at hc
      exact hT ⟨S, hS, fun j hj => Finset.mem_compl.mpr (hc j hj)⟩
    rcases T.eq_empty_or_nonempty with hT0 | ⟨i0, hi0⟩
    · -- U is empty
      have himp : IsImputation v (fun _ => 0) := ⟨fun i => by rw [hred]; norm_num, by simp⟩
      have hnot : (fun _ => (0:ℝ)) ∉ mainSet U x := by
        rintro ⟨S, hS, _⟩
        obtain ⟨j, _, hj⟩ := hTmeet S hS
        simp [hT0] at hj
      obtain ⟨α, ⟨S, hS, _⟩, _⟩ := sol.2.2 _ himp hnot
      obtain ⟨j, _, hj⟩ := hTmeet S hS
      simp [hT0] at hj
    · set d : ℝ := (n : ℝ) - ∑ i ∈ T, x i with hd
      have hd0 : 0 ≤ d := by linarith
      let β : Fin n → ℝ := fun i => -1 + (if i ∈ T then x i else 0) + (if i = i0 then d else 0)
      have hβge : ∀ i, -1 + (if i ∈ T then x i else 0) ≤ β i := by
        intro i; simp only [β]; split_ifs <;> linarith
      have himp : IsImputation v β := by
        refine ⟨fun i => ?_, ?_⟩
        · rw [hred]; have := hβge i; split_ifs at this <;> linarith [hx7 i]
        · simp only [β, Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter,
            Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          rw [hd]; ring
      have hundom : ∀ α ∈ mainSet U x, ¬ Dominates v α β := by
        rintro α ⟨S, hS, rfl⟩ ⟨P, hPne, hPeff, hPlt⟩
        have hPS : P ⊆ S \ T := by
          intro i hi
          have h1 := hPlt i hi
          have h2 := hβge i
          rw [sg_alpha_eq] at h1
          rw [Finset.mem_sdiff]
          by_cases hiS : i ∈ S
          · refine ⟨hiS, fun hiT => ?_⟩
            simp [hiS, hiT] at h1 h2
            linarith
          · simp only [hiS, if_false] at h1
            split_ifs at h2 <;> linarith [hx7 i]
        obtain ⟨j, hjS, hjT⟩ := hTmeet S hS
        have hPss : P ⊂ S := by
          refine ⟨fun i hi => (Finset.mem_sdiff.mp (hPS hi)).1, fun h => ?_⟩
          have := hPS (h hjS)
          exact (Finset.mem_sdiff.mp this).2 hjT
        have hPnw : P ∉ winningSets v := (hU hS).2 P hPss
        have hPl : P ∈ losingSets v := (hs.2 P).resolve_left hPnw
        have hPsub : P ⊆ S := fun i hi => (Finset.mem_sdiff.mp (hPS hi)).1
        unfold IsEffective at hPeff; rw [sg_sum_alpha x S P hPsub, sg_lose_val v hred P hPl] at hPeff
        have hsum0 : ∑ i ∈ P, x i = 0 :=
          le_antisymm (by linarith) (Finset.sum_nonneg fun i _ => hx7 i)
        rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hx7 i)] at hsum0
        obtain ⟨i, hi⟩ := hPne
        have h1 := hPlt i hi
        have h2 := hβge i
        rw [sg_alpha_eq, if_pos (hPsub hi), hsum0 i hi] at h1
        split_ifs at h2 <;> linarith [hx7 i]
      have hβV : β ∈ mainSet U x := by
        by_contra hc
        obtain ⟨α, hα, hd'⟩ := sol.2.2 β himp hc
        exact hundom α hα hd'
      obtain ⟨S, hS, hβS⟩ := hβV
      apply hTn
      refine ⟨S, hS, fun i hi => ?_⟩
      have h := congrFun hβS i
      simp only [β] at h
      rw [sg_alpha_eq] at h
      rcases Finset.mem_symmDiff.mp hi with ⟨hiT, hiS⟩ | ⟨hiS, hiT⟩
      · simp only [hiT, hiS, if_true, if_false] at h
        split_ifs at h <;> linarith [hx7 i]
      · have hne : i ≠ i0 := fun h' => hiT (h' ▸ hi0)
        simp only [hiT, hiS, hne, if_true, if_false] at h
        linarith
  · rintro ⟨-, hB⟩
    have himpS : ∀ S ∈ U, IsImputation v (alphaS x S) := by
      intro S hS
      refine ⟨fun i => ?_, ?_⟩
      · rw [hred, sg_alpha_eq]; split_ifs <;> linarith [hx7 i]
      · simp only [sg_alpha_eq, Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hx8 S hS]
        ring
    refine ⟨?_, ?_, ?_⟩
    · rintro α ⟨S, hS, rfl⟩
      exact himpS S hS
    · rintro α ⟨S, hS, rfl⟩ β ⟨S', hS', rfl⟩ ⟨P, hPne, hPeff, hPlt⟩
      have hPS : ∀ i ∈ P, i ∈ S ∧ i ∉ S' ∧ 0 < x i := by
        intro i hi
        have h1 := hPlt i hi
        rw [sg_alpha_eq, sg_alpha_eq] at h1
        by_cases hiS : i ∈ S <;> by_cases hiS' : i ∈ S' <;>
          simp [hiS, hiS'] at h1 <;> first | exact ⟨hiS, hiS', h1⟩ | linarith [hx7 i]
      have hPsub : P ⊆ S'ᶜ := fun i hi => Finset.mem_compl.mpr (hPS i hi).2.1
      have hL : S'ᶜ ∈ losingSets v := (hU hS').1
      have h1 := sg_le_of_sub_losing v hv hred S'ᶜ P hL hPsub
      unfold IsEffective at hPeff; rw [sg_sum_alpha x S P (fun i hi => (hPS i hi).1)] at hPeff
      have : 0 < ∑ i ∈ P, x i := Finset.sum_pos (fun i hi => (hPS i hi).2.2) hPne
      linarith
    · intro β himp hβ
      set R := rSet x β with hR
      have hRmem : ∀ i, i ∈ R ↔ -1 + x i ≤ β i := by
        intro i; simp [hR, rSet]
      by_cases hcase : ∃ S ∈ U, ∀ i ∈ S, i ∉ R
      · obtain ⟨S, hS, hSR⟩ := hcase
        refine ⟨alphaS x S, ⟨S, hS, rfl⟩, S, ?_, ?_, ?_⟩
        · rcases S.eq_empty_or_nonempty with h0 | h0
          · have := hx8 S hS
            rw [h0, Finset.sum_empty] at this
            have : (0:ℝ) < n := by exact_mod_cast hn
            linarith
          · exact h0
        · unfold IsEffective
          rw [sg_sum_alpha x S S le_rfl, hx8 S hS, sg_win_val v hv hred S (hU hS).1]
          linarith
        · intro i hi
          have := hSR i hi
          rw [hRmem] at this
          rw [sg_alpha_eq, if_pos hi]
          linarith
      · push_neg at hcase
        have hRp : R ∈ uPlus U := by
          rintro ⟨S, hS, hsub⟩
          obtain ⟨i, hiS, hiR⟩ := hcase S hS
          exact Finset.mem_compl.mp (hsub hiS) hiR
        have hfnn : ∀ i, 0 ≤ β i + 1 := fun i => by linarith [himp.1 i, hred i]
        have hfsum : ∑ i, (β i + 1) = n := by
          rw [Finset.sum_add_distrib, himp.2]; simp
        have hRle : ∑ i ∈ R, x i ≤ ∑ i ∈ R, (β i + 1) :=
          Finset.sum_le_sum fun i hi => by have := (hRmem i).mp hi; linarith
        have hRle2 : ∑ i ∈ R, (β i + 1) ≤ ∑ i, (β i + 1) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun i _ _ => hfnn i)
        have hex : ∃ S ∈ U, ∀ i ∈ symmDiff R S, x i = 0 := by
          by_contra hc
          have := hB R hRp hc
          linarith
        obtain ⟨S, hS, hRS⟩ := hex
        have hRx : ∑ i ∈ R, x i = n := hA R ⟨S, hS, hRS⟩
        have hcompl := Finset.sum_add_sum_compl R (fun i => β i + 1)
        have hdiff : ∑ i ∈ R, ((β i + 1) - x i) = 0 := by
          rw [Finset.sum_sub_distrib]; linarith
        rw [Finset.sum_eq_zero_iff_of_nonneg
          (fun i hi => by have := (hRmem i).mp hi; linarith)] at hdiff
        have hc0 : ∑ i ∈ Rᶜ, (β i + 1) = 0 := by linarith
        rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hfnn i)] at hc0
        exfalso; apply hβ
        refine ⟨S, hS, funext fun i => ?_⟩
        rw [sg_alpha_eq]
        by_cases hiR : i ∈ R
        · have h1 := hdiff i hiR
          by_cases hiS : i ∈ S
          · rw [if_pos hiS]; linarith
          · rw [if_neg hiS]
            have := hRS i (Finset.mem_symmDiff.mpr (Or.inl ⟨hiR, hiS⟩))
            linarith
        · have h1 := hc0 i (Finset.mem_compl.mpr hiR)
          by_cases hiS : i ∈ S
          · rw [if_pos hiS]
            have := hRS i (Finset.mem_symmDiff.mpr (Or.inr ⟨hiS, hiR⟩))
            linarith
          · rw [if_neg hiS]; linarith

end TheoryOfGames.SimpleGames

open TheoryOfGames.SimpleGames


theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : IsCharFunction v)
    (hs : IsSimple v) (hred : ∀ i : Fin n, v {i} = -1)
    (U : Set (Finset (Fin n))) (hU : U ⊆ minimalSets (winningSets v))
    (x : Fin n → ℝ) (hx7 : ∀ i, 0 ≤ x i) (hx8 : ∀ S ∈ U, ∑ i ∈ S, x i = (n : ℝ)) :
    IsSolution v (mainSet U x) ↔
      ((∀ T : Finset (Fin n), (∃ S ∈ U, ∀ i ∈ symmDiff T S, x i = 0) →
          ∑ i ∈ T, x i = (n : ℝ)) ∧
        (∀ T ∈ uPlus U, (¬ ∃ S ∈ U, ∀ i ∈ symmDiff T S, x i = 0) →
          (n : ℝ) < ∑ i ∈ T, x i)) := by
  exact mainSet_core v hv hs hred U hU x hx7 hx8
