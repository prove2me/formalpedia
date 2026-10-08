-- Prove2me | solution 1 for TheoryOfGames.GeneralGames.characterization
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T18:30:14.526321+00:00
-- url     : https://prove2.me/submissions/1aec7642-f4f5-4db7-8493-64d224f137c7

import Mathlib
import Definitions.Def_TheoryOfGames_GeneralGames_GeneralGame
import Definitions.Def_TheoryOfGames_GeneralGames_charFun
import Definitions.Def_TheoryOfGames_GeneralGames_CharFunConditions



namespace TheoryOfGames.GeneralGames

open Finset

section Pay
variable {n : ℕ}

def ggValid (ch : Fin n → Finset (Fin n) × Bool) (k : Fin n) : Prop :=
  (ch k).2 = false ∧ k ∈ (ch k).1 ∧ ∀ i ∈ (ch k).1, ch i = ch k

open Classical in
noncomputable def ggPay (w : Finset (Fin n) → ℝ) (Y : ℝ) (ch : Fin n → Finset (Fin n) × Bool)
    (k : Fin n) : ℝ :=
  if ggValid ch k then w (ch k).1 / (ch k).1.card else -Y

lemma ggPay_ring (w : Finset (Fin n) → ℝ) (Y : ℝ) (ch : Fin n → Finset (Fin n) × Bool)
    (B : Finset (Fin n)) (hw0 : w ∅ = 0) (hB : ∀ j ∈ B, ch j = (B, false)) :
    ∑ j ∈ B, ggPay w Y ch j = w B := by
  classical
  rcases B.eq_empty_or_nonempty with h | h
  · subst h; simp [hw0]
  have hv : ∀ j ∈ B, ggPay w Y ch j = w B / B.card := by
    intro j hj
    have hval : ggValid ch j := ⟨by rw [hB j hj], by rw [hB j hj]; exact hj,
      fun i hi => by rw [hB j hj] at hi; rw [hB i hi, hB j hj]⟩
    unfold ggPay; rw [if_pos hval, hB j hj]
  rw [sum_congr rfl hv, sum_const, nsmul_eq_mul]
  have : (B.card : ℝ) ≠ 0 := by have := h.card_pos; positivity
  field_simp

lemma gg_sum_disj_le (w : Finset (Fin n) → ℝ) (hw0 : w ∅ = 0)
    (hws : ∀ S T : Finset (Fin n), Disjoint S T → w S + w T ≤ w (S ∪ T))
    (P : Finset (Finset (Fin n))) (hP : (P : Set (Finset (Fin n))).PairwiseDisjoint id) :
    ∑ C ∈ P, w C ≤ w (P.sup id) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp [hw0]
  | insert a P ha ih =>
    rw [Finset.sum_insert ha, Finset.sup_insert]
    have hP' : (P : Set (Finset (Fin n))).PairwiseDisjoint id :=
      hP.subset (by intro x hx; simp [hx])
    have hd : Disjoint a (P.sup id) := by
      rw [Finset.disjoint_sup_right]
      intro i hi
      exact hP (by simp) (by simp [hi]) (fun h => ha (h ▸ hi))
    have := hws a (P.sup id) hd
    have e : w (a ⊔ P.sup id) = w (a ∪ P.sup id) := rfl
    simp only [id] at this ⊢
    rw [e]
    linarith [ih hP']

lemma gg_abs_le (w : Finset (Fin n) → ℝ) (T : Finset (Fin n)) : |w T| ≤ ∑ T, |w T| :=
  single_le_sum (f := fun T => |w T|) (fun _ _ => abs_nonneg _) (mem_univ T)

lemma ggPay_closed (w : Finset (Fin n) → ℝ) (hw0 : w ∅ = 0)
    (hws : ∀ S T : Finset (Fin n), Disjoint S T → w S + w T ≤ w (S ∪ T))
    (Y : ℝ) (hY : 2 * ∑ T, |w T| ≤ Y) (ch : Fin n → Finset (Fin n) × Bool)
    (W : Finset (Fin n)) (hW : ∀ j ∈ W, ggValid ch j → (ch j).1 ⊆ W) :
    ∑ j ∈ W, ggPay w Y ch j ≤ w W := by
  classical
  have hsplit : ∑ j ∈ W, ggPay w Y ch j =
      ∑ j ∈ W.filter (ggValid ch), w (ch j).1 / (ch j).1.card +
        ∑ j ∈ W.filter (fun j => ¬ ggValid ch j), (-Y) := by
    rw [← sum_filter_add_sum_filter_not W (ggValid ch)]
    congr 1
    · apply sum_congr rfl; intro j hj; unfold ggPay; rw [if_pos (mem_filter.mp hj).2]
    · apply sum_congr rfl; intro j hj; unfold ggPay; rw [if_neg (mem_filter.mp hj).2]
  have hV : ∑ j ∈ W.filter (ggValid ch), w (ch j).1 / (ch j).1.card =
      ∑ C ∈ (W.filter (ggValid ch)).image (fun j => (ch j).1), w C := by
    rw [← sum_fiberwise_of_maps_to (s := W.filter (ggValid ch))
      (t := (W.filter (ggValid ch)).image (fun j => (ch j).1)) (g := fun j => (ch j).1)
      (fun j hj => mem_image_of_mem _ hj)]
    apply sum_congr rfl
    intro C hC
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hC
    have hmv := (mem_filter.mp hm).2
    have hmW := (mem_filter.mp hm).1
    have hfib : (W.filter (ggValid ch)).filter (fun j => (ch j).1 = (ch m).1) = (ch m).1 := by
      ext j; simp only [mem_filter]
      constructor
      · rintro ⟨⟨_, hjv⟩, hj⟩; rw [← hj]; exact hjv.2.1
      · intro hj
        have e := hmv.2.2 j hj
        refine ⟨⟨hW m hmW hmv hj, ?_⟩, by rw [e]⟩
        exact ⟨by rw [e]; exact hmv.1, by rw [e]; exact hj,
          fun i hi => by rw [e] at hi ⊢; exact hmv.2.2 i hi⟩
    rw [sum_congr rfl (fun j hj => by rw [(mem_filter.mp hj).2]), sum_const, hfib, nsmul_eq_mul]
    have : ((ch m).1.card : ℝ) ≠ 0 := by have := card_pos.mpr ⟨m, hmv.2.1⟩; positivity
    field_simp
  have hdisj : (((W.filter (ggValid ch)).image (fun j => (ch j).1) : Finset (Finset (Fin n))) :
      Set (Finset (Fin n))).PairwiseDisjoint id := by
    intro C hC D hD hCD
    rw [Finset.mem_coe, Finset.mem_image] at hC hD
    obtain ⟨c, hc, rfl⟩ := hC; obtain ⟨d, hd, rfl⟩ := hD
    rw [Function.onFun, Finset.disjoint_left]
    intro i hi1 hi2
    have hcv := (mem_filter.mp hc).2
    have hdv := (mem_filter.mp hd).2
    exact hCD (by rw [← hcv.2.2 i hi1, ← hdv.2.2 i hi2])
  have hle := gg_sum_disj_le w hw0 hws _ hdisj
  have hU : ((W.filter (ggValid ch)).image (fun j => (ch j).1)).sup id ⊆ W := by
    apply Finset.sup_le
    intro C hC
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hC
    exact hW m (mem_filter.mp hm).1 (mem_filter.mp hm).2
  rw [hsplit, hV]
  rcases (W.filter (fun j => ¬ ggValid ch j)).eq_empty_or_nonempty with hO | hO
  · rw [hO, sum_empty, add_zero]
    have : ((W.filter (ggValid ch)).image (fun j => (ch j).1)).sup id = W := by
      apply le_antisymm hU
      intro j hj
      have hjv : ggValid ch j := by
        by_contra hc
        have : j ∈ W.filter (fun j => ¬ ggValid ch j) := mem_filter.mpr ⟨hj, hc⟩
        rw [hO] at this; simp at this
      exact Finset.mem_sup.mpr ⟨(ch j).1, mem_image_of_mem _ (mem_filter.mpr ⟨hj, hjv⟩), hjv.2.1⟩
    rw [this] at hle; exact hle
  · rw [sum_const, nsmul_eq_mul]
    have h0 : 0 ≤ ∑ T, |w T| := sum_nonneg (fun _ _ => abs_nonneg _)
    have hc : (1 : ℝ) ≤ (W.filter (fun j => ¬ ggValid ch j)).card := by
      exact_mod_cast hO.card_pos
    have a1 := gg_abs_le w (((W.filter (ggValid ch)).image (fun j => (ch j).1)).sup id)
    have a2 := gg_abs_le w W
    have b1 := le_abs_self (w (((W.filter (ggValid ch)).image (fun j => (ch j).1)).sup id))
    have b2 := neg_abs_le (w W)
    nlinarith
end Pay

section Ext
variable {n : ℕ}

lemma bilin_bdd' (Γ : GeneralGame n) (S : Finset (Fin (n + 1)))
    (ξ : stdSimplex ℝ (Γ.CoalStrat (GeneralGame.realPart S)))
    (η : stdSimplex ℝ (Γ.CoalStrat (GeneralGame.realPart S)ᶜ)) :
    |Γ.bilin S (ξ : Γ.CoalStrat (GeneralGame.realPart S) → ℝ)
      (η : Γ.CoalStrat (GeneralGame.realPart S)ᶜ → ℝ)| ≤
      ∑ τS, ∑ τC, |Γ.coalPayoff S τS τC| := by
  unfold GeneralGame.bilin
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun τS _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun τC _ => ?_)
  have h1 := ξ.2.1 τS; have h2 := η.2.1 τC
  have h1' : ξ.1 τS ≤ 1 := by
    have := ξ.2.2; rw [← this]
    exact Finset.single_le_sum (fun i _ => ξ.2.1 i) (mem_univ τS)
  have h2' : η.1 τC ≤ 1 := by
    have := η.2.2; rw [← this]
    exact Finset.single_le_sum (fun i _ => η.2.1 i) (mem_univ τC)
  rw [abs_mul, abs_mul]
  have a1 : |ξ.1 τS| ≤ 1 := abs_le.mpr ⟨by linarith, h1'⟩
  have a2 : |η.1 τC| ≤ 1 := abs_le.mpr ⟨by linarith, h2'⟩
  calc _ ≤ |Γ.coalPayoff S τS τC| * 1 * 1 := by gcongr <;> first | exact a1 | exact a2
    _ = _ := by ring

lemma extCharFun_eq_of_pure (Γ : GeneralGame n) (S : Finset (Fin (n + 1))) (c : ℝ)
    (σ : Γ.CoalStrat (GeneralGame.realPart S)) (hσ : ∀ τC, c ≤ Γ.coalPayoff S σ τC)
    (σ' : Γ.CoalStrat (GeneralGame.realPart S)ᶜ) (hσ' : ∀ τS, Γ.coalPayoff S τS σ' ≤ c) :
    Γ.extCharFun S = c := by
  classical
  set M := ∑ τS, ∑ τC, |Γ.coalPayoff S τS τC|
  have : Nonempty (stdSimplex ℝ (Γ.CoalStrat (GeneralGame.realPart S))) := ⟨stdSimplex.vertex σ⟩
  have : Nonempty (stdSimplex ℝ (Γ.CoalStrat (GeneralGame.realPart S)ᶜ)) := ⟨stdSimplex.vertex σ'⟩
  have hbb : ∀ ξ : stdSimplex ℝ (Γ.CoalStrat (GeneralGame.realPart S)),
      BddBelow (Set.range fun η : stdSimplex ℝ (Γ.CoalStrat (GeneralGame.realPart S)ᶜ) =>
      Γ.bilin S (ξ : Γ.CoalStrat (GeneralGame.realPart S) → ℝ)
        (η : Γ.CoalStrat (GeneralGame.realPart S)ᶜ → ℝ)) := by
    intro ξ; refine ⟨-M, ?_⟩; rintro _ ⟨η, rfl⟩
    exact (abs_le.mp (bilin_bdd' Γ S ξ η)).1
  have hup : ∀ ξ : stdSimplex ℝ (Γ.CoalStrat (GeneralGame.realPart S)),
      (⨅ η : stdSimplex ℝ (Γ.CoalStrat (GeneralGame.realPart S)ᶜ),
      Γ.bilin S (ξ : Γ.CoalStrat (GeneralGame.realPart S) → ℝ)
        (η : Γ.CoalStrat (GeneralGame.realPart S)ᶜ → ℝ)) ≤ c := by
    intro ξ
    refine (ciInf_le (hbb ξ) (stdSimplex.vertex σ')).trans ?_
    unfold GeneralGame.bilin
    simp [Pi.single_apply]
    calc ∑ τS, Γ.coalPayoff S τS σ' * ξ.1 τS ≤ ∑ τS, c * ξ.1 τS :=
          Finset.sum_le_sum fun τS _ => mul_le_mul_of_nonneg_right (hσ' τS) (ξ.2.1 τS)
      _ = c := by rw [← Finset.mul_sum, ξ.2.2, mul_one]
  unfold GeneralGame.extCharFun
  apply le_antisymm
  · exact ciSup_le hup
  · refine le_trans ?_ (le_ciSup (f := fun ξ : stdSimplex ℝ (Γ.CoalStrat (GeneralGame.realPart S)) =>
      ⨅ η : stdSimplex ℝ (Γ.CoalStrat (GeneralGame.realPart S)ᶜ),
      Γ.bilin S (ξ : Γ.CoalStrat (GeneralGame.realPart S) → ℝ)
        (η : Γ.CoalStrat (GeneralGame.realPart S)ᶜ → ℝ)) ⟨c, ?_⟩
      (stdSimplex.vertex σ))
    · apply le_ciInf
      intro η
      unfold GeneralGame.bilin
      simp [Pi.single_apply]
      calc c = ∑ τC, c * η.1 τC := by rw [← Finset.mul_sum, η.2.2, mul_one]
        _ ≤ ∑ τC, Γ.coalPayoff S σ τC * η.1 τC :=
          Finset.sum_le_sum fun τC _ => mul_le_mul_of_nonneg_right (hσ τC) (η.2.1 τC)
    · rintro _ ⟨ξ, rfl⟩; exact hup ξ

lemma sum_extH (Γ : GeneralGame n) (τ : (k : Fin n) → Fin (Γ.β k)) (S : Finset (Fin (n + 1))) :
    ∑ i ∈ S, Γ.extH τ i = ∑ k ∈ GeneralGame.realPart S, Γ.H τ k -
      (if Fin.last n ∈ S then ∑ k, Γ.H τ k else 0) := by
  classical
  have : ∑ i ∈ S, Γ.extH τ i = ∑ i, if i ∈ S then Γ.extH τ i else 0 := by
    rw [Finset.sum_ite_mem, univ_inter]
  rw [this, Fin.sum_univ_castSucc]
  unfold GeneralGame.realPart
  rw [Finset.sum_filter]
  simp only [GeneralGame.extH, Fin.lastCases_castSucc, Fin.lastCases_last]
  split_ifs <;> ring

lemma sum_extH_univ (Γ : GeneralGame n) (τ : (k : Fin n) → Fin (Γ.β k)) :
    ∑ i, Γ.extH τ i = 0 := by
  rw [Fin.sum_univ_castSucc]
  simp only [GeneralGame.extH, Fin.lastCases_castSucc, Fin.lastCases_last]
  ring

end Ext


section Build
variable {n : ℕ}

noncomputable def wOf (v : Finset (Fin (n + 1)) → ℝ) (R : Finset (Fin n)) : ℝ :=
  v (R.map Fin.castSuccEmb)

noncomputable def extGame (v : Finset (Fin (n + 1)) → ℝ) : GeneralGame n where
  β := fun _ => Fintype.card (Finset (Fin n) × Bool)
  β_pos := fun _ => Fintype.card_pos
  H := fun τ k => ggPay (wOf v) (2 * ∑ T, |wOf v T|)
    (fun j => (Fintype.equivFin (Finset (Fin n) × Bool)).symm (τ j)) k

lemma wOf_zero (v : Finset (Fin (n + 1)) → ℝ) (hv : IsExtendedCharFunction v) :
    wOf v ∅ = 0 := by
  unfold wOf; simpa using hv.1

lemma wOf_super (v : Finset (Fin (n + 1)) → ℝ) (hv : IsExtendedCharFunction v)
    (S T : Finset (Fin n)) (h : Disjoint S T) : wOf v S + wOf v T ≤ wOf v (S ∪ T) := by
  classical
  unfold wOf
  rw [Finset.map_union]
  exact hv.2.2 _ _ ((Finset.disjoint_map _).mpr h)

lemma extGame_guar (v : Finset (Fin (n + 1)) → ℝ) (hv : IsExtendedCharFunction v)
    (S : Finset (Fin (n + 1))) (τ : (k : Fin n) → Fin ((extGame v).β k))
    (hτ : ∀ k ∈ GeneralGame.realPart S, τ k =
      Fintype.equivFin (Finset (Fin n) × Bool) (GeneralGame.realPart S, decide (Fin.last n ∈ S))) :
    v S ≤ ∑ i ∈ S, (extGame v).extH τ i := by
  classical
  rw [sum_extH]
  set R := GeneralGame.realPart S with hR
  set ch : Fin n → Finset (Fin n) × Bool :=
    fun j => (Fintype.equivFin (Finset (Fin n) × Bool)).symm (τ j) with hch_def
  have hH : ∀ k, (extGame v).H τ k = ggPay (wOf v) (2 * ∑ T, |wOf v T|) ch k := fun k => rfl
  have hch : ∀ k ∈ R, ch k = (R, decide (Fin.last n ∈ S)) := by
    intro k hk; simp only [hch_def]; rw [hτ k hk]; simp
  simp only [hH]
  by_cases hl : Fin.last n ∈ S
  · rw [if_pos hl, ← sum_add_sum_compl R]
    have hcl := ggPay_closed (wOf v) (wOf_zero v hv) (wOf_super v hv) _ le_rfl ch Rᶜ (by
      intro j hj hjv i hi
      rw [mem_compl]
      intro hiR
      have e1 := hjv.2.2 i hi
      rw [hch i hiR] at e1
      have e2 := hjv.1
      rw [← e1] at e2
      simp [hl] at e2)
    have hmap : Rᶜ.map Fin.castSuccEmb = Sᶜ := by
      ext i
      induction i using Fin.lastCases with
      | last => simp [hl]
      | cast k => simp [hR, GeneralGame.realPart]
    have : wOf v Rᶜ = - v S := by unfold wOf; rw [hmap, hv.2.1]
    linarith
  · rw [if_neg hl, sub_zero]
    have hS : R.map Fin.castSuccEmb = S := by
      ext i
      induction i using Fin.lastCases with
      | last => simp [hl]
      | cast k => simp [hR, GeneralGame.realPart]
    rw [ggPay_ring (wOf v) _ ch R (wOf_zero v hv) (fun j hj => by rw [hch j hj]; simp [hl])]
    unfold wOf; rw [hS]

theorem exists_game_of_extended_core (v : Finset (Fin (n + 1)) → ℝ)
    (hv : IsExtendedCharFunction v) :
    ∃ Γ : GeneralGame n, Γ.extCharFun = v := by
  classical
  refine ⟨extGame v, funext fun S => ?_⟩
  apply extCharFun_eq_of_pure (extGame v) S (v S)
    (fun _ => Fintype.equivFin (Finset (Fin n) × Bool) (GeneralGame.realPart S, decide (Fin.last n ∈ S))) ?_
    (fun _ => Fintype.equivFin (Finset (Fin n) × Bool) (GeneralGame.realPart Sᶜ, decide (Fin.last n ∈ Sᶜ))) ?_
  · intro τC
    unfold GeneralGame.coalPayoff
    apply extGame_guar v hv
    intro k hk
    simp [GeneralGame.joint, hk]; congr
  · intro τS
    have h1 := extGame_guar v hv Sᶜ ((extGame v).joint (GeneralGame.realPart S) τS
      (fun _ => Fintype.equivFin (Finset (Fin n) × Bool) (GeneralGame.realPart Sᶜ, decide (Fin.last n ∈ Sᶜ))))
      (by
        intro k hk
        have hk' : k ∉ GeneralGame.realPart S := by
          simp only [GeneralGame.realPart, mem_filter, mem_univ, true_and, mem_compl] at hk ⊢
          exact hk
        simp [GeneralGame.joint, hk']; congr)
    have h0 := sum_extH_univ (extGame v) ((extGame v).joint (GeneralGame.realPart S) τS
      (fun _ => Fintype.equivFin (Finset (Fin n) × Bool) (GeneralGame.realPart Sᶜ, decide (Fin.last n ∈ Sᶜ))))
    rw [← Finset.sum_add_sum_compl S] at h0
    unfold GeneralGame.coalPayoff
    rw [hv.2.1] at h1
    linarith

end Build

section Restr
variable {n : ℕ}

lemma realPart_compl' (S : Finset (Fin (n + 1))) :
    GeneralGame.realPart Sᶜ = (GeneralGame.realPart S)ᶜ := by
  ext k; simp [GeneralGame.realPart]

lemma realPart_union' (S T : Finset (Fin (n + 1))) :
    GeneralGame.realPart (S ∪ T) = GeneralGame.realPart S ∪ GeneralGame.realPart T := by
  ext k; simp [GeneralGame.realPart]

lemma realPart_map' (S : Finset (Fin n)) :
    GeneralGame.realPart (S.map Fin.castSuccEmb) = S := by
  ext k; simp [GeneralGame.realPart]

lemma realPart_disj (S T : Finset (Fin (n + 1))) (h : Disjoint S T) :
    Disjoint (GeneralGame.realPart S) (GeneralGame.realPart T) := by
  rw [Finset.disjoint_left] at h ⊢
  intro k h1 h2
  simp only [GeneralGame.realPart, mem_filter, mem_univ, true_and] at h1 h2
  exact h h1 h2

open Classical in
noncomputable def extOf (v : Finset (Fin n) → ℝ) (S : Finset (Fin (n + 1))) : ℝ :=
  if Fin.last n ∈ S then -v (GeneralGame.realPart S)ᶜ else v (GeneralGame.realPart S)

lemma extOf_isExt (v : Finset (Fin n) → ℝ) (hv : IsRestrictedCharFunction v) :
    IsExtendedCharFunction (extOf v) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · unfold extOf
    rw [if_neg (by simp)]
    have : GeneralGame.realPart (∅ : Finset (Fin (n + 1))) = ∅ := by
      ext k; simp [GeneralGame.realPart]
    rw [this, hv.1]
  · intro S
    unfold extOf
    rw [realPart_compl']
    by_cases hl : Fin.last n ∈ S
    · rw [if_neg (by simpa using hl), if_pos hl]; ring
    · rw [if_pos (by simpa using hl), if_neg hl, compl_compl]
  · intro S T hST
    unfold extOf
    have hd := realPart_disj S T hST
    rw [realPart_union']
    by_cases hS : Fin.last n ∈ S
    · have hT : Fin.last n ∉ T := fun hT => (Finset.disjoint_left.mp hST) hS hT
      rw [if_pos hS, if_neg hT, if_pos (mem_union_left _ hS)]
      have hsub : GeneralGame.realPart T ⊆ (GeneralGame.realPart S)ᶜ := by
        intro k hk; rw [mem_compl]; intro hk'; exact (Finset.disjoint_left.mp hd) hk' hk
      have e : GeneralGame.realPart T ∪ (GeneralGame.realPart S ∪ GeneralGame.realPart T)ᶜ =
          (GeneralGame.realPart S)ᶜ := by
        ext k; simp only [mem_union, mem_compl]; constructor
        · rintro (h | h)
          · exact mem_compl.mp (hsub h)
          · tauto
        · intro h; by_cases h' : k ∈ GeneralGame.realPart T <;> tauto
      have := hv.2 (GeneralGame.realPart T) (GeneralGame.realPart S ∪ GeneralGame.realPart T)ᶜ
        (by rw [Finset.disjoint_left]; intro k h1 h2; simp at h2; tauto)
      rw [e] at this; linarith
    · by_cases hT : Fin.last n ∈ T
      · rw [if_neg hS, if_pos hT, if_pos (mem_union_right _ hT)]
        have hsub : GeneralGame.realPart S ⊆ (GeneralGame.realPart T)ᶜ := by
          intro k hk; rw [mem_compl]; intro hk'; exact (Finset.disjoint_left.mp hd) hk hk'
        have e : GeneralGame.realPart S ∪ (GeneralGame.realPart S ∪ GeneralGame.realPart T)ᶜ =
            (GeneralGame.realPart T)ᶜ := by
          ext k; simp only [mem_union, mem_compl]; constructor
          · rintro (h | h)
            · exact mem_compl.mp (hsub h)
            · tauto
          · intro h; by_cases h' : k ∈ GeneralGame.realPart S <;> tauto
        have := hv.2 (GeneralGame.realPart S) (GeneralGame.realPart S ∪ GeneralGame.realPart T)ᶜ
          (by rw [Finset.disjoint_left]; intro k h1 h2; simp at h2; tauto)
        rw [e] at this; linarith
      · rw [if_neg hS, if_neg hT, if_neg (by simp [hS, hT])]
        exact hv.2 _ _ hd

theorem exists_game_of_restricted_core (v : Finset (Fin n) → ℝ)
    (hv : IsRestrictedCharFunction v) :
    ∃ Γ : GeneralGame n, Γ.restrictedCharFun = v := by
  obtain ⟨Γ, hΓ⟩ := exists_game_of_extended_core (extOf v) (extOf_isExt v hv)
  refine ⟨Γ, funext fun S => ?_⟩
  unfold GeneralGame.restrictedCharFun
  rw [hΓ]
  unfold extOf
  rw [if_neg (by simp), realPart_map']

end Restr

namespace XI
variable {n : ℕ} (Γ : GeneralGame n)
local notation "rp" => GeneralGame.realPart

lemma bilin_eq1 (S : Finset (Fin (n + 1))) (ξ : Γ.CoalStrat (rp S) → ℝ) (η : Γ.CoalStrat (rp S)ᶜ → ℝ) :
    Γ.bilin S ξ η = ∑ τC, η τC * ∑ τS, ξ τS * Γ.coalPayoff S τS τC := by
  unfold GeneralGame.bilin; rw [Finset.sum_comm]
  refine sum_congr rfl fun _ _ => ?_; rw [mul_sum]
  exact sum_congr rfl fun _ _ => by ring

lemma bilin_eq2 (S : Finset (Fin (n + 1))) (ξ : Γ.CoalStrat (rp S) → ℝ) (η : Γ.CoalStrat (rp S)ᶜ → ℝ) :
    Γ.bilin S ξ η = ∑ τS, ξ τS * ∑ τC, η τC * Γ.coalPayoff S τS τC := by
  unfold GeneralGame.bilin
  refine sum_congr rfl fun _ _ => ?_; rw [mul_sum]
  exact sum_congr rfl fun _ _ => by ring

lemma bilin_bdd (S : Finset (Fin (n + 1)))
    (ξ : stdSimplex ℝ (Γ.CoalStrat (rp S))) (η : stdSimplex ℝ (Γ.CoalStrat (rp S)ᶜ)) :
    |Γ.bilin S (ξ : Γ.CoalStrat (rp S) → ℝ) (η : Γ.CoalStrat (rp S)ᶜ → ℝ)| ≤
      ∑ τS, ∑ τC, |Γ.coalPayoff S τS τC| := by
  unfold GeneralGame.bilin
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun τS _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun τC _ => ?_)
  have h1 := ξ.2.1 τS; have h2 := η.2.1 τC
  have h1' : ξ.1 τS ≤ 1 := by
    have := ξ.2.2; rw [← this]
    exact Finset.single_le_sum (fun i _ => ξ.2.1 i) (mem_univ τS)
  have h2' : η.1 τC ≤ 1 := by
    have := η.2.2; rw [← this]
    exact Finset.single_le_sum (fun i _ => η.2.1 i) (mem_univ τC)
  rw [abs_mul, abs_mul]
  have a1 : |ξ.1 τS| ≤ 1 := abs_le.mpr ⟨by linarith, h1'⟩
  have a2 : |η.1 τC| ≤ 1 := abs_le.mpr ⟨by linarith, h2'⟩
  calc _ ≤ |Γ.coalPayoff S τS τC| * 1 * 1 := by gcongr <;> first | exact a1 | exact a2
    _ = _ := by ring

lemma bddBelow_inner (S : Finset (Fin (n + 1))) (ξ : stdSimplex ℝ (Γ.CoalStrat (rp S))) :
    BddBelow (Set.range fun η : stdSimplex ℝ (Γ.CoalStrat (rp S)ᶜ) =>
      Γ.bilin S (ξ : Γ.CoalStrat (rp S) → ℝ) (η : Γ.CoalStrat (rp S)ᶜ → ℝ)) := by
  refine ⟨-(∑ τS, ∑ τC, |Γ.coalPayoff S τS τC|), ?_⟩; rintro _ ⟨η, rfl⟩
  exact (abs_le.mp (bilin_bdd Γ S ξ η)).1

lemma inner_le (S : Finset (Fin (n + 1))) (ξ : stdSimplex ℝ (Γ.CoalStrat (rp S))) :
    (⨅ η : stdSimplex ℝ (Γ.CoalStrat (rp S)ᶜ),
      Γ.bilin S (ξ : Γ.CoalStrat (rp S) → ℝ) (η : Γ.CoalStrat (rp S)ᶜ → ℝ)) ≤
      ∑ τS, ∑ τC, |Γ.coalPayoff S τS τC| := by
  classical
  have hne : Nonempty (Γ.CoalStrat (rp S)ᶜ) := ⟨fun k => ⟨0, Γ.β_pos k⟩⟩
  obtain ⟨τ⟩ := hne
  exact (ciInf_le (bddBelow_inner Γ S ξ) (stdSimplex.vertex τ)).trans
    (abs_le.mp (bilin_bdd Γ S ξ _)).2

lemma le_xcharFun (S : Finset (Fin (n + 1))) (c : ℝ) (ξ : stdSimplex ℝ (Γ.CoalStrat (rp S)))
    (h : ∀ τC, c ≤ ∑ τS, ξ τS * Γ.coalPayoff S τS τC) : c ≤ Γ.extCharFun S := by
  classical
  have hne2 : Nonempty (stdSimplex ℝ (Γ.CoalStrat (rp S)ᶜ)) :=
    ⟨stdSimplex.vertex (show Γ.CoalStrat (rp S)ᶜ from fun k => ⟨0, Γ.β_pos k⟩)⟩
  unfold GeneralGame.extCharFun
  refine le_trans ?_ (le_ciSup (f := fun ξ : stdSimplex ℝ (Γ.CoalStrat (rp S)) =>
      ⨅ η : stdSimplex ℝ (Γ.CoalStrat (rp S)ᶜ),
      Γ.bilin S (ξ : Γ.CoalStrat (rp S) → ℝ) (η : Γ.CoalStrat (rp S)ᶜ → ℝ)) ⟨∑ τS, ∑ τC, |Γ.coalPayoff S τS τC|, ?_⟩ ξ)
  · apply le_ciInf
    intro η
    rw [bilin_eq1]
    calc c = ∑ τC, η τC * c := by rw [← Finset.sum_mul, stdSimplex.sum_eq_one, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun τC _ =>
          mul_le_mul_of_nonneg_left (h τC) (stdSimplex.zero_le η τC)
  · rintro _ ⟨ξ', rfl⟩; exact inner_le Γ S ξ'

lemma xcharFun_le (S : Finset (Fin (n + 1))) (c : ℝ) (η : stdSimplex ℝ (Γ.CoalStrat (rp S)ᶜ))
    (h : ∀ τS, ∑ τC, η τC * Γ.coalPayoff S τS τC ≤ c) : Γ.extCharFun S ≤ c := by
  classical
  have hne1 : Nonempty (stdSimplex ℝ (Γ.CoalStrat (rp S))) :=
    ⟨stdSimplex.vertex (show Γ.CoalStrat (rp S) from fun k => ⟨0, Γ.β_pos k⟩)⟩
  unfold GeneralGame.extCharFun
  apply ciSup_le
  intro ξ
  refine (ciInf_le (bddBelow_inner Γ S ξ) η).trans ?_
  rw [bilin_eq2]
  calc _ ≤ ∑ τS, ξ τS * c := Finset.sum_le_sum fun τS _ =>
          mul_le_mul_of_nonneg_left (h τS) (stdSimplex.zero_le ξ τS)
    _ = c := by rw [← Finset.sum_mul, stdSimplex.sum_eq_one, one_mul]

lemma bilin_affine_left (S : Finset (Fin (n + 1))) (η : Γ.CoalStrat (rp S)ᶜ → ℝ)
    (x y : Γ.CoalStrat (rp S) → ℝ) (a b : ℝ) :
    Γ.bilin S (a • x + b • y) η = a * Γ.bilin S x η + b * Γ.bilin S y η := by
  unfold GeneralGame.bilin
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun _ _ => ?_
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun _ _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

lemma bilin_affine_right (S : Finset (Fin (n + 1))) (ξ : Γ.CoalStrat (rp S) → ℝ)
    (x y : Γ.CoalStrat (rp S)ᶜ → ℝ) (a b : ℝ) :
    Γ.bilin S ξ (a • x + b • y) = a * Γ.bilin S ξ x + b * Γ.bilin S ξ y := by
  unfold GeneralGame.bilin
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun _ _ => ?_
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun _ _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

lemma bilin_cont (S : Finset (Fin (n + 1))) :
    Continuous fun p : (Γ.CoalStrat (rp S) → ℝ) × (Γ.CoalStrat (rp S)ᶜ → ℝ) => Γ.bilin S p.1 p.2 := by
  unfold GeneralGame.bilin
  fun_prop

/-- master lemma: optimal strategies exist -/
lemma master (S : Finset (Fin (n + 1))) :
    ∃ ξ : stdSimplex ℝ (Γ.CoalStrat (rp S)), ∃ η : stdSimplex ℝ (Γ.CoalStrat (rp S)ᶜ),
      (∀ τC, Γ.extCharFun S ≤ ∑ τS, ξ τS * Γ.coalPayoff S τS τC) ∧
      (∀ τS, ∑ τC, η τC * Γ.coalPayoff S τS τC ≤ Γ.extCharFun S) := by
  classical
  have neX : (stdSimplex ℝ (Γ.CoalStrat (rp S)ᶜ)).Nonempty :=
    ⟨_, single_mem_stdSimplex ℝ (show Γ.CoalStrat (rp S)ᶜ from fun k => ⟨0, Γ.β_pos k⟩)⟩
  have neY : (stdSimplex ℝ (Γ.CoalStrat (rp S))).Nonempty :=
    ⟨_, single_mem_stdSimplex ℝ (show Γ.CoalStrat (rp S) from fun k => ⟨0, Γ.β_pos k⟩)⟩
  obtain ⟨a, ha, b, hb, hab⟩ := Sion.exists_isSaddlePointOn
    (f := fun (x : Γ.CoalStrat (rp S)ᶜ → ℝ) (y : Γ.CoalStrat (rp S) → ℝ) => Γ.bilin S y x)
    neX (convex_stdSimplex ℝ _) (isCompact_stdSimplex ℝ _)
    (fun y _ => ((bilin_cont Γ S).comp (Continuous.prodMk continuous_const continuous_id)).continuousOn.lowerSemicontinuousOn)
    (fun y _ => ConvexOn.quasiconvexOn ⟨convex_stdSimplex ℝ _, fun x _ z _ p q _ _ _ => by
      simp only [smul_eq_mul]; rw [bilin_affine_right]⟩)
    (convex_stdSimplex ℝ _) neY (isCompact_stdSimplex ℝ _)
    (fun x _ => ((bilin_cont Γ S).comp (Continuous.prodMk continuous_id continuous_const)).continuousOn.upperSemicontinuousOn)
    (fun x _ => ConcaveOn.quasiconcaveOn ⟨convex_stdSimplex ℝ _, fun x _ z _ p q _ _ _ => by
      simp only [smul_eq_mul]; rw [bilin_affine_left]⟩)
  set ξ : stdSimplex ℝ (Γ.CoalStrat (rp S)) := ⟨b, hb⟩
  set η : stdSimplex ℝ (Γ.CoalStrat (rp S)ᶜ) := ⟨a, ha⟩
  -- hab : ∀ x ∈ X, ∀ y ∈ Y, bilin y a ≤ bilin b x
  have h1 : ∀ τC, Γ.bilin S b a ≤ ∑ τS, ξ τS * Γ.coalPayoff S τS τC := by
    intro τC
    have := hab _ (single_mem_stdSimplex ℝ τC) b hb
    simp only at this
    refine this.trans (le_of_eq ?_)
    rw [bilin_eq1]
    simp [Pi.single_apply]
    rfl
  have h2 : ∀ τS, ∑ τC, η τC * Γ.coalPayoff S τS τC ≤ Γ.bilin S b a := by
    intro τS
    have := hab a ha _ (single_mem_stdSimplex ℝ τS)
    simp only at this
    refine le_trans (le_of_eq ?_) this
    rw [bilin_eq2]
    simp [Pi.single_apply]
    rfl
  have hc : Γ.extCharFun S = Γ.bilin S b a :=
    le_antisymm (xcharFun_le Γ S _ η h2) (le_xcharFun Γ S _ ξ h1)
  exact ⟨ξ, η, fun τC => hc ▸ h1 τC, fun τS => hc ▸ h2 τS⟩


lemma xcharFun_empty : Γ.extCharFun ∅ = 0 := by
  classical
  have hc : ∀ τS τC, Γ.coalPayoff ∅ τS τC = 0 := fun _ _ => by simp [GeneralGame.coalPayoff]
  apply le_antisymm
  · exact xcharFun_le Γ ∅ 0 (stdSimplex.vertex (show Γ.CoalStrat (rp (∅ : Finset (Fin (n + 1))))ᶜ from
      fun k => ⟨0, Γ.β_pos k⟩)) (fun τS => by simp [hc])
  · exact le_xcharFun Γ ∅ 0 (stdSimplex.vertex (show Γ.CoalStrat (rp (∅ : Finset (Fin (n + 1)))) from
      fun k => ⟨0, Γ.β_pos k⟩)) (fun τC => by simp [hc])

def eqv {S T : Finset (Fin n)} (h : ∀ k, k ∈ S ↔ k ∈ T) : Γ.CoalStrat S ≃ Γ.CoalStrat T where
  toFun f := fun k => f ⟨k.1, (h k.1).mpr k.2⟩
  invFun g := fun k => g ⟨k.1, (h k.1).mp k.2⟩
  left_inv f := rfl
  right_inv g := rfl

lemma mem_rp (S : Finset (Fin (n + 1))) (k : Fin n) : k ∈ rp S ↔ Fin.castSucc k ∈ S := by
  simp [GeneralGame.realPart]

lemma h1c (S : Finset (Fin (n + 1))) : ∀ k, k ∈ rp Sᶜ ↔ k ∈ (rp S)ᶜ := by
  intro k; simp [mem_rp]

lemma h2c (S : Finset (Fin (n + 1))) : ∀ k, k ∈ (rp Sᶜ)ᶜ ↔ k ∈ rp S := by
  intro k; simp [mem_rp]

lemma joint_compl (S : Finset (Fin (n + 1))) (τ1 : Γ.CoalStrat (rp Sᶜ))
    (τ2 : Γ.CoalStrat (rp Sᶜ)ᶜ) :
    Γ.joint (rp Sᶜ) τ1 τ2 = Γ.joint (rp S) (eqv Γ (h2c S) τ2) (eqv Γ (h1c S) τ1) := by
  funext k
  unfold GeneralGame.joint
  by_cases hk : k ∈ rp S
  · have : k ∉ rp Sᶜ := by rw [h1c]; simpa using hk
    rw [dif_neg this, dif_pos hk]; rfl
  · have : k ∈ rp Sᶜ := by rw [h1c]; simpa using hk
    rw [dif_pos this, dif_neg hk]; rfl

lemma coalPayoff_compl (S : Finset (Fin (n + 1))) (τ1 : Γ.CoalStrat (rp Sᶜ))
    (τ2 : Γ.CoalStrat (rp Sᶜ)ᶜ) :
    Γ.coalPayoff Sᶜ τ1 τ2 = -Γ.coalPayoff S (eqv Γ (h2c S) τ2) (eqv Γ (h1c S) τ1) := by
  unfold GeneralGame.coalPayoff
  rw [joint_compl]
  have := sum_extH_univ Γ (Γ.joint (rp S) (eqv Γ (h2c S) τ2) (eqv Γ (h1c S) τ1))
  rw [← Finset.sum_compl_add_sum S] at this
  linarith

lemma xcharFun_compl (S : Finset (Fin (n + 1))) : Γ.extCharFun Sᶜ = -Γ.extCharFun S := by
  classical
  obtain ⟨ξ, η, h1, h2⟩ := master Γ S
  set e2 := eqv Γ (h2c S)
  set e1 := eqv Γ (h1c S)
  have hmem2 : (fun τ2 => ξ (e2 τ2)) ∈ stdSimplex ℝ (Γ.CoalStrat (rp Sᶜ)ᶜ) := by
    refine ⟨fun τ2 => stdSimplex.zero_le ξ _, ?_⟩
    rw [Equiv.sum_comp e2 (fun x => ξ x), stdSimplex.sum_eq_one]
  have hmem1 : (fun τ1 => η (e1 τ1)) ∈ stdSimplex ℝ (Γ.CoalStrat (rp Sᶜ)) := by
    refine ⟨fun τ1 => stdSimplex.zero_le η _, ?_⟩
    rw [Equiv.sum_comp e1 (fun x => η x), stdSimplex.sum_eq_one]
  apply le_antisymm
  · apply xcharFun_le Γ Sᶜ _ ⟨_, hmem2⟩
    intro τ1
    change ∑ τ2, ξ (e2 τ2) * Γ.coalPayoff Sᶜ τ1 τ2 ≤ _
    simp only [coalPayoff_compl]
    rw [Equiv.sum_comp e2 (fun x => ξ x * -Γ.coalPayoff S x (e1 τ1))]
    have := h1 (e1 τ1)
    simp only [mul_neg, sum_neg_distrib]; linarith
  · apply le_xcharFun Γ Sᶜ _ ⟨_, hmem1⟩
    intro τ2
    change _ ≤ ∑ τ1, η (e1 τ1) * Γ.coalPayoff Sᶜ τ1 τ2
    simp only [coalPayoff_compl]
    rw [Equiv.sum_comp e1 (fun y => η y * -Γ.coalPayoff S (e2 τ2) y)]
    have := h2 (e2 τ2)
    simp only [mul_neg, sum_neg_distrib]; linarith

section Union
variable {S T : Finset (Fin (n + 1))} (hST : Disjoint S T)
include hST

lemma mem_rpU (k : Fin n) : k ∈ rp (S ∪ T) ↔ k ∈ rp S ∨ k ∈ rp T := by
  simp [mem_rp]

lemma rp_disj : Disjoint (rp S) (rp T) := realPart_disj S T hST

def splitEqv : Γ.CoalStrat (rp (S ∪ T)) ≃ Γ.CoalStrat (rp S) × Γ.CoalStrat (rp T) where
  toFun τ := (fun k => τ ⟨k.1, (mem_rpU hST k.1).mpr (Or.inl k.2)⟩,
    fun k => τ ⟨k.1, (mem_rpU hST k.1).mpr (Or.inr k.2)⟩)
  invFun p := fun k => if h : k.1 ∈ rp S then p.1 ⟨k.1, h⟩ else
    p.2 ⟨k.1, by rcases (mem_rpU hST k.1).mp k.2 with h' | h'; exacts [absurd h' h, h']⟩
  left_inv τ := by
    funext k
    by_cases h : k.1 ∈ rp S <;> simp [h]
  right_inv p := by
    ext k
    · simp [k.2]
    · have : k.1 ∉ rp S := fun h => Finset.disjoint_left.mp (rp_disj hST) h k.2
      simp [this]

def gS (b : Γ.CoalStrat (rp T)) (ρ : Γ.CoalStrat (rp (S ∪ T))ᶜ) : Γ.CoalStrat (rp S)ᶜ :=
  fun k => if h : k.1 ∈ rp T then b ⟨k.1, h⟩ else
    ρ ⟨k.1, by
      have := k.2; rw [mem_compl] at this ⊢; rw [mem_rpU hST]; tauto⟩

def gT (a : Γ.CoalStrat (rp S)) (ρ : Γ.CoalStrat (rp (S ∪ T))ᶜ) : Γ.CoalStrat (rp T)ᶜ :=
  fun k => if h : k.1 ∈ rp S then a ⟨k.1, h⟩ else
    ρ ⟨k.1, by
      have := k.2; rw [mem_compl] at this ⊢; rw [mem_rpU hST]; tauto⟩

lemma joint_union_S (a : Γ.CoalStrat (rp S)) (b : Γ.CoalStrat (rp T))
    (ρ : Γ.CoalStrat (rp (S ∪ T))ᶜ) :
    Γ.joint (rp (S ∪ T)) ((splitEqv Γ hST).symm (a, b)) ρ = Γ.joint (rp S) a (gS Γ hST b ρ) := by
  funext k
  unfold GeneralGame.joint gS splitEqv
  by_cases hS : k ∈ rp S
  · have hU : k ∈ rp (S ∪ T) := (mem_rpU hST k).mpr (Or.inl hS)
    simp only [Equiv.coe_fn_symm_mk, dif_pos hU, dif_pos hS]
  · by_cases hT : k ∈ rp T
    · have hU : k ∈ rp (S ∪ T) := (mem_rpU hST k).mpr (Or.inr hT)
      simp only [Equiv.coe_fn_symm_mk, dif_pos hU, dif_neg hS, dif_pos hT]
    · have hU : k ∉ rp (S ∪ T) := by rw [mem_rpU hST]; tauto
      simp only [dif_neg hU, dif_neg hS, dif_neg hT]

lemma joint_union_T (a : Γ.CoalStrat (rp S)) (b : Γ.CoalStrat (rp T))
    (ρ : Γ.CoalStrat (rp (S ∪ T))ᶜ) :
    Γ.joint (rp (S ∪ T)) ((splitEqv Γ hST).symm (a, b)) ρ = Γ.joint (rp T) b (gT Γ hST a ρ) := by
  funext k
  unfold GeneralGame.joint gT splitEqv
  by_cases hS : k ∈ rp S
  · have hT : k ∉ rp T := fun h => Finset.disjoint_left.mp (rp_disj hST) hS h
    have hU : k ∈ rp (S ∪ T) := (mem_rpU hST k).mpr (Or.inl hS)
    simp only [Equiv.coe_fn_symm_mk, dif_pos hU, dif_pos hS, dif_neg hT]
  · by_cases hT : k ∈ rp T
    · have hU : k ∈ rp (S ∪ T) := (mem_rpU hST k).mpr (Or.inr hT)
      simp only [Equiv.coe_fn_symm_mk, dif_pos hU, dif_neg hS, dif_pos hT]
    · have hU : k ∉ rp (S ∪ T) := by rw [mem_rpU hST]; tauto
      simp only [dif_neg hU, dif_neg hS, dif_neg hT]

lemma xcharFun_union : Γ.extCharFun S + Γ.extCharFun T ≤ Γ.extCharFun (S ∪ T) := by
  classical
  obtain ⟨ξS, -, hS, -⟩ := master Γ S
  obtain ⟨ξT, -, hT, -⟩ := master Γ T
  set e := splitEqv Γ hST
  let F : Γ.CoalStrat (rp (S ∪ T)) → ℝ := fun τ => ξS (e τ).1 * ξT (e τ).2
  have hF : ∀ G : Γ.CoalStrat (rp (S ∪ T)) → ℝ, ∑ τ, G τ = ∑ a, ∑ b, G (e.symm (a, b)) := by
    intro G
    rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
  have hmem : F ∈ stdSimplex ℝ (Γ.CoalStrat (rp (S ∪ T))) := by
    refine ⟨fun τ => mul_nonneg (stdSimplex.zero_le _ _) (stdSimplex.zero_le _ _), ?_⟩
    rw [hF]
    simp only [F, Equiv.apply_symm_apply]
    simp_rw [← mul_sum, stdSimplex.sum_eq_one, mul_one, stdSimplex.sum_eq_one]
  apply le_xcharFun Γ (S ∪ T) _ ⟨F, hmem⟩
  intro ρ
  change _ ≤ ∑ τ, F τ * Γ.coalPayoff (S ∪ T) τ ρ
  rw [hF]
  have hsplit : ∀ a b, Γ.coalPayoff (S ∪ T) (e.symm (a, b)) ρ =
      Γ.coalPayoff S a (gS Γ hST b ρ) + Γ.coalPayoff T b (gT Γ hST a ρ) := by
    intro a b
    unfold GeneralGame.coalPayoff
    rw [sum_union hST]
    congr 1
    · rw [joint_union_S]
    · rw [joint_union_T]
  simp only [F, Equiv.apply_symm_apply, hsplit, mul_add, sum_add_distrib]
  have e1 : ∑ a, ∑ b, ξS a * ξT b * Γ.coalPayoff S a (gS Γ hST b ρ) =
      ∑ b, ξT b * ∑ a, ξS a * Γ.coalPayoff S a (gS Γ hST b ρ) := by
    rw [sum_comm]; refine sum_congr rfl fun b _ => ?_; rw [mul_sum]
    exact sum_congr rfl fun a _ => by ring
  have e2 : ∑ a, ∑ b, ξS a * ξT b * Γ.coalPayoff T b (gT Γ hST a ρ) =
      ∑ a, ξS a * ∑ b, ξT b * Γ.coalPayoff T b (gT Γ hST a ρ) := by
    refine sum_congr rfl fun a _ => ?_; rw [mul_sum]
    exact sum_congr rfl fun b _ => by ring
  rw [e1, e2]
  have i1 : Γ.extCharFun S ≤ ∑ b, ξT b * ∑ a, ξS a * Γ.coalPayoff S a (gS Γ hST b ρ) := by
    calc Γ.extCharFun S = ∑ b, ξT b * Γ.extCharFun S := by
          rw [← sum_mul, stdSimplex.sum_eq_one, one_mul]
      _ ≤ _ := sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hS _) (stdSimplex.zero_le _ _)
  have i2 : Γ.extCharFun T ≤ ∑ a, ξS a * ∑ b, ξT b * Γ.coalPayoff T b (gT Γ hST a ρ) := by
    calc Γ.extCharFun T = ∑ a, ξS a * Γ.extCharFun T := by
          rw [← sum_mul, stdSimplex.sum_eq_one, one_mul]
      _ ≤ _ := sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hT _) (stdSimplex.zero_le _ _)
  linarith

end Union

end XI

theorem extCharFun_isExtended_core {n : ℕ} (Γ : GeneralGame n) :
    IsExtendedCharFunction Γ.extCharFun :=
  ⟨XI.xcharFun_empty Γ, XI.xcharFun_compl Γ, fun _ _ h => XI.xcharFun_union Γ h⟩

theorem restricted_isRestricted_core {n : ℕ} (Γ : GeneralGame n) :
    IsRestrictedCharFunction Γ.restrictedCharFun := by
  classical
  have h := extCharFun_isExtended_core Γ
  refine ⟨?_, ?_⟩
  · unfold GeneralGame.restrictedCharFun; simpa using h.1
  · intro S T hST
    unfold GeneralGame.restrictedCharFun
    rw [Finset.map_union]
    exact h.2.2 _ _ ((Finset.disjoint_map _).mpr hST)

theorem characterization_core (n : ℕ) :
    (∀ v : Finset (Fin n) → ℝ,
        IsRestrictedCharFunction v ↔ ∃ Γ : GeneralGame n, Γ.restrictedCharFun = v) ∧
      (∀ v : Finset (Fin (n + 1)) → ℝ,
        IsExtendedCharFunction v ↔ ∃ Γ : GeneralGame n, Γ.extCharFun = v) := by
  refine ⟨fun v => ⟨exists_game_of_restricted_core v, ?_⟩,
    fun v => ⟨exists_game_of_extended_core v, ?_⟩⟩
  · rintro ⟨Γ, rfl⟩; exact restricted_isRestricted_core Γ
  · rintro ⟨Γ, rfl⟩; exact extCharFun_isExtended_core Γ

end TheoryOfGames.GeneralGames

open TheoryOfGames.GeneralGames


theorem solution (n : ℕ) :
    (∀ v : Finset (Fin n) → ℝ,
        IsRestrictedCharFunction v ↔ ∃ Γ : GeneralGame n, Γ.restrictedCharFun = v) ∧
      (∀ v : Finset (Fin (n + 1)) → ℝ,
        IsExtendedCharFunction v ↔ ∃ Γ : GeneralGame n, Γ.extCharFun = v) := by
  exact characterization_core n
