-- Prove2me | solution 1 for TheoryOfGames.GeneralGames.exists_game_of_restricted
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T18:23:19.779818+00:00
-- url     : https://prove2.me/submissions/202cc961-0b38-4069-a8f7-a9ea4c18dfe4

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

end TheoryOfGames.GeneralGames

open TheoryOfGames.GeneralGames


theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ)
    (hv : IsRestrictedCharFunction v) :
    ∃ Γ : GeneralGame n, Γ.restrictedCharFun = v := by
  exact exists_game_of_restricted_core v hv
