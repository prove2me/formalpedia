-- Prove2me | solution 1 for TheoryOfGames.GeneralGames.singleton_removable
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T18:27:10.327785+00:00
-- url     : https://prove2.me/submissions/8c3c321e-ecf9-484f-82c9-88ca355386fa

import Mathlib
import Definitions.Def_TheoryOfGames_GeneralGames_GeneralGame
import Definitions.Def_TheoryOfGames_GeneralGames_charFun
import Definitions.Def_TheoryOfGames_GeneralGames_Removable
import Definitions.Def_TheoryOfGames_CharFun_ZeroSumGame
import Definitions.Def_TheoryOfGames_CharFun_charFun
import Definitions.Def_TheoryOfGames_CharFun_IsCharFunction



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



namespace CI
open TheoryOfGames.CharFun

variable {n : ℕ} (Γ : ZeroSumGame n)

lemma bilin_eq1 (S : Finset (Fin n)) (ξ : Γ.CoalStrat S → ℝ) (η : Γ.CoalStrat Sᶜ → ℝ) :
    Γ.bilin S ξ η = ∑ τC, η τC * ∑ τS, ξ τS * Γ.coalPayoff S τS τC := by
  unfold ZeroSumGame.bilin; rw [Finset.sum_comm]
  refine sum_congr rfl fun _ _ => ?_; rw [mul_sum]
  exact sum_congr rfl fun _ _ => by ring

lemma bilin_eq2 (S : Finset (Fin n)) (ξ : Γ.CoalStrat S → ℝ) (η : Γ.CoalStrat Sᶜ → ℝ) :
    Γ.bilin S ξ η = ∑ τS, ξ τS * ∑ τC, η τC * Γ.coalPayoff S τS τC := by
  unfold ZeroSumGame.bilin
  refine sum_congr rfl fun _ _ => ?_; rw [mul_sum]
  exact sum_congr rfl fun _ _ => by ring

lemma bilin_bdd (S : Finset (Fin n))
    (ξ : stdSimplex ℝ (Γ.CoalStrat S)) (η : stdSimplex ℝ (Γ.CoalStrat Sᶜ)) :
    |Γ.bilin S (ξ : Γ.CoalStrat S → ℝ) (η : Γ.CoalStrat Sᶜ → ℝ)| ≤
      ∑ τS, ∑ τC, |Γ.coalPayoff S τS τC| := by
  unfold ZeroSumGame.bilin
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

lemma bddBelow_inner (S : Finset (Fin n)) (ξ : stdSimplex ℝ (Γ.CoalStrat S)) :
    BddBelow (Set.range fun η : stdSimplex ℝ (Γ.CoalStrat Sᶜ) =>
      Γ.bilin S (ξ : Γ.CoalStrat S → ℝ) (η : Γ.CoalStrat Sᶜ → ℝ)) := by
  refine ⟨-(∑ τS, ∑ τC, |Γ.coalPayoff S τS τC|), ?_⟩; rintro _ ⟨η, rfl⟩
  exact (abs_le.mp (bilin_bdd Γ S ξ η)).1

lemma inner_le (S : Finset (Fin n)) (ξ : stdSimplex ℝ (Γ.CoalStrat S)) :
    (⨅ η : stdSimplex ℝ (Γ.CoalStrat Sᶜ),
      Γ.bilin S (ξ : Γ.CoalStrat S → ℝ) (η : Γ.CoalStrat Sᶜ → ℝ)) ≤
      ∑ τS, ∑ τC, |Γ.coalPayoff S τS τC| := by
  classical
  have hne : Nonempty (Γ.CoalStrat Sᶜ) := ⟨fun k => ⟨0, Γ.β_pos k⟩⟩
  obtain ⟨τ⟩ := hne
  exact (ciInf_le (bddBelow_inner Γ S ξ) (stdSimplex.vertex τ)).trans
    (abs_le.mp (bilin_bdd Γ S ξ _)).2

lemma le_charFun (S : Finset (Fin n)) (c : ℝ) (ξ : stdSimplex ℝ (Γ.CoalStrat S))
    (h : ∀ τC, c ≤ ∑ τS, ξ τS * Γ.coalPayoff S τS τC) : c ≤ Γ.charFun S := by
  classical
  have hne2 : Nonempty (stdSimplex ℝ (Γ.CoalStrat Sᶜ)) :=
    ⟨stdSimplex.vertex (show Γ.CoalStrat Sᶜ from fun k => ⟨0, Γ.β_pos k⟩)⟩
  unfold ZeroSumGame.charFun
  refine le_trans ?_ (le_ciSup (f := fun ξ : stdSimplex ℝ (Γ.CoalStrat S) =>
      ⨅ η : stdSimplex ℝ (Γ.CoalStrat Sᶜ),
      Γ.bilin S (ξ : Γ.CoalStrat S → ℝ) (η : Γ.CoalStrat Sᶜ → ℝ)) ⟨∑ τS, ∑ τC, |Γ.coalPayoff S τS τC|, ?_⟩ ξ)
  · apply le_ciInf
    intro η
    rw [bilin_eq1]
    calc c = ∑ τC, η τC * c := by rw [← Finset.sum_mul, stdSimplex.sum_eq_one, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun τC _ =>
          mul_le_mul_of_nonneg_left (h τC) (stdSimplex.zero_le η τC)
  · rintro _ ⟨ξ', rfl⟩; exact inner_le Γ S ξ'

lemma charFun_le (S : Finset (Fin n)) (c : ℝ) (η : stdSimplex ℝ (Γ.CoalStrat Sᶜ))
    (h : ∀ τS, ∑ τC, η τC * Γ.coalPayoff S τS τC ≤ c) : Γ.charFun S ≤ c := by
  classical
  have hne1 : Nonempty (stdSimplex ℝ (Γ.CoalStrat S)) :=
    ⟨stdSimplex.vertex (show Γ.CoalStrat S from fun k => ⟨0, Γ.β_pos k⟩)⟩
  unfold ZeroSumGame.charFun
  apply ciSup_le
  intro ξ
  refine (ciInf_le (bddBelow_inner Γ S ξ) η).trans ?_
  rw [bilin_eq2]
  calc _ ≤ ∑ τS, ξ τS * c := Finset.sum_le_sum fun τS _ =>
          mul_le_mul_of_nonneg_left (h τS) (stdSimplex.zero_le ξ τS)
    _ = c := by rw [← Finset.sum_mul, stdSimplex.sum_eq_one, one_mul]

lemma bilin_affine_left (S : Finset (Fin n)) (η : Γ.CoalStrat Sᶜ → ℝ)
    (x y : Γ.CoalStrat S → ℝ) (a b : ℝ) :
    Γ.bilin S (a • x + b • y) η = a * Γ.bilin S x η + b * Γ.bilin S y η := by
  unfold ZeroSumGame.bilin
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun _ _ => ?_
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun _ _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

lemma bilin_affine_right (S : Finset (Fin n)) (ξ : Γ.CoalStrat S → ℝ)
    (x y : Γ.CoalStrat Sᶜ → ℝ) (a b : ℝ) :
    Γ.bilin S ξ (a • x + b • y) = a * Γ.bilin S ξ x + b * Γ.bilin S ξ y := by
  unfold ZeroSumGame.bilin
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun _ _ => ?_
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun _ _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

lemma bilin_cont (S : Finset (Fin n)) :
    Continuous fun p : (Γ.CoalStrat S → ℝ) × (Γ.CoalStrat Sᶜ → ℝ) => Γ.bilin S p.1 p.2 := by
  unfold ZeroSumGame.bilin
  fun_prop

/-- master lemma: optimal strategies exist -/
lemma master (S : Finset (Fin n)) :
    ∃ ξ : stdSimplex ℝ (Γ.CoalStrat S), ∃ η : stdSimplex ℝ (Γ.CoalStrat Sᶜ),
      (∀ τC, Γ.charFun S ≤ ∑ τS, ξ τS * Γ.coalPayoff S τS τC) ∧
      (∀ τS, ∑ τC, η τC * Γ.coalPayoff S τS τC ≤ Γ.charFun S) := by
  classical
  have neX : (stdSimplex ℝ (Γ.CoalStrat Sᶜ)).Nonempty :=
    ⟨_, single_mem_stdSimplex ℝ (show Γ.CoalStrat Sᶜ from fun k => ⟨0, Γ.β_pos k⟩)⟩
  have neY : (stdSimplex ℝ (Γ.CoalStrat S)).Nonempty :=
    ⟨_, single_mem_stdSimplex ℝ (show Γ.CoalStrat S from fun k => ⟨0, Γ.β_pos k⟩)⟩
  obtain ⟨a, ha, b, hb, hab⟩ := Sion.exists_isSaddlePointOn
    (f := fun (x : Γ.CoalStrat Sᶜ → ℝ) (y : Γ.CoalStrat S → ℝ) => Γ.bilin S y x)
    neX (convex_stdSimplex ℝ _) (isCompact_stdSimplex ℝ _)
    (fun y _ => ((bilin_cont Γ S).comp (Continuous.prodMk continuous_const continuous_id)).continuousOn.lowerSemicontinuousOn)
    (fun y _ => ConvexOn.quasiconvexOn ⟨convex_stdSimplex ℝ _, fun x _ z _ p q _ _ _ => by
      simp only [smul_eq_mul]; rw [bilin_affine_right]⟩)
    (convex_stdSimplex ℝ _) neY (isCompact_stdSimplex ℝ _)
    (fun x _ => ((bilin_cont Γ S).comp (Continuous.prodMk continuous_id continuous_const)).continuousOn.upperSemicontinuousOn)
    (fun x _ => ConcaveOn.quasiconcaveOn ⟨convex_stdSimplex ℝ _, fun x _ z _ p q _ _ _ => by
      simp only [smul_eq_mul]; rw [bilin_affine_left]⟩)
  set ξ : stdSimplex ℝ (Γ.CoalStrat S) := ⟨b, hb⟩
  set η : stdSimplex ℝ (Γ.CoalStrat Sᶜ) := ⟨a, ha⟩
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
  have hc : Γ.charFun S = Γ.bilin S b a :=
    le_antisymm (charFun_le Γ S _ η h2) (le_charFun Γ S _ ξ h1)
  exact ⟨ξ, η, fun τC => hc ▸ h1 τC, fun τS => hc ▸ h2 τS⟩

lemma charFun_empty : Γ.charFun ∅ = 0 := by
  classical
  have hc : ∀ τS τC, Γ.coalPayoff ∅ τS τC = 0 := fun _ _ => by simp [ZeroSumGame.coalPayoff]
  apply le_antisymm
  · exact charFun_le Γ ∅ 0 (stdSimplex.vertex (show Γ.CoalStrat (∅ : Finset (Fin n))ᶜ from
      fun k => ⟨0, Γ.β_pos k⟩)) (fun τS => by simp [hc])
  · exact le_charFun Γ ∅ 0 (stdSimplex.vertex (show Γ.CoalStrat (∅ : Finset (Fin n)) from
      fun k => ⟨0, Γ.β_pos k⟩)) (fun τC => by simp [hc])

/-- transport between coalitions with the same members -/
def eqv {S T : Finset (Fin n)} (h : ∀ k, k ∈ S ↔ k ∈ T) : Γ.CoalStrat S ≃ Γ.CoalStrat T where
  toFun f := fun k => f ⟨k.1, (h k.1).mpr k.2⟩
  invFun g := fun k => g ⟨k.1, (h k.1).mp k.2⟩
  left_inv f := rfl
  right_inv g := rfl

lemma joint_compl (S : Finset (Fin n)) (τ1 : Γ.CoalStrat Sᶜ) (τ2 : Γ.CoalStrat Sᶜᶜ) :
    Γ.joint Sᶜ τ1 τ2 = Γ.joint S (eqv Γ (S := Sᶜᶜ) (T := S) (fun k => by simp) τ2) τ1 := by
  funext k
  unfold ZeroSumGame.joint
  by_cases hk : k ∈ S
  · have : k ∉ Sᶜ := by simpa using hk
    rw [dif_neg this, dif_pos hk]; rfl
  · have : k ∈ Sᶜ := by simpa using hk
    rw [dif_pos this, dif_neg hk]

lemma coalPayoff_compl (S : Finset (Fin n)) (τ1 : Γ.CoalStrat Sᶜ) (τ2 : Γ.CoalStrat Sᶜᶜ) :
    Γ.coalPayoff Sᶜ τ1 τ2 =
      -Γ.coalPayoff S (eqv Γ (S := Sᶜᶜ) (T := S) (fun k => by simp) τ2) τ1 := by
  unfold ZeroSumGame.coalPayoff
  rw [joint_compl]
  have := Γ.zero_sum (Γ.joint S (eqv Γ (S := Sᶜᶜ) (T := S) (fun k => by simp) τ2) τ1)
  rw [← Finset.sum_compl_add_sum S] at this
  linarith

lemma charFun_compl (S : Finset (Fin n)) : Γ.charFun Sᶜ = -Γ.charFun S := by
  classical
  obtain ⟨ξ, η, h1, h2⟩ := master Γ S
  set e := eqv Γ (S := Sᶜᶜ) (T := S) (fun k => by simp)
  have hmem : (fun τ2 => ξ (e τ2)) ∈ stdSimplex ℝ (Γ.CoalStrat Sᶜᶜ) := by
    refine ⟨fun τ2 => stdSimplex.zero_le ξ _, ?_⟩
    rw [Equiv.sum_comp e (fun x => ξ x), stdSimplex.sum_eq_one]
  apply le_antisymm
  · apply charFun_le Γ Sᶜ _ ⟨_, hmem⟩
    intro τ1
    change ∑ τ2, ξ (e τ2) * Γ.coalPayoff Sᶜ τ1 τ2 ≤ _
    simp only [coalPayoff_compl]
    rw [Equiv.sum_comp e (fun x => ξ x * -Γ.coalPayoff S x τ1)]
    have := h1 τ1
    simp only [mul_neg, sum_neg_distrib]; linarith
  · apply le_charFun Γ Sᶜ _ η
    intro τ2
    simp only [coalPayoff_compl, mul_neg, sum_neg_distrib]
    linarith [h2 (e τ2)]

-- superadditivity
section Union
variable {S T : Finset (Fin n)} (hST : Disjoint S T)
include hST

def splitEqv : Γ.CoalStrat (S ∪ T) ≃ Γ.CoalStrat S × Γ.CoalStrat T where
  toFun τ := (fun k => τ ⟨k.1, mem_union_left _ k.2⟩, fun k => τ ⟨k.1, mem_union_right _ k.2⟩)
  invFun p := fun k => if h : k.1 ∈ S then p.1 ⟨k.1, h⟩ else
    p.2 ⟨k.1, by rcases mem_union.mp k.2 with h' | h'; exacts [absurd h' h, h']⟩
  left_inv τ := by
    funext k
    by_cases h : k.1 ∈ S <;> simp [h]
  right_inv p := by
    ext k
    · simp [k.2]
    · have : k.1 ∉ S := fun h => Finset.disjoint_left.mp hST h k.2
      simp [this]

def gS (b : Γ.CoalStrat T) (ρ : Γ.CoalStrat (S ∪ T)ᶜ) : Γ.CoalStrat Sᶜ :=
  fun k => if h : k.1 ∈ T then b ⟨k.1, h⟩ else
    ρ ⟨k.1, by
      have := k.2; simp only [mem_compl] at this ⊢; simp [this, h]⟩

def gT (a : Γ.CoalStrat S) (ρ : Γ.CoalStrat (S ∪ T)ᶜ) : Γ.CoalStrat Tᶜ :=
  fun k => if h : k.1 ∈ S then a ⟨k.1, h⟩ else
    ρ ⟨k.1, by
      have := k.2; simp only [mem_compl] at this ⊢; simp [this, h]⟩

lemma joint_union_S (a : Γ.CoalStrat S) (b : Γ.CoalStrat T) (ρ : Γ.CoalStrat (S ∪ T)ᶜ) :
    Γ.joint (S ∪ T) ((splitEqv Γ hST).symm (a, b)) ρ = Γ.joint S a (gS Γ b ρ) := by
  funext k
  unfold ZeroSumGame.joint gS splitEqv
  by_cases hS : k ∈ S
  · simp [hS]
  · by_cases hT : k ∈ T
    · simp [hS, hT]
    · simp [hS, hT]

lemma joint_union_T (a : Γ.CoalStrat S) (b : Γ.CoalStrat T) (ρ : Γ.CoalStrat (S ∪ T)ᶜ) :
    Γ.joint (S ∪ T) ((splitEqv Γ hST).symm (a, b)) ρ = Γ.joint T b (gT Γ a ρ) := by
  funext k
  unfold ZeroSumGame.joint gT splitEqv
  by_cases hS : k ∈ S
  · have hT : k ∉ T := fun h => Finset.disjoint_left.mp hST hS h
    simp [hS, hT]
  · by_cases hT : k ∈ T
    · simp [hS, hT]
    · simp [hS, hT]

lemma charFun_union : Γ.charFun S + Γ.charFun T ≤ Γ.charFun (S ∪ T) := by
  classical
  obtain ⟨ξS, -, hS, -⟩ := master Γ S
  obtain ⟨ξT, -, hT, -⟩ := master Γ T
  set e := splitEqv Γ hST
  let F : Γ.CoalStrat (S ∪ T) → ℝ := fun τ => ξS (e τ).1 * ξT (e τ).2
  have hF : ∀ G : Γ.CoalStrat (S ∪ T) → ℝ, ∑ τ, G τ = ∑ a, ∑ b, G (e.symm (a, b)) := by
    intro G
    rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
  have hmem : F ∈ stdSimplex ℝ (Γ.CoalStrat (S ∪ T)) := by
    refine ⟨fun τ => mul_nonneg (stdSimplex.zero_le _ _) (stdSimplex.zero_le _ _), ?_⟩
    rw [hF]
    simp only [F, Equiv.apply_symm_apply]
    simp_rw [← mul_sum, stdSimplex.sum_eq_one, mul_one, stdSimplex.sum_eq_one]
  apply le_charFun Γ (S ∪ T) _ ⟨F, hmem⟩
  intro ρ
  change _ ≤ ∑ τ, F τ * Γ.coalPayoff (S ∪ T) τ ρ
  rw [hF]
  have hsplit : ∀ a b, Γ.coalPayoff (S ∪ T) (e.symm (a, b)) ρ =
      Γ.coalPayoff S a (gS Γ b ρ) + Γ.coalPayoff T b (gT Γ a ρ) := by
    intro a b
    unfold ZeroSumGame.coalPayoff
    rw [sum_union hST]
    congr 1
    · rw [joint_union_S]
    · rw [joint_union_T]
  simp only [F, Equiv.apply_symm_apply, hsplit, mul_add, sum_add_distrib]
  have e1 : ∑ a, ∑ b, ξS a * ξT b * Γ.coalPayoff S a (gS Γ b ρ) =
      ∑ b, ξT b * ∑ a, ξS a * Γ.coalPayoff S a (gS Γ b ρ) := by
    rw [sum_comm]; refine sum_congr rfl fun b _ => ?_; rw [mul_sum]
    exact sum_congr rfl fun a _ => by ring
  have e2 : ∑ a, ∑ b, ξS a * ξT b * Γ.coalPayoff T b (gT Γ a ρ) =
      ∑ a, ξS a * ∑ b, ξT b * Γ.coalPayoff T b (gT Γ a ρ) := by
    refine sum_congr rfl fun a _ => ?_; rw [mul_sum]
    exact sum_congr rfl fun b _ => by ring
  rw [e1, e2]
  have i1 : Γ.charFun S ≤ ∑ b, ξT b * ∑ a, ξS a * Γ.coalPayoff S a (gS Γ b ρ) := by
    calc Γ.charFun S = ∑ b, ξT b * Γ.charFun S := by
          rw [← sum_mul, stdSimplex.sum_eq_one, one_mul]
      _ ≤ _ := sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hS _) (stdSimplex.zero_le _ _)
  have i2 : Γ.charFun T ≤ ∑ a, ξS a * ∑ b, ξT b * Γ.coalPayoff T b (gT Γ a ρ) := by
    calc Γ.charFun T = ∑ a, ξS a * Γ.charFun T := by
          rw [← sum_mul, stdSimplex.sum_eq_one, one_mul]
      _ ≤ _ := sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hT _) (stdSimplex.zero_le _ _)
  linarith

end Union


theorem charFun_isCharFunction_core {n : ℕ} (Γ : ZeroSumGame n) :
    IsCharFunction Γ.charFun :=
  ⟨CI.charFun_empty Γ, CI.charFun_compl Γ, fun S T h => CI.charFun_union Γ h⟩

end CI

section Single
variable {n : ℕ}

def toZS (Γ : GeneralGame n) (hΓ : Γ.IsZeroSum) : TheoryOfGames.CharFun.ZeroSumGame n :=
  ⟨Γ.β, Γ.β_pos, Γ.H, hΓ⟩

lemma restricted_eq_zs (Γ : GeneralGame n) (hΓ : Γ.IsZeroSum) (S : Finset (Fin n)) :
    Γ.restrictedCharFun S = (toZS Γ hΓ).charFun S := by
  classical
  have key : ∀ (S' : Finset (Fin (n + 1))) (R : Finset (Fin n)),
      GeneralGame.realPart S' = R → Fin.last n ∉ S' →
      Γ.extCharFun S' = ⨆ ξ : stdSimplex ℝ (Γ.CoalStrat R), ⨅ η : stdSimplex ℝ (Γ.CoalStrat Rᶜ),
        ∑ τS, ∑ τC, (∑ k ∈ R, Γ.H (Γ.joint R τS τC) k) * (ξ : Γ.CoalStrat R → ℝ) τS *
          (η : Γ.CoalStrat Rᶜ → ℝ) τC := by
    intro S' R h hl
    subst h
    unfold GeneralGame.extCharFun GeneralGame.bilin GeneralGame.coalPayoff
    simp only [sum_extH, if_neg hl, sub_zero]
  unfold GeneralGame.restrictedCharFun
  rw [key _ S (by
      ext k; simp [GeneralGame.realPart]) (by simp)]
  rfl

lemma restricted_isChar (Γ : GeneralGame n) (hΓ : Γ.IsZeroSum) :
    TheoryOfGames.CharFun.IsCharFunction Γ.restrictedCharFun := by
  have : Γ.restrictedCharFun = (toZS Γ hΓ).charFun := funext (restricted_eq_zs Γ hΓ)
  rw [this]; exact CI.charFun_isCharFunction_core _

noncomputable def chOf (k : Fin n)
    (τ : (j : Fin n) → Fin (Fintype.card (Finset (Fin n) × Bool))) :
    Fin n → Finset (Fin n) × Bool := by
  classical
  exact fun j => if j = k then (∅, true) else (Fintype.equivFin (Finset (Fin n) × Bool)).symm (τ j)

noncomputable def sgH (v : Finset (Fin n) → ℝ) (k : Fin n)
    (τ : (j : Fin n) → Fin (Fintype.card (Finset (Fin n) × Bool))) (j : Fin n) : ℝ := by
  classical
  exact if j = k then -(∑ i ∈ univ.erase k, ggPay v (2 * ∑ T, |v T|) (chOf k τ) i)
    else ggPay v (2 * ∑ T, |v T|) (chOf k τ) j

noncomputable def sgGame (v : Finset (Fin n) → ℝ) (k : Fin n) : GeneralGame n where
  β := fun _ => Fintype.card (Finset (Fin n) × Bool)
  β_pos := fun _ => Fintype.card_pos
  H := sgH v k

lemma sgGame_zs (v : Finset (Fin n) → ℝ) (k : Fin n) : (sgGame v k).IsZeroSum := by
  classical
  intro τ
  show ∑ j, sgH v k τ j = 0
  rw [← Finset.add_sum_erase univ _ (mem_univ k)]
  have : ∀ j ∈ univ.erase k, sgH v k τ j = ggPay v (2 * ∑ T, |v T|) (chOf k τ) j := by
    intro j hj
    unfold sgH; rw [if_neg (Finset.ne_of_mem_erase hj)]
  rw [sum_congr rfl this]
  unfold sgH; rw [if_pos rfl]; ring

lemma sgGame_noInf (v : Finset (Fin n) → ℝ) (k : Fin n) : (sgGame v k).NoInfluence k := by
  classical
  intro τ τ' h
  have hc : chOf k τ = chOf k τ' := by
    funext j
    unfold chOf
    by_cases hj : j = k
    · simp [hj]
    · simp only [if_neg hj]; rw [h j hj]
  funext j
  show sgH v k τ j = sgH v k τ' j
  unfold sgH; rw [hc]

lemma sgGame_guar (v : Finset (Fin n) → ℝ) (hv : TheoryOfGames.CharFun.IsCharFunction v)
    (k : Fin n) (T : Finset (Fin n)) (τ : (j : Fin n) → Fin ((sgGame v k).β j))
    (hτ : ∀ j ∈ T, τ j = Fintype.equivFin (Finset (Fin n) × Bool) (T.erase k, decide (k ∈ T))) :
    v T ≤ ∑ j ∈ T, (sgGame v k).H τ j := by
  classical
  set Y := 2 * ∑ T, |v T|
  set ch := chOf k τ with hch_def
  have hchT : ∀ j ∈ T, j ≠ k → ch j = (T.erase k, decide (k ∈ T)) := by
    intro j hj hjk
    simp only [hch_def, chOf, if_neg hjk]; rw [hτ j hj]; simp
  have hH : ∀ j, j ≠ k → (sgGame v k).H τ j = ggPay v Y ch j := by
    intro j hjk; show sgH v k τ j = _; unfold sgH; rw [if_neg hjk]
  have hws : ∀ S T : Finset (Fin n), Disjoint S T → v S + v T ≤ v (S ∪ T) := hv.2.2
  by_cases hk : k ∈ T
  · rw [← Finset.add_sum_erase T _ hk]
    have hHk : (sgGame v k).H τ k = -(∑ i ∈ univ.erase k, ggPay v Y ch i) := by
      show sgH v k τ k = _; unfold sgH; rw [if_pos rfl]
    rw [hHk, sum_congr rfl (fun j hj => hH j (Finset.ne_of_mem_erase hj))]
    have e1 := Finset.add_sum_erase univ (ggPay v Y ch) (mem_univ k)
    have e2 := Finset.add_sum_erase T (ggPay v Y ch) hk
    have e3 := Finset.sum_add_sum_compl T (ggPay v Y ch)
    have hcl := ggPay_closed v hv.1 hws Y le_rfl ch Tᶜ (by
      intro j hj hjv i hi
      rw [mem_compl]
      intro hiT
      have e := hjv.2.2 i hi
      have hj2 := hjv.1
      rw [← e] at hj2
      by_cases hik : i = k
      · simp [hch_def, chOf, hik] at hj2
      · rw [hchT i hiT hik] at hj2; simp [hk] at hj2)
    have hc := hv.2.1 T
    linarith
  · rw [sum_congr rfl (fun j hj => hH j (fun h => hk (h ▸ hj)))]
    rw [ggPay_ring v Y ch T hv.1 (fun j hj => by
      rw [hchT j hj (fun h => hk (h ▸ hj)), Finset.erase_eq_of_notMem hk]; simp [hk])]

theorem singleton_removable_core (Γ : GeneralGame n) (hΓ : Γ.IsZeroSum) (k : Fin n) :
    Γ.IsRemovable {k} := by
  classical
  have hv := restricted_isChar Γ hΓ
  unfold GeneralGame.IsRemovable
  generalize Γ.restrictedCharFun = v at hv ⊢
  refine ⟨sgGame v k, sgGame_zs v k, funext fun S => ?_, ?_⟩
  · show (sgGame v k).extCharFun (S.map Fin.castSuccEmb) = v S
    set S' := S.map Fin.castSuccEmb
    have hl : Fin.last n ∉ S' := by simp [S']
    have hR : v (GeneralGame.realPart S') = v S := by
      congr 1; ext j; simp [GeneralGame.realPart, S']
    set R := GeneralGame.realPart S'
    rw [← hR]
    apply extCharFun_eq_of_pure (sgGame v k) S' (v R)
      (fun _ => Fintype.equivFin (Finset (Fin n) × Bool) (R.erase k, decide (k ∈ R))) ?_
      (fun _ => Fintype.equivFin (Finset (Fin n) × Bool) (Rᶜ.erase k, decide (k ∈ Rᶜ))) ?_
    · intro τC
      unfold GeneralGame.coalPayoff
      rw [sum_extH, if_neg hl, sub_zero]
      apply sgGame_guar v hv k R
      intro j hj
      exact dif_pos hj
    · intro τS
      unfold GeneralGame.coalPayoff
      rw [sum_extH, if_neg hl, sub_zero]
      have h1 := sgGame_guar v hv k Rᶜ ((sgGame v k).joint R τS
        (fun _ => Fintype.equivFin (Finset (Fin n) × Bool) (Rᶜ.erase k, decide (k ∈ Rᶜ))))
        (by
          intro j hj
          have hj' : j ∉ R := mem_compl.mp hj
          exact dif_neg hj')
      have h0 := sgGame_zs v k ((sgGame v k).joint R τS
        (fun _ => Fintype.equivFin (Finset (Fin n) × Bool) (Rᶜ.erase k, decide (k ∈ Rᶜ))))
      rw [← Finset.sum_add_sum_compl R] at h0
      rw [hv.2.1] at h1
      linarith
  · intro j hj
    rw [Finset.mem_singleton] at hj
    subst hj
    exact sgGame_noInf v j

end Single

end TheoryOfGames.GeneralGames

open TheoryOfGames.GeneralGames


theorem solution {n : ℕ} (Γ : GeneralGame n) (hΓ : Γ.IsZeroSum) (k : Fin n) :
    Γ.IsRemovable {k} := by
  exact singleton_removable_core Γ hΓ k
