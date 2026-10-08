-- Prove2me | solution 1 for TheoryOfGames.CharFun.exists_game_of_isCharFunction
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T17:47:20.192295+00:00
-- url     : https://prove2.me/submissions/5317552c-d17b-4a8e-9374-39acfe8d533f

import Mathlib
import Definitions.Def_TheoryOfGames_CharFun_ZeroSumGame
import Definitions.Def_TheoryOfGames_CharFun_charFun
import Definitions.Def_TheoryOfGames_CharFun_IsCharFunction



namespace TheoryOfGames.CharFun

open Finset

/-- class of player k given choices ch -/
def egCls {n : ℕ} (ch : Fin n → Finset (Fin n)) (k : Fin n) : Finset (Fin n) :=
  if k ∈ ch k ∧ ∀ j ∈ ch k, ch j = ch k then ch k else {k}

lemma egCls_self {n : ℕ} (ch : Fin n → Finset (Fin n)) (k : Fin n) : k ∈ egCls ch k := by
  unfold egCls; split_ifs with h
  · exact h.1
  · simp

lemma egCls_mem {n : ℕ} (ch : Fin n → Finset (Fin n)) (k j : Fin n) (hj : j ∈ egCls ch k) :
    egCls ch j = egCls ch k := by
  unfold egCls at hj ⊢
  by_cases h : k ∈ ch k ∧ ∀ j ∈ ch k, ch j = ch k
  · rw [if_pos h] at hj ⊢
    have hjk := h.2 j hj
    rw [if_pos ⟨by rw [hjk]; exact hj, fun i hi => by rw [hjk] at hi ⊢; exact h.2 i hi⟩, hjk]
  · rw [if_neg h] at hj ⊢
    rw [Finset.mem_singleton] at hj; subst hj; rw [if_neg h]

lemma egCls_ring {n : ℕ} (ch : Fin n → Finset (Fin n)) (T : Finset (Fin n))
    (hT : ∀ k ∈ T, ch k = T) (k : Fin n) (hk : k ∈ T) : egCls ch k = T := by
  unfold egCls
  rw [if_pos ⟨by rw [hT k hk]; exact hk, fun j hj => by rw [hT k hk] at hj ⊢; exact hT j hj⟩,
    hT k hk]

lemma sum_disj_le {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : IsCharFunction v)
    (P : Finset (Finset (Fin n))) (hP : (P : Set (Finset (Fin n))).PairwiseDisjoint id) :
    ∑ C ∈ P, v C ≤ v (P.sup id) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp [hv.1]
  | insert a P ha ih =>
    rw [Finset.sum_insert ha, Finset.sup_insert]
    have hP' : (P : Set (Finset (Fin n))).PairwiseDisjoint id :=
      hP.subset (by intro x hx; simp [hx])
    have hd : Disjoint a (P.sup id) := by
      rw [Finset.disjoint_sup_right]
      intro i hi
      exact hP (by simp) (by simp [hi]) (fun h => ha (h ▸ hi))
    have := hv.2.2 a (P.sup id) hd
    have e : v (a ⊔ P.sup id) = v (a ∪ P.sup id) := rfl
    simp only [id] at this ⊢
    rw [e]
    linarith [ih hP']

lemma egA_le {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : IsCharFunction v)
    (ch : Fin n → Finset (Fin n)) :
    ∑ k, v (egCls ch k) / (egCls ch k).card ≤ 0 := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := univ.image (egCls ch)) (g := egCls ch)
    (fun k _ => Finset.mem_image_of_mem _ (Finset.mem_univ k))]
  have hfib : ∀ C ∈ univ.image (egCls ch), univ.filter (fun k => egCls ch k = C) = C := by
    intro C hC
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hC
    ext k; simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro h; rw [← h]; exact egCls_self ch k
    · intro h; exact egCls_mem ch m k h
  have h1 : ∀ C ∈ univ.image (egCls ch),
      ∑ k ∈ univ.filter (fun k => egCls ch k = C), v (egCls ch k) / (egCls ch k).card = v C := by
    intro C hC
    rw [Finset.sum_congr rfl (fun k hk => by rw [(Finset.mem_filter.mp hk).2]), Finset.sum_const,
      hfib C hC, nsmul_eq_mul]
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hC
    have : ((egCls ch m).card : ℝ) ≠ 0 := by
      have := Finset.card_pos.mpr ⟨m, egCls_self ch m⟩; positivity
    field_simp
  rw [Finset.sum_congr rfl h1]
  refine (sum_disj_le v hv _ ?_).trans ?_
  · intro C hC D hD hCD
    simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range] at hC hD
    obtain ⟨c, rfl⟩ := hC; obtain ⟨d, rfl⟩ := hD
    rw [Function.onFun, Finset.disjoint_left]
    intro i hi1 hi2
    exact hCD ((egCls_mem ch c i hi1).symm.trans (egCls_mem ch d i hi2))
  · have : (univ.image (egCls ch)).sup id = univ := by
      apply Finset.eq_univ_of_forall
      intro k
      exact Finset.mem_sup.mpr ⟨egCls ch k, Finset.mem_image_of_mem _ (mem_univ k), egCls_self ch k⟩
    rw [this, ← Finset.compl_empty, hv.2.1, hv.1]; simp

/-- payoff -/
noncomputable def egPay {n : ℕ} (v : Finset (Fin n) → ℝ) (ch : Fin n → Finset (Fin n))
    (k : Fin n) : ℝ :=
  v (egCls ch k) / (egCls ch k).card - (∑ j, v (egCls ch j) / (egCls ch j).card) / n

lemma egPay_sum {n : ℕ} (v : Finset (Fin n) → ℝ) (ch : Fin n → Finset (Fin n)) :
    ∑ k, egPay v ch k = 0 := by
  unfold egPay
  rw [Finset.sum_sub_distrib, Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have : (n : ℝ) ≠ 0 := by positivity
    field_simp; ring

lemma egPay_ring {n : ℕ} (v : Finset (Fin n) → ℝ) (hv : IsCharFunction v)
    (ch : Fin n → Finset (Fin n)) (T : Finset (Fin n))
    (hT : ∀ k ∈ T, ch k = T) : v T ≤ ∑ k ∈ T, egPay v ch k := by
  rcases T.eq_empty_or_nonempty with h | h
  · subst h; simp [hv.1]
  unfold egPay
  rw [Finset.sum_sub_distrib, Finset.sum_congr rfl (fun k hk => by rw [egCls_ring ch T hT k hk]),
    Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have hc : (T.card : ℝ) ≠ 0 := by have := h.card_pos; positivity
  have hA := egA_le v hv ch
  have : 0 ≤ (T.card : ℝ) * (-(∑ j, v (egCls ch j) / (egCls ch j).card) / n) := by
    apply mul_nonneg (by positivity); apply div_nonneg (by linarith) (by positivity)
  rw [mul_div_cancel₀ _ hc]
  have e : (T.card : ℝ) * ((∑ j, v (egCls ch j) / (egCls ch j).card) / n) =
    -((T.card : ℝ) * (-(∑ j, v (egCls ch j) / (egCls ch j).card) / n)) := by ring
  rw [e]; linarith

noncomputable def egGame {n : ℕ} (v : Finset (Fin n) → ℝ) : ZeroSumGame n where
  β := fun _ => Fintype.card (Finset (Fin n))
  β_pos := fun _ => Fintype.card_pos
  H := fun τ k => egPay v (fun j => (Fintype.equivFin (Finset (Fin n))).symm (τ j)) k
  zero_sum := fun τ => egPay_sum v _

/-- general facts on charFun -/
lemma bilin_bdd {n : ℕ} (Γ : ZeroSumGame n) (S : Finset (Fin n))
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

lemma charFun_eq_of_pure {n : ℕ} (Γ : ZeroSumGame n) (S : Finset (Fin n)) (c : ℝ)
    (σ : Γ.CoalStrat S) (hσ : ∀ τC, c ≤ Γ.coalPayoff S σ τC)
    (σ' : Γ.CoalStrat Sᶜ) (hσ' : ∀ τS, Γ.coalPayoff S τS σ' ≤ c) : Γ.charFun S = c := by
  classical
  set M := ∑ τS, ∑ τC, |Γ.coalPayoff S τS τC|
  have hne1 : Nonempty (stdSimplex ℝ (Γ.CoalStrat S)) :=
    ⟨(stdSimplex.vertex σ)⟩
  have hne2 : Nonempty (stdSimplex ℝ (Γ.CoalStrat Sᶜ)) :=
    ⟨(stdSimplex.vertex σ')⟩
  have hbb : ∀ ξ : stdSimplex ℝ (Γ.CoalStrat S), BddBelow (Set.range fun η : stdSimplex ℝ (Γ.CoalStrat Sᶜ) =>
      Γ.bilin S (ξ : Γ.CoalStrat S → ℝ) (η : Γ.CoalStrat Sᶜ → ℝ)) := by
    intro ξ; refine ⟨-M, ?_⟩; rintro _ ⟨η, rfl⟩
    exact (abs_le.mp (bilin_bdd Γ S ξ η)).1
  -- upper: for all ξ, inf ≤ c
  have hup : ∀ ξ : stdSimplex ℝ (Γ.CoalStrat S), (⨅ η : stdSimplex ℝ (Γ.CoalStrat Sᶜ),
      Γ.bilin S (ξ : Γ.CoalStrat S → ℝ) (η : Γ.CoalStrat Sᶜ → ℝ)) ≤ c := by
    intro ξ
    refine (ciInf_le (hbb ξ) (stdSimplex.vertex σ')).trans ?_
    unfold ZeroSumGame.bilin
    simp [Pi.single_apply]
    calc ∑ τS, Γ.coalPayoff S τS σ' * ξ.1 τS ≤ ∑ τS, c * ξ.1 τS :=
          Finset.sum_le_sum fun τS _ => mul_le_mul_of_nonneg_right (hσ' τS) (ξ.2.1 τS)
      _ = c := by rw [← Finset.mul_sum, ξ.2.2, mul_one]
  unfold ZeroSumGame.charFun
  apply le_antisymm
  · exact ciSup_le hup
  · refine le_trans ?_ (le_ciSup (f := fun ξ : stdSimplex ℝ (Γ.CoalStrat S) =>
      ⨅ η : stdSimplex ℝ (Γ.CoalStrat Sᶜ),
      Γ.bilin S (ξ : Γ.CoalStrat S → ℝ) (η : Γ.CoalStrat Sᶜ → ℝ)) ⟨c, ?_⟩
      (stdSimplex.vertex σ))
    · apply le_ciInf
      intro η
      unfold ZeroSumGame.bilin
      simp [Pi.single_apply]
      calc c = ∑ τC, c * η.1 τC := by rw [← Finset.mul_sum, η.2.2, mul_one]
        _ ≤ ∑ τC, Γ.coalPayoff S σ τC * η.1 τC :=
          Finset.sum_le_sum fun τC _ => mul_le_mul_of_nonneg_right (hσ τC) (η.2.1 τC)
    · rintro _ ⟨ξ, rfl⟩; exact hup ξ

theorem exists_game_core {n : ℕ} (v : Finset (Fin n) → ℝ)
    (hv : IsCharFunction v) : ∃ Γ : ZeroSumGame n, Γ.charFun = v := by
  classical
  refine ⟨egGame v, funext fun S => ?_⟩
  have key : ∀ (T : Finset (Fin n)) (τ : (k : Fin n) → Fin ((egGame v).β k)),
      (∀ k ∈ T, τ k = Fintype.equivFin (Finset (Fin n)) T) → v T ≤ ∑ k ∈ T, (egGame v).H τ k := by
    intro T τ hτ
    exact egPay_ring v hv _ T (fun k hk => by simp [hτ k hk])
  apply charFun_eq_of_pure (egGame v) S (v S) (fun _ => Fintype.equivFin (Finset (Fin n)) S) ?_ (fun _ => Fintype.equivFin (Finset (Fin n)) Sᶜ) ?_
  · intro τC
    apply key
    intro k hk
    simp [ZeroSumGame.joint, hk]
    rfl
  · intro τS
    have h1 := key Sᶜ ((egGame v).joint S τS (fun _ => Fintype.equivFin (Finset (Fin n)) Sᶜ))
      (fun k hk => by simp [ZeroSumGame.joint, (Finset.mem_compl.mp hk)]; rfl)
    have h0 := (egGame v).zero_sum ((egGame v).joint S τS (fun _ => Fintype.equivFin (Finset (Fin n)) Sᶜ))
    rw [← Finset.sum_add_sum_compl S] at h0
    unfold ZeroSumGame.coalPayoff
    rw [hv.2.1] at h1
    linarith

end TheoryOfGames.CharFun

open TheoryOfGames.CharFun


theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ)
    (hv : IsCharFunction v) : ∃ Γ : ZeroSumGame n, Γ.charFun = v := by
  exact exists_game_core v hv
