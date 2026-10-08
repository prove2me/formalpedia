-- Prove2me | solution 1 for TheoryOfGames.CharFun.isCharFunction_iff_exists_game
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T17:52:50.505404+00:00
-- url     : https://prove2.me/submissions/70de03f3-2d89-4e6b-98a3-2a12286353c1

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



open Finset

namespace CI

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

end CI

theorem charFun_isCharFunction_core {n : ℕ} (Γ : ZeroSumGame n) :
    IsCharFunction Γ.charFun :=
  ⟨CI.charFun_empty Γ, CI.charFun_compl Γ, fun S T h => CI.charFun_union Γ h⟩


theorem iff_exists_game_core {n : ℕ} (v : Finset (Fin n) → ℝ) :
    IsCharFunction v ↔ ∃ Γ : ZeroSumGame n, Γ.charFun = v := by
  constructor
  · exact exists_game_core v
  · rintro ⟨Γ, rfl⟩; exact charFun_isCharFunction_core Γ

end TheoryOfGames.CharFun

open TheoryOfGames.CharFun


theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ) :
    IsCharFunction v ↔ ∃ Γ : ZeroSumGame n, Γ.charFun = v := by
  exact iff_exists_game_core v
