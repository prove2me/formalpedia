-- Prove2me | solution 1 for TradingNetFlow.ChainStable.corollary_5_6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T10:47:57.71329+00:00
-- url     : https://prove2.me/submissions/72837627-9d7b-4c74-8ab6-851f5d840bd2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_TradingNetFlow_ChainStable_Model
import Theorems.Thm_TradingNetFlow_ChainStable_lemma_5_5
import Theorems.Thm_TradingNetFlow_ChainStable_theorem_4_1
import Theorems.Thm_TradingNetFlow_ChainStable_theorem_4_3

open Finset TradingNetFlow.ChainStable DiscreteConvex.EconomicEquilibrium
  DiscreteConvex.MConvexFunctions

namespace TNFCor56

/-- `sup` commutes with adding a real constant in `WithBot ℝ`. -/
lemma sup_add_const {ι : Type*} (s : Finset ι) (B : ι → WithBot ℝ) (C : ℝ) :
    s.sup (fun j => B j + (C : WithBot ℝ)) = s.sup B + (C : WithBot ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sup_insert, sup_insert, ih]
    exact (max_add_add_right _ _ _)

lemma lin_pair {K : Type*} [Fintype K] (d : K → ℝ) (a b x y : K → ℤ)
    (h : ∀ k, a k + b k = x k + y k) :
    (∑ k, d k * (a k : ℝ)) + (∑ k, d k * (b k : ℝ))
      = (∑ k, d k * (x k : ℝ)) + (∑ k, d k * (y k : ℝ)) := by
  rw [← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl (fun k _ => ?_)
  have := h k
  have : (a k : ℝ) + b k = x k + y k := by exact_mod_cast this
  linear_combination d k * this

/-- Adding a linear function preserves M♮-concavity. -/
lemma mnat_add_linear {K : Type*} [Fintype K] [DecidableEq K] (U : (K → ℤ) → WithBot ℝ)
    (d : K → ℝ) (hU : MNaturalConcave U) :
    MNaturalConcave (fun x => U x + ((∑ k, d k * (x k : ℝ) : ℝ) : WithBot ℝ)) := by
  set ℓ : (K → ℤ) → ℝ := fun x => ∑ k, d k * (x k : ℝ) with hℓ
  have hdom : ∀ x, x ∈ UDom (fun x => U x + ((ℓ x : ℝ) : WithBot ℝ)) ↔ x ∈ UDom U := by
    intro x
    simp [UDom, WithBot.add_eq_bot]
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx⟩ := hU.1
    exact ⟨x, (hdom x).2 hx⟩
  intro x hx y hy i hi
  have hx' := (hdom x).1 hx
  have hy' := (hdom y).1 hy
  have key := hU.2 x hx' y hy' i hi
  set L := ℓ x + ℓ y with hL
  have h1 : ℓ (fun w => x w - CharVec i w) + ℓ (fun w => y w + CharVec i w) = L :=
    lin_pair d _ _ x y (fun k => by ring)
  have h2 : ∀ j, ℓ (fun w => x w - CharVec i w + CharVec j w)
      + ℓ (fun w => y w + CharVec i w - CharVec j w) = L :=
    fun j => lin_pair d _ _ x y (fun k => by ring)
  have hre : ∀ (a b : WithBot ℝ) (ra rb : ℝ), ra + rb = L →
      a + (ra : WithBot ℝ) + (b + (rb : WithBot ℝ)) = a + b + (L : WithBot ℝ) := by
    intro a b ra rb h
    rw [← h, WithBot.coe_add, add_add_add_comm]
  show U x + (ℓ x : WithBot ℝ) + (U y + (ℓ y : WithBot ℝ)) ≤
    max (U (fun w => x w - CharVec i w) + (ℓ (fun w => x w - CharVec i w) : WithBot ℝ)
        + (U (fun w => y w + CharVec i w) + (ℓ (fun w => y w + CharVec i w) : WithBot ℝ)))
      ((SuppNeg x y).sup (fun j =>
        U (fun w => x w - CharVec i w + CharVec j w)
          + (ℓ (fun w => x w - CharVec i w + CharVec j w) : WithBot ℝ)
        + (U (fun w => y w + CharVec i w - CharVec j w)
          + (ℓ (fun w => y w + CharVec i w - CharVec j w) : WithBot ℝ))))
  rw [hre _ _ _ _ rfl, hre _ _ _ _ h1]
  simp_rw [hre _ _ _ _ (h2 _)]
  rw [sup_add_const, max_add_add_right]
  exact add_le_add key le_rfl

variable {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]

/-- The economy with valuations `w_i(Z) + ∑_{e ∈ Z} c_e`. -/
def pert (G : Economy N E) (c : E → ℝ) : Economy N E where
  seller := G.seller
  buyer := G.buyer
  w i Z := G.w i Z + ∑ e ∈ Z, c e

lemma pert_standing (G : Economy N E) (c : E → ℝ) (hG : G.Standing) : (pert G c).Standing := by
  refine ⟨hG.1, fun i => ?_⟩
  have hlin := mnat_add_linear (G.wSigned i)
    (fun e => c e.1 * (G.sign i e.1 : ℝ)) (hG.2 i)
  show MNaturalConcave (fun x : {e // e ∈ G.delta i} → ℤ =>
    if ∀ e, x e = 0 ∨ x e = G.sign i e.1 then
      (((G.w i ((univ.filter (fun e => x e ≠ 0)).map (Function.Embedding.subtype _))
        + ∑ e ∈ (univ.filter (fun e => x e ≠ 0)).map (Function.Embedding.subtype _), c e : ℝ))
        : WithBot ℝ)
    else ⊥)
  have heq : (fun x : {e // e ∈ G.delta i} → ℤ =>
    if ∀ e, x e = 0 ∨ x e = G.sign i e.1 then
      (((G.w i ((univ.filter (fun e => x e ≠ 0)).map (Function.Embedding.subtype _))
        + ∑ e ∈ (univ.filter (fun e => x e ≠ 0)).map (Function.Embedding.subtype _), c e : ℝ))
        : WithBot ℝ)
    else ⊥)
      = fun x => G.wSigned i x + ((∑ k, c k.1 * (G.sign i k.1 : ℝ) * (x k : ℝ) : ℝ) : WithBot ℝ) := by
    funext x
    simp only [Economy.wSigned]
    by_cases hbox : ∀ e, x e = 0 ∨ x e = G.sign i e.1
    · rw [if_pos hbox, if_pos hbox, ← WithBot.coe_add]
      congr 1
      congr 1
      rw [sum_map, Finset.sum_filter]
      refine sum_congr rfl (fun e _ => ?_)
      simp only [Function.Embedding.coe_subtype]
      rcases hbox e with h | h
      · simp [h]
      · have hs : G.sign i e.1 = 1 ∨ G.sign i e.1 = -1 := by
          unfold Economy.sign; split_ifs <;> simp
        rcases hs with hs | hs
        · rw [h, hs]; simp
        · rw [h, hs]; simp
    · rw [if_neg hbox, if_neg hbox]
      simp
  rw [heq]
  exact hlin

lemma pert_utility (G : Economy N E) (c : E → ℝ) (i : N) (Y : Finset E) (p : E → ℝ) :
    (pert G c).utility i Y p = G.utility i Y p + ∑ e ∈ Y, c e := by
  have h1 : (pert G c).deltaOut i = G.deltaOut i := rfl
  have h2 : (pert G c).deltaIn i = G.deltaIn i := rfl
  unfold Economy.utility
  rw [h1, h2]
  show G.w i Y + ∑ e ∈ Y, c e + _ - _ = _
  ring

lemma pert_welfare (G : Economy N E) (c : E → ℝ) (hsb : ∀ e, G.seller e ≠ G.buyer e)
    (S : Finset E) :
    (pert G c).welfare S = G.welfare S + 2 * ∑ e ∈ S, c e := by
  unfold Economy.welfare
  have hd : ∀ i, (pert G c).delta i = G.delta i := fun _ => rfl
  show ∑ i, (G.w i (S ∩ (pert G c).delta i) + ∑ e ∈ S ∩ (pert G c).delta i, c e) = _
  simp only [hd]
  rw [sum_add_distrib]
  congr 1
  have hsplit : ∀ i, ∑ e ∈ S ∩ G.delta i, c e
      = ∑ e ∈ S.filter (fun e => G.seller e = i), c e
        + ∑ e ∈ S.filter (fun e => G.buyer e = i), c e := by
    intro i
    rw [← sum_union]
    · congr 1
      ext e
      simp [Economy.delta, Economy.deltaOut, Economy.deltaIn, pert, and_or_left]
    · rw [Finset.disjoint_left]
      intro e h1 h2
      simp only [mem_filter] at h1 h2
      exact hsb e (h1.2.trans h2.2.symm)
  rw [sum_congr rfl (fun i _ => hsplit i), sum_add_distrib, Finset.sum_fiberwise,
    Finset.sum_fiberwise]
  ring

lemma pert_isChain (G : Economy N E) (c : E → ℝ) (Z : Finset E) :
    (pert G c).IsChain Z ↔ G.IsChain Z := Iff.rfl

end TNFCor56

open TNFCor56

theorem solution {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]
    (G : Economy N E) (hG : G.Standing) (h : ¬ G.IsEfficient ∅)
    (T : Finset E) (hT : G.welfare ∅ < G.welfare T)
    (hmin : ∀ T' ⊂ T, ¬ G.welfare ∅ < G.welfare T') :
    G.IsChain T ∧ ∃ pT : E → ℝ, G.IsBlockingChain ∅ pT T pT := by
  -- a uniform bound on welfare
  set R : ℝ := ∑ S : Finset E, |G.welfare S| with hR
  have hRb : ∀ S, |G.welfare S| ≤ R := fun S =>
    single_le_sum (f := fun S => |G.welfare S|) (fun _ _ => abs_nonneg _) (mem_univ S)
  set Δ : ℝ := (G.welfare T - G.welfare ∅) / (4 * ((T.card : ℝ) + 1)) with hΔ
  have hcard : (0 : ℝ) < (T.card : ℝ) + 1 := by positivity
  have hΔpos : 0 < Δ := div_pos (by linarith) (by positivity)
  have hΔT : 2 * Δ * T.card < G.welfare T - G.welfare ∅ := by
    have : Δ * (4 * ((T.card : ℝ) + 1)) = G.welfare T - G.welfare ∅ := by
      rw [hΔ]; field_simp
    nlinarith
  set M : ℝ := R + Δ * T.card + 1 with hM
  have hsb := hG.1
  -- sums of the penalty over a set
  have hpen : ∀ (a b : ℝ) (S : Finset E),
      ∑ e ∈ S, (if e ∈ T then a else b) = a * (S ∩ T).card + b * (S \ T).card := by
    intro a b S
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
      Finset.filter_mem_eq_inter, Finset.filter_notMem_eq_sdiff]
    ring
  -- (i) `T` is a chain
  have hchain : G.IsChain T := by
    set c : E → ℝ := fun e => if e ∈ T then 0 else -M with hc
    have hst := pert_standing G c hG
    have hW : ∀ S, (pert G c).welfare S = G.welfare S - 2 * M * (S \ T).card := by
      intro S
      rw [pert_welfare G c hsb, hc, hpen]; ring
    have hne : ¬ (pert G c).IsEfficient ∅ := by
      intro he
      have := he T
      rw [hW, hW] at this
      simp at this
      linarith
    obtain ⟨Z, hZc, hZw⟩ := lemma_5_5 (pert G c) hst hne
    rw [hW, hW] at hZw
    simp only [empty_sdiff, card_empty, Nat.cast_zero, mul_zero, sub_zero] at hZw
    have hZT : Z ⊆ T := by
      by_contra hsub
      have : (1 : ℝ) ≤ (Z \ T).card := by
        have : (Z \ T).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty, Ne, Finset.sdiff_eq_empty_iff_subset]
          exact hsub
        exact_mod_cast this.card_pos
      have h1 := hRb Z
      have h2 := hRb ∅
      have h3 : 0 ≤ Δ * T.card := by positivity
      rw [abs_le] at h1 h2
      nlinarith
    have hZT' : Z = T := by
      by_contra hne'
      apply hmin Z (Finset.ssubset_iff_subset_ne.2 ⟨hZT, hne'⟩)
      have : (Z \ T).card = 0 := by
        rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset]; exact hZT
      rw [this] at hZw
      simpa using hZw
    rw [← hZT']
    exact (pert_isChain G c Z).1 hZc
  refine ⟨hchain, ?_⟩
  -- (ii) prices from an equilibrium of the perturbed economy
  set c : E → ℝ := fun e => if e ∈ T then -Δ else -M with hc
  have hst := pert_standing G c hG
  have hW : ∀ S, (pert G c).welfare S
      = G.welfare S - 2 * Δ * (S ∩ T).card - 2 * M * (S \ T).card := by
    intro S
    rw [pert_welfare G c hsb, hc, hpen]; ring
  have heff : (pert G c).IsEfficient T := by
    intro S
    rw [hW, hW]
    have hTT : T ∩ T = T := inter_self T
    have hTd : T \ T = ∅ := Finset.sdiff_self T
    rw [hTT, hTd]
    simp only [card_empty, Nat.cast_zero, mul_zero, sub_zero]
    by_cases hST : S ⊆ T
    · have hd : (S \ T).card = 0 := by
        rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset]; exact hST
      rw [hd]
      simp only [Nat.cast_zero, mul_zero, sub_zero]
      have hc0 : (0 : ℝ) ≤ (S ∩ T).card := by positivity
      by_cases hSeq : S = T
      · subst hSeq; rw [hTT]
      · have hlt := hmin S (Finset.ssubset_iff_subset_ne.2 ⟨hST, hSeq⟩)
        push Not at hlt
        nlinarith
    · have : (1 : ℝ) ≤ (S \ T).card := by
        have : (S \ T).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty, Ne, Finset.sdiff_eq_empty_iff_subset]
          exact hST
        exact_mod_cast this.card_pos
      have h1 := hRb S
      have h2 := hRb T
      have h3 : 0 ≤ Δ * T.card := by positivity
      have h4 : (0 : ℝ) ≤ (S ∩ T).card := by positivity
      rw [abs_le] at h1 h2
      nlinarith
  obtain ⟨Y0, q, hq⟩ := theorem_4_1 (pert G c) hst
  have hCE : (pert G c).IsCompetitiveEquilibrium T q := theorem_4_3 (pert G c) hst Y0 T q hq heff
  refine ⟨q, ?_, hchain, Finset.disjoint_empty_right T, ?_⟩
  · rcases Finset.eq_empty_or_nonempty T with hTe | hTne
    · subst hTe; exact absurd hT (lt_irrefl _)
    · exact hTne
  intro i _ Y hY
  have hjp : joinPrices (∅ : Finset E) q q = q := by
    funext e; simp [joinPrices]
  rw [hjp, union_empty] at hY
  obtain ⟨hYsub, hYmax⟩ := hY
  have hdel : T ∩ (pert G c).delta i = T ∩ G.delta i := rfl
  have h1 := hYmax (T ∩ G.delta i) subset_rfl
  have h2 := (hCE i).2 Y (by rw [univ_inter]; exact hYsub.trans inter_subset_right)
  rw [hdel, pert_utility, pert_utility] at h2
  have hYT : Y ⊆ T := hYsub.trans inter_subset_left
  have hsumY : ∑ e ∈ Y, c e = -Δ * Y.card := by
    rw [hc, hpen, Finset.inter_eq_left.2 hYT, Finset.sdiff_eq_empty_iff_subset.2 hYT]; simp
  have hsumT : ∑ e ∈ T ∩ G.delta i, c e = -Δ * (T ∩ G.delta i).card := by
    rw [hc, hpen, Finset.inter_eq_left.2 inter_subset_left,
      Finset.sdiff_eq_empty_iff_subset.2 inter_subset_left]; simp
  rw [hsumY, hsumT] at h2
  have hle : ((T ∩ G.delta i).card : ℝ) ≤ Y.card := by
    have : Δ * (T ∩ G.delta i).card ≤ Δ * Y.card := by linarith
    exact le_of_mul_le_mul_left this hΔpos
  have hle' : (T ∩ G.delta i).card ≤ Y.card := by exact_mod_cast hle
  rw [Finset.eq_of_subset_of_card_le hYsub hle']
