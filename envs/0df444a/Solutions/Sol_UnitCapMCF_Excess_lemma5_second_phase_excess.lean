-- Prove2me | solution 1 for UnitCapMCF.Excess.lemma5_second_phase_excess
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T11:07:29.291602+00:00
-- url     : https://prove2.me/submissions/a2ec8223-241d-4673-a758-a2c56d3e680a

import Mathlib
import Definitions.Def_UnitCapMCF_Excess_Setting

set_option autoImplicit false

namespace B446

open CostScaling.Refine UnitCapMCF.Excess

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma mem_Eplus (N : Network V) (f' f : V → V → ℝ) (a : V × V) :
    a ∈ Eplus N f' f ↔ a ∈ N.E ∧ f a.1 a.2 < f' a.1 a.2 := by
  unfold Eplus
  exact Finset.mem_filter

lemma diff_le_one (N : Network V) (hN : IsUnitCapacity N) (f' f : V → V → ℝ)
    (hf' : IsPseudoflow N f') (hf : IsPseudoflow N f) (x y : V) (hxy : (x, y) ∈ N.E) :
    f' x y - f x y ≤ 1 := by
  have hyx : (y, x) ∈ N.E := (N.symm x y).1 hxy
  have h1 := hf'.1 x y hxy
  have h2 := hf.1 y x hyx
  have h3 := hf.2 x y hxy
  rcases hN x y hxy with ⟨a, b⟩ | ⟨a, b⟩ <;> linarith

lemma excess_eq (N : Network V) (f' f : V → V → ℝ)
    (hc : CycleCanceling.MinMean.IsCirculation N f') (hf : IsPseudoflow N f) (x : V) :
    excess N f x = ∑ y ∈ Finset.univ.filter (fun y => (x, y) ∈ N.E), (f' x y - f x y) := by
  unfold excess
  have h0 := hc.2.2 x
  have : ∑ y ∈ Finset.univ.filter (fun y => (x, y) ∈ N.E), (f' x y - f x y)
      = ∑ y ∈ Finset.univ.filter (fun y => (x, y) ∈ N.E), (f y x - f' y x) := by
    apply Finset.sum_congr rfl
    intro y hy
    rw [Finset.mem_filter] at hy
    rw [hc.2.1 x y hy.2, hf.2 x y hy.2]; ring
  rw [this, Finset.sum_sub_distrib, h0, sub_zero]

lemma drop_le (N : Network V) (ε : ℝ) (hε : 0 < ε) (f' f : V → V → ℝ) (p' p : V → ℝ)
    (hf' : IsEpsOptimal N (2 * ε) f' p') (hf : IsEpsOptimal N ε f p) (x y : V)
    (h : (x, y) ∈ Eplus N f' f) :
    dlevel ε p' p x ≤ dlevel ε p' p y + 3 := by
  rw [mem_Eplus] at h
  obtain ⟨hxy, hlt⟩ := h
  have hyx : (y, x) ∈ N.E := (N.symm x y).1 hxy
  have hu := hf'.1.1 x y hxy
  have r1 : IsResidualArc N f x y := ⟨hxy, by unfold CycleCanceling.MinMean.resCap; linarith⟩
  have a1 := hf'.1.2 x y hxy
  have a2 := hf.1.2 x y hxy
  have hu2 := hf.1.1 y x hyx
  have r2 : IsResidualArc N f' y x := ⟨hyx, by unfold CycleCanceling.MinMean.resCap; linarith⟩
  have c1 := hf.2 x y r1
  have c2 := hf'.2 y x r2
  have ca := N.cost_antisymm y x hyx
  unfold reducedCost at c1 c2
  have key : p x - p' x - (p y - p' y) ≤ 3 * ε := by linarith
  have h2 : ((p x - p' x) - (p y - p' y)) / ε ≤ 3 := by rw [div_le_iff₀ hε]; linarith
  have h3 : dlevel ε p' p x - dlevel ε p' p y = ((p x - p' x) - (p y - p' y)) / ε := by
    unfold dlevel; ring
  linarith

lemma card_Eplus_le (N : Network V) (hN : IsUnitCapacity N) (f' f : V → V → ℝ)
    (hf'p : IsPseudoflow N f') (hf : IsPseudoflow N f) :
    (Eplus N f' f).card ≤ numArcs N := by
  classical
  unfold numArcs
  refine Finset.card_le_card_of_injOn (fun a => if N.u a.1 a.2 = 1 then a else a.swap) ?_ ?_
  · intro a ha
    have ha' : a ∈ Eplus N f' f := by simpa using ha
    rw [mem_Eplus] at ha'
    simp only [Finset.mem_coe, Finset.mem_filter]
    by_cases hu : N.u a.1 a.2 = 1
    · rw [if_pos hu]; exact ⟨ha'.1, hu⟩
    · rw [if_neg hu]
      rcases hN a.1 a.2 ha'.1 with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact absurd h1 hu
      · exact ⟨(N.symm a.1 a.2).1 ha'.1, h2⟩
  · rintro ⟨a1, a2⟩ ha ⟨b1, b2⟩ hb hab
    have ha' : (a1, a2) ∈ Eplus N f' f := by simpa using ha
    have hb' : (b1, b2) ∈ Eplus N f' f := by simpa using hb
    rw [mem_Eplus] at ha' hb'
    simp only at ha' hb'
    have e1 := hf.2 b1 b2 hb'.1
    have e2 := hf'p.2 b1 b2 hb'.1
    simp only at hab
    split_ifs at hab <;> simp only [Prod.swap_prod_mk, Prod.mk.injEq] at hab
    · obtain ⟨rfl, rfl⟩ := hab; rfl
    · exfalso; obtain ⟨rfl, rfl⟩ := hab; linarith
    · exfalso; obtain ⟨rfl, rfl⟩ := hab; linarith
    · obtain ⟨rfl, rfl⟩ := hab; rfl

lemma cut_bound (N : Network V) (hN : IsUnitCapacity N) (f' f : V → V → ℝ)
    (hc : CycleCanceling.MinMean.IsCirculation N f') (hf : IsPseudoflow N f) (S : Finset V)
    (hpos : ∀ v, 0 < excess N f v → v ∈ S) (hneg : ∀ v, excess N f v < 0 → v ∉ S) :
    totalExcess N f ≤ (((Eplus N f' f).filter (fun a => a.1 ∈ S ∧ a.2 ∉ S)).card : ℝ) := by
  classical
  let G : V → V → ℝ := fun x y => if (x, y) ∈ N.E then f' x y - f x y else 0
  have hGanti : ∀ x y, G y x = - G x y := by
    intro x y
    simp only [G]
    by_cases hxy : (x, y) ∈ N.E
    · have hyx : (y, x) ∈ N.E := (N.symm x y).1 hxy
      rw [if_pos hyx, if_pos hxy, hc.2.1 y x hyx, hf.2 y x hyx]; ring
    · have hyx : (y, x) ∉ N.E := fun h => hxy ((N.symm y x).1 h)
      rw [if_neg hyx, if_neg hxy]; ring
  have hexc_eq : ∀ x, excess N f x = ∑ y, G x y := by
    intro x
    rw [excess_eq N f' f hc hf x, Finset.sum_filter]
  have hTE : totalExcess N f ≤ ∑ x ∈ S, excess N f x := by
    unfold totalExcess
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro v hv
      rw [Finset.mem_filter] at hv
      exact hpos v hv.2
    · intro v hvS _
      exact not_lt.mp (fun hlt => hneg v hlt hvS)
  have h1 : ∑ x ∈ S, ∑ y ∈ S, G x y = 0 := by
    have h2 : ∑ x ∈ S, ∑ y ∈ S, G x y = ∑ x ∈ S, ∑ y ∈ S, G y x := Finset.sum_comm
    have h3 : ∑ x ∈ S, ∑ y ∈ S, G y x = - ∑ x ∈ S, ∑ y ∈ S, G x y := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro y _
      exact hGanti x y
    linarith
  have hsplit : ∑ x ∈ S, excess N f x = ∑ x ∈ S, ∑ y ∈ Sᶜ, G x y := by
    have h4 : ∀ x, ∑ y, G x y = ∑ y ∈ S, G x y + ∑ y ∈ Sᶜ, G x y := by
      intro x; rw [Finset.sum_add_sum_compl]
    simp only [hexc_eq, h4, Finset.sum_add_distrib, h1, zero_add]
  have hbound : ∑ x ∈ S, ∑ y ∈ Sᶜ, G x y ≤
      ∑ x ∈ S, ∑ y ∈ Sᶜ, (if (x, y) ∈ Eplus N f' f then (1:ℝ) else 0) := by
    apply Finset.sum_le_sum; intro x _
    apply Finset.sum_le_sum; intro y _
    simp only [G]
    by_cases hxy : (x, y) ∈ N.E
    · rw [if_pos hxy]
      by_cases hp : (x, y) ∈ Eplus N f' f
      · rw [if_pos hp]; exact diff_le_one N hN f' f ⟨hc.1, hc.2.1⟩ hf x y hxy
      · rw [if_neg hp]
        have : ¬ f x y < f' x y := fun h => hp ((mem_Eplus N f' f (x, y)).2 ⟨hxy, h⟩)
        linarith [not_lt.mp this]
    · rw [if_neg hxy]; split_ifs <;> norm_num
  have hcard : ∑ x ∈ S, ∑ y ∈ Sᶜ, (if (x, y) ∈ Eplus N f' f then (1:ℝ) else 0) ≤
      (((Eplus N f' f).filter (fun a => a.1 ∈ S ∧ a.2 ∉ S)).card : ℝ) := by
    have hp := Finset.sum_product' S Sᶜ
      (fun x y => if (x, y) ∈ Eplus N f' f then (1:ℝ) else 0)
    simp only [Prod.mk.eta] at hp
    rw [← hp, Finset.sum_boole]
    exact_mod_cast Finset.card_le_card (by
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_compl] at ha ⊢
      exact ⟨ha.2, ha.1.1, ha.1.2⟩)
  linarith

lemma case1 (N : Network V) (hN : IsUnitCapacity N) (ε : ℝ) (hε : 0 < ε)
    (f' f : V → V → ℝ) (p' p : V → ℝ)
    (hcirc : CycleCanceling.MinMean.IsCirculation N f')
    (hf' : IsEpsOptimal N (2 * ε) f' p') (hf : IsEpsOptimal N ε f p) (k : ℕ)
    (hexc : ∀ v, 0 < excess N f v → (k : ℝ) ≤ dlevel ε p' p v)
    (hdef : ∀ v, excess N f v < 0 → dlevel ε p' p v = 0)
    (hk : (k : ℝ) = Real.sqrt (numArcs N : ℝ)) : totalExcess N f ≤ 3 * (k : ℝ) := by
  classical
  have hE : ((Eplus N f' f).card : ℝ) ≤ numArcs N := by
    exact_mod_cast card_Eplus_le N hN f' f hf'.1 hf.1
  have hm : (k : ℝ) ^ 2 = numArcs N := by rw [hk, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hcut : ∀ t : ℕ, t < k → totalExcess N f ≤ (((Eplus N f' f).filter (fun a =>
      (t:ℝ) < dlevel ε p' p a.1 ∧ ¬ (t:ℝ) < dlevel ε p' p a.2)).card : ℝ) := by
    intro t ht
    have h := cut_bound N hN f' f hcirc hf.1
      (Finset.univ.filter (fun v => (t:ℝ) < dlevel ε p' p v)) ?_ ?_
    · refine h.trans ?_
      exact_mod_cast Finset.card_le_card (fun a ha => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢; exact ha)
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h1 := hexc v hv
      have h2 : (t:ℝ) < k := by exact_mod_cast ht
      linarith
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
      rw [hdef v hv]; positivity
  rcases Nat.eq_zero_or_pos k with h0 | hkpos
  · subst h0
    have hm0 : (numArcs N : ℝ) = 0 := by rw [← hm]; norm_num
    have h := cut_bound N hN f' f hcirc hf.1 (Finset.univ.filter (fun v => 0 < excess N f v))
      (fun v hv => by simp [hv]) (fun v hv => by simp; linarith)
    have h2 := Finset.card_filter_le (Eplus N f' f) (fun a =>
      a.1 ∈ Finset.univ.filter (fun v => 0 < excess N f v) ∧
      a.2 ∉ Finset.univ.filter (fun v => 0 < excess N f v))
    have h3 : (((Eplus N f' f).filter (fun a =>
      a.1 ∈ Finset.univ.filter (fun v => 0 < excess N f v) ∧
      a.2 ∉ Finset.univ.filter (fun v => 0 < excess N f v))).card : ℝ) ≤ (Eplus N f' f).card := by
      exact_mod_cast h2
    simp only [Nat.cast_zero, mul_zero]
    linarith
  · have hsum : ∑ t ∈ Finset.range k, ((Eplus N f' f).filter (fun a =>
        (t:ℝ) < dlevel ε p' p a.1 ∧ ¬ (t:ℝ) < dlevel ε p' p a.2)).card
        ≤ (Eplus N f' f).card * 3 := by
      simp only [Finset.card_filter]
      rw [Finset.sum_comm, ← smul_eq_mul]
      apply Finset.sum_le_card_nsmul
      intro a ha
      rw [← Finset.card_filter]
      have hdr := drop_le N ε hε f' f p' p hf' hf a.1 a.2 ha
      calc _ ≤ (Finset.Ico ⌈dlevel ε p' p a.2⌉₊ (⌈dlevel ε p' p a.2⌉₊ + 3)).card := by
            apply Finset.card_le_card
            intro t ht
            simp only [Finset.mem_filter, Finset.mem_range] at ht
            simp only [Finset.mem_Ico]
            constructor
            · exact Nat.ceil_le.mpr (not_lt.mp ht.2.2)
            · have h4 : (t:ℝ) < dlevel ε p' p a.2 + 3 := by linarith [ht.2.1]
              have h5 : dlevel ε p' p a.2 ≤ (⌈dlevel ε p' p a.2⌉₊ : ℝ) := Nat.le_ceil _
              have h6 : (t:ℝ) < (⌈dlevel ε p' p a.2⌉₊ : ℝ) + 3 := by linarith
              exact_mod_cast h6
        _ = 3 := by simp
    obtain ⟨t0, ht0, hmin⟩ := Finset.exists_min_image (Finset.range k)
      (fun t => ((Eplus N f' f).filter (fun a =>
        (t:ℝ) < dlevel ε p' p a.1 ∧ ¬ (t:ℝ) < dlevel ε p' p a.2)).card)
      ⟨0, Finset.mem_range.mpr hkpos⟩
    have hlow := Finset.card_nsmul_le_sum (Finset.range k) (fun t => ((Eplus N f' f).filter
      (fun a => (t:ℝ) < dlevel ε p' p a.1 ∧ ¬ (t:ℝ) < dlevel ε p' p a.2)).card) _
      (fun x hx => hmin x hx)
    rw [Finset.card_range, smul_eq_mul] at hlow
    have hT := hcut t0 (Finset.mem_range.mp ht0)
    have hlowR : (k:ℝ) * (((Eplus N f' f).filter (fun a =>
        (t0:ℝ) < dlevel ε p' p a.1 ∧ ¬ (t0:ℝ) < dlevel ε p' p a.2)).card : ℝ)
        ≤ ((Eplus N f' f).card : ℝ) * 3 := by exact_mod_cast hlow.trans hsum
    have hkR : (0:ℝ) < k := by exact_mod_cast hkpos
    have hfin : (k:ℝ) * totalExcess N f ≤ (k:ℝ) * (3 * k) := by nlinarith
    exact le_of_mul_le_mul_left hfin hkR

lemma case2 (N : Network V) (hN : IsUnitCapacity N) (ε : ℝ) (hε : 0 < ε)
    (f' f : V → V → ℝ) (p' p : V → ℝ)
    (hcirc : CycleCanceling.MinMean.IsCirculation N f')
    (hf' : IsEpsOptimal N (2 * ε) f' p') (hf : IsEpsOptimal N ε f p) (k : ℕ)
    (hexc : ∀ v, 0 < excess N f v → (k : ℝ) ≤ dlevel ε p' p v)
    (hdef : ∀ v, excess N f v < 0 → dlevel ε p' p v = 0)
    (hk : (k : ℝ) = (Fintype.card V : ℝ) ^ ((2 : ℝ) / 3)) (h6 : 6 ∣ k) :
    totalExcess N f ≤ 36 * (k : ℝ) := by
  classical
  obtain ⟨q, rfl⟩ := h6
  have hk3 : ((6 * q : ℕ) : ℝ) ^ 3 = (Fintype.card V : ℝ) ^ 2 := by
    rw [hk, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num
  rcases Nat.eq_zero_or_pos q with h0 | hqpos
  · subst h0
    have hn2 : (Fintype.card V : ℝ) ^ 2 = 0 := by rw [← hk3]; norm_num
    have hn : (Fintype.card V : ℝ) = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp hn2
    have hV : Fintype.card V = 0 := by exact_mod_cast hn
    have : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
    unfold totalExcess
    simp [Finset.univ_eq_empty]
  · let B : ℕ → Finset V := fun j => Finset.univ.filter (fun v =>
      6 * (j:ℝ) < dlevel ε p' p v ∧ dlevel ε p' p v ≤ 6 * (j:ℝ) + 6)
    have hdisj : ∀ i ∈ Finset.range q, ∀ j ∈ Finset.range q, i ≠ j → Disjoint (B i) (B j) := by
      intro i _ j _ hij
      rw [Finset.disjoint_left]
      intro v hvi hvj
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hvi hvj
      rcases Nat.lt_or_gt_of_ne hij with h | h
      · have : (i:ℝ) + 1 ≤ j := by exact_mod_cast h
        linarith [hvi.2, hvj.1]
      · have : (j:ℝ) + 1 ≤ i := by exact_mod_cast h
        linarith [hvj.2, hvi.1]
    have hsumB : ∑ j ∈ Finset.range q, (B j).card ≤ Fintype.card V := by
      rw [← Finset.card_biUnion hdisj]; exact Finset.card_le_univ _
    obtain ⟨j0, hj0, hmin⟩ := Finset.exists_min_image (Finset.range q) (fun j => (B j).card)
      ⟨0, Finset.mem_range.mpr hqpos⟩
    have hlow := Finset.card_nsmul_le_sum (Finset.range q) (fun j => (B j).card) _
      (fun x hx => hmin x hx)
    rw [Finset.card_range, smul_eq_mul] at hlow
    have hqb : q * (B j0).card ≤ Fintype.card V := hlow.trans hsumB
    have hj0q : j0 < q := Finset.mem_range.mp hj0
    have hS := cut_bound N hN f' f hcirc hf.1
      (Finset.univ.filter (fun v => 6 * (j0:ℝ) + 3 < dlevel ε p' p v)) ?_ ?_
    · have hsub : (Eplus N f' f).filter (fun a =>
          a.1 ∈ Finset.univ.filter (fun v => 6 * (j0:ℝ) + 3 < dlevel ε p' p v) ∧
          a.2 ∉ Finset.univ.filter (fun v => 6 * (j0:ℝ) + 3 < dlevel ε p' p v))
          ⊆ B j0 ×ˢ B j0 := by
        intro a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at ha
        have hdr := drop_le N ε hε f' f p' p hf' hf a.1 a.2 ha.1
        simp only [B, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨⟨by linarith [ha.2.1], by linarith [ha.2.2]⟩,
          ⟨by linarith [ha.2.1], by linarith [ha.2.2]⟩⟩
      have hc := Finset.card_le_card hsub
      rw [Finset.card_product] at hc
      have hTE : totalExcess N f ≤ ((B j0).card : ℝ) * (B j0).card :=
        hS.trans (by exact_mod_cast hc)
      have hqbR : (q:ℝ) * (B j0).card ≤ Fintype.card V := by exact_mod_cast hqb
      have hqR : (0:ℝ) < q := by exact_mod_cast hqpos
      have hk3' : (216:ℝ) * (q:ℝ) ^ 3 = (Fintype.card V : ℝ) ^ 2 := by
        rw [← hk3]; push_cast; ring
      have hsq := mul_self_le_mul_self (by positivity) hqbR
      have h2 : (q:ℝ) ^ 2 * (((B j0).card : ℝ) * (B j0).card) ≤ (q:ℝ) ^ 2 * (216 * q) := by
        have e1 : (q:ℝ) ^ 2 * (((B j0).card : ℝ) * (B j0).card)
            = ((q:ℝ) * (B j0).card) * ((q:ℝ) * (B j0).card) := by ring
        have e2 : (q:ℝ) ^ 2 * (216 * q) = (Fintype.card V : ℝ) * (Fintype.card V) := by
          linear_combination hk3'
        rw [e1, e2]; exact hsq
      have h3 : ((B j0).card : ℝ) * (B j0).card ≤ 216 * q :=
        le_of_mul_le_mul_left h2 (by positivity)
      push_cast
      linarith
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h1 := hexc v hv
      push_cast at h1
      have h2 : (j0:ℝ) + 1 ≤ q := by exact_mod_cast hj0q
      linarith
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
      rw [hdef v hv]; positivity

end B446

-- Goldberg et al., STACS 2015, Lemma 5 and its proof, p. 410.
open UnitCapMCF.Excess in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (N : CostScaling.Refine.Network V) (hN : IsUnitCapacity N)
    (ε : ℝ) (hε : 0 < ε) (f' f : V → V → ℝ) (p' p : V → ℝ)
    (hcirc : CycleCanceling.MinMean.IsCirculation N f')
    (hf' : CostScaling.Refine.IsEpsOptimal N (2 * ε) f' p')
    (hf : CostScaling.Refine.IsEpsOptimal N ε f p)
    (hd : ∀ v, ∃ k : ℤ, dlevel ε p' p v = k)
    (lam : ℕ)
    (hlam : (lam : ℝ) = min (Real.sqrt (numArcs N : ℝ))
      ((Fintype.card V : ℝ) ^ ((2 : ℝ) / 3)))
    (h3 : 3 ∣ lam)
    (hexc : ∀ v, 0 < CostScaling.Refine.excess N f v →
      (lam : ℝ) ≤ dlevel ε p' p v)
    (hdef : ∀ v, CostScaling.Refine.excess N f v < 0 →
      dlevel ε p' p v = 0) :
    ((lam : ℝ) = Real.sqrt (numArcs N : ℝ) →
      totalExcess N f ≤ 3 * (lam : ℝ)) ∧
    ((lam : ℝ) = (Fintype.card V : ℝ) ^ ((2 : ℝ) / 3) →
      6 ∣ lam → totalExcess N f ≤ 36 * (lam : ℝ)) := by
  exact ⟨fun hk => B446.case1 N hN ε hε f' f p' p hcirc hf' hf lam hexc hdef hk,
    fun hk h6 => B446.case2 N hN ε hε f' f p' p hcirc hf' hf lam hexc hdef hk h6⟩
