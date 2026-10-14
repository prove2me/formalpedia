-- Prove2me | solution 1 for RubinsteinNash.WeakNash.lemma_8_1
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:24:41.390842+00:00
-- url     : https://prove2.me/submissions/538171f6-4d6c-4614-8c13-ca78fefd2d7b

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_NashMap_nashMap
import Definitions.Def_DGPNash_WellSupported_Equilibria
import Definitions.Def_RubinsteinNash_WeakNash_ApproxEquilibria
import Definitions.Def_RubinsteinNash_WeakNash_Polymatrix

set_option linter.unusedSectionVars false

namespace RRAux_RN81
open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)]
  [∀ i, DecidableEq (S i)]

def pu {p : ι} (a : S p) : S p → ℝ := fun k => if k = a then 1 else 0

lemma pu_lottery {p : ι} (a : S p) : AGT.IsLottery (pu a) := by
  refine ⟨fun k => ?_, ?_⟩
  · unfold pu; split_ifs <;> norm_num
  · simp [pu]

lemma prob_update (x : ∀ i, S i → ℝ) (p : ι) (y : S p → ℝ) (s : ∀ i, S i) :
    AGT.profileProb (Function.update x p y) s = y (s p) * ∏ k ∈ univ.erase p, x k (s k) := by
  unfold AGT.profileProb
  rw [← Finset.mul_prod_erase univ _ (mem_univ p)]
  congr 1
  · simp
  · apply Finset.prod_congr rfl
    intro k hk
    rw [Function.update_of_ne (ne_of_mem_erase hk)]

lemma lin (x : ∀ i, S i → ℝ) (p : ι) (y : S p → ℝ) (f : (∀ i, S i) → ℝ) :
    ∑ s, AGT.profileProb (Function.update x p y) s * f s
      = ∑ a, y a * ∑ s, AGT.profileProb (Function.update x p (pu a)) s * f s := by
  simp_rw [prob_update, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro s _
  simp [pu, ite_mul, mul_ite]
  ring

lemma mass (σ : ∀ i, S i → ℝ) (h : AGT.IsMixedProfile σ) : ∑ s, AGT.profileProb σ s = 1 := by
  unfold AGT.profileProb
  rw [← Fintype.prod_sum]
  simp [(h _).2]

lemma prob_zero (σ : ∀ i, S i → ℝ) (s : ∀ i, S i) (j : ι) (h : σ j (s j) = 0) :
    AGT.profileProb σ s = 0 :=
  Finset.prod_eq_zero (mem_univ j) h

lemma mixed_update (x : ∀ i, S i → ℝ) (hx : AGT.IsMixedProfile x) (p : ι) (y : S p → ℝ)
    (hy : AGT.IsLottery y) : AGT.IsMixedProfile (Function.update x p y) := by
  intro k
  by_cases hk : k = p
  · subst hk; simpa using hy
  · rw [Function.update_of_ne hk]; exact hx k

lemma exp_eq (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (p : ι) (y : S p → ℝ) :
    AGT.expectedPayoff u (Function.update x p y) p
      = ∑ a, y a * DGPNash.NashMap.purePayoff u x p a := by
  unfold AGT.expectedPayoff
  rw [lin]
  rfl

lemma exp_self (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (p : ι) :
    AGT.expectedPayoff u x p = ∑ a, x p a * DGPNash.NashMap.purePayoff u x p a := by
  rw [← exp_eq, Function.update_eq_self]

lemma poly (G : (i j : ι) → S i → S j → ℝ) (y : ∀ i, S i → ℝ) (hy : AGT.IsMixedProfile y)
    (i : ι) (a : S i) :
    DGPNash.NashMap.purePayoff (RubinsteinNash.WeakNash.polymatrixPayoff G) y i a
      = ∑ j ∈ univ.erase i, ∑ b, y j b * G i j a b := by
  unfold DGPNash.NashMap.purePayoff AGT.expectedPayoff RubinsteinNash.WeakNash.polymatrixPayoff
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j hj
  have hji : j ≠ i := ne_of_mem_erase hj
  set σ := Function.update y i (fun k => if k = a then 1 else 0) with hσdef
  have hσj : σ j = y j := by rw [hσdef, Function.update_of_ne hji]
  have hσm : AGT.IsMixedProfile σ := mixed_update y hy i _ (pu_lottery a)
  have key := lin σ j (σ j) (fun s => G i j (s i) (s j))
  rw [Function.update_eq_self] at key
  rw [key]
  apply Finset.sum_congr rfl; intro b _
  rw [hσj]
  congr 1
  have hτ : AGT.IsMixedProfile (Function.update σ j (pu b)) :=
    mixed_update σ hσm j _ (pu_lottery b)
  have : ∀ s : ∀ i, S i, AGT.profileProb (Function.update σ j (pu b)) s * G i j (s i) (s j)
      = AGT.profileProb (Function.update σ j (pu b)) s * G i j a b := by
    intro s
    by_cases h1 : s i = a
    · by_cases h2 : s j = b
      · rw [h1, h2]
      · rw [prob_zero _ s j (by simp [pu, h2])]; simp
    · rw [prob_zero _ s i (by rw [Function.update_of_ne (Ne.symm hji)]; simp [σ, h1])]; simp
  simp_rw [this, ← Finset.sum_mul, mass _ hτ, one_mul]

lemma diff_bound (G : (i j : ι) → S i → S j → ℝ) (x x' : ∀ i, S i → ℝ)
    (hx : AGT.IsMixedProfile x) (hx' : AGT.IsMixedProfile x') (g : ι → ι → ℝ)
    (hG : ∀ i j a b, |G i j a b| ≤ g i j) (hg0 : ∀ i j, 0 ≤ g i j)
    (hg : ∀ i, ∑ j ∈ univ.erase i, g i j ≤ 1) (r : ℝ) (hr0 : 0 ≤ r)
    (hr : ∀ j, ∑ b, |x' j b - x j b| ≤ r) (i : ι) (a : S i) :
    |DGPNash.NashMap.purePayoff (RubinsteinNash.WeakNash.polymatrixPayoff G) x' i a
      - DGPNash.NashMap.purePayoff (RubinsteinNash.WeakNash.polymatrixPayoff G) x i a| ≤ r := by
  rw [poly G x' hx', poly G x hx, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j ∈ univ.erase i, |∑ b, x' j b * G i j a b - ∑ b, x j b * G i j a b|
      ≤ ∑ j ∈ univ.erase i, g i j * r := by
        apply Finset.sum_le_sum; intro j _
        rw [← Finset.sum_sub_distrib]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ b, |x' j b * G i j a b - x j b * G i j a b|
            ≤ ∑ b, |x' j b - x j b| * g i j := by
              apply Finset.sum_le_sum; intro b _
              rw [← sub_mul, abs_mul]
              exact mul_le_mul_of_nonneg_left (hG i j a b) (abs_nonneg _)
          _ = g i j * ∑ b, |x' j b - x j b| := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun b _ => mul_comm _ _)
          _ ≤ g i j * r := mul_le_mul_of_nonneg_left (hr j) (hg0 i j)
    _ = (∑ j ∈ univ.erase i, g i j) * r := by rw [Finset.sum_mul]
    _ ≤ 1 * r := mul_le_mul_of_nonneg_right (hg i) hr0
    _ = r := one_mul r

lemma z_bound (ε z : ℝ) (hε : 0 < ε) (_hz0 : 0 ≤ z)
    (h : z * (ε + Real.sqrt ε) ≤ ε) : z < 1 ∧ z ≤ Real.sqrt ε := by
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  constructor
  · nlinarith
  · by_contra hc
    rw [not_le] at hc
    have hss : Real.sqrt ε * Real.sqrt ε = ε := Real.mul_self_sqrt hε.le
    nlinarith

lemma epsk (ε : ℝ) (hε : 0 < ε) : ε * (1 + 1 / Real.sqrt ε) = ε + Real.sqrt ε := by
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hss : Real.sqrt ε * Real.sqrt ε = ε := Real.mul_self_sqrt hε.le
  field_simp
  nlinarith

/-- Facts about the trim at an ε-best responder. -/
lemma trim_facts (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (hx : AGT.IsMixedProfile x)
    (ε : ℝ) (hε : 0 < ε) (v : ι)
    (hv : RubinsteinNash.WeakNash.IsEpsBestResponse u x ε v) :
    AGT.IsLottery (DGPNash.WellSupported.trim u x ε (1 + 1 / Real.sqrt ε) v) ∧
      ∑ b, |DGPNash.WellSupported.trim u x ε (1 + 1 / Real.sqrt ε) v b - x v b|
        ≤ 2 * Real.sqrt ε := by
  set k := 1 + 1 / Real.sqrt ε with hk
  set U := fun j => DGPNash.NashMap.purePayoff u x v j with hU
  set M := DGPNash.WellSupported.maxPurePayoff u x v with hM
  have hMdef : M = ⨆ j, U j := rfl
  set z := DGPNash.WellSupported.trimMass u x ε k v with hz
  have hzdef : z = ∑ j, if U j < M - ε * k then x v j else 0 := rfl
  have htrim : ∀ j, DGPNash.WellSupported.trim u x ε k v j
      = if U j ≥ M - ε * k then x v j / (1 - z) else 0 := fun j => rfl
  have hne : Nonempty (S v) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have := (hx v).2
    simp at this
  have hle : ∀ j, U j ≤ M := fun j => le_ciSup (Set.finite_range _).bddAbove j
  obtain ⟨jstar, hjstar⟩ := exists_eq_ciSup_of_finite (f := U)
  -- best-response inequality
  have hbr := hv (pu jstar) (pu_lottery jstar)
  rw [exp_eq, exp_self] at hbr
  have hpj : ∑ a, pu jstar a * U a = M := by
    simp [pu, hMdef, ← hjstar]
  rw [hpj] at hbr
  -- upper bound
  have hupper : ∑ a, x v a * U a ≤ M - ε * k * z := by
    have : ∀ a, x v a * U a ≤ x v a * M - ε * k * (if U a < M - ε * k then x v a else 0) := by
      intro a
      have hxa := (hx v).1 a
      split_ifs with h
      · nlinarith
      · nlinarith [hle a]
    calc ∑ a, x v a * U a ≤ ∑ a, (x v a * M - ε * k * (if U a < M - ε * k then x v a else 0)) :=
          Finset.sum_le_sum (fun a _ => this a)
      _ = M - ε * k * z := by
          rw [Finset.sum_sub_distrib, ← Finset.sum_mul, (hx v).2, ← Finset.mul_sum, hzdef, one_mul]
  have hz0 : 0 ≤ z := by
    rw [hzdef]; apply Finset.sum_nonneg; intro a _; split_ifs
    · exact (hx v).1 a
    · exact le_refl _
  have hek : ε * k = ε + Real.sqrt ε := epsk ε hε
  have hzk : z * (ε + Real.sqrt ε) ≤ ε := by rw [← hek]; linarith
  obtain ⟨hz1, hzs⟩ := z_bound ε z hε hz0 hzk
  have h1z : 0 < 1 - z := by linarith
  -- split
  have hsplit : ∀ j, (if U j ≥ M - ε * k then x v j else 0)
      + (if U j < M - ε * k then x v j else 0) = x v j := by
    intro j
    by_cases h : U j < M - ε * k
    · simp [h, not_le.mpr h]
    · simp [h, not_lt.mp h]
  have hgood : ∑ j, (if U j ≥ M - ε * k then x v j else 0) = 1 - z := by
    have := Finset.sum_congr rfl (fun j (_ : j ∈ univ) => hsplit j)
    rw [Finset.sum_add_distrib, (hx v).2, ← hzdef] at this
    linarith
  refine ⟨⟨fun j => ?_, ?_⟩, ?_⟩
  · rw [htrim]; split_ifs
    · exact div_nonneg ((hx v).1 j) h1z.le
    · exact le_refl _
  · simp_rw [htrim]
    have : ∀ j, (if U j ≥ M - ε * k then x v j / (1 - z) else 0)
        = (if U j ≥ M - ε * k then x v j else 0) / (1 - z) := by
      intro j; split_ifs <;> simp
    simp_rw [this, ← Finset.sum_div, hgood]
    exact div_self h1z.ne'
  · simp_rw [htrim]
    have : ∀ j, |(if U j ≥ M - ε * k then x v j / (1 - z) else 0) - x v j|
        = (if U j ≥ M - ε * k then x v j else 0) * (z / (1 - z))
          + (if U j < M - ε * k then x v j else 0) := by
      intro j
      have hxj := (hx v).1 j
      by_cases h : U j < M - ε * k
      · simp [h, not_le.mpr h, abs_of_nonneg hxj]
      · simp only [h, not_lt.mp h, if_true, if_false]
        have : x v j / (1 - z) - x v j = x v j * (z / (1 - z)) := by
          field_simp; ring
        rw [this, abs_of_nonneg (mul_nonneg hxj (div_nonneg hz0 h1z.le))]
        ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hgood, ← hzdef]
    rw [mul_div_cancel₀ _ h1z.ne']
    linarith

end RRAux_RN81

namespace RRAux_RN81

lemma card_inv_le (n : ℕ) : (n : ℝ) * (1 / (n : ℝ)) ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · rw [mul_one_div_cancel (by exact_mod_cast h.ne')]

end RRAux_RN81

open RubinsteinNash.WeakNash in
theorem solution {VA VB : Type*} [Fintype VA] [DecidableEq VA]
    [Fintype VB] [DecidableEq VB]
    {S : VA ⊕ VB → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (PA : (v : VA) → (w : VB) → S (Sum.inl v) → S (Sum.inr w) → ℝ)
    (PB : (w : VB) → (v : VA) → S (Sum.inr w) → S (Sum.inl v) → ℝ)
    (hPA : ∀ v w a b, 0 ≤ PA v w a b ∧ PA v w a b ≤ 1 / (Fintype.card VB : ℝ))
    (hPB : ∀ w v b a, 0 ≤ PB w v b a ∧ PB w v b a ≤ 1 / (Fintype.card VA : ℝ))
    (x : ∀ i, S i → ℝ) (ε δ : ℝ) (hε : 0 < ε)
    (hx : IsWeakNash (bipartitePolymatrixPayoff PA PB) x ε δ) :
    IsWellSupportedWeakNash (bipartitePolymatrixPayoff PA PB)
      (weakTrim (bipartitePolymatrixPayoff PA PB) x ε (1 + 1 / Real.sqrt ε))
      (Real.sqrt ε * (Real.sqrt ε + 5)) δ := by
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hss : Real.sqrt ε * Real.sqrt ε = ε := Real.mul_self_sqrt hε.le
  have hek : ε * (1 + 1 / Real.sqrt ε) = ε + Real.sqrt ε := RRAux_RN81.epsk ε hε
  have he' : Real.sqrt ε * (Real.sqrt ε + 5) = ε + 5 * Real.sqrt ε := by
    rw [mul_add, hss]; ring
  have hxm : AGT.IsMixedProfile x := hx.1
  have hxh_m : AGT.IsMixedProfile
      (weakTrim (bipartitePolymatrixPayoff PA PB) x ε (1 + 1 / Real.sqrt ε)) := by
    intro i
    unfold weakTrim
    split_ifs with h
    · exact (RRAux_RN81.trim_facts _ x hxm ε hε i h).1
    · exact hxm i
  have hr : ∀ j, ∑ b, |weakTrim (bipartitePolymatrixPayoff PA PB) x ε (1 + 1 / Real.sqrt ε) j b
      - x j b| ≤ 2 * Real.sqrt ε := by
    intro j
    unfold weakTrim
    split_ifs with h
    · exact (RRAux_RN81.trim_facts _ x hxm ε hε j h).2
    · simp only [sub_self, abs_zero, Finset.sum_const_zero]; positivity
  let g : VA ⊕ VB → VA ⊕ VB → ℝ := fun i j => match i, j with
    | Sum.inl _, Sum.inr _ => 1 / (Fintype.card VB : ℝ)
    | Sum.inr _, Sum.inl _ => 1 / (Fintype.card VA : ℝ)
    | Sum.inl _, Sum.inl _ => 0
    | Sum.inr _, Sum.inr _ => 0
  have hG : ∀ i j a b, |bipartiteSubgames PA PB i j a b| ≤ g i j := by
    intro i j a b
    rcases i with v | w <;> rcases j with v' | w'
    · simp [g, bipartiteSubgames]
    · show |PA v w' a b| ≤ 1 / (Fintype.card VB : ℝ)
      rw [abs_of_nonneg (hPA v w' a b).1]; exact (hPA v w' a b).2
    · show |PB w v' a b| ≤ 1 / (Fintype.card VA : ℝ)
      rw [abs_of_nonneg (hPB w v' a b).1]; exact (hPB w v' a b).2
    · simp [g, bipartiteSubgames]
  have hg0 : ∀ i j, 0 ≤ g i j := by
    intro i j
    rcases i with v | w <;> rcases j with v' | w' <;> simp [g]
  have hg : ∀ i, ∑ j ∈ Finset.univ.erase i, g i j ≤ 1 := by
    intro i
    refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun j _ _ => hg0 i j)).trans ?_
    rw [Fintype.sum_sum_type]
    rcases i with v | w
    · simp only [g, Finset.sum_const_zero, zero_add, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      exact RRAux_RN81.card_inv_le _
    · simp only [g, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      exact RRAux_RN81.card_inv_le _
  have hdiff : ∀ i a,
      |DGPNash.NashMap.purePayoff (bipartitePolymatrixPayoff PA PB)
          (weakTrim (bipartitePolymatrixPayoff PA PB) x ε (1 + 1 / Real.sqrt ε)) i a
        - DGPNash.NashMap.purePayoff (bipartitePolymatrixPayoff PA PB) x i a|
        ≤ 2 * Real.sqrt ε := fun i a =>
    RRAux_RN81.diff_bound (bipartiteSubgames PA PB) x _ hxm hxh_m g hG hg0 hg _
      (by positivity) hr i a
  have WS : ∀ i, IsEpsBestResponse (bipartitePolymatrixPayoff PA PB) x ε i →
      IsEpsWellSupportedAt (bipartitePolymatrixPayoff PA PB)
        (weakTrim (bipartitePolymatrixPayoff PA PB) x ε (1 + 1 / Real.sqrt ε))
        (Real.sqrt ε * (Real.sqrt ε + 5)) i := by
    intro i hi a ha a'
    have hxhi : weakTrim (bipartitePolymatrixPayoff PA PB) x ε (1 + 1 / Real.sqrt ε) i
        = DGPNash.WellSupported.trim (bipartitePolymatrixPayoff PA PB) x ε
            (1 + 1 / Real.sqrt ε) i := by
      unfold weakTrim; rw [if_pos hi]
    have hgood : DGPNash.NashMap.purePayoff (bipartitePolymatrixPayoff PA PB) x i a ≥
        DGPNash.WellSupported.maxPurePayoff (bipartitePolymatrixPayoff PA PB) x i
          - ε * (1 + 1 / Real.sqrt ε) := by
      by_contra hc
      rw [hxhi] at ha
      unfold DGPNash.WellSupported.trim at ha
      rw [if_neg hc] at ha
      exact lt_irrefl _ ha
    have hle : DGPNash.NashMap.purePayoff (bipartitePolymatrixPayoff PA PB) x i a' ≤
        DGPNash.WellSupported.maxPurePayoff (bipartitePolymatrixPayoff PA PB) x i :=
      le_ciSup (f := fun j => DGPNash.NashMap.purePayoff (bipartitePolymatrixPayoff PA PB) x i j)
        (Set.finite_range _).bddAbove a'
    have d1 := abs_le.mp (hdiff i a)
    have d2 := abs_le.mp (hdiff i a')
    rw [hek] at hgood
    rw [he']
    linarith [d1.1, d1.2, d2.1, d2.2]
  refine ⟨hxh_m, le_trans hx.2 ?_⟩
  exact_mod_cast Finset.card_le_card (fun i hi => by
    simp only [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, WS i hi.2⟩)

#print axioms solution
