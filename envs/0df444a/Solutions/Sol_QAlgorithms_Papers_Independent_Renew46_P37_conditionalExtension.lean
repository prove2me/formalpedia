-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P37.conditionalExtension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T19:21:17.864818+00:00
-- url     : https://prove2.me/submissions/6bceaf88-41ae-4b2c-a664-18da8acaf315

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P37

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace X7CE

open QAlgorithms.Papers.Independent.Renew46.P37
open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)
open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

attribute [local instance] Classical.propDecidable Classical.decEq

lemma X7_P_nonneg {n : ℕ} (p : EData n) (hp : EValid p) (e : Fin p.eve) :
    0 ≤ eveLetterProbability p e :=
  Finset.sum_nonneg fun x _ => hp.2.2.1 _

lemma X7_P_zero {n : ℕ} (p : EData n) (hp : EValid p) (e : Fin p.eve)
    (h : eveLetterProbability p e = 0) (x : ClassicalBasis p.dims) : p.prob (x, e) = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hp.2.2.1 (x, e))).1 h x (Finset.mem_univ _)

lemma X7_givenE_valid {n : ℕ} (p : EData n) (hp : EValid p) (e : Fin p.eve)
    (he : 0 < eveLetterProbability p e) : IsValidClassicalData (givenE p e) := by
  refine ⟨hp.1, fun x => div_nonneg (hp.2.2.1 _) he.le, ?_⟩
  show ∑ x, p.prob (x, e) / eveLetterProbability p e = 1
  rw [← Finset.sum_div]; exact div_self he.ne'

/-- Eve public announcement: equality. -/
lemma X7_evePublic {n : ℕ} (M : CData n → ℝ) (p : EData n) (f : ℕ)
    (K : Fin p.eve → Fin f → ℝ) (hp : EValid p) (hK : IsStochastic K) :
    conditionalAverage M p ≤ ∑ j, if 0 < evePublicWeight p K j then
      evePublicWeight p K j * conditionalAverage M (evePublicBranch p K j) else 0 := by
  set P := eveLetterProbability p
  have hP0 : ∀ e, 0 ≤ P e := X7_P_nonneg p hp
  have hK0 : ∀ e j, 0 ≤ K e j := fun e j => (hK e).1 j
  have hW : ∀ j e, P e * K e j ≤ evePublicWeight p K j := by
    intro j e
    unfold evePublicWeight
    rw [Finset.sum_comm]
    have : P e * K e j = ∑ x, p.prob (x, e) * K e j := by
      simp only [P, eveLetterProbability, Finset.sum_mul]
    rw [this]
    exact Finset.single_le_sum (f := fun e' => ∑ x, p.prob (x, e') * K e' j)
      (fun e' _ => Finset.sum_nonneg fun x _ => mul_nonneg (hp.2.2.1 _) (hK0 _ _))
      (Finset.mem_univ e)
  have hB : ∀ j (e : Fin p.eve), eveLetterProbability (evePublicBranch p K j) e =
      P e * K e j / evePublicWeight p K j := by
    intro j e
    simp only [eveLetterProbability, evePublicBranch, P, Finset.sum_div, Finset.sum_mul]
    rfl
  have key : ∀ j (e : Fin p.eve), (if 0 < evePublicWeight p K j then evePublicWeight p K j *
      (if 0 < eveLetterProbability (evePublicBranch p K j) e then
        eveLetterProbability (evePublicBranch p K j) e *
          M (givenE (evePublicBranch p K j) e) else 0) else 0) =
      if 0 < P e * K e j then P e * K e j * M (givenE p e) else 0 := by
    intro j e
    rw [hB]
    by_cases hWj : 0 < evePublicWeight p K j
    · rw [if_pos hWj]
      by_cases hpk : 0 < P e * K e j
      · rw [if_pos (div_pos hpk hWj), if_pos hpk]
        have hg : givenE (evePublicBranch p K j) e = givenE p e := by
          unfold givenE
          rw [hB]
          congr 1
          show (fun x => p.prob (x,e) * K e j / evePublicWeight p K j /
            (P e * K e j / evePublicWeight p K j)) = fun x => p.prob (x,e) / P e
          funext x
          have h1 : P e ≠ 0 := by
            intro h; rw [h, zero_mul] at hpk; exact lt_irrefl _ hpk
          have h2 : K e j ≠ 0 := by
            intro h; rw [h, mul_zero] at hpk; exact lt_irrefl _ hpk
          field_simp
        rw [hg]; field_simp
      · rw [if_neg, if_neg hpk, mul_zero]
        intro h; exact hpk (by
          have := (div_pos_iff_of_pos_right hWj).1 h; exact this)
    · rw [if_neg hWj]
      have hz : P e * K e j = 0 := by
        have := hW j e
        have h0 : evePublicWeight p K j ≤ 0 := not_lt.1 hWj
        exact le_antisymm (le_trans this h0) (mul_nonneg (hP0 e) (hK0 e j))
      rw [hz, if_neg (lt_irrefl _)]
  unfold conditionalAverage
  simp only [Finset.mul_sum]
  have : ∀ j, (if 0 < evePublicWeight p K j then
      ∑ e, evePublicWeight p K j *
        (if 0 < eveLetterProbability (evePublicBranch p K j) e then
          eveLetterProbability (evePublicBranch p K j) e *
            M (givenE (evePublicBranch p K j) e) else 0) else 0) =
      ∑ e, if 0 < P e * K e j then P e * K e j * M (givenE p e) else 0 := by
    intro j
    refine Eq.trans ?_ (Finset.sum_congr rfl (fun (e : Fin p.eve) _ => key j e))
    by_cases h : 0 < evePublicWeight p K j
    · rw [if_pos h]; exact Finset.sum_congr rfl (fun e _ => by rw [if_pos h])
    · rw [if_neg h]; symm; exact Finset.sum_eq_zero (fun e _ => by rw [if_neg h])
  rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_comm]
  refine le_of_eq (Finset.sum_congr rfl fun e _ => ?_)
  by_cases he : 0 < P e
  · rw [if_pos he]
    have : ∀ j, (if 0 < P e * K e j then P e * K e j * M (givenE p e) else 0) =
        P e * M (givenE p e) * K e j := by
      intro j
      by_cases hk : 0 < K e j
      · rw [if_pos (mul_pos he hk)]; ring
      · have : K e j = 0 := le_antisymm (not_lt.1 hk) (hK0 e j)
        rw [this]; simp
    rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.mul_sum, (hK e).2, mul_one]
  · rw [if_neg he]
    have : P e = 0 := le_antisymm (not_lt.1 he) (hP0 e)
    simp [this]

lemma X7_fiber_sum {n : ℕ} {d d' : Fin n → ℕ} (π : Fin n) (hd : ∀ i, i ≠ π → d' i = d i)
    (x : ClassicalBasis d) (g : Fin (d' π) → ℝ) :
    ∑ y : ClassicalBasis d', (if ∀ i, i ≠ π → (x i).val = (y i).val then g (y π) else 0) =
      ∑ b, g b := by
  rw [← Finset.sum_filter]
  let yb : Fin (d' π) → ClassicalBasis d' := fun b i =>
    if h : i = π then Fin.cast (by rw [h]) b
    else ⟨(x i).val, by rw [hd i h]; exact (x i).isLt⟩
  have hyb : ∀ b, yb b π = b := fun b => by simp [yb]
  refine Finset.sum_nbij' (fun y => y π) yb (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_ ?_
  · intro b _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro i hi; simp [yb, hi]
  · intro y hy
    have hy := (Finset.mem_filter.1 hy).2
    funext i
    by_cases h : i = π
    · subst h; simp [yb]
    · apply Fin.ext; simp [yb, h, hy i h]
  · intro b _; exact hyb b
  · intro y _; rfl

/-- Honest local instruments: conditional average decreases. -/
lemma X7_honest {n k : ℕ} (M : CData n → ℝ) (hM : IsCMonotone M) (p : EData n)
    (w : Fin k → ℝ) (r : Fin k → EData n) (hI : EInstrument p w r) :
    (∑ j, w j * conditionalAverage M (r j)) ≤ conditionalAverage M p := by
  obtain ⟨hp, hw, hr, π, K, heve, hdims, hK0, hK1, heq⟩ := hI
  set P := eveLetterProbability p
  have hP0 : ∀ e, 0 ≤ P e := X7_P_nonneg p hp
  let e' : (j : Fin k) → Fin p.eve → Fin (r j).eve := fun j e => Fin.cast (heve j).symm e
  let R : Fin k → Fin p.eve → ℝ := fun j e => eveLetterProbability (r j) (e' j e)
  have hR0 : ∀ j e, 0 ≤ R j e := fun j e => X7_P_nonneg (r j) (hr j) _
  let S : Fin k → ClassicalBasis p.dims → ℝ := fun j x =>
    ∑ y : ClassicalBasis (r j).dims,
      if ∀ i, i ≠ π → (x i).val = (y i).val then K j (x π) (y π) else 0
  have hS1 : ∀ x, ∑ j, S j x = 1 := by
    intro x
    rw [← hK1 (x π)]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact X7_fiber_sum (d := p.dims) (d' := (r j).dims) π (hdims j) x (fun b => K j (x π) b)
  have hS0 : ∀ j x, 0 ≤ S j x := fun j x =>
    Finset.sum_nonneg fun y _ => by split_ifs; exacts [hK0 _ _ _, le_rfl]
  have hA0 : ∀ j e (y : ClassicalBasis (r j).dims), w j * (r j).prob (y, e' j e) =
      ∑ x : ClassicalBasis p.dims, if ∀ i, i ≠ π → (x i).val = (y i).val
        then p.prob (x, e) * K j (x π) (y π) else 0 := by
    intro j e y
    rw [heq j y (e' j e)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_eq_single e]
    · by_cases hc : ∀ i, i ≠ π → (x i).val = (y i).val
      · rw [if_pos ⟨rfl, hc⟩, if_pos hc]
      · rw [if_neg (fun h => hc h.2), if_neg hc]
    · intro z _ hz
      rw [if_neg]
      rintro ⟨h1, _⟩
      exact hz (Fin.ext h1.symm)
    · intro h; exact absurd (Finset.mem_univ e) h
  have hA : ∀ j e, w j * R j e = ∑ x, p.prob (x, e) * S j x := by
    intro j e
    simp only [R, eveLetterProbability, Finset.mul_sum, hA0, S]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs <;> simp
  have hry0 : ∀ j e y, R j e = 0 → (r j).prob (y, e' j e) = 0 :=
    fun j e y h => X7_P_zero (r j) (hr j) _ h y
  -- conditional instrument data
  let z0 : (j : Fin k) → ClassicalBasis (r j).dims := fun j i => ⟨0, (hr j).1 i⟩
  let rr : Fin p.eve → Fin k → CData n := fun e j =>
    ⟨(r j).dims, fun y => if 0 < R j e then (r j).prob (y, e' j e) / R j e
      else if y = z0 j then 1 else 0⟩
  let v : Fin p.eve → Fin k → ℝ := fun e j => w j * R j e / P e
  have hCI : ∀ e, 0 < P e → CInstrument (givenE p e) (v e) (rr e) := by
    intro e he
    refine ⟨X7_givenE_valid p hp e he, ⟨fun j => div_nonneg (mul_nonneg (hw.1 j) (hR0 j e)) he.le,
      ?_⟩, fun j => ⟨(hr j).1, ?_, ?_⟩, π, K, hdims, hK0, hK1, ?_⟩
    · simp only [v]
      rw [← Finset.sum_div, div_eq_one_iff_eq he.ne']
      simp only [hA]
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, hS1, mul_one]
      rfl
    · intro y
      show 0 ≤ (if 0 < R j e then (r j).prob (y, e' j e) / R j e
        else if y = z0 j then 1 else 0)
      split_ifs with h
      · exact div_nonneg ((hr j).2.2.1 _) h.le
      · norm_num
      · norm_num
    · show ∑ y, (if 0 < R j e then (r j).prob (y, e' j e) / R j e
        else if y = z0 j then 1 else 0) = 1
      by_cases h : 0 < R j e
      · simp only [if_pos h]
        rw [← Finset.sum_div]; exact div_self h.ne'
      · simp only [if_neg h]; simp
    · intro j y
      show w j * R j e / P e * (if 0 < R j e then (r j).prob (y, e' j e) / R j e
        else if y = z0 j then 1 else 0) = ∑ x : ClassicalBasis p.dims,
          if ∀ i, i ≠ π → (x i).val = (y i).val
          then p.prob (x, e) / P e * K j (x π) (y π) else 0
      have : (∑ x : ClassicalBasis p.dims,
          if ∀ i, i ≠ π → (x i).val = (y i).val
          then p.prob (x, e) / P e * K j (x π) (y π) else 0) =
          (w j * (r j).prob (y, e' j e)) / P e := by
        rw [hA0, Finset.sum_div]
        refine Finset.sum_congr rfl fun x _ => ?_
        split_ifs <;> ring
      rw [this]
      by_cases h : 0 < R j e
      · rw [if_pos h]; field_simp
      · have h0 : R j e = 0 := le_antisymm (not_lt.1 h) (hR0 j e)
        rw [h0, hry0 j e y h0]; simp
  -- per-term identity
  have term : ∀ j e, w j * (if 0 < R j e then R j e * M (givenE (r j) (e' j e)) else 0) =
      if 0 < P e then P e * (v e j * M (rr e j)) else 0 := by
    intro j e
    by_cases he : 0 < P e
    · rw [if_pos he]
      by_cases h : 0 < R j e
      · rw [if_pos h]
        have hM' : M (rr e j) = M (givenE (r j) (e' j e)) := by
          congr 1
          simp only [rr, givenE]
          congr 1
          funext y
          rw [if_pos h]
        rw [hM']; simp only [v]; field_simp
      · have h0 : R j e = 0 := le_antisymm (not_lt.1 h) (hR0 j e)
        rw [if_neg h]; simp only [v, h0]; ring
    · rw [if_neg he]
      have hPe : P e = 0 := le_antisymm (not_lt.1 he) (hP0 e)
      have hwR : w j * R j e = 0 := by
        rw [hA]
        exact Finset.sum_eq_zero fun x _ => by rw [X7_P_zero p hp e hPe x, zero_mul]
      split_ifs
      · rw [← mul_assoc, hwR, zero_mul]
      · ring
  have hcA : ∀ j, conditionalAverage M (r j) =
      ∑ e : Fin p.eve, if 0 < R j e then R j e * M (givenE (r j) (e' j e)) else 0 := by
    intro j
    unfold conditionalAverage
    exact (Fintype.sum_equiv (finCongr (heve j).symm) _ _ (fun e => rfl)).symm
  simp only [hcA, Finset.mul_sum, term]
  rw [Finset.sum_comm]
  unfold conditionalAverage
  change _ ≤ ∑ e, if 0 < P e then P e * M (givenE p e) else 0
  refine Finset.sum_le_sum fun e _ => ?_
  by_cases he : 0 < P e
  · simp only [if_pos he]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left ((hM.2.2.1 _ k _ _ (hCI e he))) he.le
  · simp only [if_neg he, Finset.sum_const_zero, le_refl]

lemma X7_sumP {n : ℕ} (p : EData n) (hp : EValid p) : ∑ e, eveLetterProbability p e = 1 := by
  unfold eveLetterProbability
  rw [Finset.sum_comm, ← Fintype.sum_prod_type']
  exact hp.2.2.2

def X7_E {n : ℕ} (a b : Fin n → ℕ) :
    ClassicalBasis (fun i => a i * b i) ≃ ClassicalBasis a × ClassicalBasis b :=
  (Equiv.piCongrRight fun i => finProdFinEquiv.symm).trans
    (Equiv.arrowProdEquivProdArrow _ _ _)

lemma X7_eP_letter {n : ℕ} (p q : EData n) (a : Fin p.eve) (b : Fin q.eve) :
    eveLetterProbability (eProduct p q) (finProdFinEquiv (a, b)) =
      eveLetterProbability p a * eveLetterProbability q b := by
  unfold eveLetterProbability
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (X7_E p.dims q.dims) _ _ fun x => ?_
  simp [eProduct, X7_E]

lemma X7_eP_given {n : ℕ} (p q : EData n) (a : Fin p.eve) (b : Fin q.eve) :
    givenE (eProduct p q) (finProdFinEquiv (a, b)) = cProduct (givenE p a) (givenE q b) := by
  unfold givenE cProduct
  rw [X7_eP_letter]
  congr 1
  funext x
  simp only [eProduct, Equiv.symm_apply_apply]
  ring

lemma X7_add {n : ℕ} (M : CData n → ℝ) (hM : IsCMonotone M) (p q : EData n)
    (hp : EValid p) (hq : EValid q) :
    conditionalAverage M (eProduct p q) = conditionalAverage M p + conditionalAverage M q := by
  unfold conditionalAverage
  rw [show (∑ z : Fin (eProduct p q).eve, if 0 < eveLetterProbability (eProduct p q) z then
      eveLetterProbability (eProduct p q) z * M (givenE (eProduct p q) z) else 0) =
      ∑ ab : Fin p.eve × Fin q.eve,
        (if 0 < eveLetterProbability (eProduct p q) (finProdFinEquiv ab) then
        eveLetterProbability (eProduct p q) (finProdFinEquiv ab) *
          M (givenE (eProduct p q) (finProdFinEquiv ab)) else 0) from
    Fintype.sum_equiv finProdFinEquiv.symm _ _ (fun z => by simp only [Equiv.apply_symm_apply])]
  rw [Fintype.sum_prod_type]
  simp only [X7_eP_letter, X7_eP_given]
  have hP0 := X7_P_nonneg p hp
  have hQ0 := X7_P_nonneg q hq
  have t : ∀ a b, (if 0 < eveLetterProbability p a * eveLetterProbability q b then
      eveLetterProbability p a * eveLetterProbability q b *
        M (cProduct (givenE p a) (givenE q b)) else 0) =
      (if 0 < eveLetterProbability p a then eveLetterProbability p a * M (givenE p a) else 0) *
        eveLetterProbability q b +
      eveLetterProbability p a *
        (if 0 < eveLetterProbability q b then eveLetterProbability q b * M (givenE q b) else 0) := by
    intro a b
    by_cases ha : 0 < eveLetterProbability p a
    · by_cases hb : 0 < eveLetterProbability q b
      · rw [if_pos (mul_pos ha hb), if_pos ha, if_pos hb,
          hM.2.2.2.1 _ _ (X7_givenE_valid p hp a ha) (X7_givenE_valid q hq b hb)]
        ring
      · have : eveLetterProbability q b = 0 := le_antisymm (not_lt.1 hb) (hQ0 b)
        simp [this]
    · have : eveLetterProbability p a = 0 := le_antisymm (not_lt.1 ha) (hP0 a)
      simp [this]
  simp only [t, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, X7_sumP p hp,
    X7_sumP q hq]
  ring

lemma X7_lawset_compact {X : Type} [Fintype X] : IsCompact {q : X → ℝ | IsLaw q} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · have : {q : X → ℝ | IsLaw q} = (⋂ x, {q : X → ℝ | 0 ≤ q x}) ∩ {q | ∑ x, q x = 1} := by
      ext q; simp [IsLaw]
    rw [this]
    refine IsClosed.inter (isClosed_iInter fun x => isClosed_le continuous_const (continuous_apply x))
      (isClosed_eq (continuous_finset_sum _ fun x _ => continuous_apply x) continuous_const)
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨1, fun q hq => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hq.1 x)]
    rw [← hq.2]
    exact Finset.single_le_sum (fun y _ => hq.1 y) (Finset.mem_univ x)

lemma X7_cont {n : ℕ} (M : CData n → ℝ) (hM : IsCMonotone M) (d : Fin n → ℕ) (e : ℕ)
    (hd : ∀ i, 0 < d i) :
    Continuous (fun p : {p : ClassicalBasis d × Fin e → ℝ // IsLaw p} =>
      conditionalAverage M ⟨d, e, p.val⟩) := by
  let Pf : Fin e → (ClassicalBasis d × Fin e → ℝ) → ℝ := fun a p => ∑ x, p (x, a)
  let φ : Fin e → (ClassicalBasis d × Fin e → ℝ) → (ClassicalBasis d → ℝ) :=
    fun a p x => p (x, a) / Pf a p
  change Continuous (fun p : {p : ClassicalBasis d × Fin e → ℝ // IsLaw p} =>
    ∑ a : Fin e, if 0 < Pf a p.val then Pf a p.val * M ⟨d, φ a p.val⟩ else 0)
  refine continuous_finset_sum _ fun a _ => ?_
  set L := {q : ClassicalBasis d → ℝ | IsLaw q}
  have hMc : ContinuousOn (fun q => M ⟨d, q⟩) L :=
    continuousOn_iff_continuous_restrict.2 (hM.2.2.2.2 d hd)
  obtain ⟨B, hB⟩ := X7_lawset_compact.exists_bound_of_continuousOn hMc
  set B' := max B 0
  have hPf : Continuous (Pf a) := continuous_finset_sum _ fun x _ => continuous_apply _
  have hφL : ∀ p : {p : ClassicalBasis d × Fin e → ℝ // IsLaw p}, 0 < Pf a p.val → φ a p.val ∈ L := by
    intro p hp
    refine ⟨fun x => div_nonneg (p.2.1 _) hp.le, ?_⟩
    simp only [φ]; rw [← Finset.sum_div]; exact div_self hp.ne'
  rw [continuous_iff_continuousAt]
  intro p0
  have hP00 : 0 ≤ Pf a p0.val := Finset.sum_nonneg fun x _ => p0.2.1 _
  rcases hP00.lt_or_eq with h0 | h0
  · have hev : ∀ᶠ p in nhds p0, 0 < Pf a p.val :=
      (hPf.comp continuous_subtype_val).continuousAt.eventually (lt_mem_nhds h0)
    have hφc : ContinuousAt (fun p : {p : ClassicalBasis d × Fin e → ℝ // IsLaw p} => φ a p.val) p0 := by
      refine continuousAt_pi.2 fun x => ?_
      exact ((continuous_apply _).comp continuous_subtype_val).continuousAt.div
        (hPf.comp continuous_subtype_val).continuousAt h0.ne'
    have hT : Filter.Tendsto (fun p : {p : ClassicalBasis d × Fin e → ℝ // IsLaw p} => φ a p.val)
        (nhds p0) (nhdsWithin (φ a p0.val) L) :=
      tendsto_nhdsWithin_iff.2 ⟨hφc, hev.mono fun p hp => hφL p hp⟩
    have hMc' : ContinuousAt
        (fun p : {p : ClassicalBasis d × Fin e → ℝ // IsLaw p} => M ⟨d, φ a p.val⟩) p0 :=
      (hMc _ (hφL p0 h0)).tendsto.comp hT
    have hG := ((hPf.comp continuous_subtype_val).continuousAt).mul hMc'
    refine hG.congr ?_
    filter_upwards [hev] with p hp
    rw [if_pos hp]; rfl
  · rw [ContinuousAt, if_neg (by rw [← h0]; exact lt_irrefl _)]
    have hlim : Filter.Tendsto (fun p : {p : ClassicalBasis d × Fin e → ℝ // IsLaw p} =>
        B' * Pf a p.val) (nhds p0) (nhds 0) := by
      have := ((hPf.comp continuous_subtype_val).tendsto p0).const_mul B'
      simpa [Function.comp, ← h0] using this
    refine squeeze_zero_norm (fun p => ?_) hlim
    split_ifs with hp
    · rw [Real.norm_eq_abs, abs_mul, abs_of_pos hp, mul_comm]
      exact mul_le_mul_of_nonneg_right ((hB _ (hφL p hp)).trans (le_max_left _ _)) hp.le
    · simp only [norm_zero]
      exact mul_nonneg (le_max_right _ _) (Finset.sum_nonneg fun x _ => p.2.1 _)

end X7CE

namespace X7CE2

open QAlgorithms.Papers.Independent.Renew46.P37
open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)
open QAlgorithms.Papers.Independent.Claimed50.P33 (InformationKind singleParties allParties)

theorem X7_shannon_const {Y : Type} [Fintype Y] (q : Y → ℝ) (c k : ℝ)
    (hc : Real.logb 2 c = -k) (h : ∀ y, q y = 0 ∨ q y = c) (hs : ∑ y, q y = 1) :
    shannon q = k := by
  unfold shannon
  have : ∀ y, q y * Real.logb 2 (q y) = q y * (-k) := by
    intro y; rcases h y with h1 | h1 <;> rw [h1]; simp; rw [hc]
  simp only [this, ← Finset.sum_mul, hs]; ring

theorem X7_marg_sum {n : ℕ} (p : CData n) (s : Finset (Fin n)) :
    ∑ a, lawMarginal p s a = ∑ x, p.prob x := by
  unfold lawMarginal
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  have : ∀ a : (i : {i : Fin n // i ∈ s}) → Fin (p.dims i.val),
      (∀ i : {i : Fin n // i ∈ s}, x i.val = a i) ↔ (fun i : {i : Fin n // i ∈ s} => x i.val) = a := fun a => by
    constructor
    · intro h; funext i; exact h i
    · rintro rfl i; rfl
  simp only [this]
  rw [Finset.sum_ite_eq]; simp

theorem X7_cH_val {n : ℕ} (p : CData n) (hp : IsLaw p.prob) (s : Finset (Fin n)) (c k : ℝ)
    (hc : Real.logb 2 c = -k) (h : ∀ a, lawMarginal p s a = 0 ∨ lawMarginal p s a = c) :
    cH p s = k :=
  X7_shannon_const _ c k hc h (by rw [X7_marg_sum, hp.2])

theorem X7_sum22 (f : (Fin 2 → Fin 2) → ℝ) :
    ∑ x, f x = f ![0,0] + f ![0,1] + f ![1,0] + f ![1,1] := by
  rw [← Equiv.sum_comp (finTwoArrowEquiv (Fin 2)).symm f, Fintype.sum_prod_type]
  simp [Fin.sum_univ_two, finTwoArrowEquiv_symm_apply]
  ring

theorem X7_marg2 (f : (Fin 2 → Fin 2) → ℝ) (c0 : ℝ) (Q : (Fin 2 → Fin 2) → Prop) [DecidablePred Q]
    (hp : ∀ x, f x = if Q x then c0 else 0) (s : Finset (Fin 2))
    (a : (i : {i : Fin 2 // i ∈ s}) → Fin 2) :
    lawMarginal (⟨fun _ => 2, f⟩ : CData 2) s a = c0 * (Finset.univ.filter (fun x : Fin 2 → Fin 2 =>
      (∀ i : {i : Fin 2 // i ∈ s}, x i.val = a i) ∧ Q x)).card := by
  unfold lawMarginal
  rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have hx : (⟨fun _ => 2, f⟩ : CData 2).prob x = if Q x then c0 else 0 := hp x
  by_cases h1 : ∀ i : {i : Fin 2 // i ∈ s}, x i.val = a i
  · by_cases h2 : Q x
    · rw [if_pos h1, hx, if_pos h2, if_pos ⟨h1, h2⟩, Nat.cast_one, mul_one]
    · rw [if_pos h1, hx, if_neg h2, if_neg (fun h => h2 h.2), Nat.cast_zero, mul_zero]
  · rw [if_neg h1, if_neg (fun h => h1 h.1), Nat.cast_zero, mul_zero]

theorem X7_val2 (f : (Fin 2 → Fin 2) → ℝ) (c0 : ℝ) (m : ℕ) (k : ℝ) (Q : (Fin 2 → Fin 2) → Prop)
    [DecidablePred Q]
    (hp : ∀ x, f x = if Q x then c0 else 0)
    (hv : IsLaw (⟨fun _ => 2, f⟩ : CData 2).prob)
    (s : Finset (Fin 2)) (hc : Real.logb 2 (c0 * m) = -k)
    (hdec : ∀ a : (i : {i : Fin 2 // i ∈ s}) → Fin 2,
      (Finset.univ.filter (fun x : Fin 2 → Fin 2 => (∀ i : {i : Fin 2 // i ∈ s}, x i.val = a i) ∧ Q x)).card = 0 ∨
      (Finset.univ.filter (fun x : Fin 2 → Fin 2 => (∀ i : {i : Fin 2 // i ∈ s}, x i.val = a i) ∧ Q x)).card = m) :
    cH (⟨fun _ => 2, f⟩ : CData 2) s = k := by
  refine X7_cH_val _ hv s (c0 * m) k hc fun a => ?_
  rw [X7_marg2 f c0 Q hp s a]
  rcases hdec a with h | h
  · left; rw [h]; simp
  · right; rw [h]

theorem X7_lb2 : Real.logb 2 (1/2 * (1:ℕ)) = -1 := by
  simp [Real.logb_inv]
theorem X7_lb4 : Real.logb 2 (1/4 * (1:ℕ)) = -2 := by
  rw [show (1/4 * ((1:ℕ):ℝ)) = (2:ℝ)⁻¹ ^ 2 by norm_num, Real.logb_pow, Real.logb_inv]; simp
theorem X7_lb42 : Real.logb 2 (1/4 * (2:ℕ)) = -1 := by
  rw [show (1/4 * ((2:ℕ):ℝ)) = (2:ℝ)⁻¹ by norm_num, Real.logb_inv]; simp

theorem X7_dual2 (p : CData 2) :
    cValue .dual p = cH p {1} + cH p {0} - cH p Finset.univ := by
  have hs : singleParties 2 = fun i => ({i} : Finset (Fin 2)) := rfl
  simp only [cValue, cInfo, allParties, hs, Finset.biUnion_singleton_eq_self, Fin.sum_univ_two]
  have e0 : (Finset.univ.erase 0 : Finset (Fin 2)) = {1} := by decide
  have e1 : (Finset.univ.erase 1 : Finset (Fin 2)) = {0} := by decide
  rw [e0, e1]; norm_num

def X7_q (e : ℕ) : CData 2 :=
  ⟨fun _ => 2, fun x => if ((x 0).val + (x 1).val) % 2 = e then 1/2 else 0⟩

def X7_u : CData 2 := ⟨fun _ => 2, fun x => if True then 1/4 else 0⟩

theorem X7_q_val (e : ℕ) (he : e < 2) : cValue .dual (X7_q e) = 1 := by
  have hv : IsLaw (X7_q e).prob := by
    refine ⟨fun x => by unfold X7_q; dsimp only; split_ifs <;> norm_num, ?_⟩
    refine (X7_sum22 (fun x => (X7_q e).prob x)).trans ?_
    unfold X7_q
    interval_cases e <;> norm_num
  rw [X7_dual2]
  interval_cases e
  · have e1 := X7_val2 _ (1/2) 1 1 (fun x : Fin 2 → Fin 2 => ((x 0).val + (x 1).val) % 2 = 0)
      (fun x => rfl) hv {1} X7_lb2 (by decide)
    have e0 := X7_val2 _ (1/2) 1 1 (fun x : Fin 2 → Fin 2 => ((x 0).val + (x 1).val) % 2 = 0)
      (fun x => rfl) hv {0} X7_lb2 (by decide)
    have eU := X7_val2 _ (1/2) 1 1 (fun x : Fin 2 → Fin 2 => ((x 0).val + (x 1).val) % 2 = 0)
      (fun x => rfl) hv Finset.univ X7_lb2 (by decide)
    unfold X7_q; rw [e1, e0, eU]; norm_num
  · have e1 := X7_val2 _ (1/2) 1 1 (fun x : Fin 2 → Fin 2 => ((x 0).val + (x 1).val) % 2 = 1)
      (fun x => rfl) hv {1} X7_lb2 (by decide)
    have e0 := X7_val2 _ (1/2) 1 1 (fun x : Fin 2 → Fin 2 => ((x 0).val + (x 1).val) % 2 = 1)
      (fun x => rfl) hv {0} X7_lb2 (by decide)
    have eU := X7_val2 _ (1/2) 1 1 (fun x : Fin 2 → Fin 2 => ((x 0).val + (x 1).val) % 2 = 1)
      (fun x => rfl) hv Finset.univ X7_lb2 (by decide)
    unfold X7_q; rw [e1, e0, eU]; norm_num

theorem X7_u_val : cValue .dual X7_u = 0 := by
  have hv : IsLaw X7_u.prob := by
    refine ⟨fun x => by unfold X7_u; norm_num, ?_⟩
    refine (X7_sum22 (fun x => X7_u.prob x)).trans ?_
    unfold X7_u; norm_num
  rw [X7_dual2]
  have e1 := X7_val2 _ (1/4) 2 1 (fun _ : Fin 2 → Fin 2 => True)
      (fun x => rfl) hv {1} X7_lb42 (by decide)
  have e0 := X7_val2 _ (1/4) 2 1 (fun _ : Fin 2 → Fin 2 => True)
      (fun x => rfl) hv {0} X7_lb42 (by decide)
  have eU := X7_val2 _ (1/4) 1 2 (fun _ : Fin 2 → Fin 2 => True)
      (fun x => rfl) hv Finset.univ X7_lb4 (by decide)
  unfold X7_u; rw [e1, e0, eU]; norm_num

theorem X7_ccP (e : Fin 2) : eveLetterProbability conditionalCounterexample e = 1/2 := by
  unfold eveLetterProbability
  refine (X7_sum22 (fun x => conditionalCounterexample.prob (x, e))).trans ?_
  fin_cases e <;> simp [conditionalCounterexample] <;> norm_num

theorem X7_ccG (e : Fin 2) : givenE conditionalCounterexample e = X7_q e.val := by
  unfold givenE
  rw [X7_ccP]
  unfold X7_q
  show (⟨fun _ => 2, _⟩ : CData 2) = ⟨fun _ => 2, _⟩
  congr 1
  funext x
  show (if (e : ℕ) = ((x 0).val + (x 1).val) % 2 then (1/4 : ℝ) else 0) / (1/2) =
    if ((x 0).val + (x 1).val) % 2 = e.val then 1/2 else 0
  by_cases h : ((x 0).val + (x 1).val) % 2 = e.val
  · rw [if_pos h.symm, if_pos h]; norm_num
  · rw [if_neg (Ne.symm h), if_neg h]; norm_num

theorem X7_cc_val : conditionalAverage (cValue .dual : CData 2 → ℝ) conditionalCounterexample = 1 := by
  unfold conditionalAverage
  show ∑ e : Fin 2, _ = _
  rw [Fin.sum_univ_two, X7_ccP, X7_ccP, X7_ccG, X7_ccG]
  simp only [Fin.val_zero, Fin.val_one]
  rw [X7_q_val 0 (by norm_num), X7_q_val 1 (by norm_num)]
  norm_num

theorem X7_pe_val : conditionalAverage (cValue .dual : CData 2 → ℝ)
    (processE conditionalCounterexample (fun (_ : Fin 2) (_ : Fin 1) => 1)) = 0 := by
  have hx : ∀ x : Fin 2 → Fin 2, ∑ e : Fin 2, conditionalCounterexample.prob (x, e) * 1 = 1/4 := by
    intro x
    rw [Fin.sum_univ_two]
    show (if ((0 : Fin 2) : ℕ) = ((x 0).val + (x 1).val) % 2 then (1/4 : ℝ) else 0) * 1 +
      (if ((1 : Fin 2) : ℕ) = ((x 0).val + (x 1).val) % 2 then (1/4 : ℝ) else 0) * 1 = 1/4
    have : ((x 0).val + (x 1).val) % 2 = 0 ∨ ((x 0).val + (x 1).val) % 2 = 1 := by omega
    rcases this with h | h <;> rw [h] <;> norm_num
  have hP : eveLetterProbability (processE conditionalCounterexample (fun (_ : Fin 2) (_ : Fin 1) => 1)) (0 : Fin 1) = 1 := by
    unfold eveLetterProbability processE
    show ∑ x : Fin 2 → Fin 2, ∑ e : Fin 2, conditionalCounterexample.prob (x, e) * 1 = 1
    simp only [hx]; simp
  have hG : givenE (processE conditionalCounterexample (fun (_ : Fin 2) (_ : Fin 1) => 1)) (0 : Fin 1) = X7_u := by
    unfold givenE
    rw [hP]
    unfold X7_u
    show (⟨fun _ => 2, _⟩ : CData 2) = ⟨fun _ => 2, _⟩
    congr 1
    funext x
    show (∑ e : Fin 2, conditionalCounterexample.prob (x, e) * 1) / 1 = if True then 1/4 else 0
    rw [div_one, if_pos trivial]; exact hx x
  unfold conditionalAverage
  show ∑ e : Fin 1, _ = _
  rw [Fin.sum_univ_one, hP, hG, X7_u_val]
  norm_num

theorem X7_ccValid : EValid conditionalCounterexample := by
  refine ⟨fun i => by norm_num [conditionalCounterexample], by norm_num [conditionalCounterexample],
    fun z => ?_, ?_⟩
  · show 0 ≤ (if z.2.val = ((z.1 0).val + (z.1 1).val) % 2 then (1/4 : ℝ) else 0)
    split_ifs <;> norm_num
  · rw [Fintype.sum_prod_type]
    show ∑ x : Fin 2 → Fin 2, ∑ e : Fin 2, conditionalCounterexample.prob (x, e) = 1
    have := X7_ccP 0
    have h1 := X7_ccP 1
    unfold eveLetterProbability at this h1
    rw [Finset.sum_comm, Fin.sum_univ_two]
    exact (congrArg₂ (· + ·) this h1).trans (by norm_num)

end X7CE2

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)
open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)
open QAlgorithms.Papers.Independent.Claimed50.P33
  (InformationKind RegisterBasis FiniteState singleParties allParties
   info entropyAt trivialExtension informationFunctional LocalInstrument
   IsContinuousFunctional partyProduct registerMarginal)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Renew46.P37 X7CE X7CE2 in
theorem solution {n : ℕ} (hn : 2 ≤ n) (M : CData n → ℝ)
    (hM : IsCMonotone M) :
    ExtensionBasics (conditionalAverage M) ∧ ExtensionMonotonicity (conditionalAverage M) ∧
    EValid conditionalCounterexample ∧
    conditionalAverage (cValue .dual : CData 2 → ℝ)
      (processE conditionalCounterexample (fun (_ : Fin 2) (_ : Fin 1) => 1)) = 0 ∧
    conditionalAverage (cValue .dual : CData 2 → ℝ) conditionalCounterexample = 1 := by
  refine ⟨⟨fun p hp => ?_, fun p hp hc => ?_, fun p q hp hq => X7_add M hM p q hp hq,
    fun d e hd _ => X7_cont M hM d e hd⟩,
    ⟨fun p k w r hI => X7_honest M hM p w r hI,
     fun p f K hp _ hK => X7_evePublic M p f K hp hK⟩,
    X7_ccValid, X7_pe_val, X7_cc_val⟩
  · unfold conditionalAverage
    refine Finset.sum_nonneg fun e _ => ?_
    split_ifs with he
    · exact mul_nonneg he.le (hM.1 _ (X7_givenE_valid p hp e he))
    · exact le_rfl
  · unfold conditionalAverage
    refine Finset.sum_eq_zero fun e _ => ?_
    split_ifs with he
    · rw [hM.2.1 _ (X7_givenE_valid p hp e he) (hc e he), mul_zero]
    · rfl
