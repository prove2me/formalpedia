-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P03.conditionalMinEntropy_splitting
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T21:22:16.591242+00:00
-- url     : https://prove2.me/submissions/077a7e37-3b1e-4f59-b9f0-82d66a8401b9

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P03
noncomputable section

open QAlgorithms.Papers.Independent.Gap20.P03

open MeasureTheory Filter

open scoped ENNReal ComplexConjugate ComplexOrder Topology

-- Exact accepted finite Shannon entropy in bits (zero log zero is zero).

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

attribute [local instance] Classical.propDecidable

theorem g73b_fiber {V Y : Type*} (μ : V → ℝ≥0∞) (Yf : V → Y) (g : Y → ℝ≥0∞) :
    ∑' v, g (Yf v) * μ v = ∑' y, g y * massAt μ Yf y := by
  unfold massAt
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  congr 1; ext v
  rw [tsum_eq_single (Yf v)]
  · simp
  · intro y hy; simp [Ne.symm hy]

theorem g73b_mass_total {V Y : Type*} (μ : V → ℝ≥0∞) (Yf : V → Y) :
    ∑' y, massAt μ Yf y = ∑' v, μ v := by
  have := g73b_fiber μ Yf (fun _ => 1)
  simpa using this.symm

theorem g73b_le_mass {V Y : Type*} (μ : V → ℝ≥0∞) (Yf : V → Y) (v : V) :
    μ v ≤ massAt μ Yf (Yf v) := by
  unfold massAt
  calc μ v = (if Yf v = Yf v then μ v else 0) := by simp
    _ ≤ _ := ENNReal.le_tsum (f := fun w => if Yf w = Yf v then μ w else 0) v

def g73b_heavy {A0 A1 Z : Type*} (p : PMF ((A0 × A1) × Z)) (alpha : ℝ) (x1 : A1) (z : Z) : Prop :=
  ENNReal.ofReal (Real.rpow 2 (-alpha/2)) * massAt (fun w => p w) Prod.snd z ≤
    massAt (fun w => p w) (fun w => (w.1.2, w.2)) (x1, z)

def g73b_C {A0 A1 Z : Type*} (p : PMF ((A0 × A1) × Z)) (alpha : ℝ) (w : (A0 × A1) × Z) : Bool :=
  decide (g73b_heavy p alpha w.1.2 w.2)

def g73b_pe {A0 A1 Z : Type*} (p : PMF ((A0 × A1) × Z)) (alpha : ℝ) : PMF (((A0 × A1) × Z) × Bool) :=
  PMF.map (fun w => (w, g73b_C p alpha w)) p

theorem g73b_pe_apply {A0 A1 Z : Type*} (p : PMF ((A0 × A1) × Z)) (alpha : ℝ) (w : (A0 × A1) × Z)
    (c : Bool) : g73b_pe p alpha (w, c) = if c = g73b_C p alpha w then p w else 0 := by
  unfold g73b_pe
  rw [PMF.map_apply, tsum_eq_single w]
  · simp
  · intro a ha; simp [Ne.symm ha]

theorem g73b_marg {A0 A1 Z : Type*} (p : PMF ((A0 × A1) × Z)) (alpha : ℝ) (x : (A0 × A1) × Z) :
    massAt (fun w => g73b_pe p alpha w) Prod.fst x = p x := by
  unfold massAt
  rw [ENNReal.tsum_prod', tsum_eq_single x]
  · simp [g73b_pe_apply, tsum_fintype, Fintype.sum_bool]
  · intro a ha; simp [ha]

theorem g73b_threshold_of_lt {W A B : Type*} (p : W → ℝ≥0∞) (X : W → A) (Y : W → B) (eps alpha r : ℝ)
    (h : (alpha:EReal) ≤ smoothMin p X Y eps) (hr : r < alpha) : EntropyThreshold p X Y eps r := by
  have hlt : (r:EReal) < smoothMin p X Y eps := lt_of_lt_of_le (by exact_mod_cast hr) h
  unfold smoothMin at hlt
  obtain ⟨t, ⟨r', rfl, q, hq1, hq2, hq3⟩, hrt⟩ := lt_sSup_iff.mp hlt
  have hrr : r ≤ r' := by exact_mod_cast hrt.le
  refine ⟨q, hq1, hq2, fun x y => (hq3 x y).trans ?_⟩
  apply ENNReal.ofReal_le_ofReal
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

theorem g73b_qb {A0 A1 Z : Type*} (p : PMF ((A0 × A1) × Z)) (q : (A0 × A1) × Z → ℝ≥0∞)
    (hq1 : ∀ w, q w ≤ p w) (b : ℝ)
    (hq3 : ∀ x z, retainedConditional (fun w => p w) q Prod.fst Prod.snd x z ≤ ENNReal.ofReal b)
    (w : (A0 × A1) × Z) : q w ≤ ENNReal.ofReal b * massAt (fun w => p w) Prod.snd w.2 := by
  by_cases h0 : massAt (fun w => p w) Prod.snd w.2 = 0
  · have : p w = 0 := by
      have := g73b_le_mass (fun w => p w) Prod.snd w
      rw [h0] at this; exact le_antisymm this (zero_le)
    have := hq1 w
    rw [‹p w = 0›] at this
    rw [le_antisymm this (zero_le)]; exact zero_le
  · have h3 := hq3 w.1 w.2
    unfold retainedConditional at h3
    rw [if_neg h0] at h3
    have hfin : massAt (fun w => p w) Prod.snd w.2 ≠ ⊤ := by
      refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
      rw [← p.tsum_coe]
      unfold massAt
      exact ENNReal.tsum_le_tsum fun v => by split_ifs <;> simp
    rw [ENNReal.div_le_iff_le_mul (Or.inl h0) (Or.inl hfin)] at h3
    have h4 := g73b_le_mass q (fun w => (w.1, w.2)) w
    calc q w ≤ _ := h4
      _ ≤ _ := h3

def g73b_D {A0 A1 Z : Type*} (p : PMF ((A0 × A1) × Z)) (alpha e : ℝ) (z : Z) (c : Bool) : Prop :=
  massAt (fun v => g73b_pe p alpha v) (fun v => (v.1.2, v.2)) (z, c) <
    ENNReal.ofReal (e/2) * massAt (fun w => p w) Prod.snd z

theorem g73b_del {A0 A1 Z : Type*} (p : PMF ((A0 × A1) × Z)) (alpha e : ℝ) (he : 0 < e) :
    ∑' w, (if g73b_D p alpha e w.2 (g73b_C p alpha w) then p w else 0) ≤ ENNReal.ofReal e := by
  have h1 : ∑' w, (if g73b_D p alpha e w.2 (g73b_C p alpha w) then p w else 0) =
      ∑' v : ((A0 × A1) × Z) × Bool, (fun y : Z × Bool => if g73b_D p alpha e y.1 y.2 then (1:ℝ≥0∞) else 0)
        ((fun v : ((A0 × A1) × Z) × Bool => (v.1.2, v.2)) v) * g73b_pe p alpha v := by
    conv_rhs => rw [ENNReal.tsum_prod']
    congr 1; funext w
    rw [tsum_fintype, Fintype.sum_bool]
    simp only [g73b_pe_apply]
    cases hC : g73b_C p alpha w <;> simp
  rw [h1, g73b_fiber (⇑(g73b_pe p alpha)) (fun v : ((A0 × A1) × Z) × Bool => (v.1.2, v.2))
    (fun y : Z × Bool => if g73b_D p alpha e y.1 y.2 then (1:ℝ≥0∞) else 0)]
  calc _ ≤ ∑' y : Z × Bool, ENNReal.ofReal (e/2) * massAt (fun w => p w) Prod.snd y.1 := by
        refine ENNReal.tsum_le_tsum fun y => ?_
        by_cases hD : g73b_D p alpha e y.1 y.2
        · simp only [hD, if_true, one_mul]; exact hD.le
        · simp [hD]
    _ = ∑' z : Z, 2 * (ENNReal.ofReal (e/2) * massAt (fun w => p w) Prod.snd z) := by
        rw [ENNReal.tsum_prod']
        congr 1; funext z
        rw [tsum_fintype, Fintype.sum_bool, two_mul]
    _ = ENNReal.ofReal e := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, g73b_mass_total, p.tsum_coe, mul_one,
          ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1; ring

def g73b_q' {A0 A1 Z : Type*} (p : PMF ((A0 × A1) × Z)) (alpha e : ℝ) (q : (A0 × A1) × Z → ℝ≥0∞)
    (v : ((A0 × A1) × Z) × Bool) : ℝ≥0∞ :=
  if v.2 = g73b_C p alpha v.1 ∧ ¬ g73b_D p alpha e v.1.2 v.2 then q v.1 else 0

theorem g73b_sum_px1z {A0 A1 Z : Type*} (p : PMF ((A0 × A1) × Z)) (x0 : A0) (z : Z) :
    ∑' w : (A0 × A1) × Z, (if w.1.1 = x0 ∧ w.2 = z then
      massAt (fun w => p w) (fun w => (w.1.2, w.2)) (w.1.2, z) else 0) =
    massAt (fun w => p w) Prod.snd z := by
  unfold massAt
  simp_rw [ite_and]
  have : ∀ w : (A0 × A1) × Z, (if w.1.1 = x0 then if w.2 = z then
      ∑' w' : (A0 × A1) × Z, (if (w'.1.2, w'.2) = (w.1.2, z) then p w' else 0) else 0 else 0) =
      ∑' w' : (A0 × A1) × Z, (if w.1.1 = x0 ∧ w.2 = z ∧ w'.1.2 = w.1.2 ∧ w'.2 = z then p w' else 0) := by
    intro w
    by_cases h1 : w.1.1 = x0 <;> by_cases h2 : w.2 = z <;> simp [h1, h2, Prod.ext_iff]
  simp_rw [this]
  rw [ENNReal.tsum_comm]
  congr 1; funext w'
  rw [tsum_eq_single ((x0, w'.1.2), z)]
  · by_cases h : w'.2 = z <;> simp [h]
  · intro w hw
    have : ¬ (w.1.1 = x0 ∧ w.2 = z ∧ w'.1.2 = w.1.2 ∧ w'.2 = z) := by
      rintro ⟨h1, h2, h3, -⟩
      apply hw
      obtain ⟨⟨a, b⟩, c⟩ := w
      simp_all
    simp [this]

theorem g73b_num_true {A0 A1 Z : Type*} (p : PMF ((A0 × A1) × Z)) (alpha e b : ℝ)
    (q : (A0 × A1) × Z → ℝ≥0∞)
    (hqb : ∀ w, q w ≤ ENNReal.ofReal b * massAt (fun w => p w) Prod.snd w.2) (x0 : A0) (z : Z) :
    massAt (g73b_q' p alpha e q) (fun v => (selected v.1.1.1 v.1.1.2 v.2, (v.1.2, v.2)))
      (Sum.inl x0, (z, true)) ≤
    ENNReal.ofReal b * ENNReal.ofReal (Real.rpow 2 (alpha/2)) * massAt (fun w => p w) Prod.snd z := by
  unfold massAt
  rw [ENNReal.tsum_prod']
  calc _ ≤ ∑' w : (A0 × A1) × Z, (if w.1.1 = x0 ∧ w.2 = z then
        ENNReal.ofReal b * ENNReal.ofReal (Real.rpow 2 (alpha/2)) *
          massAt (fun w => p w) (fun w => (w.1.2, w.2)) (w.1.2, z) else 0) := by
        refine ENNReal.tsum_le_tsum fun w => ?_
        rw [tsum_fintype, Fintype.sum_bool]
        simp only [selected, g73b_q', if_true, if_false, Prod.mk.injEq, reduceCtorEq, false_and,
          and_true, Sum.inl.injEq]
        simp only [Bool.false_eq_true, and_false, if_false, add_zero]
        by_cases h1 : w.1.1 = x0 ∧ w.2 = z
        · rw [if_pos h1, if_pos h1]
          obtain ⟨h1a, h1b⟩ := h1
          split_ifs with h2
          · have hh : g73b_heavy p alpha w.1.2 w.2 := by
              have := h2.1; unfold g73b_C at this; simpa using this.symm
            rw [h1b] at hh
            have hq := hqb w
            rw [h1b] at hq
            refine hq.trans ?_
            rw [mul_assoc]
            gcongr _ * ?_
            unfold g73b_heavy at hh
            calc massAt (fun w => p w) Prod.snd z
                = ENNReal.ofReal (Real.rpow 2 (alpha/2)) * (ENNReal.ofReal (Real.rpow 2 (-alpha/2)) *
                    massAt (fun w => p w) Prod.snd z) := by
                  have h22 : Real.rpow 2 (alpha/2) * Real.rpow 2 (-alpha/2) = 1 := by
                    show (2:ℝ)^(alpha/2) * (2:ℝ)^(-alpha/2) = 1
                    rw [← Real.rpow_add (by norm_num)]; ring_nf; simp
                  rw [← mul_assoc, ← ENNReal.ofReal_mul (show (0:ℝ) ≤ Real.rpow 2 (alpha/2) from Real.rpow_nonneg (by norm_num) _), h22]
                  simp
              _ ≤ _ := by gcongr
          · exact zero_le
        · rw [if_neg h1]
          have : ¬ (w.1.1 = x0 ∧ w.2 = z) := h1
          simp only [this, if_false, le_refl]
    _ = ENNReal.ofReal b * ENNReal.ofReal (Real.rpow 2 (alpha/2)) * massAt (fun w => p w) Prod.snd z := by
        simp_rw [← mul_ite_zero]
        rw [ENNReal.tsum_mul_left, g73b_sum_px1z]

theorem g73b_num_false {A0 A1 Z : Type*} (p : PMF ((A0 × A1) × Z)) (alpha e : ℝ)
    (q : (A0 × A1) × Z → ℝ≥0∞) (hq1 : ∀ w, q w ≤ p w) (x1 : A1) (z : Z) :
    massAt (g73b_q' p alpha e q) (fun v => (selected v.1.1.1 v.1.1.2 v.2, (v.1.2, v.2)))
      (Sum.inr x1, (z, false)) ≤
    ENNReal.ofReal (Real.rpow 2 (-alpha/2)) * massAt (fun w => p w) Prod.snd z := by
  by_cases hh : g73b_heavy p alpha x1 z
  · have : massAt (g73b_q' p alpha e q) (fun v => (selected v.1.1.1 v.1.1.2 v.2, (v.1.2, v.2)))
        (Sum.inr x1, (z, false)) = 0 := by
      unfold massAt
      refine ENNReal.tsum_eq_zero.mpr fun v => ?_
      unfold g73b_q'
      split_ifs with h1 h2
      · exfalso
        obtain ⟨⟨⟨a0, a1⟩, zz⟩, c⟩ := v
        simp only [Prod.mk.injEq] at h1
        obtain ⟨hs, rfl, rfl⟩ := h1
        simp only [selected, Bool.false_eq_true, if_false, Sum.inr.injEq] at hs
        subst hs
        have h3 : decide (g73b_heavy p alpha a1 zz) = false := h2.1.symm
        rw [decide_eq_false_iff_not] at h3
        exact h3 hh
      · rfl
      · rfl
    rw [this]; exact zero_le
  · unfold g73b_heavy at hh
    push Not at hh
    refine le_trans ?_ hh.le
    unfold massAt
    rw [ENNReal.tsum_prod']
    refine ENNReal.tsum_le_tsum fun w => ?_
    rw [tsum_fintype, Fintype.sum_bool]
    obtain ⟨⟨a0, a1⟩, zz⟩ := w
    simp only [selected, g73b_q', Prod.mk.injEq, reduceCtorEq, false_and, if_false, Sum.inr.injEq,
      Bool.false_eq_true, add_zero, if_true]
    split_ifs <;> simp_all

theorem g73b_num {A0 A1 Z : Type*} (p : PMF ((A0 × A1) × Z)) (alpha e b K : ℝ)
    (q : (A0 × A1) × Z → ℝ≥0∞) (hq1 : ∀ w, q w ≤ p w)
    (hqb : ∀ w, q w ≤ ENNReal.ofReal b * massAt (fun w => p w) Prod.snd w.2)
    (hb1 : ENNReal.ofReal b * ENNReal.ofReal (Real.rpow 2 (alpha/2)) ≤ ENNReal.ofReal K)
    (hb2 : ENNReal.ofReal (Real.rpow 2 (-alpha/2)) ≤ ENNReal.ofReal K)
    (x : A0 ⊕ A1) (z : Z) (c : Bool) :
    massAt (g73b_q' p alpha e q) (fun v => (selected v.1.1.1 v.1.1.2 v.2, (v.1.2, v.2)))
      (x, (z, c)) ≤ ENNReal.ofReal K * massAt (fun w => p w) Prod.snd z := by
  rcases x with x0 | x1 <;> cases c
  · -- inl, false : zero
    have : massAt (g73b_q' p alpha e q) (fun v => (selected v.1.1.1 v.1.1.2 v.2, (v.1.2, v.2)))
        (Sum.inl x0, (z, false)) = 0 := by
      unfold massAt
      refine ENNReal.tsum_eq_zero.mpr fun v => ?_
      split_ifs with h1
      swap; · rfl
      exfalso
      obtain ⟨⟨⟨a0, a1⟩, zz⟩, c⟩ := v
      simp only [Prod.mk.injEq] at h1
      obtain ⟨hs, -, rfl⟩ := h1
      simp [selected] at hs
    rw [this]; exact zero_le
  · exact (g73b_num_true p alpha e b q hqb x0 z).trans (by gcongr)
  · exact (g73b_num_false p alpha e q hq1 x1 z).trans (by gcongr)
  · have : massAt (g73b_q' p alpha e q) (fun v => (selected v.1.1.1 v.1.1.2 v.2, (v.1.2, v.2)))
        (Sum.inr x1, (z, true)) = 0 := by
      unfold massAt
      refine ENNReal.tsum_eq_zero.mpr fun v => ?_
      split_ifs with h1
      swap; · rfl
      exfalso
      obtain ⟨⟨⟨a0, a1⟩, zz⟩, c⟩ := v
      simp only [Prod.mk.injEq] at h1
      obtain ⟨hs, -, rfl⟩ := h1
      simp [selected] at hs
    rw [this]; exact zero_le

theorem g73b_ret {A0 A1 Z : Type*} (p : PMF ((A0 × A1) × Z)) (alpha e b K : ℝ)
    (q : (A0 × A1) × Z → ℝ≥0∞) (hq1 : ∀ w, q w ≤ p w)
    (hqb : ∀ w, q w ≤ ENNReal.ofReal b * massAt (fun w => p w) Prod.snd w.2)
    (hb1 : ENNReal.ofReal b * ENNReal.ofReal (Real.rpow 2 (alpha/2)) ≤ ENNReal.ofReal K)
    (hb2 : ENNReal.ofReal (Real.rpow 2 (-alpha/2)) ≤ ENNReal.ofReal K)
    (s : ℝ) (hK : ENNReal.ofReal K ≤ ENNReal.ofReal (Real.rpow 2 (-s)) * ENNReal.ofReal (e/2))
    (x : A0 ⊕ A1) (y : Z × Bool) :
    retainedConditional (fun v => g73b_pe p alpha v) (g73b_q' p alpha e q)
      (fun v => selected v.1.1.1 v.1.1.2 v.2) (fun v => (v.1.2, v.2)) x y ≤
      ENNReal.ofReal (Real.rpow 2 (-s)) := by
  obtain ⟨z, c⟩ := y
  unfold retainedConditional
  split_ifs with h0
  · exact zero_le
  by_cases hD : g73b_D p alpha e z c
  · have : massAt (g73b_q' p alpha e q)
        (fun v => (selected v.1.1.1 v.1.1.2 v.2, (v.1.2, v.2))) (x, (z, c)) = 0 := by
      unfold massAt
      refine ENNReal.tsum_eq_zero.mpr fun v => ?_
      split_ifs with h1
      swap; · rfl
      simp only [Prod.mk.injEq] at h1
      obtain ⟨-, h2, h3⟩ := h1
      unfold g73b_q'
      split_ifs with h4
      · exact absurd (h2 ▸ h3 ▸ hD) h4.2
      · rfl
    rw [this, ENNReal.zero_div]; exact zero_le
  · unfold g73b_D at hD
    push Not at hD
    apply ENNReal.div_le_of_le_mul
    calc _ ≤ ENNReal.ofReal K * massAt (fun w => p w) Prod.snd z :=
          g73b_num p alpha e b K q hq1 hqb hb1 hb2 x z c
      _ ≤ ENNReal.ofReal (Real.rpow 2 (-s)) * ENNReal.ofReal (e/2) * massAt (fun w => p w) Prod.snd z := by
          gcongr
      _ ≤ _ := by rw [mul_assoc]; gcongr

theorem g73b_qmass {A0 A1 Z : Type*} (p : PMF ((A0 × A1) × Z)) (alpha e eps : ℝ) (he : 0 < e)
    (q : (A0 × A1) × Z → ℝ≥0∞) (hq1 : ∀ w, q w ≤ p w)
    (hq2 : ENNReal.ofReal (1 - eps) ≤ ∑' w, q w) :
    ENNReal.ofReal (1 - (eps + e)) ≤ ∑' v, g73b_q' p alpha e q v := by
  have h1 : ∑' v, g73b_q' p alpha e q v =
      ∑' w, (if ¬ g73b_D p alpha e w.2 (g73b_C p alpha w) then q w else 0) := by
    rw [ENNReal.tsum_prod']
    congr 1; funext w
    rw [tsum_fintype, Fintype.sum_bool]
    unfold g73b_q'
    cases hC : g73b_C p alpha w <;> simp
  have h2 : ∑' w, q w = ∑' w, (if ¬ g73b_D p alpha e w.2 (g73b_C p alpha w) then q w else 0) +
      ∑' w, (if g73b_D p alpha e w.2 (g73b_C p alpha w) then q w else 0) := by
    rw [← ENNReal.tsum_add]
    congr 1; funext w
    split_ifs <;> simp
  have h3 : ∑' w, (if g73b_D p alpha e w.2 (g73b_C p alpha w) then q w else 0) ≤ ENNReal.ofReal e :=
    le_trans (ENNReal.tsum_le_tsum fun w => by split_ifs <;> simp [hq1 w]) (g73b_del p alpha e he)
  rw [h1]
  have h4 : ENNReal.ofReal (1 - eps) ≤ ∑' w, (if ¬ g73b_D p alpha e w.2 (g73b_C p alpha w) then q w else 0)
      + ENNReal.ofReal e := by
    calc _ ≤ ∑' w, q w := hq2
      _ = _ := h2
      _ ≤ _ := add_le_add_right h3 _
  have h5 := tsub_le_iff_right.mpr h4
  rw [← ENNReal.ofReal_sub _ he.le] at h5
  calc ENNReal.ofReal (1 - (eps + e)) = ENNReal.ofReal (1 - eps - e) := by ring_nf
    _ ≤ _ := h5

theorem solution {A0 A1 Z : Type*}
    (p : PMF ((A0 × A1) × Z)) (alpha epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hentropy : (alpha:EReal) ≤ smoothMin (fun w => p w) Prod.fst Prod.snd epsilon) :
    ∃ pe : PMF (((A0 × A1) × Z) × Bool),
      (∀ x, massAt (fun w => pe w) Prod.fst x = p x) ∧
      ∀ epsilonPrime : ℝ, 0 < epsilonPrime →
        ((alpha/2-1-Real.logb 2 (1/epsilonPrime):ℝ):EReal) ≤
        smoothMin (fun w => pe w) (fun w => selected w.1.1.1 w.1.1.2 w.2)
          (fun w => (w.1.2,w.2)) (epsilon+epsilonPrime) := by
  refine ⟨g73b_pe p alpha, fun x => g73b_marg p alpha x, fun e he => ?_⟩
  apply le_of_forall_lt_imp_le_of_dense
  intro t ht
  induction t using EReal.rec with
  | bot => exact bot_le
  | top => exact absurd ht (not_lt.mpr le_top)
  | coe s =>
    have hs : s < alpha/2 - 1 - Real.logb 2 (1/e) := by exact_mod_cast ht
    apply le_sSup
    refine ⟨s, rfl, ?_⟩
    have hr : s + alpha/2 + 1 + Real.logb 2 (1/e) < alpha := by linarith
    obtain ⟨q, hq1, hq2, hq3⟩ := g73b_threshold_of_lt _ _ _ epsilon alpha _ hentropy hr
    have hqb := g73b_qb p q hq1 _ hq3
    have hlog : Real.rpow 2 (-Real.logb 2 (1/e)) = e := by
      show (2:ℝ) ^ (-Real.logb 2 (1/e)) = e
      rw [Real.rpow_neg (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]
      simp
    have hKeq : Real.rpow 2 (-s) * (e/2) = Real.rpow 2 (-s - 1 - Real.logb 2 (1/e)) := by
      show (2:ℝ) ^ (-s) * (e/2) = (2:ℝ) ^ (-s - 1 - Real.logb 2 (1/e))
      rw [sub_eq_add_neg, Real.rpow_add (by norm_num), sub_eq_add_neg, Real.rpow_add (by norm_num)]
      rw [show (2:ℝ) ^ (-Real.logb 2 (1/e)) = e from hlog]
      rw [Real.rpow_neg_one]; ring
    have hb1eq : Real.rpow 2 (-(s + alpha/2 + 1 + Real.logb 2 (1/e))) * Real.rpow 2 (alpha/2) =
        Real.rpow 2 (-s - 1 - Real.logb 2 (1/e)) := by
      show (2:ℝ) ^ (-(s + alpha/2 + 1 + Real.logb 2 (1/e))) * (2:ℝ) ^ (alpha/2) =
        (2:ℝ) ^ (-s - 1 - Real.logb 2 (1/e))
      rw [← Real.rpow_add (by norm_num)]; congr 1; ring
    refine ⟨g73b_q' p alpha e q, ?_, g73b_qmass p alpha e epsilon he q hq1 hq2, ?_⟩
    · intro v
      obtain ⟨w, c⟩ := v
      unfold g73b_q'
      show _ ≤ g73b_pe p alpha (w, c)
      rw [g73b_pe_apply]
      split_ifs with h1 h2
      · exact hq1 w
      · exact absurd h1.1 h2
      · exact zero_le
      · exact zero_le
    · refine g73b_ret p alpha e _ (Real.rpow 2 (-s - 1 - Real.logb 2 (1/e))) q hq1 hqb ?_ ?_ s ?_
      · rw [← ENNReal.ofReal_mul (show (0:ℝ) ≤ Real.rpow 2 (-(s + alpha/2 + 1 + Real.logb 2 (1/e))) from
          Real.rpow_nonneg (by norm_num) _), hb1eq]
      · apply ENNReal.ofReal_le_ofReal
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      · rw [← ENNReal.ofReal_mul (show (0:ℝ) ≤ Real.rpow 2 (-s) from Real.rpow_nonneg (by norm_num) _),
          hKeq]
