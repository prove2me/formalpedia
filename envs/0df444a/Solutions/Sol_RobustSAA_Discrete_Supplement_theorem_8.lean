-- Prove2me | solution 1 for RobustSAA.Discrete.Supplement.theorem_8
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:14:03.351441+00:00
-- url     : https://prove2.me/submissions/b084026e-71a8-488f-9f9c-3670d8d43199

import Mathlib
import Definitions.Def_RobustSAA_Discrete_Setting
import Definitions.Def_RobustSAA_Convergence_Setting
import Definitions.Def_RobustSAA_Discrete_Supplement_Cones
import Definitions.Def_RobustSAA_Discrete_Supplement_DiscreteDual

open RobustSAA
open RobustSAA.Discrete
open RobustSAA.Discrete.Supplement

open MeasureTheory Filter Topology RobustSAA.Discrete

theorem solution {n N d dx : ℕ} (hN : 0 < N) (smp : Fin N → Fin n)
    (ξhat : Fin n → RobustSAA.Convergence.Pt d) (X : Set (RobustSAA.Convergence.Pt dx))
    (hX : IsClosed X) (c : RobustSAA.Convergence.Pt dx → RobustSAA.Convergence.Pt d → ℝ)
    (hequi : Equicontinuous (fun j : Fin n => fun x => c x (ξhat j)))
    (hcomp : IsCompact X ∨
      ∀ j, Tendsto (fun x => c x (ξhat j))
        (Bornology.cobounded (RobustSAA.Convergence.Pt dx)) atTop)
    (x : RobustSAA.Convergence.Pt dx) (hx : x ∈ X) (q : ℝ) (hq : 0 < q) :
    ((∃ x₀ ∈ X, discWorstCase (chiRegion ((N : ℝ) * q ^ 2) N smp)
        (fun j => c x₀ (ξhat j)) < ⊤) →
      IsMinValue (discWorstCase (chiRegion ((N : ℝ) * q ^ 2) N smp) (fun j => c x (ξhat j)))
        (chiDualValues q smp (fun j => c x (ξhat j)))) ∧
    ((∃ x₀ ∈ X, discWorstCase (gRegion ((N : ℝ) * q ^ 2) N smp)
        (fun j => c x₀ (ξhat j)) < ⊤) →
      discWorstCase (gRegion ((N : ℝ) * q ^ 2) N smp) (fun j => c x (ξhat j)) =
          sInf ((fun v : ℝ => (v : EReal)) '' gDualValues q smp (fun j => c x (ξhat j))) ∧
        ((∀ j, 0 < phat smp j) →
          IsMinValue (discWorstCase (gRegion ((N : ℝ) * q ^ 2) N smp)
            (fun j => c x (ξhat j))) (gDualValues q smp (fun j => c x (ξhat j))))) := by
              clear hX hequi hcomp hx
              revert hN hq
              have key : ∀ (P a : Fin n → ℝ) (D : (Fin n → ℝ) → ℝ) (B W : ℝ), (∀ j, 0 ≤ P j) → ∑ j, P j = 1 → D P < B →
                  (∀ p p' : Fin n → ℝ, (∀ j, 0 ≤ p j ∧ (0 < P j → 0 < p j)) → (∀ j, 0 ≤ p' j ∧ (0 < P j → 0 < p' j)) →
                    ∀ α β : ℝ, 0 ≤ α → 0 ≤ β → α + β = 1 → D (fun j => α * p j + β * p' j) ≤ α * D p + β * D p') →
                  (∀ p : Fin n → ℝ, (∀ j, 0 ≤ p j ∧ (0 < P j → 0 < p j)) → ContinuousAt (fun τ : ℝ => D (fun j => τ * p j)) 1) →
                  (∀ p : Fin n → ℝ, (∀ j, 0 ≤ p j ∧ (0 < P j → 0 < p j)) → ∑ j, p j = 1 → D p ≤ B → ∑ j, p j * a j ≤ W) →
                  ∃ r s : ℝ, 0 ≤ s ∧ ∀ p : Fin n → ℝ, (∀ j, 0 ≤ p j ∧ (0 < P j → 0 < p j)) →
                    ∑ j, p j * a j - r * ∑ j, p j - s * D p ≤ W - r - s * B := by
                intro P a D B W hP0 hP1 hDB hconv hcont hW
                have hPd : ∀ j, 0 ≤ P j ∧ (0 < P j → 0 < P j) := fun j => ⟨hP0 j, id⟩
                obtain ⟨S, hS⟩ : ∃ S : Set (ℝ × ℝ × ℝ), S = {v | ∃ p : Fin n → ℝ, (∀ j, 0 ≤ p j ∧ (0 < P j → 0 < p j)) ∧
                  ∑ j, p j = v.1 ∧ D p < v.2.1 ∧ v.2.2 < ∑ j, p j * a j} := ⟨_, rfl⟩
                have hSc : Convex ℝ S := by
                  rw [hS]
                  rintro ⟨x1, x2, x3⟩ ⟨p, hp, hp1, hp2, hp3⟩ ⟨y1, y2, y3⟩ ⟨p', hp', hp1', hp2', hp3'⟩ α β hα hβ hαβ
                  simp only at hp1 hp2 hp3 hp1' hp2' hp3'
                  refine ⟨fun j => α * p j + β * p' j, ?_, ?_, ?_, ?_⟩
                  · intro j
                    refine ⟨by have := (hp j).1; have := (hp' j).1; positivity, fun h => ?_⟩
                    have h1 := (hp j).2 h
                    have h2 := (hp' j).2 h
                    rcases hα.eq_or_lt with h0 | h0
                    · have : β = 1 := by linarith
                      rw [← h0, this]; simpa using h2
                    · have := mul_pos h0 h1
                      have := mul_nonneg hβ h2.le
                      linarith
                  · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hp1, hp1']
                    simp
                  · refine lt_of_le_of_lt (hconv p p' hp hp' α β hα hβ hαβ) ?_
                    simp
                    rcases hα.eq_or_lt with h0 | h0
                    · have : β = 1 := by linarith
                      rw [← h0, this]; simpa using hp2'
                    · have := mul_lt_mul_of_pos_left hp2 h0
                      have := mul_le_mul_of_nonneg_left hp2'.le hβ
                      linarith
                  · have e : ∑ j, (α * p j + β * p' j) * a j = α * ∑ j, p j * a j + β * ∑ j, p' j * a j := by
                      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
                      exact Finset.sum_congr rfl fun j _ => by ring
                    rw [e]
                    simp
                    rcases hα.eq_or_lt with h0 | h0
                    · have : β = 1 := by linarith
                      rw [← h0, this]; simpa using hp3'
                    · have := mul_lt_mul_of_pos_left hp3 h0
                      have := mul_le_mul_of_nonneg_left hp3'.le hβ
                      linarith
                have hSo : IsOpen S := by
                  rw [isOpen_iff_mem_nhds]
                  intro v hv
                  have hv' := hv
                  rw [hS] at hv'
                  obtain ⟨p, hp, hp1, hp2, hp3⟩ := hv'
                  have hpos : 0 < ∑ j, p j := by
                    have : ∃ j, 0 < P j := by
                      by_contra hcon
                      push Not at hcon
                      have : ∑ j, P j ≤ 0 := Finset.sum_nonpos fun j _ => hcon j
                      linarith
                    obtain ⟨j, hj⟩ := this
                    exact Finset.sum_pos' (fun i _ => (hp i).1) ⟨j, Finset.mem_univ j, (hp j).2 hj⟩
                  have hv1 : 0 < v.1 := hp1 ▸ hpos
                  have ct : ContinuousAt (fun w : ℝ × ℝ × ℝ => w.1 / v.1) v := by fun_prop
                  have cD : ContinuousAt (fun w : ℝ × ℝ × ℝ => D (fun j => (w.1 / v.1) * p j)) v := by
                    have h1 : v.1 / v.1 = 1 := div_self hv1.ne'
                    have h2 := hcont p hp
                    rw [← h1] at h2
                    exact ContinuousAt.comp (f := fun w : ℝ × ℝ × ℝ => w.1 / v.1) (g := fun τ : ℝ => D (fun j => τ * p j)) h2 ct
                  have e1 : ∀ᶠ w in 𝓝 v, D (fun j => (w.1 / v.1) * p j) < w.2.1 := by
                    refine cD.eventually_lt (by fun_prop) ?_
                    simpa [div_self hv1.ne'] using hp2
                  have e2 : ∀ᶠ w in 𝓝 v, w.2.2 < (w.1 / v.1) * ∑ j, p j * a j := by
                    refine ContinuousAt.eventually_lt (f := fun w : ℝ × ℝ × ℝ => w.2.2) (g := fun w : ℝ × ℝ × ℝ => (w.1 / v.1) * ∑ j, p j * a j) (by fun_prop) (by fun_prop) ?_
                    simpa [div_self hv1.ne'] using hp3
                  have e3 : ∀ᶠ w in 𝓝 v, (0:ℝ) < w.1 := by
                    exact ContinuousAt.eventually_lt (f := fun _ : ℝ × ℝ × ℝ => (0:ℝ)) (g := fun w : ℝ × ℝ × ℝ => w.1) (by fun_prop) (by fun_prop) hv1
                  filter_upwards [e1, e2, e3] with w h1 h2 h3
                  rw [hS]
                  have h4 : 0 < w.1 / v.1 := div_pos h3 hv1
                  refine ⟨fun j => (w.1 / v.1) * p j, fun j => ⟨mul_nonneg h4.le (hp j).1, fun h => mul_pos h4 ((hp j).2 h)⟩, ?_, h1, ?_⟩
                  · rw [← Finset.mul_sum, hp1]; field_simp
                  · have : ∑ j, (w.1 / v.1) * p j * a j = (w.1 / v.1) * ∑ j, p j * a j := by
                      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
                    rw [this]; exact h2
                have hnot : ((1 : ℝ), B, W) ∉ S := by
                  rw [hS]
                  rintro ⟨p, hp, hp1, hp2, hp3⟩
                  have := hW p hp hp1 hp2.le
                  simp only at hp3
                  linarith
                obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hSc hSo hnot
                obtain ⟨l, hl⟩ : ∃ l, l = f (1, 0, 0) := ⟨_, rfl⟩
                obtain ⟨m, hm⟩ : ∃ l, l = f (0, 1, 0) := ⟨_, rfl⟩
                obtain ⟨k, hk⟩ : ∃ l, l = f (0, 0, 1) := ⟨_, rfl⟩
                have hfe : ∀ x y z : ℝ, f (x, y, z) = l * x + m * y + k * z := by
                  intro x y z
                  have : ((x, y, z) : ℝ × ℝ × ℝ) = x • (1, 0, 0) + y • (0, 1, 0) + z • (0, 0, 1) := by simp
                  rw [this, map_add, map_add, map_smul, map_smul, map_smul, hl, hm, hk]
                  simp [mul_comm]
                have hH : ∀ p : Fin n → ℝ, (∀ j, 0 ≤ p j ∧ (0 < P j → 0 < p j)) → ∀ y z : ℝ, D p < y → z < ∑ j, p j * a j →
                    l * ∑ j, p j + m * y + k * z < l + m * B + k * W := by
                  intro p hp y z hy hz
                  have h := hf (∑ j, p j, y, z) (by rw [hS]; exact ⟨p, hp, rfl, hy, hz⟩)
                  rw [hfe, hfe] at h
                  linarith
                have hm0 : m ≤ 0 := by
                  by_contra hcon
                  push Not at hcon
                  obtain ⟨C, hC⟩ : ∃ C, C = l + m * B + k * W - (l + m * (D P + 1) + k * (∑ j, P j * a j - 1)) := ⟨_, rfl⟩
                  have h := hH P hPd (D P + 1 + |C| / m) (∑ j, P j * a j - 1) (by have : 0 ≤ |C| / m := by positivity
                                                                                  linarith) (by linarith)
                  have h2 : m * (D P + 1 + |C| / m) = m * (D P + 1) + |C| := by field_simp
                  rw [h2, hP1] at h
                  have := le_abs_self C
                  linarith
                have hk0 : 0 ≤ k := by
                  by_contra hcon
                  push Not at hcon
                  obtain ⟨C, hC⟩ : ∃ C, C = l + m * B + k * W - (l + m * (D P + 1) + k * (∑ j, P j * a j - 1)) := ⟨_, rfl⟩
                  have h := hH P hPd (D P + 1) (∑ j, P j * a j - 1 + |C| / k) (by linarith) (by
                    have : |C| / k ≤ 0 := div_nonpos_of_nonneg_of_nonpos (abs_nonneg _) hcon.le
                    linarith)
                  have h2 : k * (∑ j, P j * a j - 1 + |C| / k) = k * (∑ j, P j * a j - 1) + |C| := by
                    have := hcon.ne
                    field_simp
                  rw [h2, hP1] at h
                  have := le_abs_self C
                  linarith
                have hk1 : 0 < k := by
                  refine lt_of_le_of_ne hk0 fun h0 => ?_
                  have h := hH P hPd B (∑ j, P j * a j - 1) hDB (by linarith)
                  rw [← h0, hP1] at h
                  linarith
                have hlim : ∀ p : Fin n → ℝ, (∀ j, 0 ≤ p j ∧ (0 < P j → 0 < p j)) →
                    l * ∑ j, p j + m * D p + k * ∑ j, p j * a j ≤ l + m * B + k * W := by
                  intro p hp
                  refine le_of_forall_pos_le_add fun ε hε => ?_
                  have hkm : 0 < k - m := by linarith
                  have h := hH p hp (D p + ε / (k - m)) (∑ j, p j * a j - ε / (k - m)) (by have := div_pos hε hkm; linarith) (by have := div_pos hε hkm; linarith)
                  have h3 : (k - m) * (ε / (k - m)) = ε := by field_simp
                  linarith
                refine ⟨-l / k, -m / k, div_nonneg (by linarith) hk0, fun p hp => ?_⟩
                have h := hlim p hp
                have e1 : k * (∑ j, p j * a j - -l / k * ∑ j, p j - -m / k * D p) = l * ∑ j, p j + m * D p + k * ∑ j, p j * a j := by
                  field_simp; ring
                have e2 : k * (W - -l / k - -m / k * B) = l + m * B + k * W := by
                  field_simp; ring
                rw [← e1, ← e2] at h
                exact le_of_mul_le_mul_left h hk1
              have pv0 : ∀ (F : ProbabilityMeasure (Fin n)) (j : Fin n), 0 ≤ pvec F j := by
                intro F j
                exact measureReal_nonneg
              have pv1 : ∀ (F : ProbabilityMeasure (Fin n)), ∑ j, pvec F j = 1 := by
                intro F
                unfold pvec
                have h : (F : Measure (Fin n)).real Set.univ = 1 := by simp
                rw [← h, ← Finset.coe_univ, ← sum_measureReal_singleton]
              have pvex : ∀ (p : Fin n → ℝ), (∀ j, 0 ≤ p j) → ∑ j, p j = 1 → ∃ F : ProbabilityMeasure (Fin n), ∀ j, pvec F j = p j := by
                intro p hp h1
                refine ⟨⟨(PMF.ofFintype (fun j => ENNReal.ofReal (p j)) (by
                  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hp j), h1, ENNReal.ofReal_one])).toMeasure, inferInstance⟩, fun j => ?_⟩
                unfold pvec
                simp only [ProbabilityMeasure.coe_mk, Measure.real]
                rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton j)]
                simp [hp j]
              have ph0 : ∀ (smp : Fin N → Fin n) (j : Fin n), 0 ≤ phat smp j := by
                intro smp j
                unfold phat
                positivity
              have ph1 : 0 < N → ∀ (smp : Fin N → Fin n), ∑ j, phat smp j = 1 := by
                intro hN smp
                unfold phat
                rw [← Finset.sum_div]
                have h : ∑ j : Fin n, (Finset.univ.filter (fun i => smp i = j)).card = N := by
                  have := Finset.card_eq_sum_card_fiberwise (f := smp) (s := Finset.univ) (t := Finset.univ) (by intro x _; simp)
                  simpa using this.symm
                have hN' : (N : ℝ) ≠ 0 := by positivity
                rw [← Nat.cast_sum, h, div_self hN']
              have chiR : 0 < N → ∀ (smp : Fin N → Fin n) (q : ℝ), 0 < q → ∀ F : ProbabilityMeasure (Fin n), (∑ j, phat smp j = 1) →
                  (F ∈ chiRegion ((N : ℝ) * q ^ 2) N smp ↔ (∀ j, 0 ≤ pvec F j ∧ (0 < phat smp j → 0 < pvec F j)) ∧
                    ∑ j, phat smp j ^ 2 / pvec F j ≤ 1 + q ^ 2) := by
                intro hN smp q hq F hP1
                have hN' : (N : ℝ) ≠ 0 := by positivity
                have e0 : Real.sqrt ((N : ℝ) * q ^ 2 / N) = q := by
                  rw [mul_div_cancel_left₀ _ hN', Real.sqrt_sq hq.le]
                have h0 : F ∈ chiRegion ((N : ℝ) * q ^ 2) N smp ↔ (∑ j : Fin n,
                  ENNReal.ofReal ((pvec F j - phat smp j) ^ 2) / ENNReal.ofReal (pvec F j)) ≤ ENNReal.ofReal (q ^ 2) := by
                  unfold chiRegion chiStat
                  rw [Set.mem_ofPred_eq, e0]
                  have : ENNReal.ofReal q = (ENNReal.ofReal (q ^ 2)) ^ (1 / 2 : ℝ) := by
                    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow, Real.sqrt_sq hq.le]
                  rw [this, ENNReal.rpow_le_rpow_iff (by norm_num)]
                have key : (∀ j, 0 ≤ pvec F j ∧ (0 < phat smp j → 0 < pvec F j)) → ((∑ j : Fin n,
                  ENNReal.ofReal ((pvec F j - phat smp j) ^ 2) / ENNReal.ofReal (pvec F j)) ≤ ENNReal.ofReal (q ^ 2) ↔ 
                    ∑ j, phat smp j ^ 2 / pvec F j ≤ 1 + q ^ 2) := by
                  intro hd
                  have hz : ∀ j, pvec F j = 0 → phat smp j = 0 := by
                    intro j hj
                    by_contra hne
                    have := (hd j).2 (lt_of_le_of_ne (by unfold phat; positivity) (Ne.symm hne))
                    linarith
                  have e1 : ∀ j, ENNReal.ofReal ((pvec F j - phat smp j) ^ 2) / ENNReal.ofReal (pvec F j) = ENNReal.ofReal (pvec F j - 2 * phat smp j + phat smp j ^ 2 / pvec F j) := by
                    intro j
                    rcases (hd j).1.eq_or_lt with h | h
                    · rw [← h, hz j h.symm]; simp
                    · rw [← ENNReal.ofReal_div_of_pos h]
                      congr 1
                      field_simp
                      ring
                  have nn : ∀ j, 0 ≤ pvec F j - 2 * phat smp j + phat smp j ^ 2 / pvec F j := by
                    intro j
                    rcases (hd j).1.eq_or_lt with h | h
                    · rw [← h, hz j h.symm]; simp
                    · have : pvec F j - 2 * phat smp j + phat smp j ^ 2 / pvec F j = (pvec F j - phat smp j) ^ 2 / pvec F j := by
                        field_simp
                        ring
                      rw [this]; positivity
                  rw [Finset.sum_congr rfl fun j _ => e1 j, ← ENNReal.ofReal_sum_of_nonneg fun j _ => nn j, ENNReal.ofReal_le_ofReal_iff (by positivity)]
                  have hp1 : ∑ j, pvec F j = 1 := pv1 F
                  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hP1, hp1]
                  constructor <;> intro h <;> linarith
                rw [h0]
                constructor
                · intro h
                  have hd : ∀ j, 0 ≤ pvec F j ∧ (0 < phat smp j → 0 < pvec F j) := by
                    intro j
                    refine ⟨pv0 F j, fun hj => ?_⟩
                    refine lt_of_le_of_ne (pv0 F j) fun h0 => ?_
                    have h1 := Finset.single_le_sum (f := fun j => ENNReal.ofReal ((pvec F j - phat smp j) ^ 2) / ENNReal.ofReal (pvec F j)) (fun i _ => bot_le) (Finset.mem_univ j)
                    have h2 := h1.trans h
                    simp only [← h0] at h2
                    rw [ENNReal.ofReal_zero, ENNReal.div_zero (by simpa using hj.ne')] at h2
                    simp at h2
                  exact ⟨hd, (key hd).1 h⟩
                · rintro ⟨hd, h⟩
                  exact (key hd).2 h
              have gR : 0 < N → ∀ (smp : Fin N → Fin n) (q : ℝ), 0 < q → ∀ F : ProbabilityMeasure (Fin n), (∑ j, phat smp j = 1) →
                  (F ∈ gRegion ((N : ℝ) * q ^ 2) N smp ↔ (∀ j, 0 ≤ pvec F j ∧ (0 < phat smp j → 0 < pvec F j)) ∧
                    ∑ j, phat smp j * Real.log (phat smp j / pvec F j) ≤ q ^ 2 / 2) := by
                intro hN smp q hq F hP1
                have hN' : (N : ℝ) ≠ 0 := by positivity
                have e0 : ((N : ℝ) * q ^ 2 / N) = q ^ 2 := by
                  rw [mul_div_cancel_left₀ _ hN']
                have key : (∀ j, 0 ≤ pvec F j ∧ (0 < phat smp j → 0 < pvec F j)) → gStatSq F smp = ((2 * ∑ j, phat smp j * Real.log (phat smp j / pvec F j) : ℝ) : EReal) := by
                  intro hd
                  unfold gStatSq
                  have e1 : ∀ j, gTerm F smp j = ((phat smp j * Real.log (phat smp j / pvec F j) : ℝ) : EReal) := by
                    intro j
                    unfold gTerm
                    split_ifs with h1 h2
                    · simp [h1]
                    · have := (hd j).2 (lt_of_le_of_ne (ph0 smp j) (Ne.symm h1))
                      linarith
                    · rfl
                  rw [Finset.sum_congr rfl fun j _ => e1 j]
                  have cs : ∀ (T : Finset (Fin n)) (g : Fin n → ℝ), ∑ j ∈ T, ((g j : ℝ) : EReal) = ((∑ j ∈ T, g j : ℝ) : EReal) := by
                    intro T g
                    induction T using Finset.induction_on with
                    | empty => simp
                    | insert x T hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, ih, EReal.coe_add]
                  rw [cs, EReal.coe_mul]
                  rfl
                unfold gRegion
                rw [Set.mem_ofPred_eq, e0]
                constructor
                · intro h
                  have hd : ∀ j, 0 ≤ pvec F j ∧ (0 < phat smp j → 0 < pvec F j) := by
                    intro j
                    refine ⟨pv0 F j, fun hj => ?_⟩
                    refine lt_of_le_of_ne (pv0 F j) fun h0 => ?_
                    have nb : ∀ i, gTerm F smp i ≠ ⊥ := by
                      intro i
                      unfold gTerm
                      split_ifs
                      · simp
                      · simp
                      · exact EReal.coe_ne_bot _
                    have nbs : ∀ T : Finset (Fin n), ∑ i ∈ T, gTerm F smp i ≠ ⊥ := by
                      intro T
                      induction T using Finset.induction_on with
                      | empty => simp
                      | insert x T hx ih =>
                        rw [Finset.sum_insert hx]
                        intro hbot
                        rcases EReal.add_eq_bot_iff.1 hbot with h | h
                        · exact nb x h
                        · exact ih h
                    have ht : gTerm F smp j = ⊤ := by
                      unfold gTerm
                      rw [if_neg hj.ne', if_pos h0.symm]
                    unfold gStatSq at h
                    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), ht, EReal.top_add_of_ne_bot (nbs _), EReal.mul_top_of_pos (by norm_num)] at h
                    exact absurd h (not_le.2 (EReal.coe_lt_top _))
                  refine ⟨hd, ?_⟩
                  rw [key hd, EReal.coe_le_coe_iff] at h
                  linarith
                · rintro ⟨hd, h⟩
                  rw [key hd, EReal.coe_le_coe_iff]
                  linarith
              have ub : ∀ (P a : Fin n → ℝ) (D : (Fin n → ℝ) → ℝ) (r s V : ℝ) (_ : ∀ j, 0 ≤ P j) (_ : 0 ≤ s)
                  (_ : ∀ p : Fin n → ℝ, (∀ j, P j ≤ p j) → D p ≤ D P)
                  (_ : ∀ p : Fin n → ℝ, (∀ j, 0 ≤ p j ∧ (0 < P j → 0 < p j)) →
                    ∑ j, p j * a j - r * ∑ j, p j - s * D p ≤ V), ∀ j, a j ≤ r := by
                intro P a D r s V hP hs hD h j
                by_contra hcon
                push Not at hcon
                obtain ⟨C, hC⟩ : ∃ C, C = V - (∑ j, P j * a j - r * ∑ j, P j - s * D P) := ⟨_, rfl⟩
                obtain ⟨M, hM⟩ : ∃ M, M = (|C| + 1) / (a j - r) := ⟨_, rfl⟩
                have hM0 : 0 ≤ M := by
                  have : 0 < a j - r := by linarith
                  rw [hM]; positivity
                have hM1 : M * (a j - r) = |C| + 1 := by
                  have : a j - r ≠ 0 := by linarith
                  rw [hM]; field_simp
                have hge : ∀ i, P i ≤ P i + (if i = j then M else 0) := by
                  intro i
                  split_ifs <;> linarith
                have h1 := h (fun i => P i + (if i = j then M else 0)) (fun i => ⟨(hP i).trans (hge i), fun h => h.trans_le (hge i)⟩)
                have h2 := hD (fun i => P i + (if i = j then M else 0)) hge
                have h3 := mul_le_mul_of_nonneg_left h2 hs
                simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1 h3
                have := le_abs_self C
                linarith
              have chiWeak : ∀ (smp : Fin N → Fin n) (a : Fin n → ℝ) (q : ℝ), (∑ j, phat smp j = 1) → ∀ p : Fin n → ℝ,
                  (∀ j, 0 ≤ p j ∧ (0 < phat smp j → 0 < p j)) → ∑ j, p j = 1 → ∑ j, phat smp j ^ 2 / p j ≤ 1 + q ^ 2 →
                  ∀ v ∈ chiDualValues q smp a, ∑ j, p j * a j ≤ v := by
                intro smp a q hP1 p hd hp1 hD v hv
                obtain ⟨r, s, t, y, c, hs, hy, hc, ht, hsoc, hac, rfl⟩ := hv
                have key : ∀ j, phat smp j * t j ≤ p j * (s + r) - p j * a j + s * (phat smp j ^ 2 / p j) - 2 * s * phat smp j := by
                  intro j
                  have hPj := ph0 smp j
                  have h1 : phat smp j * t j ≤ phat smp j * (y j - 2 * s) := mul_le_mul_of_nonneg_left (by linarith [ht j]) hPj
                  rcases (hd j).1.eq_or_lt with h | h
                  · have hz : phat smp j = 0 := by
                      by_contra hne
                      have := (hd j).2 (lt_of_le_of_ne hPj (Ne.symm hne))
                      linarith
                    rw [← h, hz]; simp
                  · have h2 := hsoc j
                    unfold soc3 at h2
                    rw [Set.mem_ofPred_eq, Real.sqrt_le_iff] at h2
                    obtain ⟨h3, h4⟩ := h2
                    simp only at h3 h4
                    have hu : 0 ≤ s + r - c j := by linarith [hc j]
                    have hy2 : y j ^ 2 ≤ 4 * s * (s + r - c j) := by linarith
                    obtain ⟨w, hw⟩ : ∃ w, w = phat smp j / p j := ⟨_, rfl⟩
                    have hw0 : 0 ≤ w := by rw [hw]; positivity
                    have hPw : phat smp j = p j * w := by rw [hw]; field_simp
                    have h5 : w * y j ≤ (s + r - c j) + s * w ^ 2 := by
                      refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
                      have : (w * y j) ^ 2 ≤ w ^ 2 * (4 * s * (s + r - c j)) := by
                        rw [mul_pow]; exact mul_le_mul_of_nonneg_left hy2 (sq_nonneg _)
                      linarith [sq_nonneg ((s + r - c j) - s * w ^ 2)]
                    have h6 := mul_le_mul_of_nonneg_left h5 h.le
                    have h7 := mul_le_mul_of_nonneg_left (hac j) h.le
                    have h8 : phat smp j ^ 2 / p j = p j * w ^ 2 := by rw [hPw]; field_simp
                    rw [h8]
                    rw [hPw] at h1 ⊢
                    linarith
                have h := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => key j
                rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum, hp1, hP1] at h
                linarith [mul_le_mul_of_nonneg_left hD hs]
              have chiStrong : ∀ (smp : Fin N → Fin n) (a : Fin n → ℝ) (q W : ℝ), 0 < q → (∑ j, phat smp j = 1) →
                  (∀ p : Fin n → ℝ, (∀ j, 0 ≤ p j ∧ (0 < phat smp j → 0 < p j)) → ∑ j, p j = 1 → ∑ j, phat smp j ^ 2 / p j ≤ 1 + q ^ 2 → ∑ j, p j * a j ≤ W) →
                  ∃ v ∈ chiDualValues q smp a, v ≤ W := by
                intro smp a q W hq hP1 hW
                have hz : ∀ p : Fin n → ℝ, (∀ j, 0 ≤ p j ∧ (0 < phat smp j → 0 < p j)) → ∀ j, p j = 0 → phat smp j = 0 := by
                  intro p hd j hj
                  by_contra hne
                  have := (hd j).2 (lt_of_le_of_ne (ph0 smp j) (Ne.symm hne))
                  linarith
                have hDP : ∑ j, phat smp j ^ 2 / phat smp j = 1 := by
                  rw [← hP1]
                  refine Finset.sum_congr rfl fun j _ => ?_
                  by_cases h : phat smp j = 0
                  · simp [h]
                  · field_simp
                obtain ⟨r, s, hs, hL⟩ := key (phat smp) a (fun p => ∑ j, phat smp j ^ 2 / p j) (1 + q ^ 2) W (ph0 smp) hP1 (by
                    simp only [hDP]; have := pow_pos hq 2; linarith) (by
                  intro p p' hp hp' α β hα hβ hαβ
                  simp only
                  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
                  refine Finset.sum_le_sum fun j _ => ?_
                  rcases (ph0 smp j).eq_or_lt with h | h
                  · rw [← h]; simp
                  · have h1 := (hp j).2 h
                    have h2 := (hp' j).2 h
                    have hmix : 0 < α * p j + β * p' j := by
                      rcases hα.eq_or_lt with h0 | h0
                      · have : β = 1 := by linarith
                        rw [← h0, this]; simpa using h2
                      · have := mul_pos h0 h1
                        have := mul_nonneg hβ h2.le
                        linarith
                    rw [div_le_iff₀ hmix]
                    have e : (α * (phat smp j ^ 2 / p j) + β * (phat smp j ^ 2 / p' j)) * (α * p j + β * p' j) - phat smp j ^ 2 * (α + β) ^ 2
                        = phat smp j ^ 2 * (α * β) * ((p j - p' j) ^ 2 / (p j * p' j)) := by
                      field_simp; ring
                    rw [hαβ] at e
                    have : 0 ≤ phat smp j ^ 2 * (α * β) * ((p j - p' j) ^ 2 / (p j * p' j)) := by positivity
                    linarith) (by
                  intro p hp
                  simp only
                  refine tendsto_finsetSum _ fun j _ => ?_
                  rcases (hp j).1.eq_or_lt with h | h
                  · rw [← h]; simp
                  · exact ContinuousAt.div (by fun_prop) (by fun_prop) (by simpa using h.ne')) hW
                have hr := ub (phat smp) a (fun p => ∑ j, phat smp j ^ 2 / p j) r s _ (ph0 smp) hs (by
                  intro p hp
                  refine Finset.sum_le_sum fun j _ => ?_
                  rcases (ph0 smp j).eq_or_lt with h | h
                  · rw [← h]; simp
                  · exact div_le_div_of_nonneg_left (by positivity) h (hp j)) hL
                have hbound : -(2 * ∑ j, phat smp j * Real.sqrt (s * (r - a j))) ≤ W - r - s * (1 + q ^ 2) := by
                  have hδ : ∀ δ : ℝ, 0 < δ → -(2 * ∑ j, phat smp j * (Real.sqrt (s + δ) * Real.sqrt (r - a j + δ))) ≤ W - r - s * (1 + q ^ 2) := by
                    intro δ hδ
                    have hA : 0 < Real.sqrt (s + δ) := Real.sqrt_pos.2 (by linarith)
                    have hC : ∀ j, 0 < Real.sqrt (r - a j + δ) := fun j => Real.sqrt_pos.2 (by linarith [hr j])
                    have hA2 : Real.sqrt (s + δ) ^ 2 = s + δ := Real.sq_sqrt (by linarith)
                    have hC2 : ∀ j, Real.sqrt (r - a j + δ) ^ 2 = r - a j + δ := fun j => Real.sq_sqrt (by linarith [hr j])
                    have h := hL (fun j => phat smp j * (Real.sqrt (s + δ) / Real.sqrt (r - a j + δ))) (fun j =>
                      ⟨mul_nonneg (ph0 smp j) (div_pos hA (hC j)).le, fun h => mul_pos h (div_pos hA (hC j))⟩)
                    refine le_trans ?_ h
                    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
                    refine Finset.sum_le_sum fun j _ => ?_
                    rcases (ph0 smp j).eq_or_lt with h' | h'
                    · rw [← h']; simp
                    · have hCj := hC j
                      have hCj2 := hC2 j
                      clear hL hW hC hC2 hz
                      generalize Real.sqrt (r - a j + δ) = C at hCj hCj2 ⊢
                      generalize Real.sqrt (s + δ) = A at hA hA2 ⊢
                      have e1 : phat smp j ^ 2 / (phat smp j * (A / C)) = phat smp j * (C / A) := by field_simp
                      rw [e1]
                      have h1 : (A / C) * (r - a j) ≤ A * C := by
                        rw [div_mul_eq_mul_div, div_le_iff₀ hCj]
                        have e3 : A * C * C = A * (r - a j + δ) := by rw [← hCj2]; ring
                        have := mul_pos hA hδ
                        rw [e3]; linarith
                      have h2 : s * (C / A) ≤ A * C := by
                        rw [mul_div_assoc', div_le_iff₀ hA]
                        have e3 : A * C * A = C * (s + δ) := by rw [← hA2]; ring
                        have := mul_pos hCj hδ
                        rw [e3]; linarith
                      linarith [mul_le_mul_of_nonneg_left h1 h'.le, mul_le_mul_of_nonneg_left h2 h'.le]
                  have hcont : Tendsto (fun δ : ℝ => -(2 * ∑ j, phat smp j * (Real.sqrt (s + δ) * Real.sqrt (r - a j + δ)))) (𝓝[>] 0) (𝓝 (-(2 * ∑ j, phat smp j * (Real.sqrt (s + 0) * Real.sqrt (r - a j + 0))))) := by
                    refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
                    refine Continuous.tendsto (f := fun δ : ℝ => -(2 * ∑ j, phat smp j * (Real.sqrt (s + δ) * Real.sqrt (r - a j + δ)))) ?_ 0
                    fun_prop
                  have := le_of_tendsto hcont (eventually_nhdsWithin_of_forall fun δ hd => hδ δ hd)
                  simpa [Real.sqrt_mul hs] using this
                refine ⟨_, ⟨r - s, s, fun j => 2 * Real.sqrt (s * (r - a j)) - 2 * s, fun j => 2 * Real.sqrt (s * (r - a j)), a, hs, fun j => by positivity, fun j => by linarith [hr j], fun j => by linarith, fun j => ?_, fun j => le_rfl, rfl⟩, ?_⟩
                · unfold soc3
                  rw [Set.mem_ofPred_eq, Real.sqrt_le_iff]
                  simp only
                  have hu : 0 ≤ r - a j := by linarith [hr j]
                  have := Real.sq_sqrt (mul_nonneg hs hu)
                  refine ⟨by linarith, ?_⟩
                  linarith
                · have e : ∑ j, phat smp j * (2 * Real.sqrt (s * (r - a j)) - 2 * s) = 2 * ∑ j, phat smp j * Real.sqrt (s * (r - a j)) - 2 * s := by
                    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hP1, Finset.mul_sum]
                    rw [one_mul]
                    congr 1
                    exact Finset.sum_congr rfl fun j _ => by ring
                  rw [e]; linarith
              have coneIneq : ∀ x y z : ℝ, (x, y, z) ∈ expCone → 0 ≤ z ∧ ∀ P p : ℝ, 0 < P → 0 < p → P * x ≤ p * z - P * y + y * (P * Real.log (P / p)) := by
                intro x y z h
                constructor
                · have hsub : expCone ⊆ {v : ℝ × ℝ × ℝ | 0 ≤ v.2.2} := by
                    refine closure_minimal ?_ (isClosed_le (by fun_prop) (by fun_prop))
                    rintro ⟨x, y, z⟩ ⟨h1, h2⟩
                    simp only at h1 h2
                    have : 0 < y * Real.exp (x / y) := by positivity
                    simp only [Set.mem_ofPred_eq]
                    linarith
                  exact hsub h
                · intro P p hP hp
                  have hsub : expCone ⊆ {v : ℝ × ℝ × ℝ | P * v.1 ≤ p * v.2.2 - P * v.2.1 + v.2.1 * (P * Real.log (P / p))} := by
                    refine closure_minimal ?_ (isClosed_le (by fun_prop) (by fun_prop))
                    rintro ⟨x, y, z⟩ ⟨h1, h2⟩
                    simp only at h1 h2
                    simp only [Set.mem_ofPred_eq]
                    have e : Real.exp (x / y + Real.log (p / P)) = Real.exp (x / y) * (p / P) := by
                      rw [Real.exp_add, Real.exp_log (by positivity)]
                    have h3 := Real.add_one_le_exp (x / y + Real.log (p / P))
                    rw [e] at h3
                    have h4 : Real.log (p / P) = - Real.log (P / p) := by
                      rw [← Real.log_inv, inv_div]
                    rw [h4] at h3
                    have h5 := mul_le_mul_of_nonneg_left h3 (mul_pos hP h1).le
                    have e1 : P * y * (x / y + -Real.log (P / p) + 1) = P * x - y * (P * Real.log (P / p)) + P * y := by
                      field_simp; ring
                    have e2 : P * y * (Real.exp (x / y) * (p / P)) = p * (y * Real.exp (x / y)) := by
                      field_simp
                    rw [e1, e2] at h5
                    have h6 := mul_le_mul_of_nonneg_left h2 hp.le
                    linarith
                  exact hsub h
              have gWeak : ∀ (smp : Fin N → Fin n) (a : Fin n → ℝ) (q : ℝ), (∑ j, phat smp j = 1) → ∀ p : Fin n → ℝ,
                  (∀ j, 0 ≤ p j ∧ (0 < phat smp j → 0 < p j)) → ∑ j, p j = 1 → ∑ j, phat smp j * Real.log (phat smp j / p j) ≤ q ^ 2 / 2 →
                  ∀ v ∈ gDualValues q smp a, ∑ j, p j * a j ≤ v := by
                intro smp a q hP1 p hd hp1 hD v hv
                obtain ⟨r, s, t, c, hs, hcone, hac, rfl⟩ := hv
                have key : ∀ j, phat smp j * t j ≤ p j * (s + r) - p j * a j + s * (phat smp j * Real.log (phat smp j / p j)) - s * phat smp j := by
                  intro j
                  obtain ⟨h1, h2⟩ := coneIneq _ _ _ (hcone j)
                  have h7 := mul_le_mul_of_nonneg_left (hac j) (hd j).1
                  rcases (ph0 smp j).eq_or_lt with h | h
                  · rw [← h]
                    have := mul_nonneg (hd j).1 h1
                    simp only [zero_mul, mul_zero]
                    linarith
                  · have := h2 _ _ h ((hd j).2 h)
                    linarith
                have h := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => key j
                rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum, hp1, hP1] at h
                linarith [mul_le_mul_of_nonneg_left hD hs]
              have gStrong : ∀ (smp : Fin N → Fin n) (a : Fin n → ℝ) (q W : ℝ), 0 < q → (∑ j, phat smp j = 1) →
                  (∀ p : Fin n → ℝ, (∀ j, 0 ≤ p j ∧ (0 < phat smp j → 0 < p j)) → ∑ j, p j = 1 → ∑ j, phat smp j * Real.log (phat smp j / p j) ≤ q ^ 2 / 2 → ∑ j, p j * a j ≤ W) →
                  (∀ ε : ℝ, 0 < ε → ∃ v ∈ gDualValues q smp a, v ≤ W + ε) ∧ ((∀ j, 0 < phat smp j) → ∃ v ∈ gDualValues q smp a, v ≤ W) := by
                intro smp a q W hq hP1 hW
                have hDP : ∑ j, phat smp j * Real.log (phat smp j / phat smp j) = 0 := by
                  refine Finset.sum_eq_zero fun j _ => ?_
                  by_cases h : phat smp j = 0
                  · simp [h]
                  · simp [div_self h]
                obtain ⟨r, s, hs, hL⟩ := key (phat smp) a (fun p => ∑ j, phat smp j * Real.log (phat smp j / p j)) (q ^ 2 / 2) W (ph0 smp) hP1 (by
                    simp only [hDP]; positivity) (by
                  intro p p' hp hp' α β hα hβ hαβ
                  simp only
                  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
                  refine Finset.sum_le_sum fun j _ => ?_
                  rcases (ph0 smp j).eq_or_lt with h | h
                  · rw [← h]; simp
                  · have h1 := (hp j).2 h
                    have h2 := (hp' j).2 h
                    have hmix : 0 < α * p j + β * p' j := by
                      rcases hα.eq_or_lt with h0 | h0
                      · have : β = 1 := by linarith
                        rw [← h0, this]; simpa using h2
                      · have := mul_pos h0 h1
                        have := mul_nonneg hβ h2.le
                        linarith
                    have hlog := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.2 h1) (Set.mem_Ioi.2 h2) hα hβ hαβ
                    simp only [smul_eq_mul] at hlog
                    rw [Real.log_div h.ne' hmix.ne', Real.log_div h.ne' h1.ne', Real.log_div h.ne' h2.ne']
                    have h3 := mul_le_mul_of_nonneg_left hlog h.le
                    have h4 : β = 1 - α := by linarith
                    rw [h4] at h3 ⊢
                    linarith) (by
                  intro p hp
                  refine tendsto_finsetSum _ fun j _ => ?_
                  rcases (ph0 smp j).eq_or_lt with h | h
                  · rw [← h]; simp
                  · have h1 := (hp j).2 h
                    refine ContinuousAt.mul (by fun_prop) (ContinuousAt.log (ContinuousAt.div (by fun_prop) (by fun_prop) (by simpa using h1.ne')) ?_)
                    simp [h.ne', h1.ne']) hW
                have hr := ub (phat smp) a (fun p => ∑ j, phat smp j * Real.log (phat smp j / p j)) r s _ (ph0 smp) hs (by
                  intro p hp
                  refine Finset.sum_le_sum fun j _ => ?_
                  rcases (ph0 smp j).eq_or_lt with h | h
                  · rw [← h]; simp
                  · have : 0 < p j := h.trans_le (hp j)
                    refine mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) ?_) h.le
                    exact div_le_div_of_nonneg_left h.le h (hp j)) hL
                have main : ∀ ε : ℝ, 0 ≤ ε → (s = 0 ∨ ∀ j, 0 < r + ε - a j) → ∃ v ∈ gDualValues q smp a, v ≤ W + ε := by
                  intro ε hε hcase
                  by_cases hs0 : s = 0
                  · subst hs0
                    refine ⟨_, ⟨r, 0, fun _ => 0, a, le_rfl, fun j => ?_, fun j => le_rfl, rfl⟩, ?_⟩
                    · have hu : 0 ≤ r - a j := by linarith [hr j]
                      have hlim : Tendsto (fun δ : ℝ => ((0 : ℝ), δ, r - a j + δ)) (𝓝[>] 0) (𝓝 ((0 : ℝ), 0, 0 + r - a j)) := by
                        refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
                        have : Continuous (fun δ : ℝ => ((0 : ℝ), δ, r - a j + δ)) := by fun_prop
                        simpa using this.tendsto 0
                      refine mem_closure_of_tendsto hlim (eventually_nhdsWithin_of_forall fun δ hδ => ?_)
                      refine ⟨hδ, ?_⟩
                      simp
                      exact hr j
                    · have hlim : Tendsto (fun δ : ℝ => δ * (∑ j, phat smp j * a j - r)) (𝓝[>] 0) (𝓝 (0 * (∑ j, phat smp j * a j - r))) := by
                        refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
                        exact (continuous_id.mul continuous_const).tendsto 0
                      have : 0 * (∑ j, phat smp j * a j - r) ≤ W - r := by
                        refine le_of_tendsto hlim (eventually_nhdsWithin_of_forall fun δ hδ => ?_)
                        have hδ' : 0 < δ := hδ
                        have h := hL (fun j => δ * phat smp j) (fun j => ⟨mul_nonneg hδ'.le (ph0 smp j), fun h => mul_pos hδ' h⟩)
                        simp only [mul_assoc, ← Finset.mul_sum, hP1] at h
                        linarith
                      simp
                      linarith
                  · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
                    have hu : ∀ j, 0 < r + ε - a j := by
                      rcases hcase with h | h
                      · exact absurd h hs0
                      · exact h
                    refine ⟨_, ⟨r + ε - s, s, fun j => s * Real.log ((r + ε - a j) / s), a, hs, fun j => ?_, fun j => le_rfl, rfl⟩, ?_⟩
                    · refine subset_closure ⟨hspos, ?_⟩
                      simp only
                      have huj := hu j
                      rw [mul_div_cancel_left₀ _ hs0, Real.exp_log (by positivity)]
                      have : s * ((r + ε - a j) / s) = r + ε - a j := by field_simp
                      rw [this]; linarith
                    · have h := hL (fun j => phat smp j * (s / (r + ε - a j))) (fun j => ⟨mul_nonneg (ph0 smp j) (div_pos hspos (hu j)).le, fun h => mul_pos h (div_pos hspos (hu j))⟩)
                      have e : ∀ j, -(phat smp j * (s * Real.log ((r + ε - a j) / s))) - s * phat smp j ≤ 
                        phat smp j * (s / (r + ε - a j)) * a j - r * (phat smp j * (s / (r + ε - a j))) - s * (phat smp j * Real.log (phat smp j / (phat smp j * (s / (r + ε - a j))))) := by
                        intro j
                        rcases (ph0 smp j).eq_or_lt with h | h
                        · rw [← h]; simp
                        · have huj := hu j
                          have e1 : phat smp j / (phat smp j * (s / (r + ε - a j))) = (r + ε - a j) / s := by field_simp
                          rw [e1]
                          have h1 : (s / (r + ε - a j)) * (r - a j) ≤ s := by
                            rw [div_mul_eq_mul_div, div_le_iff₀ huj]
                            exact mul_le_mul_of_nonneg_left (by linarith) hs
                          have h2 := mul_le_mul_of_nonneg_left h1 h.le
                          linarith
                      have h2 := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => e j
                      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hP1] at h2
                      linarith
                constructor
                · intro ε hε
                  exact main ε hε.le (Or.inr fun j => by linarith [hr j])
                · intro hPpos
                  have := main 0 le_rfl ?_
                  · simpa using this
                  by_contra hcon
                  push Not at hcon
                  obtain ⟨hs0, j, hj⟩ := hcon
                  have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
                  have haj : a j = r := by linarith [hr j]
                  obtain ⟨C, hC⟩ : ∃ C, C = W - r - s * (q ^ 2 / 2) - (∑ j, phat smp j * a j - r) := ⟨_, rfl⟩
                  obtain ⟨K, hK⟩ : ∃ K, K = (|C| + 1) / (s * phat smp j) := ⟨_, rfl⟩
                  have hsp : 0 < s * phat smp j := mul_pos hspos (hPpos j)
                  have hK0 : 0 ≤ K := by rw [hK]; positivity
                  have hK1 : s * phat smp j * K = |C| + 1 := by rw [hK, mul_comm]; exact div_mul_cancel₀ _ hsp.ne'
                  have hge : ∀ i, phat smp i ≤ phat smp i + (if i = j then phat smp j * (Real.exp K - 1) else 0) := by
                    intro i
                    have h1 := Real.add_one_le_exp K
                    have : 0 ≤ phat smp j * (Real.exp K - 1) := mul_nonneg (ph0 smp j) (by linarith)
                    split_ifs <;> linarith
                  have h := hL (fun i => phat smp i + (if i = j then phat smp j * (Real.exp K - 1) else 0)) (fun i => ⟨(ph0 smp i).trans (hge i), fun h => h.trans_le (hge i)⟩)
                  have e : ∀ i, phat smp i * Real.log (phat smp i / (phat smp i + (if i = j then phat smp j * (Real.exp K - 1) else 0))) = if i = j then - (phat smp j * K) else 0 := by
                    intro i
                    have hpi := hPpos i
                    split_ifs with hij
                    · subst hij
                      have : phat smp i / (phat smp i + phat smp i * (Real.exp K - 1)) = Real.exp (-K) := by
                        rw [Real.exp_neg]
                        have e2 : phat smp i + phat smp i * (Real.exp K - 1) = phat smp i * Real.exp K := by ring
                        rw [e2]; field_simp
                      rw [this, Real.log_exp]; ring
                    · rw [add_zero, div_self hpi.ne', Real.log_one, mul_zero]
                  simp only [e, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, haj, hP1] at h
                  have := le_abs_self C
                  linarith
              have asm : ∀ (𝒢 : Set (ProbabilityMeasure (Fin n))) (C : (Fin n → ℝ) → Prop) (a P : Fin n → ℝ) (D : Set ℝ),
                  (∀ F, F ∈ 𝒢 ↔ C (pvec F)) → (∀ j, 0 ≤ P j) → ∑ j, P j = 1 → C P → 
                  (∀ p : Fin n → ℝ, C p → ∑ j, p j = 1 → ∀ v ∈ D, ∑ j, p j * a j ≤ v) →
                  ∃ W : ℝ, discWorstCase 𝒢 a = (W : EReal) ∧ (∀ v ∈ D, W ≤ v) ∧
                    (∀ p : Fin n → ℝ, (∀ j, 0 ≤ p j) → ∑ j, p j = 1 → C p → ∑ j, p j * a j ≤ W) := by
                intro 𝒢 C a P D hG hP0 hP1 hCP hweak
                have hmem : ∀ p : Fin n → ℝ, (∀ j, 0 ≤ p j) → ∑ j, p j = 1 → C p → ((∑ j, p j * a j : ℝ) : EReal) ≤ discWorstCase 𝒢 a := by
                  intro p h0 h1 hC
                  obtain ⟨F, hF⟩ := pvex p h0 h1
                  have hFe : pvec F = p := funext hF
                  have hFG : F ∈ 𝒢 := by rw [hG, hFe]; exact hC
                  unfold discWorstCase
                  have := le_iSup₂ (f := fun F₀ (_ : F₀ ∈ 𝒢) => ((∑ j, pvec F₀ j * a j : ℝ) : EReal)) F hFG
                  rw [hFe] at this
                  exact this
                have hle : ∀ x : ℝ, (∀ F ∈ 𝒢, ∑ j, pvec F j * a j ≤ x) → discWorstCase 𝒢 a ≤ (x : EReal) := by
                  intro x hx
                  unfold discWorstCase
                  exact iSup₂_le fun F hF => EReal.coe_le_coe_iff.2 (hx F hF)
                have hb : discWorstCase 𝒢 a ≤ ((∑ j, |a j| : ℝ) : EReal) := by
                  refine hle _ fun F hF => Finset.sum_le_sum fun j _ => ?_
                  have h1 : pvec F j ≤ 1 := by
                    rw [← pv1 F]; exact Finset.single_le_sum (fun i _ => pv0 F i) (Finset.mem_univ j)
                  have h2 := le_abs_self (a j)
                  have h3 := pv0 F j
                  have h4 := abs_nonneg (a j)
                  nlinarith
                have hnt : discWorstCase 𝒢 a ≠ ⊤ := (hb.trans_lt (EReal.coe_lt_top _)).ne
                have hnb : discWorstCase 𝒢 a ≠ ⊥ := ((EReal.bot_lt_coe _).trans_le (hmem P hP0 hP1 hCP)).ne'
                refine ⟨(discWorstCase 𝒢 a).toReal, (EReal.coe_toReal hnt hnb).symm, ?_, ?_⟩
                · intro v hv
                  rw [← EReal.coe_le_coe_iff, EReal.coe_toReal hnt hnb]
                  exact hle v fun F hF => hweak _ ((hG F).1 hF) (pv1 F) v hv
                · intro p h0 h1 hC
                  rw [← EReal.coe_le_coe_iff, EReal.coe_toReal hnt hnb]
                  exact hmem p h0 h1 hC
              intro hN hq
              have hP1 := ph1 hN smp
              constructor
              · intro _
                obtain ⟨W, hW, hlow, hup⟩ := asm (chiRegion ((N : ℝ) * q ^ 2) N smp) (fun p => (∀ j, 0 ≤ p j ∧ (0 < phat smp j → 0 < p j)) ∧
                  ∑ j, phat smp j ^ 2 / p j ≤ 1 + q ^ 2) (fun j => c x (ξhat j)) (phat smp) (chiDualValues q smp (fun j => c x (ξhat j)))
                  (fun F => chiR hN smp q hq F hP1) (ph0 smp) hP1 ⟨fun j => ⟨ph0 smp j, id⟩, by
                    have : ∑ j, phat smp j ^ 2 / phat smp j = 1 := by
                      rw [← hP1]
                      refine Finset.sum_congr rfl fun j _ => ?_
                      by_cases h : phat smp j = 0
                      · simp [h]
                      · field_simp
                    rw [this]; have := pow_pos hq 2; linarith⟩ (fun p hp h1 v hv => chiWeak smp _ q hP1 p hp.1 h1 hp.2 v hv)
                obtain ⟨v, hv, hvW⟩ := chiStrong smp (fun j => c x (ξhat j)) q W hq hP1 (fun p hd h1 hD => hup p (fun j => (hd j).1) h1 ⟨hd, hD⟩)
                have hvW' : v = W := le_antisymm hvW (hlow v hv)
                rw [hW]
                refine ⟨le_antisymm (le_sInf ?_) (sInf_le ⟨v, hv, by rw [hvW']⟩), fun _ => ⟨v, hv, by rw [hvW']⟩⟩
                rintro _ ⟨w, hw, rfl⟩
                exact EReal.coe_le_coe_iff.2 (hlow w hw)
              · intro _
                obtain ⟨W, hW, hlow, hup⟩ := asm (gRegion ((N : ℝ) * q ^ 2) N smp) (fun p => (∀ j, 0 ≤ p j ∧ (0 < phat smp j → 0 < p j)) ∧
                  ∑ j, phat smp j * Real.log (phat smp j / p j) ≤ q ^ 2 / 2) (fun j => c x (ξhat j)) (phat smp) (gDualValues q smp (fun j => c x (ξhat j)))
                  (fun F => gR hN smp q hq F hP1) (ph0 smp) hP1 ⟨fun j => ⟨ph0 smp j, id⟩, by
                    have : ∑ j, phat smp j * Real.log (phat smp j / phat smp j) = 0 := by
                      refine Finset.sum_eq_zero fun j _ => ?_
                      by_cases h : phat smp j = 0
                      · simp [h]
                      · simp [div_self h]
                    rw [this]; positivity⟩ (fun p hp h1 v hv => gWeak smp _ q hP1 p hp.1 h1 hp.2 v hv)
                obtain ⟨hs1, hs2⟩ := gStrong smp (fun j => c x (ξhat j)) q W hq hP1 (fun p hd h1 hD => hup p (fun j => (hd j).1) h1 ⟨hd, hD⟩)
                rw [hW]
                have hinf : (W : EReal) = sInf ((fun v : ℝ => (v : EReal)) '' gDualValues q smp (fun j => c x (ξhat j))) := by
                  refine le_antisymm (le_sInf ?_) ?_
                  · rintro _ ⟨w, hw, rfl⟩
                    exact EReal.coe_le_coe_iff.2 (hlow w hw)
                  · by_contra hcon
                    rw [not_le] at hcon
                    obtain ⟨y, hy1, hy2⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
                    have hy1' := EReal.coe_lt_coe_iff.1 hy1
                    obtain ⟨v, hv, hvy⟩ := hs1 (y - W) (by linarith)
                    have h1 : sInf ((fun v : ℝ => (v : EReal)) '' gDualValues q smp (fun j => c x (ξhat j))) ≤ (v : EReal) := sInf_le ⟨v, hv, rfl⟩
                    have h2 : (v : EReal) ≤ (y : EReal) := EReal.coe_le_coe_iff.2 (by linarith)
                    exact absurd hy2 (not_lt.2 (h1.trans h2))
                refine ⟨hinf, fun hPpos => ⟨hinf, fun _ => ?_⟩⟩
                obtain ⟨v, hv, hvW⟩ := hs2 hPpos
                exact ⟨v, hv, by rw [le_antisymm hvW (hlow v hv)]⟩
