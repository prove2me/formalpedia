-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P03.minEntropy_splitting
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T20:47:34.820729+00:00
-- url     : https://prove2.me/submissions/e144c954-02ec-41a6-9c1d-da7c45be4d0e

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P03
noncomputable section

open QAlgorithms.Papers.Independent.Gap20.P03

open MeasureTheory Filter

open scoped ENNReal ComplexConjugate ComplexOrder Topology

-- Exact accepted finite Shannon entropy in bits (zero log zero is zero).

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

attribute [local instance] Classical.propDecidable


theorem g73a_tsum_bool (f : Bool → ℝ≥0∞) : ∑' b, f b = f false + f true := by
  rw [tsum_fintype, Fintype.sum_bool, add_comm]

theorem g73a_unitMass {W : Type*} (p : PMF W) : massAt (fun w => p w) (fun _ => ()) () = 1 := by
  simp [massAt, PMF.tsum_coe]

/-- Lemma 4.2, p.9 and Appendix A.3 p.19. The extension p' preserves the
original (X0,X1) law, allowing random choices on an enlarged probability space. -/
theorem solution {A0 A1 : Type*} (p : PMF (A0 × A1))
    (alpha epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hentropy : (alpha:EReal) ≤ smoothJoint (fun w => p w) id epsilon) :
    ∃ pe : PMF ((A0 × A1) × Bool),
      (∀ x, massAt (fun w => pe w) Prod.fst x = p x) ∧
      ((alpha/2:ℝ):EReal) ≤ smoothJoint (fun w => pe w)
        (fun w => (selected w.1.1 w.1.2 w.2,w.2)) epsilon := by
  classical
  set H : ℝ≥0∞ := ENNReal.ofReal (Real.rpow 2 (-(alpha/2))) with hH
  let P1 : A1 → ℝ≥0∞ := fun x1 => ∑' x0, p (x0, x1)
  let C : A0 × A1 → Bool := fun w => decide (H < P1 w.2)
  let pe : PMF ((A0 × A1) × Bool) := p.map (fun w => (w, C w))
  have hpe : ∀ w c, pe (w, c) = if c = C w then p w else 0 := by
    intro w c
    simp only [pe, PMF.map_apply]
    rw [tsum_eq_single w]
    · simp [Prod.ext_iff]
    · intro w' hw'
      rw [if_neg]; intro h; exact hw' (congrArg Prod.fst h).symm
  refine ⟨pe, ?_, ?_⟩
  · intro x
    have : massAt (fun w => pe w) Prod.fst x = (pe.map Prod.fst) x := by
      simp only [massAt, PMF.map_apply]; congr 1; funext v; simp [eq_comm]
    rw [this]
    simp only [pe, PMF.map_comp]
    have : (Prod.fst ∘ fun w => (w, C w)) = id := rfl
    rw [this, PMF.map_id]
  · apply le_of_forall_lt_imp_le_of_dense
    intro b hb
    induction b using EReal.rec with
    | bot => exact bot_le
    | top => exact absurd hb not_top_lt
    | coe b0 =>
      have hb0 : b0 < alpha/2 := by exact_mod_cast hb
      have hlt : ((b0 + alpha/2 : ℝ) : EReal) < smoothJoint (fun w => p w) id epsilon :=
        lt_of_lt_of_le (by exact_mod_cast (by linarith : b0 + alpha/2 < alpha)) hentropy
      unfold smoothJoint smoothMin at hlt
      obtain ⟨t, ⟨r, rfl, q, hqp, hqsum, hqbd⟩, htr⟩ := lt_sSup_iff.mp hlt
      have hr : b0 + alpha/2 < r := by exact_mod_cast htr
      have hq_pt : ∀ w, q w ≤ ENNReal.ofReal (Real.rpow 2 (-r)) := by
        intro w
        have := hqbd w ()
        unfold retainedConditional at this
        rw [g73a_unitMass p, if_neg one_ne_zero, div_one] at this
        have e : massAt q (fun w => (id w, ())) (w, ()) = q w := by
          unfold massAt
          rw [tsum_eq_single w]
          · simp
          · intro w' hw'; rw [if_neg]; intro h; exact hw' (congrArg Prod.fst h)
        rwa [e] at this
      unfold smoothJoint smoothMin
      apply le_sSup
      refine ⟨b0, rfl, ?_⟩
      let q' : (A0 × A1) × Bool → ℝ≥0∞ := fun v => if v.2 = C v.1 then q v.1 else 0
      refine ⟨q', ?_, ?_, ?_⟩
      · rintro ⟨w, c⟩
        show q' (w,c) ≤ pe (w,c)
        rw [hpe]; simp only [q']; split_ifs
        · exact hqp w
        · exact le_rfl
      · have : ∑' v, q' v = ∑' w, q w := by
          rw [ENNReal.tsum_prod']; congr 1; funext w
          rw [g73a_tsum_bool]; cases h : C w <;> simp [q', h]
        rw [this]; exact hqsum
      · rintro ⟨s, c⟩ u
        unfold retainedConditional
        rw [g73a_unitMass pe, if_neg one_ne_zero, div_one]
        unfold massAt
        rw [ENNReal.tsum_prod', ENNReal.tsum_prod']
        simp_rw [g73a_tsum_bool]
        have hHle : H ≤ ENNReal.ofReal (2 ^ (-b0)) := by
          rw [hH]; apply ENNReal.ofReal_le_ofReal
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        have hHpos : 0 < (2:ℝ) ^ (-(alpha/2)) := Real.rpow_pos_of_pos (by norm_num) _
        cases c <;> cases s <;> simp [q', selected]
        case false.inr a1 =>
          by_cases hh : H < P1 a1
          · simp [C, hh]
          · calc (∑' (a : A0), if C (a, a1) = false then q (a, a1) else 0)
                ≤ ∑' a, p (a, a1) := by
                  apply ENNReal.tsum_le_tsum; intro a; split_ifs
                  · exact hqp _
                  · exact zero_le
              _ = P1 a1 := rfl
              _ ≤ H := not_lt.mp hh
              _ ≤ _ := hHle
        case true.inl a0 =>
          rw [tsum_eq_single a0]
          · simp only [if_true]
            set K : ℝ≥0∞ := ENNReal.ofReal (Real.rpow 2 (-r)) with hK
            have hH0 : H ≠ 0 := by rw [hH]; exact (ENNReal.ofReal_pos.mpr hHpos).ne'
            have hHt : H ≠ ⊤ := by rw [hH]; exact ENNReal.ofReal_ne_top
            have hsum1 : ∑' b, P1 b = 1 := by
              simp only [P1]
              rw [ENNReal.tsum_comm, ← ENNReal.tsum_prod']
              exact PMF.tsum_coe p
            calc (∑' (b : A1), if C (a0, b) = true then q (a0, b) else 0)
                ≤ ∑' b, K * H⁻¹ * P1 b := by
                  apply ENNReal.tsum_le_tsum; intro b
                  by_cases hh : H < P1 b
                  · have hc : C (a0, b) = true := by simp [C, hh]
                    rw [if_pos hc]
                    calc q (a0, b) ≤ K := hq_pt _
                      _ = K * H⁻¹ * H := by
                          rw [mul_assoc, ENNReal.inv_mul_cancel hH0 hHt, mul_one]
                      _ ≤ K * H⁻¹ * P1 b := by gcongr
                  · have hc : C (a0, b) = false := by simp [C, hh]
                    rw [if_neg (by simp [hc])]; exact zero_le
              _ = K * H⁻¹ := by rw [ENNReal.tsum_mul_left, hsum1, mul_one]
              _ ≤ _ := by
                  rw [hK, hH]
                  show ENNReal.ofReal ((2:ℝ) ^ (-r)) * (ENNReal.ofReal ((2:ℝ) ^ (-(alpha / 2))))⁻¹ ≤ _
                  rw [← ENNReal.ofReal_inv_of_pos hHpos,
                    ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
                  apply ENNReal.ofReal_le_ofReal
                  show (2:ℝ) ^ (-r) * ((2:ℝ) ^ (-(alpha/2)))⁻¹ ≤ 2 ^ (-b0)
                  rw [← Real.rpow_neg (by norm_num), ← Real.rpow_add (by norm_num)]
                  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          · intro a ha; simp [ha]


end
