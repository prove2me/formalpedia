-- Prove2me | solution 1 for OpaquePricing.Dominance.Supplement.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:22:15.628626+00:00
-- url     : https://prove2.me/submissions/b89f5455-760d-4f48-84eb-fbd3674e6600

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting
import Definitions.Def_OpaquePricing_Dominance_Supplement_SinglePricing
import Definitions.Def_OpaquePricing_Dominance_Supplement_OneOpaque

open MeasureTheory

open OpaquePricing
open OpaquePricing.Dominance
open OpaquePricing.Dominance.Supplement

theorem solution {N : ℕ} (hN : 2 ≤ N) (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ v ∂μ, ∀ i, 0 ≤ v i) (α : ℝ) (hα : α ∈ Set.Icc 0 1) :
    optOne μ α ≤ ENNReal.ofReal (2 - (1 - α) / (N : ℝ)) * optSP μ ∧
    (∀ ε : ℝ, 0 < ε → ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      (∀ᵐ x ∂ν, 0 ≤ x) ∧
      0 < optSP (Measure.pi (fun _ : Fin N => ν)) ∧
      optSP (Measure.pi (fun _ : Fin N => ν)) < ⊤ ∧
      ENNReal.ofReal (2 - ε) * optSP (Measure.pi (fun _ : Fin N => ν)) <
        optOne (Measure.pi (fun _ : Fin N => ν)) 1) ∧
    (∀ ε : ℝ, 0 < ε → ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      (∀ᵐ x ∂ν, 0 ≤ x) ∧
      0 < optSP (Measure.pi (fun _ : Fin N => ν)) ∧
      optSP (Measure.pi (fun _ : Fin N => ν)) < ⊤ ∧
      ENNReal.ofReal (2 - 1 / (N : ℝ) - ε) * optSP (Measure.pi (fun _ : Fin N => ν)) <
        optOne (Measure.pi (fun _ : Fin N => ν)) 0) := by
          classical
          have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
          have hNpos : (0 : ℝ) < N := by linarith
          have : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.mpr hN
          have hNe : N ≠ 1 := by omega
          -- menuRevenue facts
          have hlow : ∀ (s : Finset (Finset (Fin N))) (u price : Finset (Fin N) → ℝ) (o : Finset (Fin N)),
              o ∈ s → 0 ≤ u o → (∀ o' ∈ s, u o' ≤ u o) → price o ≤ menuRevenue s u price := by
            intro s u price o ho h0 hmax
            unfold menuRevenue
            dsimp only
            split
            next hne =>
              exact Finset.le_sup'_of_le price (by simp only [Finset.mem_filter]; exact ⟨ho, h0, hmax⟩) le_rfl
            next hne =>
              exact absurd ⟨o, by simp only [Finset.mem_filter]; exact ⟨ho, h0, hmax⟩⟩ hne
          have hup : ∀ (s : Finset (Finset (Fin N))) (u price : Finset (Fin N) → ℝ) (B : ℝ), 0 ≤ B →
              (∀ o ∈ s, 0 ≤ u o → (∀ o' ∈ s, u o' ≤ u o) → price o ≤ B) → menuRevenue s u price ≤ B := by
            intro s u price B hB h
            unfold menuRevenue
            dsimp only
            split
            · apply Finset.sup'_le
              intro o ho
              simp only [Finset.mem_filter] at ho
              exact h o ho.1 ho.2.1 ho.2.2
            · exact hB
          have hmem : ∀ S : Finset (Fin N), S ∈ oneOptions N ↔ (∃ j, S = {j}) ∨ S = Finset.univ := by
            intro S
            unfold oneOptions opqOptions
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.card_eq_one]
            constructor
            · rintro ⟨_, h⟩; exact h
            · rintro h
              refine ⟨?_, h⟩
              rcases h with ⟨j, rfl⟩ | rfl
              · exact Finset.singleton_nonempty j
              · exact Finset.univ_nonempty
          have hsing : ∀ j : Fin N, ({j} : Finset (Fin N)) ∈ oneOptions N := fun j => (hmem _).2 (Or.inl ⟨j, rfl⟩)
          have huniv : (Finset.univ : Finset (Fin N)) ∈ oneOptions N := (hmem _).2 (Or.inr rfl)
          have hp1 : ∀ (p r : ℝ) (j : Fin N), opqPrice p (fun _ => r) ({j} : Finset (Fin N)) = p := by
            intro p r j; simp [opqPrice]
          have hpU : ∀ (p r : ℝ), opqPrice p (fun _ => r) (Finset.univ : Finset (Fin N)) = r := by
            intro p r; simp [opqPrice, Finset.card_univ, hNe]
          have hpe1 : ∀ (v : Fin N → ℝ) (j : Fin N), pessValue v {j} = v j := by
            intro v j; simp [pessValue]
          have hrn1 : ∀ (v : Fin N → ℝ) (j : Fin N), rnValue v {j} = v j := by
            intro v j; simp [rnValue]
          have hrnU : ∀ (v : Fin N → ℝ), rnValue v Finset.univ = (∑ i, v i) / N := by
            intro v; simp [rnValue]
          have hpeU : ∀ (v : Fin N → ℝ) (k : Fin N), pessValue v Finset.univ ≤ v k := by
            intro v k
            simp only [pessValue, dif_pos Finset.univ_nonempty]
            exact Finset.inf'_le _ (Finset.mem_univ k)
          have hAmeas : ∀ x : ℝ, MeasurableSet {v : Fin N → ℝ | ∃ i, x ≤ v i} := by
            intro x
            have : {v : Fin N → ℝ | ∃ i, x ≤ v i} = ⋃ i, {v | x ≤ v i} := by ext; simp
            rw [this]
            exact MeasurableSet.iUnion fun i => measurableSet_le measurable_const (measurable_pi_apply i)
          have hR : ∀ (ρ : Measure (Fin N → ℝ)) (x : ℝ), 0 ≤ x →
              ENNReal.ofReal x * ρ {v | ∃ i, x ≤ v i} ≤ optSP ρ := by
            intro ρ x hx
            exact le_iSup₂ (f := fun p (_ : 0 ≤ p) => expSP ρ p) x hx
          have bound : ∀ (val : (Fin N → ℝ) → Finset (Fin N) → ℝ) (κ p r t : ℝ), 0 ≤ p → 0 ≤ r → 0 ≤ κ →
              p ≤ t → p - min p r ≤ κ * t →
              (∀ v j, val v {j} = v j) → (∀ v, ∃ k, val v Finset.univ ≤ v k) →
              (∀ v : Fin N → ℝ, (∀ i, 0 ≤ v i) → ∀ i, (∀ j, v j ≤ v i) → val v Finset.univ - r ≤ v i - p →
                0 ≤ v i - p → r < p → t ≤ v i) →
              ∫⁻ v, ENNReal.ofReal (oneRevenue val p r v) ∂μ ≤ optSP μ + ENNReal.ofReal κ * optSP μ := by
            intro val κ p r t hp hr hκ hpt hpm H0 H1 H2
            set m := min p r with hm
            have hm0 : 0 ≤ m := le_min hp hr
            have hmp : m ≤ p := min_le_left _ _
            have hpw : ∀ v : Fin N → ℝ, (∀ i, 0 ≤ v i) → ENNReal.ofReal (oneRevenue val p r v) ≤
                {v : Fin N → ℝ | ∃ i, m ≤ v i}.indicator (fun _ => ENNReal.ofReal m) v +
                {v : Fin N → ℝ | ∃ i, t ≤ v i}.indicator (fun _ => ENNReal.ofReal (p - m)) v := by
              intro v hv
              have key : oneRevenue val p r v ≤ (if ∃ i, m ≤ v i then m else 0) +
                  (if ∃ i, t ≤ v i then p - m else 0) := by
                unfold oneRevenue
                apply hup
                · split_ifs <;> linarith
                · intro o ho h0 hmax
                  rcases (hmem o).1 ho with ⟨i, rfl⟩ | rfl
                  · rw [hp1]
                    rw [hp1, H0] at h0
                    have hvi : ∀ j, v j ≤ v i := by
                      intro j; have := hmax {j} (hsing j); rw [hp1, hp1, H0, H0] at this; linarith
                    have hU : val v Finset.univ - r ≤ v i - p := by
                      have := hmax _ huniv; rw [hpU, hp1, H0] at this; exact this
                    rw [if_pos ⟨i, by linarith⟩]
                    by_cases hrp : r < p
                    · rw [if_pos ⟨i, H2 v hv i hvi hU h0 hrp⟩]; linarith
                    · have : m = p := min_eq_left (not_lt.mp hrp)
                      split_ifs <;> linarith
                  · rw [hpU]
                    rw [hpU] at h0
                    obtain ⟨k, hk⟩ := H1 v
                    by_cases hrp : r ≤ p
                    · have : m = r := min_eq_right hrp
                      rw [if_pos ⟨k, by linarith⟩]
                      split_ifs <;> linarith
                    · exfalso
                      have := hmax {k} (hsing k); rw [hpU, hp1, H0] at this; linarith [not_le.mp hrp]
              calc ENNReal.ofReal (oneRevenue val p r v) ≤ ENNReal.ofReal ((if ∃ i, m ≤ v i then m else 0) +
                    (if ∃ i, t ≤ v i then p - m else 0)) := ENNReal.ofReal_le_ofReal key
                _ = _ := by
                  rw [ENNReal.ofReal_add (by split_ifs <;> linarith) (by split_ifs <;> linarith)]
                  simp only [Set.indicator_apply, Set.mem_setOf_eq]
                  split_ifs <;> simp
            calc ∫⁻ v, ENNReal.ofReal (oneRevenue val p r v) ∂μ ≤ ∫⁻ v, ({v : Fin N → ℝ | ∃ i, m ≤ v i}.indicator
                  (fun _ => ENNReal.ofReal m) v + {v : Fin N → ℝ | ∃ i, t ≤ v i}.indicator
                  (fun _ => ENNReal.ofReal (p - m)) v) ∂μ := lintegral_mono_ae (hμ.mono fun v hv => hpw v hv)
              _ = ENNReal.ofReal m * μ {v | ∃ i, m ≤ v i} + ENNReal.ofReal (p - m) * μ {v | ∃ i, t ≤ v i} := by
                  rw [lintegral_add_left ((measurable_const.indicator (hAmeas m))),
                    lintegral_indicator_const (hAmeas m), lintegral_indicator_const (hAmeas t)]
              _ ≤ optSP μ + ENNReal.ofReal κ * optSP μ := by
                  refine add_le_add (hR μ m hm0) ?_
                  calc ENNReal.ofReal (p - m) * μ {v | ∃ i, t ≤ v i} ≤
                          ENNReal.ofReal κ * (ENNReal.ofReal t * μ {v | ∃ i, t ≤ v i}) := by
                          rw [← mul_assoc, ← ENNReal.ofReal_mul hκ]; gcongr
                    _ ≤ _ := by gcongr; exact hR μ t (by linarith)
          have hκpos : 0 < 1 - 1 / (N : ℝ) := by
            have : 1 / (N : ℝ) < 1 := by rw [div_lt_one hNpos]; exact hN1
            linarith
          have i0 : Fin N := ⟨0, by omega⟩
          have key : ∀ q : ℝ, 0 < q → (N : ℝ) * q < 1 → ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
              (∀ᵐ x ∂ν, 0 ≤ x) ∧
              0 < optSP (Measure.pi fun _ : Fin N => ν) ∧ optSP (Measure.pi fun _ : Fin N => ν) ≤ 1 ∧
              ENNReal.ofReal (1 + (1 / (N * q) - 1) * (N * q * (1 - q) ^ (N - 1))) ≤
                optOne (Measure.pi fun _ : Fin N => ν) 1 ∧
              ENNReal.ofReal (1 + (1 - 1 / N) * ((1 / (N * q) - 1) * (N * q * (1 - q) ^ (N - 1)))) ≤
                optOne (Measure.pi fun _ : Fin N => ν) 0 := by
            intro q hq hNq
            obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 1 / (N * q) := ⟨_, rfl⟩
            have hM1 : 1 < M := by rw [hM, lt_div_iff₀ (by positivity)]; linarith
            have hMq : M * q = 1 / N := by rw [hM]; field_simp
            have hq1 : q < 1 := by nlinarith
            obtain ⟨w, hw⟩ : ∃ w : ℝ, w = 1 - q := ⟨_, rfl⟩
            rw [← hw]
            have hw0 : 0 < w := by linarith
            obtain ⟨ν, hν⟩ : ∃ ν : Measure ℝ,
                ν = ENNReal.ofReal w • Measure.dirac 1 + ENNReal.ofReal q • Measure.dirac M := ⟨_, rfl⟩
            have hνapp : ∀ s : Set ℝ, ν s = ENNReal.ofReal w * s.indicator 1 1 +
                ENNReal.ofReal q * s.indicator 1 M := by
              intro s; rw [hν]; simp [Measure.dirac_apply]
            have hprob : IsProbabilityMeasure ν := ⟨by
              rw [hνapp]; simp; rw [← ENNReal.ofReal_add hw0.le hq.le, hw]; simp⟩
            have hae : ∀ᵐ x ∂ν, x = 1 ∨ x = M := by
              rw [ae_iff, hνapp]; simp [Set.indicator_apply, hM1.ne']
            have hν1 : ν {1} = ENNReal.ofReal w := by
              rw [hνapp]; simp [Set.indicator_apply, hM1.ne']
            have hνM : ν {M} = ENNReal.ofReal q := by
              rw [hνapp]; simp [Set.indicator_apply, hM1.ne]
            refine ⟨ν, hprob, hae.mono fun x hx => by rcases hx with rfl | rfl <;> linarith, ?_⟩
            obtain ⟨μ', hμ'⟩ : ∃ μ' : Measure (Fin N → ℝ), μ' = Measure.pi fun _ : Fin N => ν := ⟨_, rfl⟩
            rw [← hμ']
            have hprob' : IsProbabilityMeasure μ' := by rw [hμ']; infer_instance
            have haeμ : ∀ᵐ v ∂μ', ∀ i, v i = 1 ∨ v i = M := by
              rw [hμ', ae_all_iff]; intro i; exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin N => ν) (i := i)).eventually hae
            have hmarg : ∀ (i : Fin N) (x : ℝ), μ' {v | x ≤ v i} = ν (Set.Ici x) := by
              intro i x; rw [hμ']
              exact (measurePreserving_eval (fun _ => ν) i).measure_preimage measurableSet_Ici.nullMeasurableSet
            obtain ⟨A, hA⟩ : ∃ A : Fin N → Set (Fin N → ℝ),
                A = fun i => Set.pi Set.univ (fun j => if j = i then {M} else {1}) := ⟨_, rfl⟩
            have hAmem : ∀ i v, v ∈ A i ↔ ∀ j, v j = if j = i then M else 1 := by
              intro i v; rw [hA]; simp only [Set.mem_univ_pi]; apply forall_congr'; intro j
              split_ifs <;> simp
            have hAm : ∀ i, MeasurableSet (A i) := by
              intro i; rw [hA]
              exact MeasurableSet.univ_pi fun j => by split_ifs <;> exact measurableSet_singleton _
            have hAμ : ∀ i, μ' (A i) = ENNReal.ofReal q * ENNReal.ofReal w ^ (N - 1) := by
              intro i; rw [hA, hμ', Measure.pi_pi]
              rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
              simp only [if_pos rfl, hνM]
              congr 1
              rw [Finset.prod_congr rfl (g := fun _ => ENNReal.ofReal w)]
              · simp [Finset.card_erase_of_mem]
              · intro j hj
                rw [if_neg (Finset.ne_of_mem_erase hj), hν1]
            -- upper bound on optSP
            have hsp : optSP μ' ≤ 1 := by
              apply iSup₂_le; intro x hx
              unfold expSP
              by_cases hx1 : x ≤ 1
              · calc ENNReal.ofReal x * μ' {v | ∃ i, x ≤ v i} ≤ 1 * 1 :=
                      mul_le_mul' (ENNReal.ofReal_le_one.2 hx1) prob_le_one
                  _ = 1 := one_mul 1
              · push Not at hx1
                have hsplit : {v : Fin N → ℝ | ∃ i, x ≤ v i} = ⋃ i, {v | x ≤ v i} := by ext; simp
                have hIci : ENNReal.ofReal x * ν (Set.Ici x) ≤ ENNReal.ofReal (1 / N) := by
                  rw [hνapp]; simp only [Set.indicator_apply, Set.mem_Ici, Pi.one_apply]
                  rw [if_neg (by linarith)]
                  split_ifs with hxM
                  · simp only [mul_zero, zero_add, mul_one]
                    rw [← ENNReal.ofReal_mul hx]
                    exact ENNReal.ofReal_le_ofReal (by rw [← hMq]; nlinarith)
                  · simp
                calc ENNReal.ofReal x * μ' {v | ∃ i, x ≤ v i} ≤ ENNReal.ofReal x * ∑ i, μ' {v | x ≤ v i} := by
                      rw [hsplit]; gcongr; exact measure_iUnion_fintype_le _ _
                  _ = ∑ i : Fin N, ENNReal.ofReal x * ν (Set.Ici x) := by
                      rw [Finset.mul_sum]; simp only [hmarg]
                  _ ≤ ∑ i : Fin N, ENNReal.ofReal (1 / N) := Finset.sum_le_sum fun i _ => hIci
                  _ = 1 := by
                      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
                        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
                        mul_one_div_cancel hNpos.ne', ENNReal.ofReal_one]
            have hpos : 0 < optSP μ' := by
              have h1 := hR μ' 1 zero_le_one
              rw [ENNReal.ofReal_one, one_mul] at h1
              have h2 : μ' (A i0) ≤ μ' {v | ∃ i, 1 ≤ v i} := measure_mono fun v hv =>
                ⟨i0, by rw [(hAmem i0 v).1 hv i0, if_pos rfl]; exact hM1.le⟩
              have h3 : 0 < μ' (A i0) := by
                rw [hAμ]
                exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 hq).ne'
                  (pow_ne_zero _ (ENNReal.ofReal_pos.2 hw0).ne')
              exact lt_of_lt_of_le h3 (h2.trans h1)
            refine ⟨hpos, hsp, ?_⟩
            -- lower bound machinery
            have lowint : ∀ (f : (Fin N → ℝ) → ℝ) (c : ℝ), 0 ≤ c →
                (∀ v : Fin N → ℝ, (∀ i, v i = 1 ∨ v i = M) → 1 ≤ f v ∧ ∀ i, v ∈ A i → 1 + c ≤ f v) →
                ENNReal.ofReal (1 + c * (N * q * w ^ (N - 1))) ≤ ∫⁻ v, ENNReal.ofReal (f v) ∂μ' := by
              intro f c hc hf
              have hsum : ∫⁻ v, (1 + ∑ i, (A i).indicator (fun _ => ENNReal.ofReal c) v) ∂μ' =
                  ENNReal.ofReal (1 + c * (N * q * w ^ (N - 1))) := by
                rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
                  lintegral_finsetSum _ (fun i _ => measurable_const.indicator (hAm i))]
                simp only [lintegral_indicator_const (hAm _), hAμ]
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
                rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one,
                  ENNReal.ofReal_mul hc, ENNReal.ofReal_mul (by positivity),
                  ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hw0.le, ENNReal.ofReal_natCast]
                ring
              rw [← hsum]
              apply lintegral_mono_ae
              filter_upwards [haeμ] with v hv
              obtain ⟨h1, h2⟩ := hf v hv
              by_cases hex : ∃ i, v ∈ A i
              · obtain ⟨i, hi⟩ := hex
                rw [Finset.sum_eq_single i]
                · rw [Set.indicator_of_mem hi, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one hc]
                  exact ENNReal.ofReal_le_ofReal (h2 i hi)
                · intro j _ hji
                  apply Set.indicator_of_notMem
                  intro hj
                  have a := (hAmem i v).1 hi j
                  have b := (hAmem j v).1 hj j
                  rw [if_neg hji] at a; rw [if_pos rfl] at b
                  linarith
                · intro h; exact absurd (Finset.mem_univ i) h
              · push Not at hex
                rw [Finset.sum_eq_zero (fun i _ => Set.indicator_of_notMem (hex i) _), add_zero,
                  ← ENNReal.ofReal_one]
                exact ENNReal.ofReal_le_ofReal h1
            have hge1 : ∀ v : Fin N → ℝ, (∀ i, v i = 1 ∨ v i = M) → ∀ i, 1 ≤ v i := by
              intro v hv i; rcases hv i with h | h <;> rw [h]; linarith
            have hleM : ∀ v : Fin N → ℝ, (∀ i, v i = 1 ∨ v i = M) → ∀ i, v i ≤ M := by
              intro v hv i; rcases hv i with h | h <;> rw [h]; linarith
            have hAi : ∀ i v, v ∈ A i → v i = M ∧ ∀ j, j ≠ i → v j = 1 := by
              intro i v hv
              refine ⟨by rw [(hAmem i v).1 hv i, if_pos rfl], fun j hj => by rw [(hAmem i v).1 hv j, if_neg hj]⟩
            constructor
            · -- pessimistic, p = M, r = 1
              have hopt : expOne μ' 1 M 1 ≤ optOne μ' 1 :=
                le_iSup_of_le M (le_iSup_of_le 1 (le_iSup_of_le ⟨by linarith, zero_le_one⟩ le_rfl))
              have hexp : expOne μ' 1 M 1 = ∫⁻ v, ENNReal.ofReal (oneRevenue pessValue M 1 v) ∂μ' := by
                simp [expOne]
              refine le_trans ?_ (hexp ▸ hopt)
              have := lowint (fun v => oneRevenue pessValue M 1 v) (M - 1) (by linarith) ?_
              · rw [show 1 / ((N:ℝ) * q) - 1 = M - 1 by rw [hM]]; exact this
              intro v hv
              have hU1 : 1 ≤ pessValue v Finset.univ := by
                unfold pessValue; rw [dif_pos Finset.univ_nonempty]
                exact Finset.le_inf' _ _ (fun k _ => hge1 v hv k)
              constructor
              · have := hlow (oneOptions N) (fun S => pessValue v S - opqPrice M (fun _ => 1) S)
                  (opqPrice M (fun _ => 1)) Finset.univ huniv (by simp only [hpU]; linarith) (by
                    intro o' ho'
                    rcases (hmem o').1 ho' with ⟨j, rfl⟩ | rfl
                    · simp only [hp1, hpU, hpe1]; linarith [hleM v hv j]
                    · exact le_rfl)
                rw [hpU] at this
                exact this
              · intro i hi
                obtain ⟨hvi, hvj⟩ := hAi i v hi
                have := hlow (oneOptions N) (fun S => pessValue v S - opqPrice M (fun _ => 1) S)
                  (opqPrice M (fun _ => 1)) {i} (hsing i) (by simp only [hp1, hpe1]; linarith) (by
                    intro o' ho'
                    rcases (hmem o').1 ho' with ⟨j, rfl⟩ | rfl
                    · simp only [hp1, hpe1]; linarith [hleM v hv j]
                    · simp only [hp1, hpU, hpe1]
                      obtain ⟨j, hj⟩ := exists_ne i
                      linarith [hpeU v j, hvj j hj])
                rw [hp1] at this
                unfold oneRevenue
                linarith
            · -- risk neutral, p = M - (M-1)/N, r = 1
              obtain ⟨p3, hp3⟩ : ∃ p3 : ℝ, p3 = M - (M - 1) / N := ⟨_, rfl⟩
              have hp3a : p3 - 1 = (1 - 1 / N) * (M - 1) := by rw [hp3]; field_simp; ring
              have hp3b : M - p3 = (M - 1) / N := by rw [hp3]; ring
              have hp3c : 1 ≤ p3 := by nlinarith
              have hopt : expOne μ' 0 p3 1 ≤ optOne μ' 0 :=
                le_iSup_of_le p3 (le_iSup_of_le 1 (le_iSup_of_le ⟨by linarith, zero_le_one⟩ le_rfl))
              have hexp : expOne μ' 0 p3 1 = ∫⁻ v, ENNReal.ofReal (oneRevenue rnValue p3 1 v) ∂μ' := by
                simp [expOne]
              refine le_trans ?_ (hexp ▸ hopt)
              have := lowint (fun v => oneRevenue rnValue p3 1 v) (p3 - 1) (by linarith) ?_
              · rw [show (1:ℝ) + (1 - 1 / N) * ((1 / (N * q) - 1) * (N * q * w ^ (N - 1))) =
                  1 + (p3 - 1) * (N * q * w ^ (N - 1)) by rw [hp3a, hM]; ring]
                exact this
              intro v hv
              have hsub : ∑ k, (v k - 1) = (∑ k, v k) - N := by
                simp [Finset.sum_sub_distrib]
              have hdiv : (∑ k, v k) / N - 1 = (∑ k, (v k - 1)) / N := by
                rw [hsub]; field_simp
              have hS : ∀ j, v j - 1 ≤ ∑ k, (v k - 1) :=
                fun j => Finset.single_le_sum (fun k _ => sub_nonneg.2 (hge1 v hv k)) (Finset.mem_univ j)
              have hS0 : 0 ≤ ∑ k, (v k - 1) := Finset.sum_nonneg (fun k _ => sub_nonneg.2 (hge1 v hv k))
              have hMN : 0 ≤ (M - 1) / N := div_nonneg (by linarith) hNpos.le
              constructor
              · have := hlow (oneOptions N) (fun S => rnValue v S - opqPrice p3 (fun _ => 1) S)
                  (opqPrice p3 (fun _ => 1)) Finset.univ huniv (by
                    simp only [hpU, hrnU]; rw [hdiv]; exact div_nonneg hS0 hNpos.le) (by
                    intro o' ho'
                    rcases (hmem o').1 ho' with ⟨j, rfl⟩ | rfl
                    · simp only [hp1, hpU, hrn1, hrnU]; rw [hdiv]
                      rcases hv j with h | h
                      · rw [h]; linarith [div_nonneg hS0 hNpos.le]
                      · have : (M - 1) / N ≤ (∑ k, (v k - 1)) / N :=
                          div_le_div_of_nonneg_right (by have := hS j; rw [h] at this; exact this) hNpos.le
                        rw [h]; linarith
                    · exact le_rfl)
                rw [hpU] at this
                exact this
              · intro i hi
                obtain ⟨hvi, hvj⟩ := hAi i v hi
                have hsumA : ∑ k, (v k - 1) = M - 1 := by
                  rw [Finset.sum_eq_single i (fun k _ hk => by rw [hvj k hk]; ring) (by simp), hvi]
                have := hlow (oneOptions N) (fun S => rnValue v S - opqPrice p3 (fun _ => 1) S)
                  (opqPrice p3 (fun _ => 1)) {i} (hsing i) (by simp only [hp1, hrn1]; linarith) (by
                    intro o' ho'
                    rcases (hmem o').1 ho' with ⟨j, rfl⟩ | rfl
                    · simp only [hp1, hrn1]; linarith [hleM v hv j]
                    · simp only [hp1, hpU, hrn1, hrnU]
                      rw [hdiv, hsumA, hvi]; linarith)
                rw [hp1] at this
                unfold oneRevenue
                linarith
          have hLbound : ∀ q : ℝ, 0 < q → (N : ℝ) * q < 1 →
              1 - (2 * N - 1) * q ≤ (1 / (N * q) - 1) * (N * q * (1 - q) ^ (N - 1)) := by
            intro q hq hNq
            have e : (1 / (N * q) - 1) * (N * q * (1 - q) ^ (N - 1)) = (1 - N * q) * (1 - q) ^ (N - 1) := by
              field_simp
            rw [e]
            have hq1 : q < 1 := by nlinarith
            have hb := one_add_mul_le_pow (a := -q) (by linarith) (N - 1)
            have hc : ((N - 1 : ℕ) : ℝ) = N - 1 := by rw [Nat.cast_sub (by omega)]; simp
            rw [hc, ← sub_eq_add_neg] at hb
            have h0 : 0 ≤ 1 - N * q := by linarith
            nlinarith [mul_le_mul_of_nonneg_left hb h0, mul_nonneg (mul_nonneg hNpos.le (by linarith : (0:ℝ) ≤ N - 1)) (sq_nonneg q)]
          have hqchoice : ∀ ε : ℝ, 0 < ε → ∃ q : ℝ, 0 < q ∧ (N : ℝ) * q < 1 ∧ (2 * N - 1) * q < ε ∧
              (2 * N - 1) * q < 1 := by
            intro ε hε
            refine ⟨ε / (2 * N * (1 + ε)), by positivity, ?_⟩
            have h2Nq : 2 * N * (ε / (2 * N * (1 + ε))) = ε / (1 + ε) := by field_simp
            have hε1 : ε / (1 + ε) < 1 := by rw [div_lt_one (by linarith)]; linarith
            have hε2 : ε / (1 + ε) < ε := by rw [div_lt_iff₀ (by linarith)]; nlinarith
            have hq0 : 0 < ε / (2 * N * (1 + ε)) := by positivity
            refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
          refine ⟨?_, ?_, ?_⟩
          · have hpess : ∀ p r : ℝ, 0 ≤ p → 0 ≤ r → ∫⁻ v, ENNReal.ofReal (oneRevenue pessValue p r v) ∂μ ≤
                optSP μ + ENNReal.ofReal 1 * optSP μ := fun p r hp hr =>
              bound pessValue 1 p r p hp hr zero_le_one le_rfl (by rw [one_mul]; linarith [le_min hp hr])
                hpe1 (fun v => ⟨i0, hpeU v _⟩) (fun v hv i _ _ h0 _ => by linarith)
            have hrn : ∀ p r : ℝ, 0 ≤ p → 0 ≤ r → ∫⁻ v, ENNReal.ofReal (oneRevenue rnValue p r v) ∂μ ≤
                optSP μ + ENNReal.ofReal (1 - 1 / N) * optSP μ := by
              intro p r hp hr
              apply bound rnValue (1 - 1 / N) p r (max p ((p - min p r) / (1 - 1 / N))) hp hr hκpos.le
                (le_max_left _ _)
              · calc p - min p r = (1 - 1 / N) * ((p - min p r) / (1 - 1 / N)) := by
                      rw [mul_div_cancel₀ _ hκpos.ne']
                  _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) hκpos.le
              · exact hrn1
              · intro v
                rw [hrnU]
                obtain ⟨k, _, hk⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty
                  (f := fun _ => (∑ i, v i) / N) (g := v) (by
                    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
                    rw [mul_div_cancel₀ _ hNpos.ne'])
                exact ⟨k, hk⟩
              · intro v hv i hvi hU h0 hrp
                rw [hrnU] at hU
                have hmr : min p r = r := min_eq_right hrp.le
                rw [hmr]
                apply max_le (by linarith)
                rw [div_le_iff₀ hκpos]
                have hs : v i ≤ ∑ j, v j := Finset.single_le_sum (fun j _ => hv j) (Finset.mem_univ i)
                have : v i / N ≤ (∑ j, v j) / N := div_le_div_of_nonneg_right hs hNpos.le
                have e : v i * (1 - 1 / N) = v i - v i / N := by ring
                linarith
            have e : ENNReal.ofReal (2 - (1 - α) / N) = ENNReal.ofReal α * (1 + ENNReal.ofReal 1) +
                ENNReal.ofReal (1 - α) * (1 + ENNReal.ofReal (1 - 1 / N)) := by
              have h1 : (1 : ENNReal) = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
              rw [h1, ← ENNReal.ofReal_add zero_le_one zero_le_one, ← ENNReal.ofReal_add zero_le_one hκpos.le,
                ← ENNReal.ofReal_mul hα.1, ← ENNReal.ofReal_mul (by linarith [hα.2] : (0:ℝ) ≤ 1 - α),
                ← ENNReal.ofReal_add (mul_nonneg hα.1 (by norm_num))
                  (mul_nonneg (by linarith [hα.2]) (by linarith))]
              congr 1; field_simp; ring
            apply iSup_le; intro p; apply iSup_le; intro r; apply iSup_le; rintro ⟨hp, hr⟩
            unfold expOne
            calc _ ≤ ENNReal.ofReal α * (optSP μ + ENNReal.ofReal 1 * optSP μ) +
                  ENNReal.ofReal (1 - α) * (optSP μ + ENNReal.ofReal (1 - 1 / N) * optSP μ) := by
                  gcongr
                  · exact hpess p r hp hr
                  · exact hrn p r hp hr
              _ = (ENNReal.ofReal α * (1 + ENNReal.ofReal 1) +
                  ENNReal.ofReal (1 - α) * (1 + ENNReal.ofReal (1 - 1 / N))) * optSP μ := by ring
              _ = _ := by rw [e]
          · intro ε hε
            obtain ⟨q, hq0, hNq, hqε, hq1⟩ := hqchoice ε hε
            obtain ⟨ν, h1, h2, h3, h4, h5, h6⟩ := key q hq0 hNq
            have hL := hLbound q hq0 hNq
            refine ⟨ν, h1, h2, h3, lt_of_le_of_lt h4 ENNReal.one_lt_top, ?_⟩
            calc ENNReal.ofReal (2 - ε) * optSP (Measure.pi fun _ : Fin N => ν)
                ≤ ENNReal.ofReal (2 - ε) * 1 := by gcongr
              _ = ENNReal.ofReal (2 - ε) := mul_one _
              _ < ENNReal.ofReal (1 + (1 / (N * q) - 1) * (N * q * (1 - q) ^ (N - 1))) := by
                  rw [ENNReal.ofReal_lt_ofReal_iff (by linarith)]; linarith
              _ ≤ _ := h5
          · intro ε hε
            obtain ⟨q, hq0, hNq, hqε, hq1⟩ := hqchoice ε hε
            obtain ⟨ν, h1, h2, h3, h4, h5, h6⟩ := key q hq0 hNq
            have hL := hLbound q hq0 hNq
            have hm := mul_le_mul_of_nonneg_left hL hκpos.le
            have hx : 0 ≤ (1 / (N : ℝ)) * ((2 * N - 1) * q) :=
              mul_nonneg (by positivity) (mul_nonneg (by linarith) hq0.le)
            have hpos2 : 0 < (1 - 1 / (N : ℝ)) * (1 - (2 * N - 1) * q) := mul_pos hκpos (by linarith)
            refine ⟨ν, h1, h2, h3, lt_of_le_of_lt h4 ENNReal.one_lt_top, ?_⟩
            calc ENNReal.ofReal (2 - 1 / N - ε) * optSP (Measure.pi fun _ : Fin N => ν)
                ≤ ENNReal.ofReal (2 - 1 / N - ε) * 1 := by gcongr
              _ = ENNReal.ofReal (2 - 1 / N - ε) := mul_one _
              _ < ENNReal.ofReal (1 + (1 - 1 / N) * ((1 / (N * q) - 1) * (N * q * (1 - q) ^ (N - 1)))) := by
                  rw [ENNReal.ofReal_lt_ofReal_iff (by linarith)]
                  have e : (1 - 1 / (N : ℝ)) * (1 - (2 * N - 1) * q) =
                      (1 - 1 / N) - (2 * N - 1) * q + (1 / (N : ℝ)) * ((2 * N - 1) * q) := by ring
                  linarith
              _ ≤ _ := h6
