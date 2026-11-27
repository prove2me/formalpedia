-- Prove2me | solution 1 for SocialManip.Beliefs.Supplement.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:34:28.257582+00:00
-- url     : https://prove2.me/submissions/49f90700-4502-40c2-bf56-e4dff1a426d5

import Mathlib
import Definitions.Def_SocialManip_Beliefs_Setting
import Definitions.Def_SocialManip_Beliefs_Supplement_Network
import Definitions.Def_SocialManip_Beliefs_Supplement_Game

open Filter Topology

open SocialManip
open SocialManip.Beliefs
open SocialManip.Beliefs.Supplement

open SocialManip.Beliefs

/-- The printed chain alternative allows the Bayesian block size to vary with n. Even n
leave one DeGroot, odd n have one Bayesian. No single cutoff can satisfy the two conclusions,
even if η* is allowed outside [0,1]. This refutes the complete printed family-level claim. -/
theorem solution :
    let Bf : ∀ n : ℕ, Finset (Fin n) := fun n =>
      if Even n then Finset.univ.filter (fun i : Fin n => i.val ≠ 0) else Finset.univ.filter (fun i : Fin n => i.val = 0)
    let Mf : ∀ n : ℕ, ℝ → Model n := fun n η =>
      ⟨Bf n, etaTheta n η, etaAlpha n η, (fun _ => 3 / 4), 1 / 2, 1, 1, 1 / 4, 1 / 2⟩
    (∀ n, IsRingArc (Bf n)) ∧
      ¬ ∃ ηstar : ℝ,
        (∀ η ∈ Set.Icc (0 : ℝ) 1, η < ηstar → ∀ K : ℕ, ∃ N : ℕ, ∀ n, N ≤ n →
          ManipulatesAtLeast (Mf n η) K) ∧
        (∀ η ∈ Set.Icc (0 : ℝ) 1, ηstar < η → ∀ n, Impervious (Mf n η)) := by
          classical
          dsimp only
          let Bf : ∀ n : ℕ, Finset (Fin n) := fun n =>
            if Even n then Finset.univ.filter (fun i : Fin n => i.val ≠ 0)
            else Finset.univ.filter (fun i : Fin n => i.val = 0)
          let Mf : ∀ n : ℕ, ℝ → Model n := fun n η =>
            ⟨Bf n, etaTheta n η, etaAlpha n η, (fun _ => 3 / 4), 1 / 2, 1, 1, 1 / 4, 1 / 2⟩
          change (∀ n, IsRingArc (Bf n)) ∧ _
          have harc : ∀ n, IsRingArc (Bf n) := by
            intro n
            by_cases he : Even n
            · by_cases hn : n ≤ 1
              · refine ⟨0, 0, ?_⟩
                intro i
                simp only [Bf, if_pos he, Finset.mem_filter, Finset.mem_univ, true_and]
                have : i.val = 0 := by omega
                simp [this]
              · refine ⟨1, n - 1, ?_⟩
                intro i
                simp only [Bf, if_pos he, Finset.mem_filter, Finset.mem_univ, true_and]
                have hn' : 1 < n := by omega
                rw [Nat.mod_eq_of_lt hn']
                by_cases hi : i.val = 0
                · simp [hi, Nat.mod_eq_of_lt (show n - 1 < n by omega)]
                · rw [Nat.add_sub_assoc (by omega : 1 ≤ n),
                    Nat.add_mod, Nat.mod_eq_of_lt i.isLt]
                  have hh : i.val + (n - 1) = n + (i.val - 1) := by omega
                  rw [Nat.mod_eq_of_lt (show n - 1 < n by omega), hh, Nat.add_mod_left,
                    Nat.mod_eq_of_lt (by omega)]
                  omega
            · refine ⟨0, 1, ?_⟩
              intro i
              simp only [Bf, if_neg he, Finset.mem_filter, Finset.mem_univ, true_and,
                Nat.zero_mod, Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
              omega
          refine ⟨harc, ?_⟩
          intro hc
          obtain ⟨ηstar, hlo, hhi⟩ := hc
          change (∀ η ∈ Set.Icc (0 : ℝ) 1, η < ηstar → ∀ K : ℕ, ∃ N : ℕ,
            ∀ n, N ≤ n → ManipulatesAtLeast (Mf n η) K) at hlo
          change (∀ η ∈ Set.Icc (0 : ℝ) 1, ηstar < η → ∀ n, Impervious (Mf n η)) at hhi
          have heq : ∀ {n : ℕ} (M : Model n) (T : ℝ),
              ∃ σP σD, IsEquilibrium M T σP σD := by
            intro n M T
            let σD : DeGrootStrategy n := fun _ π => if (1 - M.b) / 2 < π then 1 else 0
            have hD : IsDeGrootBestResponse M σD := by
              intro i hi π
              dsimp [σD]
              split_ifs with h <;> simp_all <;> linarith
            have hmax : ∀ y : State, ∃ a : State × (Fin n → Bool),
                ∀ a' : State × (Fin n → Bool), principalPayoff M T σD y a'.1 a'.2 ≤ principalPayoff M T σD y a.1 a.2 := by
              intro y
              exact Finite.exists_max (fun a : State × (Fin n → Bool) =>
                principalPayoff M T σD y a.1 a.2)
            choose a ha using hmax
            refine ⟨fun y => PMF.pure (a y), σD, hD, ?_⟩
            intro y a' ha' a''
            have : a' = a y := by
              by_contra hn
              simpa [PMF.pure_apply, hn, Ne.symm hn] using ha'
            subst a'
            exact ha y a''
          have hcount : ∀ {n : ℕ} (M : Model n), (∀ i : Fin n, i.val ≠ 0 → i ∈ M.B) →
              ∀ T σD y yhat x ω j, 2 ≤ j → countLaw (manipProb M T σD y yhat x ω) j = 0 := by
            intro n M hB T σD y yhat x ω j hj
            apply Finset.sum_eq_zero
            intro A hA
            have hcard : 2 ≤ A.card := by
              have := (Finset.mem_filter.mp hA).2
              omega
            have hex : ∃ i ∈ A, i.val ≠ 0 := by
              by_contra hh
              push_neg at hh
              have hc : A.card ≤ 1 := by
                apply Finset.card_le_one.mpr
                intro a ha b hb
                apply Fin.ext
                rw [hh a ha, hh b hb]
              omega
            obtain ⟨i, hi, hi0⟩ := hex
            have hz : manipProb M T σD y yhat x ω i = 0 := by simp [manipProb, hB i hi0]
            rw [Finset.prod_eq_zero hi hz, zero_mul]
          have hnot : ∀ n, Even n → ¬ ManipulatesAtLeast (Mf n 0) 2 := by
            intro n hn hm
            obtain ⟨Tstar, hT⟩ := hm (1 / 2) (by norm_num)
            obtain ⟨σP, σD, he⟩ := heq (Mf n 0) (Tstar + 1)
            have hb : ∀ i : Fin n, i.val ≠ 0 → i ∈ (Mf n 0).B := by
              intro i hi
              simp [Mf, Bf, hn, hi]
            have hc : ∀ j, 2 ≤ j → manipLawGiven (Mf n 0) (Tstar + 1) σP σD State.S j = 0 := by
              intro j hj
              unfold manipLawGiven
              simp only [hcount _ hb _ _ _ _ _ _ j hj, MeasureTheory.integral_zero, mul_zero,
                Finset.sum_const_zero]
            have hh := hT (Tstar + 1) (by linarith) σP σD he
            have hz : (∑ j ∈ Finset.Icc 2 n,
                manipLawGiven (Mf n 0) (Tstar + 1) σP σD State.S j) = 0 := by
              apply Finset.sum_eq_zero
              intro j hj
              exact hc j (Finset.mem_Icc.mp hj).1
            rw [hz] at hh
            norm_num at hh
          have hstar : ηstar ≤ 0 := by
            by_contra hh
            have hp : 0 < ηstar := lt_of_not_ge hh
            obtain ⟨N, hN⟩ := hlo 0 (by norm_num) hp 2
            exact hnot (2 * N) (even_two_mul N) (hN (2 * N) (by omega))
          have him := hhi 1 (by norm_num) (by linarith) 2
          change Impervious (Mf 2 1) at him
          have hexpI : MeasureTheory.Integrable (fun x : ℝ => x) (ProbabilityTheory.expMeasure 1) := by
            change MeasureTheory.Integrable (fun x : ℝ => x)
              (MeasureTheory.volume.withDensity (ProbabilityTheory.gammaPDF 1 1))
            apply (MeasureTheory.integrable_withDensity_iff_integrable_smul'
              (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
              (f := ProbabilityTheory.gammaPDF 1 1) (by unfold ProbabilityTheory.gammaPDF; fun_prop)
              (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
            have hi := (MeasureTheory.integrable_indicator_iff measurableSet_Ioi).mpr
              (Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 2))
            apply hi.congr
            filter_upwards [] with x
            by_cases hx : 0 < x
            · norm_num [ProbabilityTheory.gammaPDF, ProbabilityTheory.gammaPDFReal, le_of_lt hx,
                ENNReal.toReal_ofReal, Real.exp_nonneg, Set.indicator, Set.mem_Ioi, hx, mul_comm]
            · by_cases hx0 : x = 0
              · subst x; norm_num [ProbabilityTheory.gammaPDF, ProbabilityTheory.gammaPDFReal]
              · norm_num [ProbabilityTheory.gammaPDF, ProbabilityTheory.gammaPDFReal,
                  show ¬0 ≤ x from fun h => hx0 (le_antisymm (le_of_not_gt hx) h), Set.indicator, Set.mem_Ioi, hx]
          have hexpE : (∫ x : ℝ, x ∂(ProbabilityTheory.expMeasure 1)) = 1 := by
            change (∫ x : ℝ, x ∂(MeasureTheory.volume.withDensity
              (ProbabilityTheory.gammaPDF 1 1))) = 1
            rw [integral_withDensity_eq_integral_toReal_smul
              (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
              (f := ProbabilityTheory.gammaPDF 1 1) (by unfold ProbabilityTheory.gammaPDF; fun_prop) (Filter.Eventually.of_forall (fun x =>
                ENNReal.ofReal_lt_top))]
            have heq : (fun x : ℝ => (ProbabilityTheory.gammaPDF 1 1 x).toReal • x) =
                Set.indicator (Set.Ioi 0) (fun x : ℝ => x ^ ((2 : ℝ) - 1) * Real.exp (-(1 * x))) := by
              funext x
              by_cases hx : 0 < x
              · norm_num [ProbabilityTheory.gammaPDF, ProbabilityTheory.gammaPDFReal, le_of_lt hx,
                  ENNReal.toReal_ofReal, Real.exp_nonneg, Set.indicator, Set.mem_Ioi, hx, mul_comm]
              · by_cases hx0 : x = 0
                · subst x; norm_num [ProbabilityTheory.gammaPDF, ProbabilityTheory.gammaPDFReal]
                · norm_num [ProbabilityTheory.gammaPDF, ProbabilityTheory.gammaPDFReal,
                    show ¬0 ≤ x from fun h => hx0 (le_antisymm (le_of_not_gt hx) h), Set.indicator, Set.mem_Ioi, hx]
            rw [heq, MeasureTheory.integral_indicator measurableSet_Ioi,
              Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) (by norm_num)]
            norm_num
          let ν : MeasureTheory.Measure (ℕ → ℝ) :=
            MeasureTheory.Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.expMeasure 1)
          have hwait : ∀ᵐ e ∂ν, Tendsto (fun k : ℕ => (∑ l ∈ Finset.range k, e l) / (k : ℝ))
              atTop (𝓝 (1 : ℝ)) := by
            have hind := ProbabilityTheory.iIndepFun_infinitePi
              (P := fun _ : ℕ => ProbabilityTheory.expMeasure 1)
              (X := fun _ : ℕ => fun x : ℝ => x) (fun _ => measurable_id)
            have hident : ∀ k : ℕ, ProbabilityTheory.IdentDistrib (fun e : ℕ → ℝ => e k)
                (fun e : ℕ → ℝ => e 0) ν ν := by
              intro k
              exact (measurePreserving_eval_infinitePi (fun _ : ℕ => ProbabilityTheory.expMeasure 1) k).hasLaw.identDistrib
                (measurePreserving_eval_infinitePi (fun _ : ℕ => ProbabilityTheory.expMeasure 1) 0).hasLaw
            have hI : MeasureTheory.Integrable (fun e : ℕ → ℝ => e 0) ν :=
              (measurePreserving_eval_infinitePi (fun _ : ℕ => ProbabilityTheory.expMeasure 1) 0).integrable_comp_of_integrable hexpI
            have hE : (∫ e : ℕ → ℝ, e 0 ∂ν) = 1 := by
              rw [(measurePreserving_eval_infinitePi
                (fun _ : ℕ => ProbabilityTheory.expMeasure 1) 0).hasLaw.integral_eq]
              exact hexpE
            simpa only [hE] using ProbabilityTheory.strong_law_ae_real
              (fun k (e : ℕ → ℝ) => e k) hI (fun _ _ h => hind.indepFun h) hident
          have hexpN : ∀ᵐ x ∂(ProbabilityTheory.expMeasure 1), 0 ≤ x := by
            change ∀ᵐ x ∂(MeasureTheory.volume.withDensity (ProbabilityTheory.gammaPDF 1 1)), 0 ≤ x
            apply (MeasureTheory.ae_withDensity_iff
              ((ProbabilityTheory.measurable_gammaPDFReal 1 1).ennreal_ofReal)).mpr
            exact Filter.Eventually.of_forall (fun x hx => by
              by_contra hn
              exact hx (ProbabilityTheory.gammaPDF_of_neg (lt_of_not_ge hn)))
          have hwaitN : ∀ᵐ e ∂ν, ∀ k, 0 ≤ e k := by
            rw [MeasureTheory.ae_all_iff]
            intro k
            have hmp := measurePreserving_eval_infinitePi
              (fun _ : ℕ => ProbabilityTheory.expMeasure 1) k
            exact MeasureTheory.ae_of_ae_map hmp.measurable.aemeasurable (hmp.map_eq.symm ▸ hexpN)
          have hinv : ∀ (A : ℕ → ℝ), Monotone A → A 0 = 0 →
              Tendsto (fun k : ℕ => A k / (k : ℝ)) atTop (𝓝 1) →
              ∃ c : ℕ → ℕ, (∀ (n k : ℕ), A (k + 1) ≤ (n : ℝ) ↔ k < c n) ∧
                Tendsto c atTop atTop ∧
                Tendsto (fun n : ℕ => (c n : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
            intro A hA hA0 hlim
            have htop : Tendsto A atTop atTop := by
              have hh := hlim.pos_mul_atTop (by norm_num : (0 : ℝ) < 1)
                (tendsto_natCast_atTop_atTop (R := ℝ))
              apply hh.congr'
              filter_upwards [eventually_ne_atTop 0] with n hn
              exact div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hn)
            have hex : ∀ n : ℕ, ∃ k, (n : ℝ) < A (k + 1) := by
              intro n
              obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp (htop.eventually_gt_atTop (n : ℝ))
              exact ⟨k, hk (k + 1) (by omega)⟩
            let c : ℕ → ℕ := fun n => Nat.find (hex n)
            have hspec : ∀ (n k : ℕ), A (k + 1) ≤ (n : ℝ) ↔ k < c n := by
              intro n k
              constructor
              · intro hk
                by_contra hh
                have hc := Nat.find_spec (hex n)
                have hm := hA (show c n + 1 ≤ k + 1 by omega)
                change (n : ℝ) < A (c n + 1) at hc
                linarith
              · intro hk
                exact le_of_not_gt (Nat.find_min (hex n) hk)
            have hcTop : Tendsto c atTop atTop := by
              apply tendsto_atTop.2
              intro k
              filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (A (k + 1))] with n hn
              exact le_of_lt ((hspec n k).mp hn)
            have hlo : ∀ n : ℕ, A (c n) ≤ (n : ℝ) := by
              intro n
              by_cases hc : c n = 0
              · simp [hc, hA0]
              · simpa [Nat.sub_add_cancel (show 1 ≤ c n by omega)] using
                  (hspec n (c n - 1)).mpr (by omega)
            have hhi : ∀ n : ℕ, (n : ℝ) ≤ A (c n + 1) := by
              intro n
              exact (Nat.find_spec (hex n)).le
            have hl : Tendsto (fun n : ℕ => A (c n) / ((c n : ℝ) + 1)) atTop (𝓝 1) := by
              have hh := (hlim.comp hcTop).mul ((tendsto_natCast_div_add_atTop (1 : ℝ)).comp hcTop)
              simp only [mul_one] at hh
              apply hh.congr'
              filter_upwards [hcTop.eventually_ne_atTop 0] with n hn
              dsimp only [Function.comp_def]
              field_simp [Nat.cast_ne_zero.mpr hn]
            have hr : Tendsto (fun n : ℕ => A (c n + 1) / ((c n : ℝ) + 1)) atTop (𝓝 1) := by
              simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using hlim.comp
                (Filter.tendsto_add_atTop_nat 1 |>.comp hcTop)
            have hm : Tendsto (fun n : ℕ => (n : ℝ) / ((c n : ℝ) + 1)) atTop (𝓝 1) := by
              apply tendsto_of_tendsto_of_tendsto_of_le_of_le hl hr
              · intro n; exact (div_le_div_iff_of_pos_right (by positivity)).mpr (hlo n)
              · intro n; exact (div_le_div_iff_of_pos_right (by positivity)).mpr (hhi n)
            have hm' := hm.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
            have hh := hm'.sub (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
            simp only [inv_one, sub_zero] at hh
            refine ⟨c, hspec, hcTop, hh.congr' ?_⟩
            filter_upwards [eventually_ne_atTop 0] with n hn
            simp only [inv_div]
            rw [← sub_div]
            congr 1
            ring
          let τ : unitInterval := ⟨3 / 4, by constructor <;> norm_num⟩
          let ρ : MeasureTheory.Measure (Fin 2 × ℕ → State) :=
            MeasureTheory.Measure.infinitePi (fun _ : Fin 2 × ℕ =>
              ProbabilityTheory.bernoulliMeasure State.S State.R τ)
          let Z : State → ℝ := fun s => if s = State.S then 1 else 0
          have hZ : Measurable Z := by
            exact measurable_of_countable Z
          have hmark : ∀ᵐ w ∂ρ,
              Tendsto (fun k : ℕ => (∑ l ∈ Finset.range k, Z (w (0, l))) / (k : ℝ))
                atTop (𝓝 (3 / 4 : ℝ)) := by
            have hind := ProbabilityTheory.iIndepFun_infinitePi
              (P := fun _ : Fin 2 × ℕ => ProbabilityTheory.bernoulliMeasure State.S State.R τ)
              (X := fun _ : Fin 2 × ℕ => Z) (fun _ => hZ)
            have hind' := hind.precomp (g := fun k : ℕ => ((0 : Fin 2), k))
              (fun _ _ h => (Prod.mk.inj h).2)
            have hident : ∀ k : ℕ, ProbabilityTheory.IdentDistrib
                (fun w : Fin 2 × ℕ → State => Z (w (0, k)))
                (fun w : Fin 2 × ℕ → State => Z (w (0, 0))) ρ ρ := by
              intro k
              exact ((measurePreserving_eval_infinitePi
                (fun _ : Fin 2 × ℕ => ProbabilityTheory.bernoulliMeasure State.S State.R τ) (0, k)).hasLaw.identDistrib
                (measurePreserving_eval_infinitePi
                (fun _ : Fin 2 × ℕ => ProbabilityTheory.bernoulliMeasure State.S State.R τ) (0, 0)).hasLaw).comp hZ
            have hZI : MeasureTheory.Integrable Z (ProbabilityTheory.bernoulliMeasure State.S State.R τ) := by
              apply MeasureTheory.Integrable.of_bound hZ.aestronglyMeasurable 1
              exact Filter.Eventually.of_forall (fun s => by cases s <;> norm_num [Z, show State.R ≠ State.S by decide])
            have hI : MeasureTheory.Integrable (fun w : Fin 2 × ℕ → State => Z (w (0, 0))) ρ :=
              (measurePreserving_eval_infinitePi
                (fun _ : Fin 2 × ℕ => ProbabilityTheory.bernoulliMeasure State.S State.R τ) (0, 0)).integrable_comp_of_integrable hZI
            have hE : (∫ w : Fin 2 × ℕ → State, Z (w (0, 0)) ∂ρ) = (3 / 4 : ℝ) := by
              have hmp := measurePreserving_eval_infinitePi
                (fun _ : Fin 2 × ℕ => ProbabilityTheory.bernoulliMeasure State.S State.R τ) (0, 0)
              calc
                _ = ∫ z, Z z ∂(ρ.map (fun w => w (0, 0))) :=
                  (MeasureTheory.integral_map hmp.measurable.aemeasurable hZ.aestronglyMeasurable).symm
                _ = ∫ z, Z z ∂(ProbabilityTheory.bernoulliMeasure State.S State.R τ) := by rw [hmp.map_eq]
                _ = 3 / 4 := by
                  rw [ProbabilityTheory.integral_bernoulliMeasure]
                  norm_num [Z, τ, show State.R ≠ State.S by decide]
            simpa only [hE] using ProbabilityTheory.strong_law_ae_real
              (fun k (w : Fin 2 × ℕ → State) => Z (w (0, k))) hI
              (fun _ _ h => hind'.indepFun h) hident
          let C : (ℕ → ℝ) → ℕ → ℕ := fun e n => {k : ℕ | arrivalTime e 1 k ≤ (n : ℝ)}.ncard
          let O : (Fin 2 × ℕ → State) → (ℕ → ℝ) → ℕ → State → ℕ := fun w e n s =>
            {k : ℕ | arrivalTime e 1 k ≤ (n : ℝ) ∧ w (0, k) = s}.ncard
          have hclock : ∀ e : ℕ → ℝ, (∀ k, 0 ≤ e k) →
              Tendsto (fun k : ℕ => (∑ l ∈ Finset.range k, e l) / (k : ℝ)) atTop (𝓝 1) →
              Tendsto (C e) atTop atTop ∧
              Tendsto (fun n : ℕ => (C e n : ℝ) / (n : ℝ)) atTop (𝓝 1) ∧
              (∀ (n k : ℕ), arrivalTime e 1 k ≤ (n : ℝ) ↔ k < C e n) := by
            intro e he hlim
            let A : ℕ → ℝ := fun k => ∑ l ∈ Finset.range k, e l
            have hm : Monotone A := by
              intro i j hij
              apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hij)
              intro i hi hi'; exact he i
            obtain ⟨c, hc, hcTop, hcLim⟩ := hinv A hm (by simp [A]) hlim
            have hC : C e = c := by
              funext n
              have hs : {k : ℕ | arrivalTime e 1 k ≤ (n : ℝ)} = Set.Iio (c n) := by
                ext k
                simpa [arrivalTime, A] using hc n k
              simp [C, hs]
            rw [hC]
            exact ⟨hcTop, hcLim, fun n k => by simpa [arrivalTime, A] using hc n k⟩
          have horganic : ∀ (e : ℕ → ℝ) (w : Fin 2 × ℕ → State),
              (∀ (n k : ℕ), arrivalTime e 1 k ≤ (n : ℝ) ↔ k < C e n) →
              Tendsto (C e) atTop atTop →
              Tendsto (fun n : ℕ => (C e n : ℝ) / (n : ℝ)) atTop (𝓝 1) →
              Tendsto (fun k : ℕ => (∑ l ∈ Finset.range k, Z (w (0, l))) / (k : ℝ))
                atTop (𝓝 (3 / 4 : ℝ)) →
              Tendsto (fun n : ℕ => (O w e n State.S : ℝ) / (n : ℝ)) atTop (𝓝 (3 / 4 : ℝ)) ∧
              Tendsto (fun n : ℕ => (O w e n State.R : ℝ) / (n : ℝ)) atTop (𝓝 (1 / 4 : ℝ)) := by
            intro e w hc hcTop hcLim hw
            have hs : ∀ (n : ℕ) s, {k : ℕ | arrivalTime e 1 k ≤ (n : ℝ) ∧ w (0, k) = s} =
                ↑((Finset.range (C e n)).filter (fun k => w (0, k) = s)) := by
              intro n s
              ext k
              simp [hc n k]
            have hS : ∀ n, (O w e n State.S : ℝ) =
                ∑ l ∈ Finset.range (C e n), Z (w (0, l)) := by
              intro n
              dsimp only [O]
              rw [hs, Set.ncard_coe_finset]
              simp [Z]
            have hR : ∀ n, (O w e n State.R : ℝ) = (C e n : ℝ) - (O w e n State.S : ℝ) := by
              intro n
              rw [hS]
              have heq : (fun l => if w (0, l) = State.R then (1 : ℝ) else 0) =
                  (fun l => 1 - Z (w (0, l))) := by
                funext l
                cases h : w (0, l) <;> norm_num [Z, h, show State.R ≠ State.S by decide,
                  show State.S ≠ State.R by decide]
              dsimp only [O]
              rw [hs]
              simp only [Set.ncard_coe_finset]
              rw [← Finset.sum_boole, heq, Finset.sum_sub_distrib]
              simp
            have hSLim : Tendsto (fun n : ℕ => (O w e n State.S : ℝ) / (n : ℝ)) atTop (𝓝 (3 / 4 : ℝ)) := by
              have hh := (hw.comp hcTop).mul hcLim
              simp only [mul_one] at hh
              apply hh.congr'
              filter_upwards [hcTop.eventually_ne_atTop 0] with n hn
              rw [hS]
              dsimp only [Function.comp_def]
              field_simp [Nat.cast_ne_zero.mpr hn]
            refine ⟨hSLim, ?_⟩
            have hh := hcLim.sub hSLim
            norm_num at hh
            simpa only [hR, sub_div] using hh
          let M : Model 2 := Mf 2 1
          let μ : MeasureTheory.Measure (Sample 2) := sampleMeasure M State.S
          have hμ : μ = ρ.prod (ν.prod ν) := by
            have ht : clampProb (3 / 4) = τ := by
              exact Set.projIcc_of_mem zero_le_one (by constructor <;> norm_num)
            simp [μ, sampleMeasure, M, Mf, organicProbS, ht, ρ, ν]
          have hpaths : ∀ᵐ ω ∂μ,
              Tendsto (fun n : ℕ => (O ω.1 ω.2.1 n State.S : ℝ) / (n : ℝ)) atTop (𝓝 (3 / 4 : ℝ)) ∧
              Tendsto (fun n : ℕ => (O ω.1 ω.2.1 n State.R : ℝ) / (n : ℝ)) atTop (𝓝 (1 / 4 : ℝ)) ∧
              Tendsto (fun n : ℕ => (C ω.2.2 n : ℝ) / (n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
            have hp0 : MeasureTheory.MeasurePreserving (fun ω : Sample 2 => ω.1) μ ρ := by
              rw [hμ]; exact MeasureTheory.measurePreserving_fst
            have hp1 : MeasureTheory.MeasurePreserving (fun ω : Sample 2 => ω.2.1) μ ν := by
              rw [hμ]; exact MeasureTheory.measurePreserving_fst.comp MeasureTheory.measurePreserving_snd
            have hp2 : MeasureTheory.MeasurePreserving (fun ω : Sample 2 => ω.2.2) μ ν := by
              rw [hμ]; exact MeasureTheory.measurePreserving_snd.comp MeasureTheory.measurePreserving_snd
            have hm := MeasureTheory.ae_of_ae_map hp0.measurable.aemeasurable (hp0.map_eq.symm ▸ hmark)
            have h1 := MeasureTheory.ae_of_ae_map hp1.measurable.aemeasurable (hp1.map_eq.symm ▸ hwait)
            have h2 := MeasureTheory.ae_of_ae_map hp2.measurable.aemeasurable (hp2.map_eq.symm ▸ hwait)
            have hn1 := MeasureTheory.ae_of_ae_map hp1.measurable.aemeasurable (hp1.map_eq.symm ▸ hwaitN)
            have hn2 := MeasureTheory.ae_of_ae_map hp2.measurable.aemeasurable (hp2.map_eq.symm ▸ hwaitN)
            filter_upwards [hm, h1, h2, hn1, hn2] with ω hm h1 h2 hn1 hn2
            obtain ⟨hc1, hr1, hs1⟩ := hclock ω.2.1 hn1 h1
            obtain ⟨hc2, hr2, hs2⟩ := hclock ω.2.2 hn2 h2
            exact ⟨(horganic ω.2.1 ω.1 hs1 hc1 hr1 hm).1,
              (horganic ω.2.1 ω.1 hs1 hc1 hr1 hm).2, hr2⟩
          have hgaps : ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
              O ω.1 ω.2.1 n State.R + 2 ≤ O ω.1 ω.2.1 n State.S ∧
              O ω.1 ω.2.1 n State.S + 2 ≤ O ω.1 ω.2.1 n State.R + C ω.2.2 n := by
            filter_upwards [hpaths] with ω hω
            have h1 := hω.1.sub hω.2.1
            have h2 := (hω.2.1.add hω.2.2).sub hω.1
            norm_num at h1 h2
            have ht1 := h1.pos_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
              (tendsto_natCast_atTop_atTop (R := ℝ))
            have ht2 := h2.pos_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
              (tendsto_natCast_atTop_atTop (R := ℝ))
            filter_upwards [ht1.eventually_ge_atTop 2, ht2.eventually_ge_atTop 2,
              eventually_ne_atTop 0] with n hn1 hn2 hn
            have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
            rw [← sub_div, div_mul_cancel₀ _ hn'] at hn1
            rw [← add_div, ← sub_div, div_mul_cancel₀ _ hn'] at hn2
            constructor
            · have hh : (O ω.1 ω.2.1 n State.R : ℝ) + 2 ≤ (O ω.1 ω.2.1 n State.S : ℝ) := by linarith
              exact_mod_cast hh
            · have hh : (O ω.1 ω.2.1 n State.S : ℝ) + 2 ≤
                  (O ω.1 ω.2.1 n State.R : ℝ) + (C ω.2.2 n : ℝ) := by linarith
              exact_mod_cast hh
          have hBUS : ∀ a b : ℕ, BUS (3 / 4) (1 / 2) a b =
              (3 : ℝ)^a / ((3 : ℝ)^a + (3 : ℝ)^b) := by
            intro a b
            unfold BUS
            norm_num only
            simp only [div_pow, one_pow]
            field_simp <;> ring
          have hsmall : ∀ a b : ℕ, b + 2 ≤ a →
              (3 : ℝ)^b / ((3 : ℝ)^a + (3 : ℝ)^b) ≤ 1 / 10 := by
            intro a b h
            have ha : (9 : ℝ) * 3^b ≤ (3 : ℝ)^a := by
              calc
                _ = (3 : ℝ)^(b+2) := by rw [pow_add]; norm_num; ring
                _ ≤ _ := by gcongr; norm_num
            apply (div_le_iff₀ (by positivity)).mpr
            nlinarith
          have hpers : ∀ yhat x ω i T,
              0 ≤ personalR M yhat x ω i T ∧ personalR M yhat x ω i T ≤ 1 := by
            intro yhat x ω i T
            simp only [personalR, show M.p i = 3 / 4 from rfl, show M.q = 1 / 2 from rfl, hBUS]
            have hp : (0 : ℝ) < 3 ^ countAt M yhat x ω i T State.S := by positivity
            have hq : (0 : ℝ) < 3 ^ countAt M yhat x ω i T State.R := by positivity
            constructor
            · have hh : (3 : ℝ)^countAt M yhat x ω i T State.S /
                  (3^countAt M yhat x ω i T State.S + 3^countAt M yhat x ω i T State.R) ≤ 1 := by
                apply (div_le_one (by positivity)).mpr
                linarith
              linarith
            · have hh : 0 ≤ (3 : ℝ)^countAt M yhat x ω i T State.S /
                  (3^countAt M yhat x ω i T State.S + 3^countAt M yhat x ω i T State.R) := by positivity
              linarith
          have hMB : M.B = {1} := by
            ext i
            fin_cases i <;> norm_num [M, Mf, Bf, show Even 2 by decide]
          have hMθ : ∀ i, M.θ i = 1 / 3 := by intro i; norm_num [M, Mf, etaTheta]
          have hMα : ∀ i j, M.α i j = 1 / 3 := by intro i j; norm_num [M, Mf, etaAlpha]
          have hgrid : ∀ yhat x ω k,
              (0 ≤ gridBeliefR M State.S yhat x ω k 0 ∧ gridBeliefR M State.S yhat x ω k 0 ≤ 1 / 2) ∧
              gridBeliefR M State.S yhat x ω k 1 = 0 := by
            intro yhat x ω k
            induction k with
            | zero => norm_num [gridBeliefR, hMB, truth, priorOf, show M.q = 1 / 2 from rfl, show State.R ≠ State.S by decide]
            | succ k ih =>
              have hp := hpers yhat x ω 0 ((k : ℝ) + 1)
              norm_num [gridBeliefR, hMB, hMθ, hMα, Fin.sum_univ_two, truth,
                show State.R ≠ State.S by decide, ih.2]
              constructor <;> nlinarith [ih.1.1, ih.1.2]
          have hbel : ∀ yhat x ω T, 0 < T →
              beliefR M State.S yhat x ω T 0 =
                (1 / 3) * personalR M yhat x ω 0 T +
                  (1 / 3) * gridBeliefR M State.S yhat x ω (⌈T⌉₊ - 1) 0 := by
            intro yhat x ω T hT
            norm_num [beliefR, hMB, not_le.mpr hT, hMθ, hMα, Fin.sum_univ_two,
              (hgrid yhat x ω (⌈T⌉₊ - 1)).2]
          let D : DeGrootStrategy 2 := fun _ π => if (1 / 4 : ℝ) < π then 1 else 0
          have hDb : ∀ i π, 0 ≤ D i π ∧ D i π ≤ 1 := by
            intro i π; dsimp [D]; split_ifs <;> norm_num
          have hD : IsDeGrootBestResponse M D := by
            intro i hi π
            refine ⟨hDb i π, ?_, ?_⟩
            · intro hh; exact if_pos (by norm_num [M, Mf] at hh; exact hh)
            · intro hh; exact if_neg (by have := hh; simp [M, Mf] at this; linarith)
          have hact : ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
              D 0 (beliefR M State.S State.R (fun _ => true) ω n 0) = 1 ∧
              D 0 (beliefR M State.S State.R (fun _ => false) ω n 0) = 0 := by
            filter_upwards [hgaps] with ω hω
            filter_upwards [hω, eventually_gt_atTop 0] with n hn hn0
            have hcS : countAt M State.R (fun _ => true) ω 0 n State.S = O ω.1 ω.2.1 n State.S := by
              simp [countAt, M, Mf, O, show State.R ≠ State.S by decide]
            have hcR : countAt M State.R (fun _ => true) ω 0 n State.R =
                O ω.1 ω.2.1 n State.R + C ω.2.2 n := by
              simp [countAt, M, Mf, O, C]
            have hfS : countAt M State.R (fun _ => false) ω 0 n State.S = O ω.1 ω.2.1 n State.S := by
              simp [countAt, M, Mf, O]
            have hfR : countAt M State.R (fun _ => false) ω 0 n State.R = O ω.1 ω.2.1 n State.R := by
              simp [countAt, M, Mf, O]
            have hpf : personalR M State.R (fun _ => false) ω 0 n ≤ 1 / 10 := by
              simp only [personalR, show M.p 0 = 3 / 4 from rfl, show M.q = 1 / 2 from rfl,
                hBUS, hfS, hfR]
              have hh := hsmall _ _ hn.1
              have heq : 1 - (3 : ℝ) ^ O ω.1 ω.2.1 n State.S /
                  (3 ^ O ω.1 ω.2.1 n State.S + 3 ^ O ω.1 ω.2.1 n State.R) =
                  3 ^ O ω.1 ω.2.1 n State.R /
                  (3 ^ O ω.1 ω.2.1 n State.S + 3 ^ O ω.1 ω.2.1 n State.R) := by field_simp; ring
              rw [heq]; exact hh
            have hpt : 9 / 10 ≤ personalR M State.R (fun _ => true) ω 0 n := by
              simp only [personalR, show M.p 0 = 3 / 4 from rfl, show M.q = 1 / 2 from rfl,
                hBUS, hcS, hcR]
              have hh := hsmall _ _ hn.2
              rw [add_comm] at hh
              linarith
            constructor
            · apply if_pos
              rw [hbel _ _ _ _ (by exact_mod_cast hn0)]
              nlinarith [(hgrid State.R (fun _ => true) ω (⌈(n : ℝ)⌉₊ - 1)).1.1]
            · apply if_neg
              rw [hbel _ _ _ _ (by exact_mod_cast hn0)]
              nlinarith [(hgrid State.R (fun _ => false) ω (⌈(n : ℝ)⌉₊ - 1)).1.2]
          have hca : ∀ yhat x i T s, Measurable (fun ω : Sample 2 => countAt M yhat x ω i T s) := by
            intro yhat x i T s
            unfold countAt
            apply Measurable.add
            · apply measurable_ncard.comp
              apply measurable_setOfPred.comp
              apply measurable_pi_lambda
              intro k
              apply measurableSet_setOfPred.mp
              exact (measurableSet_le
                (show Measurable (fun ω : Sample 2 => arrivalTime ω.2.1 M.lam k) by
                  unfold arrivalTime; fun_prop) measurable_const).inter
                (measurableSet_eq_fun (show Measurable (fun ω : Sample 2 => ω.1 (i, k)) by fun_prop)
                  measurable_const)
            · split_ifs
              · apply measurable_ncard.comp
                apply measurable_setOfPred.comp
                apply measurable_pi_lambda
                intro k
                apply measurableSet_setOfPred.mp
                apply measurableSet_le
                · unfold arrivalTime; fun_prop
                · exact measurable_const
              · exact measurable_const
          have hpm : ∀ yhat x i T, Measurable (fun ω : Sample 2 => personalR M yhat x ω i T) := by
            intro yhat x i T
            unfold personalR BUS
            fun_prop (disch := aesop)
          have hgm : ∀ y yhat x k i, Measurable (fun ω : Sample 2 => gridBeliefR M y yhat x ω k i) := by
            intro y yhat x k
            induction k with
            | zero => intro i; simp only [gridBeliefR]; exact measurable_const
            | succ k ih =>
              intro i
              simp only [gridBeliefR]
              split_ifs
              · exact measurable_const
              · fun_prop (disch := aesop)
          have hbm : ∀ y yhat x T i, Measurable (fun ω : Sample 2 => beliefR M y yhat x ω T i) := by
            intro y yhat x T i
            unfold beliefR
            split_ifs <;> fun_prop (disch := aesop)
          have hdm : ∀ y yhat x T i, Measurable (fun ω : Sample 2 => D i (beliefR M y yhat x ω T i)) := by
            intro y yhat x T i
            exact Measurable.ite (measurableSet_lt measurable_const (hbm _ _ _ _ _))
              measurable_const measurable_const
          have hdi : ∀ y yhat x T i,
              MeasureTheory.Integrable (fun ω : Sample 2 => D i (beliefR M y yhat x ω T i))
                (sampleMeasure M y) := by
            intro y yhat x T i
            apply MeasureTheory.Integrable.of_bound (hdm _ _ _ _ _).aestronglyMeasurable 1
            exact Filter.Eventually.of_forall (fun ω => by
              rw [Real.norm_eq_abs, abs_of_nonneg (hDb i _).1]
              exact (hDb i _).2)
          let I : ℝ → State → (Fin 2 → Bool) → ℝ := fun T yhat x =>
            ∫ ω, D 0 (beliefR M State.S yhat x ω T 0) ∂μ
          have hIl : Tendsto (fun n : ℕ => I n State.R (fun _ => true)) atTop (𝓝 1) ∧
              Tendsto (fun n : ℕ => I n State.R (fun _ => false)) atTop (𝓝 0) := by
            constructor
            · have hh := MeasureTheory.tendsto_integral_of_dominated_convergence
                (μ := μ) (F := fun n : ℕ => fun ω : Sample 2 =>
                  D 0 (beliefR M State.S State.R (fun _ => true) ω n 0))
                (f := fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
                (fun n => (hdm _ _ _ _ _).aestronglyMeasurable)
                (MeasureTheory.integrable_const 1)
                (fun n => Filter.Eventually.of_forall (fun ω => by
                  rw [Real.norm_eq_abs, abs_of_nonneg (hDb 0 _).1]; exact (hDb 0 _).2))
                (by
                  filter_upwards [hact] with ω hω
                  exact tendsto_const_nhds.congr' (hω.mono (fun n hn => hn.1.symm)))
              simpa only [MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul] using hh
            · have hh := MeasureTheory.tendsto_integral_of_dominated_convergence
                (μ := μ) (F := fun n : ℕ => fun ω : Sample 2 =>
                  D 0 (beliefR M State.S State.R (fun _ => false) ω n 0))
                (f := fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
                (fun n => (hdm _ _ _ _ _).aestronglyMeasurable)
                (MeasureTheory.integrable_const 1)
                (fun n => Filter.Eventually.of_forall (fun ω => by
                  rw [Real.norm_eq_abs, abs_of_nonneg (hDb 0 _).1]; exact (hDb 0 _).2))
                (by
                  filter_upwards [hact] with ω hω
                  exact tendsto_const_nhds.congr' (hω.mono (fun n hn => hn.2.symm)))
              simpa only [MeasureTheory.integral_zero] using hh
          have hfbel : ∀ y yhat ω T i,
              beliefR M y yhat (fun _ => false) ω T i =
                beliefR M y State.R (fun _ => false) ω T i := by
            have hp : ∀ yhat ω T i, personalR M yhat (fun _ => false) ω i T =
                personalR M State.R (fun _ => false) ω i T := by
              intro yhat ω T i
              simp [personalR, countAt]
            have hg : ∀ y yhat ω k i, gridBeliefR M y yhat (fun _ => false) ω k i =
                gridBeliefR M y State.R (fun _ => false) ω k i := by
              intro y yhat ω k
              induction k with
              | zero => intro i; rfl
              | succ k ih => intro i; simp only [gridBeliefR, hp, ih]
            intro y yhat ω T i
            simp only [beliefR, hp, hg]
          have hmpi : ∀ y yhat x T,
              MeasureTheory.Integrable (fun ω : Sample 2 => manipProb M T D y yhat x ω 0)
                (sampleMeasure M y) := by
            intro y yhat x T
            simp only [manipProb, hMB]
            norm_num only [Finset.mem_singleton, Fin.zero_eq_one_iff, if_false]
            split_ifs
            · simpa only [max_comm, Pi.sub_apply] using ((hdi _ _ _ _ _).sub (hdi _ _ _ _ _)).pos_part
            · simpa only [max_comm, Pi.sub_apply] using ((hdi _ _ _ _ _).sub (hdi _ _ _ _ _)).pos_part
          have hzero : ∀ (r : Fin 2 → ℝ), countLaw r 0 = (1 - r 0) * (1 - r 1) := by
            intro r
            have hs : (Finset.univ.filter fun A : Finset (Fin 2) => A.card = 0) = {∅} := by
              ext A
              simp
            unfold countLaw
            rw [hs]
            simp [Fin.prod_univ_two]
          have hcz : ∀ T y yhat x ω,
              countLaw (manipProb M T D y yhat x ω) 0 = 1 - manipProb M T D y yhat x ω 0 := by
            intro T y yhat x ω
            rw [hzero]
            have hz : manipProb M T D y yhat x ω 1 = 0 := by simp [manipProb, hMB]
            rw [hz]; ring
          have hcint : ∀ T y yhat x,
              (∫ ω, countLaw (manipProb M T D y yhat x ω) 0 ∂(sampleMeasure M y)) =
              1 - ∫ ω, manipProb M T D y yhat x ω 0 ∂(sampleMeasure M y) := by
            intro T y yhat x
            simp_rw [hcz]
            rw [MeasureTheory.integral_sub (MeasureTheory.integrable_const 1) (hmpi _ _ _ _)]
            simp
          have hpos : ∀ T y yhat x,
              0 ≤ ∫ ω, manipProb M T D y yhat x ω 0 ∂(sampleMeasure M y) := by
            intro T y yhat x
            apply MeasureTheory.integral_nonneg
            intro ω
            unfold manipProb
            split_ifs <;> positivity
          have hdiff : ∀ T yhat x,
              I T yhat x - I T State.R (fun _ => false) ≤
                ∫ ω, manipProb M T D State.S yhat x ω 0 ∂μ := by
            intro T yhat x
            dsimp only [I]
            rw [← MeasureTheory.integral_sub (hdi _ _ _ _ _) (hdi _ _ _ _ _)]
            apply MeasureTheory.integral_mono ((hdi _ _ _ _ _).sub (hdi _ _ _ _ _)) (hmpi _ _ _ _)
            intro ω
            simp only [manipProb, hMB]
            norm_num only [Finset.mem_singleton, Fin.zero_eq_one_iff, if_false]
            rw [if_neg (by decide : State.S ≠ State.R), hfbel]
            exact le_max_right _ _
          have hfilt : Finset.univ.filter (· ∉ M.B) = {0} := by rw [hMB]; decide
          have hpay : ∀ T yhat x, principalPayoff M T D State.S yhat x =
              I T yhat x - (1 / 4) * ((Finset.univ.filter fun i => x i = true).card : ℝ) := by
            intro T yhat x
            simp [principalPayoff, hfilt, I, μ, show M.ε = 1 / 4 from rfl,
              show State.S ≠ State.R by decide]
          obtain ⟨Tstar, hT⟩ := him (1 / 10) (by norm_num)
          have hlarge : ∀ᶠ n : ℕ in atTop,
              9 / 10 < I n State.R (fun _ => true) ∧
              I n State.R (fun _ => false) < 1 / 10 ∧ Tstar < (n : ℝ) := by
            filter_upwards [hIl.1.eventually (Ioi_mem_nhds (by norm_num : (9 / 10 : ℝ) < 1)),
              hIl.2.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 10)),
              (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop Tstar] with n hn1 hn2 hn3
            exact ⟨hn1, hn2, hn3⟩
          obtain ⟨n, hn1, hn2, hn3⟩ := hlarge.exists
          have hmax : ∀ y : State, ∃ a : State × (Fin 2 → Bool),
              ∀ a' : State × (Fin 2 → Bool),
                principalPayoff M n D y a'.1 a'.2 ≤ principalPayoff M n D y a.1 a.2 := by
            intro y
            exact Finite.exists_max (fun a : State × (Fin 2 → Bool) =>
              principalPayoff M n D y a.1 a.2)
          choose a ha using hmax
          let P : PrincipalStrategy 2 := fun y => PMF.pure (a y)
          have he : IsEquilibrium M n P D := by
            refine ⟨hD, ?_⟩
            intro y a' ha' a''
            have hh : a' = a y := by
              by_contra hh
              simpa [P, PMF.pure_apply, hh, Ne.symm hh] using ha'
            subst a'
            exact ha y a''
          have hbest := ha State.S (State.R, fun _ => true)
          rw [hpay, hpay] at hbest
          norm_num at hbest
          have hcost : 0 ≤ (1 / 4 : ℝ) *
              ((Finset.univ.filter fun i => (a State.S).2 i = true).card : ℝ) := by positivity
          have hsel : 2 / 5 < I n (a State.S).1 (a State.S).2 := by linarith
          have hman : 3 / 10 < ∫ ω, manipProb M n D State.S (a State.S).1 (a State.S).2 ω 0 ∂μ := by
            have hh := hdiff n (a State.S).1 (a State.S).2
            linarith
          have hgiven : ∀ y, manipLawGiven M n P D y 0 =
              ∫ ω, countLaw (manipProb M n D y (a y).1 (a y).2 ω) 0 ∂(sampleMeasure M y) := by
            intro y
            simp [manipLawGiven, P, PMF.pure_apply, apply_ite]
          have hS : manipLawGiven M n P D State.S 0 < 7 / 10 := by
            rw [hgiven, hcint]
            change 1 - (∫ ω, manipProb M n D State.S (a State.S).1 (a State.S).2 ω 0 ∂μ) < _
            linarith
          have hR : manipLawGiven M n P D State.R 0 ≤ 1 := by
            rw [hgiven, hcint]
            linarith [hpos n State.R (a State.R).1 (a State.R).2]
          have hsum : manipLaw M n P D 0 =
              (1 / 2) * manipLawGiven M n P D State.S 0 +
              (1 / 2) * manipLawGiven M n P D State.R 0 := by
            unfold manipLaw
            change (∑ y ∈ ({State.S, State.R} : Finset State), priorOf M.q y * manipLawGiven M n P D y 0) = _
            rw [Finset.sum_pair (by decide : State.S ≠ State.R)]
            norm_num [priorOf, show M.q = 1 / 2 from rfl, show State.R ≠ State.S by decide,
              show State.S ≠ State.R by decide]
          have hh := hT (n : ℝ) hn3 P D he
          change 1 - (1 / 10 : ℝ) ≤ manipLaw M n P D 0 at hh
          rw [hsum] at hh
          linarith
