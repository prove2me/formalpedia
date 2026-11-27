-- Prove2me | solution 1 for OpaquePricing.Dominance.Supplement.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:19:20.6738+00:00
-- url     : https://prove2.me/submissions/0a1a599e-ad42-4e7a-8933-b7d361ff8546

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting
import Definitions.Def_OpaquePricing_Dominance_Supplement_SinglePricing

open MeasureTheory

open OpaquePricing
open OpaquePricing.Dominance
open OpaquePricing.Dominance.Supplement

theorem solution {N : ℕ} (hN : 2 ≤ N) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ x ∂ν, 0 ≤ x) :
    optOPQ (Measure.pi (fun _ : Fin N => ν)) 1 ≤
      3 * optSP (Measure.pi (fun _ : Fin N => ν)) := by
        set μ := Measure.pi (fun _ : Fin N => ν) with hμ
        obtain ⟨A, hA⟩ : ∃ A : ℝ → Set (Fin N → ℝ),
            A = fun t => {v | ∃ i j, i ≠ j ∧ t ≤ v i ∧ t ≤ v j} := ⟨_, rfl⟩
        obtain ⟨B, hB⟩ : ∃ B : ℝ → Set (Fin N → ℝ),
            B = fun t => {v | ∃ i, t ≤ v i} := ⟨_, rfl⟩
        have hBm : ∀ t, MeasurableSet (B t) := by
          intro t
          have : B t = ⋃ i, {v : Fin N → ℝ | t ≤ v i} := by ext v; simp [hB]
          rw [this]
          exact MeasurableSet.iUnion fun i => measurableSet_le measurable_const (measurable_pi_apply i)
        have hAm : ∀ t, MeasurableSet (A t) := by
          intro t
          have : A t = ⋃ i, ⋃ j, ({v : Fin N → ℝ | i ≠ j} ∩ {v | t ≤ v i} ∩ {v | t ≤ v j}) := by
            ext v; simp [hA, and_assoc]
          rw [this]
          exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j =>
            ((MeasurableSet.const _).inter (measurableSet_le measurable_const (measurable_pi_apply i))).inter
              (measurableSet_le measurable_const (measurable_pi_apply j))
        have hCm : MeasurableSet {z : (Fin N → ℝ) × ℝ | z.1 ∈ A z.2} := by
          have : {z : (Fin N → ℝ) × ℝ | z.1 ∈ A z.2} = ⋃ i, ⋃ j,
              ({z : (Fin N → ℝ) × ℝ | i ≠ j} ∩ {z | z.2 ≤ z.1 i} ∩ {z | z.2 ≤ z.1 j}) := by
            ext z; simp [hA, and_assoc]
          rw [this]
          exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j =>
            ((MeasurableSet.const _).inter (measurableSet_le measurable_snd
              ((measurable_pi_apply i).comp measurable_fst))).inter
              (measurableSet_le measurable_snd ((measurable_pi_apply j).comp measurable_fst))
        have hSP : ∀ t, 0 ≤ t → ENNReal.ofReal t * μ (B t) ≤ optSP μ := by
          intro t ht
          have : expSP μ t = ENNReal.ofReal t * μ (B t) := by simp [expSP, hB]
          rw [← this]
          exact le_iSup₂ (f := fun p (_ : 0 ≤ p) => expSP μ p) t ht
        have hAB : ∀ t, μ (A t) ≤ μ (B t) ^ 2 := by
          intro t
          set x := ν (Set.Ici t) with hx
          set y := ν (Set.Iio t) with hy
          have hxy : x + y = 1 := by
            have := measure_add_measure_compl (μ := ν) (measurableSet_Ici (a := t))
            rwa [Set.compl_Ici, measure_univ] at this
          have hBc : (B t)ᶜ = Set.pi Set.univ (fun _ : Fin N => Set.Iio t) := by
            ext v; simp [hB]
          have hμBc : μ (B t)ᶜ = y ^ N := by
            rw [hBc, hμ, Measure.pi_pi]; simp [hy]
          obtain ⟨E, hE⟩ : ∃ E : Fin N → Set (Fin N → ℝ),
              E = fun i => Set.pi Set.univ (fun j => if j = i then Set.Ici t else Set.Iio t) :=
            ⟨_, rfl⟩
          have hEm : ∀ i, MeasurableSet (E i) := by
            intro i; rw [hE]
            exact MeasurableSet.univ_pi fun j => by
              split_ifs
              · exact measurableSet_Ici
              · exact measurableSet_Iio
          have hμE : ∀ i, μ (E i) = x * y ^ (N - 1) := by
            intro i
            rw [hE, hμ, Measure.pi_pi, Fintype.prod_eq_mul_prod_compl i]
            simp only [if_pos rfl]
            congr 1
            rw [Finset.prod_congr rfl (g := fun _ => y) (fun j hj => by
              simp only [Finset.mem_compl, Finset.mem_singleton] at hj; simp [hj, hy])]
            simp [Finset.card_compl]
          have hEdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin N))) E := by
            intro i _ j _ hij
            rw [Function.onFun, Set.disjoint_left]
            intro v hvi hvj
            rw [hE] at hvi hvj
            have h1 := hvi i (Set.mem_univ _)
            have h2 := hvj i (Set.mem_univ _)
            simp [hij] at h1 h2
            linarith
          have hBEdisj : Disjoint (B t)ᶜ (⋃ i ∈ (Finset.univ : Finset (Fin N)), E i) := by
            rw [Set.disjoint_left]
            intro v hv hv'
            simp only [Set.mem_iUnion, Finset.mem_univ, exists_true_left] at hv'
            obtain ⟨i, hi⟩ := hv'
            rw [hE] at hi
            have h1 := hi i (Set.mem_univ _)
            simp at h1
            exact hv (by rw [hB]; exact ⟨i, h1⟩)
          have hsub : (B t)ᶜ ∪ (⋃ i ∈ (Finset.univ : Finset (Fin N)), E i) ⊆ (A t)ᶜ := by
            intro v hv
            rcases hv with hv | hv
            · intro hvA
              rw [hA] at hvA
              obtain ⟨i, j, _, hi, _⟩ := hvA
              exact hv (by rw [hB]; exact ⟨i, hi⟩)
            · simp only [Set.mem_iUnion, Finset.mem_univ, exists_true_left] at hv
              obtain ⟨k, hk⟩ := hv
              intro hvA
              rw [hA] at hvA
              obtain ⟨i, j, hij, hi, hj⟩ := hvA
              rw [hE] at hk
              have h1 := hk i (Set.mem_univ _)
              have h2 := hk j (Set.mem_univ _)
              by_cases hik : i = k
              · subst hik
                simp only [if_neg (Ne.symm hij), Set.mem_Iio] at h2
                linarith
              · simp only [if_neg hik, Set.mem_Iio] at h1
                linarith
          have hle : y ^ N + N * (x * y ^ (N - 1)) ≤ μ (A t)ᶜ := by
            calc y ^ N + N * (x * y ^ (N - 1))
                = μ ((B t)ᶜ ∪ (⋃ i ∈ (Finset.univ : Finset (Fin N)), E i)) := by
                  rw [measure_union hBEdisj (Finset.measurableSet_biUnion _ (fun i _ => hEm i)),
                    measure_biUnion_finset hEdisj (fun i _ => hEm i), hμBc]
                  simp [hμE]
              _ ≤ μ (A t)ᶜ := measure_mono hsub
          have hA1 : μ (A t) + μ (A t)ᶜ = 1 := by
            rw [measure_add_measure_compl (hAm t), measure_univ]
          have hB1 : μ (B t) + μ (B t)ᶜ = 1 := by
            rw [measure_add_measure_compl (hBm t), measure_univ]
          have fin : ∀ s, μ s ≠ ⊤ := fun s => measure_ne_top μ s
          have finν : ∀ s, ν s ≠ ⊤ := fun s => measure_ne_top ν s
          rw [← ENNReal.toReal_le_toReal (fin _) (by simp [fin]), ENNReal.toReal_pow]
          have rA1 := congrArg ENNReal.toReal hA1
          have rB1 := congrArg ENNReal.toReal hB1
          have rxy := congrArg ENNReal.toReal hxy
          have rle := ENNReal.toReal_mono (fin _) hle
          rw [ENNReal.toReal_add (fin _) (fin _)] at rA1 rB1
          rw [ENNReal.toReal_add (finν _) (finν _)] at rxy
          have hyfin : y ≠ ⊤ := finν _
          have hxfin : x ≠ ⊤ := finν _
          rw [ENNReal.toReal_add (ENNReal.pow_ne_top hyfin) (ENNReal.mul_ne_top
            (ENNReal.natCast_ne_top N) (ENNReal.mul_ne_top hxfin (ENNReal.pow_ne_top hyfin))),
            ENNReal.toReal_mul,
            ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_natCast] at rle
          rw [hμBc, ENNReal.toReal_pow] at rB1
          simp only [ENNReal.toReal_one] at rA1 rB1 rxy
          set X := x.toReal
          set Y := y.toReal
          set Z := Y ^ N with hZ
          set W := Y ^ (N - 1) with hW
          have hY0 : 0 ≤ Y := ENNReal.toReal_nonneg
          have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
          have hY1 : Y ≤ 1 := by linarith
          have hYN : Z = W * Y := by rw [hZ, hW, ← pow_succ]; congr 1; omega
          have hbern : 1 - Z ≤ N * X := by
            have := one_add_mul_le_pow (a := Y - 1) (by linarith) N
            rw [add_sub_cancel] at this
            have : X = 1 - Y := by linarith
            rw [this]; linarith
          have hZ1 : Z ≤ 1 := pow_le_one₀ hY0 hY1
          have hW0 : 0 ≤ W := pow_nonneg hY0 _
          have k1 : Y * (1 - Z) ≤ N * X :=
            le_trans (mul_le_of_le_one_left (by linarith) hY1) hbern
          have k2 : W * (Y * (1 - Z)) ≤ W * (N * X) := mul_le_mul_of_nonneg_left k1 hW0
          have k3 : W * (Y * (1 - Z)) = Z - Z ^ 2 := by rw [hYN]; ring
          have hb : (μ (B t)).toReal = 1 - Z := by linarith
          rw [hb]
          nlinarith
        have hint : ∫⁻ t in Set.Ioi 0, μ (A t) ≤ 2 * optSP μ := by
          by_cases hR : optSP μ = ⊤
          · rw [hR]; simp
          set r := (optSP μ).toReal with hr
          have hRr : optSP μ = ENNReal.ofReal r := (ENNReal.ofReal_toReal hR).symm
          have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
          have hbnd : ∀ t, 0 < t → μ (A t) ≤ ENNReal.ofReal (r ^ 2 * t ^ (-2 : ℝ)) := by
            intro t ht
            have h1 : μ (B t) ≤ ENNReal.ofReal (r / t) := by
              rw [ENNReal.ofReal_div_of_pos ht, ENNReal.le_div_iff_mul_le (Or.inl (by simpa using ht))
                (Or.inl ENNReal.ofReal_ne_top), mul_comm, ← hRr]
              exact hSP t ht.le
            have h2 : r ^ 2 * t ^ (-2 : ℝ) = (r / t) ^ 2 := by
              rw [Real.rpow_neg ht.le, Real.rpow_two]; field_simp
            rw [h2, ENNReal.ofReal_pow (div_nonneg hr0 ht.le)]
            exact le_trans (hAB t) (pow_le_pow_left₀ zero_le h1 2)
          rw [← Set.Ioc_union_Ioi_eq_Ioi hr0]
          refine le_trans (lintegral_union_le _ _ _) ?_
          have hI1 : ∫⁻ t in Set.Ioc 0 r, μ (A t) ≤ ENNReal.ofReal r := by
            calc ∫⁻ t in Set.Ioc 0 r, μ (A t) ≤ ∫⁻ t in Set.Ioc 0 r, 1 :=
                  lintegral_mono fun t => prob_le_one
              _ = ENNReal.ofReal r := by simp [Real.volume_Ioc]
          have hI2 : ∫⁻ t in Set.Ioi r, μ (A t) ≤ ENNReal.ofReal r := by
            calc ∫⁻ t in Set.Ioi r, μ (A t)
                ≤ ∫⁻ t in Set.Ioi r, ENNReal.ofReal (r ^ 2 * t ^ (-2 : ℝ)) := by
                  apply lintegral_mono_ae
                  exact ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
                    hbnd t (lt_of_le_of_lt hr0 ht)
              _ = ENNReal.ofReal r := by
                  rcases hr0.lt_or_eq with hrpos | hrz
                  · rw [← ofReal_integral_eq_lintegral_ofReal]
                    · congr 1
                      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hrpos]
                      have : r ^ ((-2 : ℝ) + 1) = r⁻¹ := by
                        norm_num [Real.rpow_neg_one]
                      rw [this]; field_simp; ring
                    · exact (integrableOn_Ioi_rpow_of_lt (by norm_num) hrpos).const_mul (r ^ 2)
                    · exact ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
                        have : 0 < t := lt_trans hrpos ht
                        simp only [Pi.zero_apply]
                        positivity
                  · rw [← hrz]; simp
          rw [hRr, two_mul]
          exact add_le_add hI1 hI2
        have hpt : ∀ p : ℝ, ∀ q : ℕ → ℝ, 0 ≤ p → (∀ k, 0 ≤ q k) → ∀ v,
            ENNReal.ofReal (opqRevenue pessValue p q v) ≤
              (B p).indicator (fun _ => ENNReal.ofReal p) v +
                ∫⁻ t in Set.Ioo 0 p, (A t).indicator 1 v := by
          intro p q hp hq v
          unfold opqRevenue menuRevenue
          dsimp only
          split_ifs with h
          · obtain ⟨S, hS, hSeq⟩ := Finset.exists_mem_eq_sup' h (opqPrice p q)
            rw [hSeq]
            simp only [Finset.mem_filter, opqOptions, Finset.mem_univ, true_and] at hS
            obtain ⟨hne, h0, hmax⟩ := hS
            by_cases hc : S.card = 1
            · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hc
              have hpr : opqPrice p q {i} = p := by simp [opqPrice]
              have hpv : pessValue v {i} = v i := by simp [pessValue]
              rw [hpr, hpv] at h0
              rw [hpr]
              have hvB : v ∈ B p := by rw [hB]; exact ⟨i, by linarith⟩
              rw [Set.indicator_of_mem hvB]
              exact le_add_right le_rfl
            · have hpr : opqPrice p q S = q S.card := by simp [opqPrice, hc]
              have hpv : pessValue v S = S.inf' hne v := by simp [pessValue, hne]
              rw [hpr, hpv] at h0
              rw [hpr]
              have h1 : 1 < S.card := by
                have := hne.card_pos; omega
              obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h1
              have hqp : q S.card ≤ p := by
                have := hmax {a} (Finset.singleton_nonempty a)
                have hpr' : opqPrice p q {a} = p := by simp [opqPrice]
                have hpv' : pessValue v {a} = v a := by simp [pessValue]
                rw [hpr', hpv', hpr, hpv] at this
                have := Finset.inf'_le v ha
                linarith
              have hqa : q S.card ≤ v a := le_trans (by linarith) (Finset.inf'_le v ha)
              have hqb : q S.card ≤ v b := le_trans (by linarith) (Finset.inf'_le v hb)
              refine le_add_left ?_
              calc ENNReal.ofReal (q S.card) = ∫⁻ t in Set.Ioo 0 (q S.card), 1 := by
                    simp [Real.volume_Ioo]
                _ = ∫⁻ t in Set.Ioo 0 (q S.card), (A t).indicator 1 v := by
                    apply setLIntegral_congr_fun measurableSet_Ioo
                    intro t ht
                    have : v ∈ A t := by
                      rw [hA]; exact ⟨a, b, hab, by linarith [ht.2], by linarith [ht.2]⟩
                    simp [Set.indicator_of_mem this]
                _ ≤ ∫⁻ t in Set.Ioo 0 p, (A t).indicator 1 v :=
                    lintegral_mono_set (Set.Ioo_subset_Ioo_right hqp)
          · simp
        -- main
        apply iSup_le; intro p; apply iSup_le; intro q; apply iSup_le; intro hpq
        obtain ⟨hp, hq⟩ := hpq
        have hE : expOPQ μ 1 p q = ∫⁻ v, ENNReal.ofReal (opqRevenue pessValue p q v) ∂μ := by
          rw [expOPQ]; norm_num
        rw [hE]
        calc ∫⁻ v, ENNReal.ofReal (opqRevenue pessValue p q v) ∂μ
            ≤ ∫⁻ v, ((B p).indicator (fun _ => ENNReal.ofReal p) v +
                ∫⁻ t in Set.Ioo 0 p, (A t).indicator 1 v) ∂μ := lintegral_mono (hpt p q hp hq)
          _ = ENNReal.ofReal p * μ (B p) + ∫⁻ t in Set.Ioo 0 p, μ (A t) := by
              rw [lintegral_add_left ((measurable_const.indicator (hBm p))),
                lintegral_indicator_const (hBm p)]
              congr 1
              rw [lintegral_lintegral_swap]
              · apply lintegral_congr; intro t
                exact lintegral_indicator_one (hAm t)
              · have : Function.uncurry (fun v t => (A t).indicator (1 : (Fin N → ℝ) → ENNReal) v)
                    = {z : (Fin N → ℝ) × ℝ | z.1 ∈ A z.2}.indicator 1 := by
                  rfl
                rw [this]
                exact (measurable_one.indicator hCm).aemeasurable
          _ ≤ optSP μ + 2 * optSP μ := by
              gcongr
              · exact hSP p hp
              · exact le_trans (lintegral_mono_set Set.Ioo_subset_Ioi_self) hint
          _ = 3 * optSP μ := by ring
