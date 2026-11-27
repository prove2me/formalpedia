-- Prove2me | solution 1 for SPPRevenue.SingleUnit.Supplement.lemma_2_6
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:12:44.417782+00:00
-- url     : https://prove2.me/submissions/e6014d8b-01fb-4052-8575-c5dc710ee77d

import Mathlib
import Definitions.Def_SPPRevenue_SingleUnit_Setting
import Definitions.Def_SPPRevenue_SingleUnit_Supplement_Programs
import Definitions.Def_SPPRevenue_SingleUnit_Supplement_EspProgram

open SPPRevenue
open SPPRevenue.SingleUnit
open SPPRevenue.SingleUnit.Supplement

open MeasureTheory
open scoped ENNReal

theorem solution {n : ℕ} (hn : 1 ≤ n) (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (t : Fin n → (Fin n → ℝ) → ℝ) (ht : IsThresholdMech μ t) (τ : ℝ) (hτ : 0 ≤ τ) :
    2 * resampleLaw μ {x | ZTau t τ x = 0} + resampleLaw μ {x | ZTau t τ x = 1} ≤
        ENNReal.ofReal (rn n (sStar μ t τ).toReal) ∧
      rn n (sStar μ t τ).toReal ≤ rLim (sStar μ t τ).toReal ∧
      Filter.Tendsto (fun N : ℕ => rn N (sStar μ t τ).toReal) Filter.atTop
        (nhds (rLim (sStar μ t τ).toReal)) := by
          have hprod : ∀ (N : ℕ) (k : Fin N) (c d : ℝ), ∏ l, (if l = k then c else d) = c * d ^ (N - 1) := by
            intro N k c d
            rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), if_pos rfl,
              Finset.prod_congr rfl (fun l hl => if_neg (Finset.ne_of_mem_erase hl)), Finset.prod_const,
              Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
          have hBins : ∀ (N : ℕ) (p : Fin N → ℝ) (T : Finset (Fin N)) (i : Fin N), i ∉ T →
              ∑ k ∈ insert i T, ∏ l ∈ insert i T, (if l = k then p l else 1 - p l) =
                p i * ∏ l ∈ T, (1 - p l) + (1 - p i) * ∑ k ∈ T, ∏ l ∈ T, (if l = k then p l else 1 - p l) := by
            intro N p T i hi
            rw [Finset.sum_insert hi, Finset.prod_insert hi, if_pos rfl, Finset.mul_sum]
            congr 1
            · congr 1
              exact Finset.prod_congr rfl (fun l hl => if_neg (fun (h : l = i) => hi (h ▸ hl)))
            · refine Finset.sum_congr rfl (fun k hk => ?_)
              rw [Finset.prod_insert hi, if_neg (fun (h : i = k) => hi (h ▸ hk))]
          have hBnn : ∀ (N : ℕ) (p : Fin N → ℝ) (T : Finset (Fin N)), (∀ i, 0 ≤ p i ∧ p i ≤ 1) →
              0 ≤ ∑ k ∈ T, ∏ l ∈ T, (if l = k then p l else 1 - p l) := by
            intro N p T hp
            refine Finset.sum_nonneg (fun k _ => Finset.prod_nonneg (fun l _ => ?_))
            split_ifs
            · exact (hp l).1
            · linarith [(hp l).2]
          have key : ∀ (N : ℕ) (p : Fin N → ℝ), (∀ i, 0 ≤ p i ∧ p i ≤ 1) →
              2 * ∏ i, (1 - p i) + ∑ k, ∏ l, (if l = k then p l else 1 - p l) ≤ rn N (∑ i, p i) := by
            intro N p0 hp0
            rcases Nat.eq_zero_or_pos N with hN | hN
            · subst hN; simp [rn]
            have hNr : (0 : ℝ) < N := by exact_mod_cast hN
            set m : ℝ := (∑ i, p0 i) / N with hm
            have main : ∀ c : ℕ, ∀ p : Fin N → ℝ, (∀ i, 0 ≤ p i ∧ p i ≤ 1) → ∑ i, p i = N * m →
                (Finset.univ.filter (fun i => p i ≠ m)).card = c →
                2 * ∏ i, (1 - p i) + ∑ k, ∏ l, (if l = k then p l else 1 - p l) ≤
                  2 * (1 - m) ^ N + N * m * (1 - m) ^ (N - 1) := by
              intro c
              induction c using Nat.strong_induction_on with
              | _ c ih =>
              intro p hp hsum hc
              by_cases hall : ∀ i, p i = m
              · have : p = fun _ => m := funext hall
                subst this
                simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
                rw [Finset.sum_congr rfl (fun k _ => hprod N k m (1 - m))]
                simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
                ring_nf; rfl
              push Not at hall
              obtain ⟨i0, hi0⟩ := hall
              have hlo : ∃ i, p i < m := by
                by_contra h
                push Not at h
                have : ∑ i : Fin N, m < ∑ i, p i :=
                  Finset.sum_lt_sum (fun i _ => h i) ⟨i0, Finset.mem_univ _, lt_of_le_of_ne (h i0) (Ne.symm hi0)⟩
                simp at this; linarith
              have hhi : ∃ j, m < p j := by
                by_contra h
                push Not at h
                have : ∑ i, p i < ∑ i : Fin N, m :=
                  Finset.sum_lt_sum (fun i _ => h i) ⟨i0, Finset.mem_univ _, lt_of_le_of_ne (h i0) hi0⟩
                simp at this; linarith
              obtain ⟨i, hi⟩ := hlo
              obtain ⟨j, hj⟩ := hhi
              have hij : i ≠ j := by intro h; subst h; linarith
              set p' : Fin N → ℝ := Function.update (Function.update p i m) j (p i + p j - m) with hp'
              have hp'j : p' j = p i + p j - m := by simp [p']
              have hp'i : p' i = m := by simp [p', Function.update_apply, hij]
              have hp'o : ∀ l, l ≠ i → l ≠ j → p' l = p l := by
                intro l hli hlj; simp [p', Function.update_apply, hli, hlj]
              set S : Finset (Fin N) := (Finset.univ.erase i).erase j with hS
              have hjS : j ∉ S := by simp [S]
              have hiS : i ∉ insert j S := by simp [S, hij]
              have huniv : (Finset.univ : Finset (Fin N)) = insert i (insert j S) := by
                ext l; by_cases h1 : l = i <;> by_cases h2 : l = j <;> simp [S, h1, h2]
              have hSo : ∀ l ∈ S, p' l = p l := by
                intro l hl; simp [S] at hl; exact hp'o l hl.2 hl.1
              have hAS : ∏ l ∈ S, (1 - p' l) = ∏ l ∈ S, (1 - p l) :=
                Finset.prod_congr rfl (fun l hl => by rw [hSo l hl])
              have hBS : ∑ k ∈ S, ∏ l ∈ S, (if l = k then p' l else 1 - p' l) =
                  ∑ k ∈ S, ∏ l ∈ S, (if l = k then p l else 1 - p l) :=
                Finset.sum_congr rfl (fun k _ => Finset.prod_congr rfl (fun l hl => by rw [hSo l hl]))
              have hp'b : ∀ l, 0 ≤ p' l ∧ p' l ≤ 1 := by
                intro l
                by_cases h1 : l = j
                · subst h1; rw [hp'j]; constructor <;> linarith [hp i, hp l]
                by_cases h2 : l = i
                · subst h2; rw [hp'i]; constructor <;> linarith [hp l, hp j]
                rw [hp'o l h2 h1]; exact hp l
              have hsum' : ∑ l, p' l = N * m := by
                rw [← hsum, huniv, Finset.sum_insert hiS, Finset.sum_insert hjS, Finset.sum_insert hiS,
                  Finset.sum_insert hjS, hp'i, hp'j, Finset.sum_congr rfl hSo]
                ring
              have hcard : (Finset.univ.filter (fun l => p' l ≠ m)).card < c := by
                rw [← hc]
                apply Finset.card_lt_card
                refine Finset.ssubset_iff_of_subset ?_ |>.2 ⟨i, by simp; linarith, by simp [hp'i]⟩
                intro l hl
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
                by_cases h1 : l = j
                · subst h1; linarith
                by_cases h2 : l = i
                · subst h2; exact absurd hp'i hl
                rwa [hp'o l h2 h1] at hl
              refine le_trans ?_ (ih _ hcard p' hp'b hsum' rfl)
              rw [huniv, Finset.prod_insert hiS, Finset.prod_insert hjS, Finset.prod_insert hiS,
                Finset.prod_insert hjS, hBins N p _ i hiS, hBins N p S j hjS, hBins N p' _ i hiS,
                hBins N p' S j hjS, Finset.prod_insert hjS, Finset.prod_insert hjS, hAS, hBS, hp'i, hp'j]
              have hB0 := hBnn N p S hp
              have hm1 : 0 ≤ (m - p i) * (p j - m) := mul_nonneg (by linarith) (by linarith)
              nlinarith [mul_nonneg hB0 hm1]
            have := main _ p0 hp0 (by rw [hm]; field_simp) rfl
            have hm' : (∑ i, p0 i) / N = m := rfl
            unfold rn
            rw [hm']
            have : (∑ i, p0 i) = N * m := by rw [hm]; field_simp
            rw [this]; linarith
          have mono : ∀ N : ℕ, 1 ≤ N → ∀ y : ℝ, 0 ≤ y → y ≤ N → rn N y ≤ rn (N + 1) y := by
            intro N hN y hy0 hyN
            have hNr : (0 : ℝ) < N := by exact_mod_cast hN
            have hyN' : y / N ≤ 1 := by rw [div_le_one hNr]; exact hyN
            have hy' : 0 ≤ y / N := div_nonneg hy0 hNr.le
            set p : Fin (N + 1) → ℝ := fun i => if (i : ℕ) < N then y / N else 0 with hpdef
            have hpb : ∀ i, 0 ≤ p i ∧ p i ≤ 1 := by
              intro i; simp only [p]; split_ifs <;> constructor <;> linarith
            have h := key (N + 1) p hpb
            have hs : ∑ i, p i = y := by
              simp [p, Fin.sum_univ_castSucc]; field_simp
            have hF : 2 * ∏ i, (1 - p i) + ∑ k, ∏ l, (if l = k then p l else 1 - p l) = rn N y := by
              simp only [p, Fin.sum_univ_castSucc, Fin.prod_univ_castSucc, Fin.val_castSucc, Fin.is_lt,
                if_true, Fin.val_last, lt_irrefl, if_false, Fin.castSucc_inj, sub_zero, mul_one]
              simp only [Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm, if_false, mul_one, mul_zero,
                add_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
              rw [Finset.sum_congr rfl (fun k _ => hprod N k (y / N) (1 - y / N))]
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, rn]
              field_simp
            rw [hF, hs] at h; exact h
          have tend : ∀ y : ℝ, Filter.Tendsto (fun N : ℕ => rn N y) Filter.atTop (nhds (rLim y)) := by
            intro y
            have h1 : Filter.Tendsto (fun N : ℕ => (1 - y / N) ^ N) Filter.atTop (nhds (Real.exp (-y))) := by
              have := Real.tendsto_one_add_div_pow_exp (-y)
              refine this.congr (fun N => ?_)
              ring_nf
            have h2 : Filter.Tendsto (fun N : ℕ => 1 - y / N) Filter.atTop (nhds 1) := by
              have : Filter.Tendsto (fun N : ℕ => y / (N : ℝ)) Filter.atTop (nhds 0) :=
                tendsto_const_div_atTop_nhds_zero_nat y
              simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this
            have h3 : Filter.Tendsto (fun N : ℕ => (1 - y / N) ^ (N - 1)) Filter.atTop
                (nhds (Real.exp (-y))) := by
              have := h1.div h2 one_ne_zero
              rw [div_one] at this
              refine this.congr' ?_
              have hev := h2.eventually (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
              filter_upwards [hev, Filter.eventually_ge_atTop 1] with N hN hN1
              show (1 - y / N) ^ N / (1 - y / N) = _
              rw [div_eq_iff hN.ne']
              rw [← pow_succ, Nat.sub_add_cancel hN1]
            have := (h1.const_mul 2).add (h3.const_mul y)
            have h4 : rLim y = 2 * Real.exp (-y) + y * Real.exp (-y) := by unfold rLim; ring
            rw [h4]; exact this.congr (fun N => rfl)
          have bound : ∀ y : ℝ, 0 ≤ y → y ≤ n → rn n y ≤ rLim y := by
            intro y hy0 hyn
            refine ge_of_tendsto (tend y) (Filter.eventually_atTop.2 ⟨n, fun N hN => ?_⟩)
            induction N, hN using Nat.le_induction with
            | base => exact le_rfl
            | succ N hN ih =>
              exact ih.trans (mono N (hn.trans hN) y hy0 (hyn.trans (by exact_mod_cast hN)))
          -- probabilistic part
          set E : Fin n → Set ((Fin n → ℝ) × ℝ) := fun i => {z | t i z.1 ≤ z.2 ∧ τ ≤ t i z.1} with hEdef
          have hEm : ∀ i, MeasurableSet (E i) := by
            intro i
            exact (measurableSet_le ((ht.measurable i).comp measurable_fst) measurable_snd).inter
              (measurableSet_le measurable_const ((ht.measurable i).comp measurable_fst))
          have hEP : ∀ i, ((Measure.pi μ).prod (μ i)) (E i) = sStarI μ t i τ := by
            intro i
            have hφ : Measurable (fun z : (Fin n → ℝ) × ℝ => Function.update z.1 i z.2) :=
              measurable_update'
            have hmap : ((Measure.pi μ).prod (μ i)).map (fun z : (Fin n → ℝ) × ℝ => Function.update z.1 i z.2)
                = Measure.pi μ := by
              refine (Measure.pi_eq (fun s hs => ?_)).symm
              rw [Measure.map_apply hφ (MeasurableSet.univ_pi hs)]
              have hpre : (fun z : (Fin n → ℝ) × ℝ => Function.update z.1 i z.2) ⁻¹' (Set.univ.pi s) =
                  (Set.univ.pi (Function.update s i Set.univ)) ×ˢ s i := by
                ext z
                simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
                constructor
                · intro h
                  refine ⟨fun j => ?_, by simpa using h i⟩
                  by_cases hj : j = i
                  · subst hj; simp
                  · have := h j; rw [Function.update_of_ne hj] at this; rw [Function.update_of_ne hj]; exact this
                · rintro ⟨h1, h2⟩ j
                  by_cases hj : j = i
                  · subst hj; simpa using h2
                  · have := h1 j; rw [Function.update_of_ne hj] at this; rw [Function.update_of_ne hj]; exact this
              rw [hpre, Measure.prod_prod, Measure.pi_pi]
              have hfun : (fun j => μ j (Function.update s i Set.univ j)) =
                  Function.update (fun j => μ j (s j)) i 1 := by
                funext j
                by_cases hj : j = i
                · subst hj; simp
                · simp [Function.update_of_ne hj]
              rw [hfun, Finset.prod_update_of_mem (Finset.mem_univ i),
                Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i) (fun j => μ j (s j))]
              ring
            have hS : MeasurableSet {v : Fin n → ℝ | t i v ≤ v i ∧ τ ≤ t i v} :=
              (measurableSet_le (ht.measurable i) (measurable_pi_apply i)).inter
                (measurableSet_le measurable_const (ht.measurable i))
            unfold sStarI
            conv_rhs => rw [← hmap, Measure.map_apply hφ hS]
            congr 1
            show E i = _
            ext z
            have hti : t i (Function.update z.1 i z.2) = t i z.1 :=
              ht.indep_own i _ _ (fun j hj => Function.update_of_ne hj _ _)
            simp [E, hti]
          set P : Fin n → ℝ≥0∞ := fun i => sStarI μ t i τ with hPdef
          have hPle : ∀ i, P i ≤ 1 := by
            intro i; rw [hPdef]; simp only; rw [← hEP i]; exact prob_le_one
          have hPne : ∀ i, P i ≠ ⊤ := fun i => ne_top_of_le_ne_top ENNReal.one_ne_top (hPle i)
          set p : Fin n → ℝ := fun i => (P i).toReal with hpdef
          have hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1 := by
            intro i
            refine ⟨ENNReal.toReal_nonneg, ?_⟩
            have := ENNReal.toReal_mono ENNReal.one_ne_top (hPle i)
            simpa using this
          have hPp : ∀ i, P i = ENNReal.ofReal (p i) := fun i => (ENNReal.ofReal_toReal (hPne i)).symm
          have hs : (sStar μ t τ).toReal = ∑ i, p i := by
            unfold sStar
            rw [ENNReal.toReal_sum (fun i _ => hPne i)]
          have hs0 : 0 ≤ ∑ i, p i := Finset.sum_nonneg (fun i _ => (hp i).1)
          have hsn : ∑ i, p i ≤ n := by
            calc ∑ i, p i ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => (hp i).2)
              _ = n := by simp
          refine ⟨?_, ?_, ?_⟩
          rotate_left
          · rw [hs]; exact bound _ hs0 hsn
          · exact tend _
          have hmp := measurePreserving_arrowProdEquivProdArrow (Fin n → ℝ) ℝ (Fin n)
            (fun _ => Measure.pi μ) μ
          have hR : ∀ A, resampleLaw μ A = (Measure.pi fun i => (Measure.pi μ).prod (μ i))
              ((MeasurableEquiv.arrowProdEquivProdArrow (Fin n → ℝ) ℝ (Fin n)) ⁻¹' A) := by
            intro A
            rw [hmp.measure_preimage_equiv A]; rfl
          have happ : ∀ (y : Fin n → (Fin n → ℝ) × ℝ),
              MeasurableEquiv.arrowProdEquivProdArrow (Fin n → ℝ) ℝ (Fin n) y =
                (fun i => (y i).1, fun i => (y i).2) := fun y => rfl
          have hZ0 : (MeasurableEquiv.arrowProdEquivProdArrow (Fin n → ℝ) ℝ (Fin n)) ⁻¹'
              {x | ZTau t τ x = 0} = Set.univ.pi (fun i => (E i)ᶜ) := by
            ext y
            simp only [Set.mem_preimage, Set.mem_setOf_eq, happ, ZTau, Finset.card_eq_zero,
              Finset.filter_eq_empty_iff, Set.mem_univ_pi, Set.mem_compl_iff, E, Finset.mem_univ,
              true_implies]
          have hZ1 : (MeasurableEquiv.arrowProdEquivProdArrow (Fin n → ℝ) ℝ (Fin n)) ⁻¹'
              {x | ZTau t τ x = 1} = ⋃ i, Set.univ.pi (fun j => if j = i then E j else (E j)ᶜ) := by
            ext y
            simp only [Set.mem_preimage, Set.mem_setOf_eq, happ, ZTau, Finset.card_eq_one,
              Set.mem_iUnion, Set.mem_univ_pi]
            constructor
            · rintro ⟨a, ha⟩
              refine ⟨a, fun j => ?_⟩
              have hj := congrArg (fun S => j ∈ S) ha
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
                eq_iff_iff] at hj
              split_ifs with h
              · exact hj.2 h
              · exact fun h' => h (hj.1 h')
            · rintro ⟨a, ha⟩
              refine ⟨a, Finset.ext (fun j => ?_)⟩
              have hj := ha j
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
              constructor
              · intro h'
                by_contra hne
                rw [if_neg hne] at hj
                exact hj h'
              · intro h; subst h; rw [if_pos rfl] at hj; exact hj
          have hm0 : resampleLaw μ {x | ZTau t τ x = 0} = ∏ i, (1 - P i) := by
            rw [hR, hZ0, Measure.pi_pi]
            refine Finset.prod_congr rfl (fun i _ => ?_)
            rw [prob_compl_eq_one_sub (hEm i), hEP i]
          have hm1 : resampleLaw μ {x | ZTau t τ x = 1} = ∑ i, ∏ j, (if j = i then P j else 1 - P j) := by
            rw [hR, hZ1, measure_iUnion, tsum_fintype]
            · refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [Measure.pi_pi]
              refine Finset.prod_congr rfl (fun j _ => ?_)
              split_ifs
              · exact hEP j
              · rw [prob_compl_eq_one_sub (hEm j), hEP j]
            · intro i i' hii'
              rw [Function.onFun, Set.disjoint_left]
              intro y h1 h2
              rw [Set.mem_univ_pi] at h1 h2
              have a1 := h1 i
              have a2 := h2 i
              rw [if_pos rfl] at a1
              rw [if_neg hii'] at a2
              exact a2 a1
            · intro i
              refine MeasurableSet.univ_pi (fun j => ?_)
              split_ifs
              · exact hEm j
              · exact (hEm j).compl
          have h1sub : ∀ j, 1 - P j = ENNReal.ofReal (1 - p j) := by
            intro j
            rw [hPp j, ENNReal.ofReal_sub _ (hp j).1, ENNReal.ofReal_one]
          have hite : ∀ i j, (if j = i then P j else 1 - P j) =
              ENNReal.ofReal (if j = i then p j else 1 - p j) := by
            intro i j
            split_ifs
            · exact hPp j
            · exact h1sub j
          have hnn : ∀ i j, 0 ≤ (if j = i then p j else 1 - p j) := by
            intro i j; split_ifs
            · exact (hp j).1
            · linarith [(hp j).2]
          rw [hm0, hm1, Finset.prod_congr rfl (fun j _ => h1sub j),
            Finset.sum_congr rfl (fun i _ => Finset.prod_congr rfl (fun j _ => hite i j)),
            ← ENNReal.ofReal_prod_of_nonneg (fun j _ => by linarith [(hp j).2]),
            Finset.sum_congr rfl (fun i _ => (ENNReal.ofReal_prod_of_nonneg (fun j _ => hnn i j)).symm),
            ← ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.prod_nonneg (fun j _ => hnn i j))]
          have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
          rw [h2, ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_add (mul_nonneg (by norm_num)
              (Finset.prod_nonneg (fun j _ => by linarith [(hp j).2])))
              (Finset.sum_nonneg (fun i _ => Finset.prod_nonneg (fun j _ => hnn i j))), hs]
          exact ENNReal.ofReal_le_ofReal (key n p hp)
