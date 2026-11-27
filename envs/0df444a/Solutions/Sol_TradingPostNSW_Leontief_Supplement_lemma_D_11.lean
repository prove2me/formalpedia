-- Prove2me | solution 1 for TradingPostNSW.Leontief.Supplement.lemma_D_11
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:17:18.756832+00:00
-- url     : https://prove2.me/submissions/56ac483d-ec72-4668-b041-c35e729828b9

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting
import Definitions.Def_TradingPostNSW_Leontief_Supplement_Setting

open MeasureTheory

open TradingPostNSW
open TradingPostNSW.Leontief
open TradingPostNSW.Leontief.Supplement

theorem solution {n m : ℕ} (I : Instance n m) (U : Fin n → (Fin m → ℝ) → ℝ)
    (i : Fin n) (hU : IsConcaveUtility (U i)) (hns : StrictMonoOn (U i) (box m))
    (σ : Fin n → ProbabilityMeasure (Fin m → ℝ))
    (hσ : ∀ k, k ≠ i → ∀ᵐ b ∂(σ k : Measure (Fin m → ℝ)), Strategy I k b)
    (hval : ∃ s' : Fin n → Fin m → ℝ, (∀ k, k ≠ i → 0 < (σ k : Measure (Fin m → ℝ)) {s' k}) ∧
      ∀ j, 0 < ∑ k ∈ Finset.univ.erase i, s' k j) :
    StrictConcaveOn ℝ {b : Fin m → ℝ | Strategy I i b}
      (fun b => expPay U 0 (Function.update σ i (pureBid b)) i) := by
        classical
        obtain ⟨hconc, hmono, hnn⟩ := hU
        have hbox : ∀ x : Fin m → ℝ, x ∈ box m ↔ ∀ j, 0 ≤ x j ∧ x j ≤ 1 := by
          intro x
          simp only [box, Set.mem_Icc, Pi.le_def, Pi.zero_apply, Pi.one_apply]
          exact ⟨fun h j => ⟨h.1 j, h.2 j⟩, fun h => ⟨fun j => (h j).1, fun j => (h j).2⟩⟩
        have hone : (1 : Fin m → ℝ) ∈ box m := by
          rw [hbox]; intro j; simp
        have hzero : (0 : Fin m → ℝ) ∈ box m := by
          rw [hbox]; intro j; simp
        -- measurability of U i on the box
        have hlsc : LowerSemicontinuous (fun x : box m => U i x.1) := by
          intro x a ha
          have hx := (hbox _).1 x.2
          have hUx := hnn _ x.2
          obtain ⟨t, ht0, ht1, hta⟩ : ∃ t : ℝ, 0 < t ∧ t < 1 ∧ a < (1 - t) * U i x.1 := by
            have hc : Filter.Tendsto (fun t : ℝ => (1 - t) * U i x.1) (nhdsWithin 0 (Set.Ioi 0))
                (nhds ((1 - 0) * U i x.1)) := by
              apply Filter.Tendsto.mono_left _ nhdsWithin_le_nhds
              exact (Continuous.tendsto (by fun_prop) 0)
            have h1 : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), a < (1 - t) * U i x.1 :=
              hc.eventually (lt_mem_nhds (by simpa using ha))
            have h2 : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), t ∈ Set.Ioo (0:ℝ) 1 :=
              Ioo_mem_nhdsGT (by norm_num)
            obtain ⟨t, h⟩ := (h1.and h2).exists
            exact ⟨t, h.2.1, h.2.2, h.1⟩
          have hev : ∀ᶠ y : box m in nhds x, ∀ j, (1 - t) * x.1 j ≤ y.1 j := by
            rw [Filter.eventually_all]
            intro j
            rcases eq_or_lt_of_le (hx j).1 with h0 | h0
            · refine Filter.Eventually.of_forall fun y => ?_
              rw [← h0]; simpa using (((hbox _).1 y.2) j).1
            · have hcont : Continuous (fun y : box m => y.1 j) :=
                (continuous_apply j).comp continuous_subtype_val
              have : (1 - t) * x.1 j < x.1 j := by nlinarith
              filter_upwards [hcont.continuousAt.eventually (lt_mem_nhds this)] with y hy using hy.le
          filter_upwards [hev] with y hy
          have hw : ((1 - t) • x.1 : Fin m → ℝ) ∈ box m := by
            rw [hbox]; intro j
            simp only [Pi.smul_apply, smul_eq_mul]
            have := hx j
            constructor <;> nlinarith
          have h1 := hmono hw y.2 (by intro j; simpa using hy j)
          have h2 := hconc.2 x.2 hzero (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
          have h3 := hnn _ hzero
          simp only [smul_zero, add_zero, smul_eq_mul] at h2
          have h4 : 0 ≤ t * U i 0 := mul_nonneg ht0.le h3
          show a < U i y.1
          linarith
        -- effective bids
        have heff0 : ∀ (s : Fin n → Fin m → ℝ) k j, 0 ≤ effBid 0 s k j := by
          intro s k j
          unfold effBid
          split_ifs with h
          · exact h
          · exact le_rfl
        have hA : ∀ (s : Fin n → Fin m → ℝ), tpAlloc 0 s i ∈ box m := by
          intro s
          rw [hbox]; intro j
          unfold tpAlloc
          split_ifs with h
          · have hle : effBid 0 s i j ≤ ∑ k, effBid 0 s k j :=
              Finset.single_le_sum (f := fun k => effBid 0 s k j) (fun k _ => heff0 s k j)
                (Finset.mem_univ i)
            exact ⟨div_nonneg h.le (h.le.trans hle), div_le_one_of_le₀ hle (h.le.trans hle)⟩
          · exact ⟨le_rfl, zero_le_one⟩
        have hmeff : ∀ k j, Measurable (fun s : Fin n → Fin m → ℝ => effBid 0 s k j) := by
          intro k j
          have hm : Measurable (fun s : Fin n → Fin m → ℝ => s k j) := by fun_prop
          unfold effBid
          exact Measurable.ite (measurableSet_le measurable_const hm) hm measurable_const
        have hmA : Measurable (fun s : Fin n → Fin m → ℝ => tpAlloc 0 s i) := by
          rw [measurable_pi_iff]
          intro j
          unfold tpAlloc
          refine Measurable.ite (measurableSet_lt measurable_const (hmeff i j)) ?_ measurable_const
          exact (hmeff i j).div (Finset.measurable_sum _ (fun k _ => hmeff k j))
        have hmH : Measurable (fun s : Fin n → Fin m → ℝ => U i (tpAlloc 0 s i)) :=
          hlsc.measurable.comp (hmA.subtype_mk (h := hA))
        -- the joint law
        have hjoint : ∀ b : Fin m → ℝ, joint (Function.update σ i (pureBid b)) =
            (joint σ).map (fun s => Function.update s i b) := by
          intro b
          have hmu : Measurable (fun s : Fin n → Fin m → ℝ => Function.update s i b) := by
            rw [measurable_pi_iff]
            intro k
            by_cases hk : k = i
            · subst hk; simp
            · simp only [Function.update_of_ne hk]; fun_prop
          unfold joint
          apply Measure.pi_eq
          intro S hS
          rw [Measure.map_apply hmu (MeasurableSet.univ_pi hS)]
          rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
          have hp : ∏ k ∈ Finset.univ.erase i,
              ((Function.update σ i (pureBid b) k : ProbabilityMeasure (Fin m → ℝ)) :
                Measure (Fin m → ℝ)) (S k) =
              ∏ k ∈ Finset.univ.erase i, (σ k : Measure (Fin m → ℝ)) (S k) := by
            refine Finset.prod_congr rfl fun k hk => ?_
            rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
          rw [hp, Function.update_self]
          have hd : ((pureBid b : ProbabilityMeasure (Fin m → ℝ)) : Measure (Fin m → ℝ)) (S i) =
              (S i).indicator 1 b := by
            show Measure.dirac b (S i) = _
            exact Measure.dirac_apply' b (hS i)
          rw [hd]
          by_cases hb : b ∈ S i
          · have hpre : (fun s : Fin n → Fin m → ℝ => Function.update s i b) ⁻¹' (Set.univ.pi S) =
                Set.univ.pi (Function.update S i Set.univ) := by
              ext s
              simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff]
              refine forall_congr' fun k => ?_
              by_cases hk : k = i
              · subst hk; simp [hb]
              · simp [Function.update_of_ne hk]
            rw [hpre, Measure.pi_pi, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
            simp only [Function.update_self, measure_univ, Set.indicator_of_mem hb, Pi.one_apply]
            congr 1
            refine Finset.prod_congr rfl fun k hk => ?_
            rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
          · have hpre : (fun s : Fin n → Fin m → ℝ => Function.update s i b) ⁻¹' (Set.univ.pi S) = ∅ := by
              ext s
              simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff, Set.mem_empty_iff_false,
                iff_false, not_forall]
              exact ⟨i, by simpa using hb⟩
            rw [hpre]; simp [hb]
        have hmupd : ∀ b : Fin m → ℝ,
            Measurable (fun s : Fin n → Fin m → ℝ => Function.update s i b) := by
          intro b
          rw [measurable_pi_iff]
          intro k
          by_cases hk : k = i
          · subst hk; simp
          · simp only [Function.update_of_ne hk]; fun_prop
        have hmF : ∀ b : Fin m → ℝ, Measurable
            (fun s : Fin n → Fin m → ℝ => U i (tpAlloc 0 (Function.update s i b) i)) :=
          fun b => hmH.comp (hmupd b)
        have hprob : IsProbabilityMeasure (joint σ) := by unfold joint; infer_instance
        have hint : ∀ b : Fin m → ℝ, Integrable
            (fun s : Fin n → Fin m → ℝ => U i (tpAlloc 0 (Function.update s i b) i)) (joint σ) := by
          intro b
          refine Integrable.of_bound (hmF b).aestronglyMeasurable (U i 1) ?_
          refine Filter.Eventually.of_forall fun s => ?_
          rw [Real.norm_of_nonneg (hnn _ (hA _))]
          exact hmono (hA _) hone ((hA _).2)
        have hexp : ∀ b : Fin m → ℝ, expPay U 0 (Function.update σ i (pureBid b)) i =
            ∫ s, U i (tpAlloc 0 (Function.update s i b) i) ∂joint σ := by
          intro b
          unfold expPay
          rw [hjoint b, integral_map (hmupd b).aemeasurable hmH.aestronglyMeasurable]
        -- allocation formula
        have hform : ∀ (s : Fin n → Fin m → ℝ) (b : Fin m → ℝ) (j : Fin m), 0 ≤ b j →
            tpAlloc 0 (Function.update s i b) i j =
              b j / (b j + ∑ k ∈ Finset.univ.erase i, effBid 0 s k j) := by
          intro s b j hb
          have h1 : effBid 0 (Function.update s i b) i j = b j := by
            unfold effBid; simp [hb]
          have h2 : ∑ k, effBid 0 (Function.update s i b) k j =
              b j + ∑ k ∈ Finset.univ.erase i, effBid 0 s k j := by
            rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i), h1]
            congr 1
            refine Finset.sum_congr rfl fun k hk => ?_
            unfold effBid
            rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
          unfold tpAlloc
          rw [h1, h2]
          split_ifs with h
          · rfl
          · have : b j = 0 := le_antisymm (not_lt.1 h) hb
            simp [this]
        -- scalar facts
        have hid : ∀ (x y c p q : ℝ), 0 ≤ x → 0 ≤ y → 0 < c → 0 < p → 0 < q → p + q = 1 →
            (p * x + q * y) / (p * x + q * y + c) - (p * (x / (x + c)) + q * (y / (y + c))) =
              p * q * c * (x - y) ^ 2 / ((x + c) * (y + c) * (p * x + q * y + c)) := by
          intro x y c p q hx hy hc hp hq hpq
          have h1 : x + c ≠ 0 := by positivity
          have h2 : y + c ≠ 0 := by positivity
          have h3 : p * x + q * y + c ≠ 0 := by positivity
          have hq' : q = 1 - p := by linarith
          subst hq'
          field_simp
          ring
        have hscalar : ∀ (x y c p q : ℝ), 0 ≤ x → 0 ≤ y → 0 ≤ c → 0 < p → 0 < q → p + q = 1 →
            p * (x / (x + c)) + q * (y / (y + c)) ≤ (p * x + q * y) / (p * x + q * y + c) := by
          intro x y c p q hx hy hc hp hq hpq
          rcases eq_or_lt_of_le hc with h0 | h0
          · subst h0
            simp only [add_zero]
            rcases eq_or_lt_of_le hx with hx0 | hx0
            · rcases eq_or_lt_of_le hy with hy0 | hy0
              · simp [← hx0, ← hy0]
              · have hM : p * x + q * y ≠ 0 := by positivity
                rw [div_self hM, div_self hy0.ne', ← hx0]
                simp; linarith
            · have hM : p * x + q * y ≠ 0 := by positivity
              rw [div_self hM, div_self hx0.ne']
              have : y / y ≤ 1 := div_self_le_one y
              nlinarith
          · have h := hid x y c p q hx hy h0 hp hq hpq
            have : 0 ≤ p * q * c * (x - y) ^ 2 / ((x + c) * (y + c) * (p * x + q * y + c)) := by
              positivity
            linarith
        have hscalar' : ∀ (x y c p q : ℝ), 0 ≤ x → 0 ≤ y → 0 < c → 0 < p → 0 < q → p + q = 1 → x ≠ y →
            p * (x / (x + c)) + q * (y / (y + c)) < (p * x + q * y) / (p * x + q * y + c) := by
          intro x y c p q hx hy h0 hp hq hpq hne
          have h := hid x y c p q hx hy h0 hp hq hpq
          have hxy : 0 < (x - y) ^ 2 := by
            have := sub_ne_zero.2 hne
            positivity
          have : 0 < p * q * c * (x - y) ^ 2 / ((x + c) * (y + c) * (p * x + q * y + c)) := by
            positivity
          linarith
        -- convexity of the strategy set
        have hconv : Convex ℝ {b : Fin m → ℝ | Strategy I i b} := by
          intro x hx y hy p q hp hq hpq
          obtain ⟨hx1, hx2⟩ := hx
          obtain ⟨hy1, hy2⟩ := hy
          refine ⟨fun j => ?_, ?_⟩
          · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            have a1 := hx1 j
            have a2 := hy1 j
            constructor
            · have := mul_nonneg hp a1.1
              have := mul_nonneg hq a2.1
              linarith
            · have e1 := mul_le_mul_of_nonneg_left a1.2 hp
              have e2 := mul_le_mul_of_nonneg_left a2.2 hq
              have : p * I.B i + q * I.B i = I.B i := by rw [← add_mul, hpq, one_mul]
              linarith
          · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hx2, hy2, ← add_mul, hpq,
              one_mul]
        refine ⟨hconv, ?_⟩
        intro x hx y hy hxy p q hp hq hpq
        simp only [hexp, smul_eq_mul]
        have hx0 : ∀ j, 0 ≤ x j := fun j => (hx.1 j).1
        have hy0 : ∀ j, 0 ≤ y j := fun j => (hy.1 j).1
        have hz0 : ∀ j, 0 ≤ (p • x + q • y) j := fun j => by
          have := mul_nonneg hp.le (hx0 j)
          have := mul_nonneg hq.le (hy0 j)
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          linarith
        -- pointwise
        have hcomb : ∀ s : Fin n → Fin m → ℝ,
            p • tpAlloc 0 (Function.update s i x) i + q • tpAlloc 0 (Function.update s i y) i ∈ box m :=
          fun s => hconc.1 (hA _) (hA _) hp.le hq.le hpq
        have hle : ∀ s : Fin n → Fin m → ℝ,
            p • tpAlloc 0 (Function.update s i x) i + q • tpAlloc 0 (Function.update s i y) i ≤
              tpAlloc 0 (Function.update s i (p • x + q • y)) i := by
          intro s j
          rw [hform s _ j (hz0 j)]
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          rw [hform s _ j (hx0 j), hform s _ j (hy0 j)]
          exact hscalar _ _ _ _ _ (hx0 j) (hy0 j) (Finset.sum_nonneg fun k _ => heff0 s k j) hp hq hpq
        have hpt : ∀ s : Fin n → Fin m → ℝ,
            p * U i (tpAlloc 0 (Function.update s i x) i) + q * U i (tpAlloc 0 (Function.update s i y) i)
              ≤ U i (tpAlloc 0 (Function.update s i (p • x + q • y)) i) := by
          intro s
          have h1 := hconc.2 (hA (Function.update s i x)) (hA (Function.update s i y)) hp.le hq.le hpq
          have h2 := hmono (hcomb s) (hA _) (hle s)
          simp only [smul_eq_mul] at h1
          exact h1.trans h2
        obtain ⟨s', hs', hsum⟩ := hval
        obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := Function.ne_iff.1 hxy
        have hstrict : ∀ s : Fin n → Fin m → ℝ, (∀ k, k ≠ i → s k = s' k) →
            p * U i (tpAlloc 0 (Function.update s i x) i) + q * U i (tpAlloc 0 (Function.update s i y) i)
              < U i (tpAlloc 0 (Function.update s i (p • x + q • y)) i) := by
          intro s hs
          have h1 := hconc.2 (hA (Function.update s i x)) (hA (Function.update s i y)) hp.le hq.le hpq
          have hc : 0 < ∑ k ∈ Finset.univ.erase i, effBid 0 s k j := by
            refine (hsum j).trans_le (Finset.sum_le_sum fun k hk => ?_)
            unfold effBid
            rw [hs k (Finset.ne_of_mem_erase hk)]
            split_ifs with h
            · exact le_rfl
            · exact (not_le.1 h).le
          have hlt : p • tpAlloc 0 (Function.update s i x) i + q • tpAlloc 0 (Function.update s i y) i <
              tpAlloc 0 (Function.update s i (p • x + q • y)) i := by
            refine Pi.lt_def.2 ⟨hle s, j, ?_⟩
            rw [hform s _ j (hz0 j)]
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            rw [hform s _ j (hx0 j), hform s _ j (hy0 j)]
            exact hscalar' _ _ _ _ _ (hx0 j) (hy0 j) hc hp hq hpq hj
          have h2 := hns (hcomb s) (hA _) hlt
          simp only [smul_eq_mul] at h1
          exact h1.trans_lt h2
        have hApos : 0 < joint σ {s | ∀ k, k ≠ i → s k = s' k} := by
          have hset : {s : Fin n → Fin m → ℝ | ∀ k, k ≠ i → s k = s' k} =
              Set.univ.pi (fun k => if k = i then Set.univ else {s' k}) := by
            ext s
            simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_imp_iff]
            refine forall_congr' fun k => ?_
            by_cases hk : k = i <;> simp [hk]
          rw [hset]
          unfold joint
          rw [Measure.pi_pi, pos_iff_ne_zero, Finset.prod_ne_zero_iff]
          intro k _
          by_cases hk : k = i
          · simp [hk]
          · simpa [hk] using (hs' k hk).ne'
        have hi1 := (hint x).const_mul p
        have hi2 := (hint y).const_mul q
        have hi3 := hint (p • x + q • y)
        have hi12 : Integrable (fun s => p * U i (tpAlloc 0 (Function.update s i x) i) +
              q * U i (tpAlloc 0 (Function.update s i y) i)) (joint σ) := hi1.add hi2
        have hpos : 0 < ∫ s, (U i (tpAlloc 0 (Function.update s i (p • x + q • y)) i) -
            (p * U i (tpAlloc 0 (Function.update s i x) i) +
              q * U i (tpAlloc 0 (Function.update s i y) i))) ∂joint σ := by
          rw [integral_pos_iff_support_of_nonneg]
          · refine hApos.trans_le (measure_mono ?_)
            intro s hs
            rw [Function.mem_support]
            exact (sub_pos.2 (hstrict s hs)).ne'
          · intro s
            exact sub_nonneg.2 (hpt s)
          · exact hi3.sub hi12
        rw [integral_sub hi3 hi12, integral_add hi1 hi2, integral_const_mul,
          integral_const_mul] at hpos
        linarith
