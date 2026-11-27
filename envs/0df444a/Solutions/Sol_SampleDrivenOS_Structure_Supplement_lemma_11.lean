-- Prove2me | solution 1 for SampleDrivenOS.Structure.Supplement.lemma_11
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:16:14.17074+00:00
-- url     : https://prove2.me/submissions/d14045d0-06c4-420e-8b14-39873f9e600d

import Definitions.Def_SampleDrivenOS_Structure_Supplement_Thresholds

open MeasureTheory Filter
open scoped Topology

open SampleDrivenOS
open SampleDrivenOS.Structure
open SampleDrivenOS.Structure.Supplement

theorem solution (p : ℝ) (hp : 0 ≤ p ∧ p < 1) (t : ℕ → ℝ)
    (ht : IsThresholds p t) (j : ℕ) (hj : 1 ≤ j) :
    (∀ i : ℕ, 1 ≤ i → IntervalIntegrable (rankLimitIntegrand t j i) volume (t i) (t (i + 1))) ∧
    Summable (fun i : ℕ => rankLimitTerm t j (i + 1)) ∧
    Tendsto (fun N : ℕ => selectionProbability (N + 1) p t j) atTop
      (𝓝 (∑' i : ℕ, rankLimitTerm t j (i + 1))) := by
        set_option maxHeartbeats 1600000 in
          set_option maxRecDepth 2000 in
            set_option backward.isDefEq.respectTransparency false in
              classical
              have htmon : Monotone t := ht.2.1
              have ht0 : ∀ i, 0 ≤ t i := fun i => hp.1.trans (ht.2.2 i).1
              have ht1 : ∀ i, t i ≤ 1 := fun i => (ht.2.2 i).2
              have hprod0 (i : ℕ) (hi : 1 ≤ i) (hz : t 1 = 0) :
                  thresholdProd t i = 0 := by
                apply Finset.prod_eq_zero (Finset.mem_Icc.mpr ⟨le_refl 1, hi⟩)
                exact hz
              have hint (i : ℕ) (hi : 1 ≤ i) :
                  IntervalIntegrable (rankLimitIntegrand t j i) volume (t i) (t (i + 1)) := by
                by_cases hz : t 1 = 0
                · have heq : rankLimitIntegrand t j i = fun _ => 0 := by
                    funext x
                    simp [rankLimitIntegrand, hprod0 i hi hz]
                  rw [heq]
                  exact intervalIntegrable_const
                · have hpos : 0 < t 1 := lt_of_le_of_ne (ht0 1) (Ne.symm hz)
                  apply ContinuousOn.intervalIntegrable
                  rw [Set.uIcc_of_le (htmon (Nat.le_succ i))]
                  unfold rankLimitIntegrand
                  apply continuousOn_finsetSum
                  intro l hl
                  apply ContinuousOn.mul
                  · apply ContinuousOn.mul
                    · apply ContinuousOn.mul
                      · apply ContinuousOn.div continuousOn_const (continuousOn_id.pow i)
                        intro x hx
                        exact pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le hpos ((htmon hi).trans hx.1)))
                      · exact continuousOn_const
                    · exact (continuousOn_const.sub continuousOn_id).pow _
                  · exact continuousOn_id.pow _
              have hprod_nonneg (i : ℕ) : 0 ≤ thresholdProd t i := by
                apply Finset.prod_nonneg
                intro k hk
                exact ht0 k
              have hprod_le (i : ℕ) (x : ℝ) (hx : t i ≤ x) :
                  thresholdProd t i ≤ x ^ i := by
                unfold thresholdProd
                calc
                  (∏ k ∈ Finset.Icc 1 i, t k) ≤ ∏ k ∈ Finset.Icc 1 i, x := by
                    apply Finset.prod_le_prod
                    · intro k hk
                      exact ht0 k
                    · intro k hk
                      exact (htmon (Finset.mem_Icc.mp hk).2).trans hx
                  _ = x ^ i := by simp
              let C : ℝ := ∑ l ∈ Finset.Icc 1 j, ((j - 1).choose (l - 1) : ℝ)
              have hC : 0 ≤ C := by positivity
              have hbound (i : ℕ) (hi : 1 ≤ i) (x : ℝ) (hx : x ∈ Set.Icc (t i) (t (i + 1))) :
                  0 ≤ rankLimitIntegrand t j i x ∧ rankLimitIntegrand t j i x ≤ C := by
                have hx0 : 0 ≤ x := (ht0 i).trans hx.1
                have hx1 : x ≤ 1 := hx.2.trans (ht1 (i + 1))
                have hratio0 : 0 ≤ thresholdProd t i / x ^ i :=
                  div_nonneg (hprod_nonneg i) (pow_nonneg hx0 _)
                have hratio1 : thresholdProd t i / x ^ i ≤ 1 := by
                  by_cases hzero : x = 0
                  · simp [hzero, Nat.ne_of_gt hi]
                  · exact (div_le_one (pow_pos (lt_of_le_of_ne hx0 (Ne.symm hzero)) _)).mpr (hprod_le i x hx.1)
                constructor
                · unfold rankLimitIntegrand
                  apply Finset.sum_nonneg
                  intro l hl
                  exact mul_nonneg (mul_nonneg (mul_nonneg hratio0 (Nat.cast_nonneg _))
                    (pow_nonneg (sub_nonneg.mpr hx1) _)) (pow_nonneg hx0 _)
                · calc
                    rankLimitIntegrand t j i x ≤ ∑ l ∈ Finset.Icc 1 (min j i),
                        ((j - 1).choose (l - 1) : ℝ) := by
                      unfold rankLimitIntegrand
                      apply Finset.sum_le_sum
                      intro l hl
                      calc
                        _ ≤ 1 * ((j - 1).choose (l - 1) : ℝ) * 1 * 1 := by
                          apply mul_le_mul
                          · apply mul_le_mul
                            · exact mul_le_mul_of_nonneg_right hratio1 (Nat.cast_nonneg _)
                            · exact pow_le_one₀ (sub_nonneg.mpr hx1) (by linarith)
                            · positivity
                            · positivity
                          · exact pow_le_one₀ hx0 hx1
                          · positivity
                          · positivity
                        _ = _ := by ring
                    _ ≤ C := by
                      apply Finset.sum_le_sum_of_subset_of_nonneg
                      · intro l hl
                        obtain ⟨hl1, hl2⟩ := Finset.mem_Icc.mp hl
                        exact Finset.mem_Icc.mpr ⟨hl1, hl2.trans (min_le_left _ _)⟩
                      · intro l hl hln
                        positivity
              have hterm0 (i : ℕ) (hi : 1 ≤ i) : 0 ≤ rankLimitTerm t j i := by
                exact intervalIntegral.integral_nonneg (htmon (Nat.le_succ i))
                  (fun x hx => (hbound i hi x hx).1)
              have hterm_le (i : ℕ) (hi : 1 ≤ i) :
                  rankLimitTerm t j i ≤ (t (i + 1) - t i) * C := by
                calc
                  rankLimitTerm t j i ≤ ∫ _ in t i..t (i + 1), C := by
                    exact intervalIntegral.integral_mono_on (htmon (Nat.le_succ i)) (hint i hi)
                      intervalIntegrable_const (fun x hx => (hbound i hi x hx).2)
                  _ = _ := by simp
              have hsum : Summable (fun i : ℕ => rankLimitTerm t j (i + 1)) := by
                apply summable_of_sum_range_le (fun i => hterm0 (i + 1) (by omega))
                  (c := C)
                intro n
                calc
                  (∑ i ∈ Finset.range n, rankLimitTerm t j (i + 1)) ≤
                      ∑ i ∈ Finset.range n, (t (i + 1 + 1) - t (i + 1)) * C := by
                    apply Finset.sum_le_sum
                    intro i hi
                    exact hterm_le (i + 1) (by omega)
                  _ = (t (n + 1) - t 1) * C := by
                    rw [← Finset.sum_mul]
                    congr 1
                    exact Finset.sum_range_sub (fun k => t (k + 1)) n
                  _ ≤ C := by
                    calc
                      _ ≤ 1 * C := mul_le_mul_of_nonneg_right (by linarith [ht1 (n + 1), ht0 1]) hC
                      _ = _ := one_mul _
              have hfirst {N : ℕ} (A : Finset (Fin N)) (u : Fin N → ℝ) (a : Fin N) :
                  firstItem A u = some a ↔ a ∈ A ∧ (∀ b ∈ A, u a ≤ u b) ∧
                    ∀ b ∈ A, u b ≤ u a → a ≤ b := by
                unfold firstItem
                dsimp only
                split
                · rename_i h
                  constructor
                  · intro heq
                    have heq' := Option.some.inj heq
                    have hmem := Finset.min'_mem (A.filter (fun a => ∀ b ∈ A, u a ≤ u b)) h
                    rw [heq'] at hmem
                    obtain ⟨ha, hmin⟩ := Finset.mem_filter.mp hmem
                    refine ⟨ha, hmin, ?_⟩
                    intro b hb hba
                    have hbmem : b ∈ A.filter (fun a => ∀ b ∈ A, u a ≤ u b) := by
                      exact Finset.mem_filter.mpr ⟨hb, fun c hc => hba.trans (hmin c hc)⟩
                    simpa only [heq'] using Finset.min'_le _ b hbmem
                  · rintro ⟨ha, hmin, hties⟩
                    apply congrArg some
                    apply le_antisymm
                    · exact Finset.min'_le _ a (Finset.mem_filter.mpr ⟨ha, hmin⟩)
                    · obtain ⟨hb, hbmin⟩ := Finset.mem_filter.mp (Finset.min'_mem _ h)
                      exact hties _ hb (hbmin a ha)
                · rename_i h
                  constructor
                  · simp
                  · rintro ⟨ha, hmin, _⟩
                    exact (h ⟨a, Finset.mem_filter.mpr ⟨ha, hmin⟩⟩).elim
              have hchoice {N : ℕ} (u : Fin N → ℝ) (a : Fin N) :
                  thresholdChoice N p t u = some a ↔
                    (p ≤ u a ∧ t (clockRank u a) ≤ u a) ∧
                    (∀ b : Fin N, p ≤ u b → t (clockRank u b) ≤ u b → u a ≤ u b) ∧
                    (∀ b : Fin N, p ≤ u b → t (clockRank u b) ≤ u b → u b ≤ u a → a ≤ b) := by
                rw [thresholdChoice, hfirst]
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_imp]
              have hnostop {N : ℕ} (u : Fin N → ℝ) (τ : ℝ) :
                  (∀ a, u a < τ → u a < t (clockRank u a)) ↔
                  ∀ a, u a < τ → u a < t (1 + (Finset.univ.filter
                    (fun b : Fin N => b < a ∧ u b < τ)).card) := by
                constructor
                · intro h a ha
                  apply lt_of_lt_of_le (h a ha)
                  apply htmon
                  apply Nat.add_le_add_left
                  apply Finset.card_le_card
                  intro b hb
                  obtain ⟨_, hba, hub⟩ := Finset.mem_filter.mp hb
                  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hba, hub.trans_lt ha⟩
                · intro h a ha
                  let B := Finset.univ.filter (fun b : Fin N => b < a ∧ u b < τ ∧ u a < u b)
                  by_cases hB : B.Nonempty
                  · let b := B.min' hB
                    have hbB : b ∈ B := Finset.min'_mem B hB
                    obtain ⟨_, hba, hbτ, hab⟩ := Finset.mem_filter.mp hbB
                    have hsub : Finset.univ.filter (fun c : Fin N => c < b ∧ u c < τ) ⊆
                        Finset.univ.filter (fun c : Fin N => c < a ∧ u c ≤ u a) := by
                      intro c hc
                      obtain ⟨_, hcb, hcτ⟩ := Finset.mem_filter.mp hc
                      have hca := hcb.trans hba
                      have hcu : u c ≤ u a := by
                        by_contra hcu
                        have hcB : c ∈ B := Finset.mem_filter.mpr
                          ⟨Finset.mem_univ _, hca, hcτ, lt_of_not_ge hcu⟩
                        have hbc : b ≤ c := Finset.min'_le B c hcB
                        exact (not_lt_of_ge hbc) hcb
                      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hca, hcu⟩
                    exact lt_of_lt_of_le (hab.trans (h b hbτ))
                      (htmon (Nat.add_le_add_left (Finset.card_le_card hsub) 1))
                  · have hsub : Finset.univ.filter (fun c : Fin N => c < a ∧ u c < τ) ⊆
                        Finset.univ.filter (fun c : Fin N => c < a ∧ u c ≤ u a) := by
                      intro c hc
                      obtain ⟨_, hca, hcτ⟩ := Finset.mem_filter.mp hc
                      have hcu : u c ≤ u a := by
                        by_contra hcu
                        exact hB ⟨c, Finset.mem_filter.mpr
                          ⟨Finset.mem_univ _, hca, hcτ, lt_of_not_ge hcu⟩⟩
                      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hca, hcu⟩
                    exact lt_of_lt_of_le (h a ha)
                      (htmon (Nat.add_le_add_left (Finset.card_le_card hsub) 1))
              have hchoice_nostop {N : ℕ} (u : Fin N → ℝ) (a : Fin N)
                  (hne : ∀ b, b ≠ a → u b ≠ u a) :
                  thresholdChoice N p t u = some a ↔
                    t (clockRank u a) ≤ u a ∧ ∀ b, u b < u a → u b < t (clockRank u b) := by
                rw [hchoice]
                constructor
                · rintro ⟨ha, hmin, hties⟩
                  refine ⟨ha.2, ?_⟩
                  intro b hba
                  by_contra hbt
                  have hb := le_of_not_gt hbt
                  have hbp : p ≤ u b := ((ht.2.2 _).1).trans hb
                  exact (not_lt_of_ge (hmin b hbp hb)) hba
                · rintro ⟨ha, hbefore⟩
                  refine ⟨⟨((ht.2.2 _).1).trans ha, ha⟩, ?_, ?_⟩
                  · intro b hbp hb
                    by_contra hba
                    exact (not_lt_of_ge hb) (hbefore b (lt_of_not_ge hba))
                  · intro b hbp hb hba
                    by_cases heq : b = a
                    · subst b; rfl
                    · have hne' := hne b heq
                      have hlt : u b < u a := lt_of_le_of_ne hba hne'
                      exact ((not_lt_of_ge hb) (hbefore b hlt)).elim
              have hlaw (N : ℕ) : arrivalLaw N Set.univ = 1 := by
                simp [arrivalLaw, Measure.pi_univ, Measure.restrict_apply_univ]
              have hrank_meas (N : ℕ) (a : Fin N) : Measurable (fun u : Fin N → ℝ => clockRank u a) := by
                unfold clockRank
                simp_rw [Finset.card_filter]
                apply measurable_const.add
                apply Finset.measurable_sum
                intro b hb
                exact Measurable.ite ((MeasurableSet.const (b < a)).inter
                  (measurableSet_le (measurable_pi_apply b) (measurable_pi_apply a)))
                  measurable_const measurable_const
              have ht_meas (N : ℕ) (a : Fin N) : Measurable (fun u : Fin N → ℝ => t (clockRank u a)) :=
                (measurable_of_countable t).comp (hrank_meas N a)
              have hevent_meas (N : ℕ) : MeasurableSet {u : Fin N → ℝ |
                  ∃ a : Fin N, a.val + 1 = j ∧ thresholdChoice N p t u = some a} := by
                simp_rw [hchoice]
                measurability
              have hind_meas (N : ℕ) : Measurable (fun u : Fin N → ℝ =>
                  if ∃ a : Fin N, a.val + 1 = j ∧ thresholdChoice N p t u = some a
                    then (1 : ENNReal) else 0) :=
                Measurable.ite (hevent_meas N) measurable_const measurable_const
              let S : ℕ → ℕ → ℝ → ℝ := fun n => Nat.rec (fun _ _ => 1)
                (fun _ f k τ => (1 - τ) * f k τ + min (t (k + 1)) τ * f (k + 1) τ) n
              have hS0 (k : ℕ) (τ : ℝ) : S 0 k τ = 1 := rfl
              have hSs (n k : ℕ) (τ : ℝ) : S (n + 1) k τ =
                  (1 - τ) * S n k τ + min (t (k + 1)) τ * S n (k + 1) τ := rfl
              have hSbounds (n k : ℕ) (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
                  0 ≤ S n k τ ∧ S n k τ ≤ 1 := by
                induction n generalizing k with
                | zero => simp [hS0]
                | succ n ih =>
                  rw [hSs]
                  have hk := ih k
                  have hks := ih (k + 1)
                  have hmin0 : 0 ≤ min (t (k + 1)) τ := le_min (ht0 _) hτ.1
                  constructor
                  · exact add_nonneg (mul_nonneg (sub_nonneg.mpr hτ.2) hk.1) (mul_nonneg hmin0 hks.1)
                  · calc
                      _ ≤ (1 - τ) * 1 + min (t (k + 1)) τ * 1 :=
                        add_le_add (mul_le_mul_of_nonneg_left hk.2 (sub_nonneg.mpr hτ.2))
                          (mul_le_mul_of_nonneg_left hks.2 hmin0)
                      _ ≤ 1 := by have := min_le_right (t (k + 1)) τ; linarith
              have hSanti (k : ℕ) (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
                  Antitone (fun n => S n k τ) := by
                apply antitone_nat_of_succ_le
                intro n
                induction n generalizing k with
                | zero => simpa [hS0] using (hSbounds 1 k τ hτ).2
                | succ n ih =>
                  rw [hSs (n + 1), hSs n]
                  exact add_le_add (mul_le_mul_of_nonneg_left (ih k) (sub_nonneg.mpr hτ.2))
                    (mul_le_mul_of_nonneg_left (ih (k + 1)) (le_min (ht0 _) hτ.1))
              have hSconv (k : ℕ) (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
                  Tendsto (fun n => S n k τ) atTop (𝓝 (⨅ n, S n k τ)) := by
                apply tendsto_atTop_ciInf (hSanti k τ hτ)
                exact ⟨0, by rintro _ ⟨n, rfl⟩; exact (hSbounds n k τ hτ).1⟩
              have hSfixed (k : ℕ) (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
                  (⨅ n, S n k τ) = (1 - τ) * (⨅ n, S n k τ) +
                    min (t (k + 1)) τ * (⨅ n, S n (k + 1) τ) := by
                have hlim := (((tendsto_const_nhds (x := (1 - τ))).mul (hSconv k τ hτ)).add
                  ((tendsto_const_nhds (x := min (t (k + 1)) τ)).mul (hSconv (k + 1) τ hτ)))
                have hlim' : Tendsto (fun n => S (n + 1) k τ) atTop (𝓝 (⨅ n, S n k τ)) :=
                  (tendsto_add_atTop_iff_nat 1).mpr (hSconv k τ hτ)
                exact tendsto_nhds_unique hlim' (by simpa only [hSs] using hlim)
              have hSone (n k : ℕ) (τ : ℝ) (hk : τ ≤ t (k + 1)) : S n k τ = 1 := by
                induction n generalizing k with
                | zero => exact hS0 k τ
                | succ n ih =>
                  rw [hSs, ih k hk, ih (k + 1) (hk.trans (htmon (by omega))), min_eq_right hk]
                  ring
              have hScont (n k : ℕ) : Continuous (fun τ => S n k τ) := by
                induction n generalizing k with
                | zero => exact continuous_const
                | succ n ih =>
                  simp_rw [hSs]
                  exact (continuous_const.sub continuous_id).mul (ih k) |>.add
                    ((continuous_const.min continuous_id).mul (ih (k + 1)))
              let count : (n : ℕ) → ℝ → (Fin n → ℝ) → ℕ :=
                fun n τ u => (Finset.univ.filter (fun b : Fin n => u b < τ)).card
              let good : (n : ℕ) → ℕ → ℝ → (Fin n → ℝ) → Prop :=
                fun n k τ u => ∀ a : Fin n, u a < τ → u a <
                  t (k + 1 + (Finset.univ.filter (fun b : Fin n => b < a ∧ u b < τ)).card)
              let scan : (n : ℕ) → ℕ → ℝ → (ℕ → ℝ) → (Fin n → ℝ) → ℝ :=
                fun n k τ f u => if good n k τ u then f (k + count n τ u) else 0
              have hcount_meas (n : ℕ) (τ : ℝ) : Measurable (count n τ) := by
                dsimp only [count]
                simp_rw [Finset.card_filter]
                apply Finset.measurable_sum
                intro b hb
                exact Measurable.ite (measurableSet_lt (measurable_pi_apply b) measurable_const)
                  measurable_const measurable_const
              have hgood_meas (n k : ℕ) (τ : ℝ) : MeasurableSet {u | good n k τ u} := by
                have hcount a : Measurable (fun u : Fin n → ℝ => k + 1 +
                    (Finset.univ.filter (fun b : Fin n => b < a ∧ u b < τ)).card) := by
                  simp_rw [Finset.card_filter]
                  apply measurable_const.add
                  apply Finset.measurable_sum
                  intro b hb
                  exact Measurable.ite ((MeasurableSet.const (b < a)).inter
                    (measurableSet_lt (measurable_pi_apply b) measurable_const))
                    measurable_const measurable_const
                have hth a := (measurable_of_countable t).comp (hcount a)
                dsimp only [good]
                rw [Set.setOf_forall]
                apply MeasurableSet.iInter
                intro a
                have hi := (measurableSet_lt (measurable_pi_apply a) (measurable_const (a := τ))).compl.union
                  (measurableSet_lt (measurable_pi_apply a) (hth a))
                convert hi using 1
                ext u
                simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_setOf_eq, imp_iff_not_or, Function.comp_apply]
              have hscan_meas (n k : ℕ) (τ : ℝ) (f : ℕ → ℝ) : Measurable (scan n k τ f) := by
                exact Measurable.ite (hgood_meas n k τ)
                  ((measurable_of_countable f).comp (measurable_const.add (hcount_meas n τ))) measurable_const
              have hscan_bound (n k : ℕ) (τ : ℝ) (f : ℕ → ℝ)
                  (hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1) (u : Fin n → ℝ) :
                  0 ≤ scan n k τ f u ∧ scan n k τ f u ≤ 1 := by
                dsimp only [scan]
                split
                · exact hf _
                · norm_num
              have hscan_int (n k : ℕ) (τ : ℝ) (f : ℕ → ℝ)
                  (hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1) : Integrable (scan n k τ f) (arrivalLaw n) := by
                letI : IsProbabilityMeasure (arrivalLaw n) := ⟨hlaw n⟩
                apply (integrable_const (1 : ℝ)).mono' (hscan_meas n k τ f).aestronglyMeasurable
                exact Filter.Eventually.of_forall fun u => by
                  rw [Real.norm_eq_abs, abs_of_nonneg (hscan_bound n k τ f hf u).1]
                  exact (hscan_bound n k τ f hf u).2
              have hcount_cons (n : ℕ) (τ x : ℝ) (u : Fin n → ℝ) :
                  count (n + 1) τ (Fin.cons (α := fun _ => ℝ) x u) = (if x < τ then 1 else 0) + count n τ u := by
                simp only [count, Finset.card_filter, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
              have hcount_before_cons (n : ℕ) (τ x : ℝ) (u : Fin n → ℝ) (a : Fin n) :
                  (Finset.univ.filter (fun b : Fin (n + 1) => b < a.succ ∧ Fin.cons (α := fun _ => ℝ) x u b < τ)).card =
                  (if x < τ then 1 else 0) +
                    (Finset.univ.filter (fun b : Fin n => b < a ∧ u b < τ)).card := by
                simp only [Finset.card_filter, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
                  (show (0 : Fin (n + 1)) < a.succ by change 0 < a.val + 1; omega), true_and, Fin.succ_lt_succ_iff]
              have hgood_cons (n k : ℕ) (τ x : ℝ) (u : Fin n → ℝ) :
                  good (n + 1) k τ (Fin.cons (α := fun _ => ℝ) x u) ↔
                  if x < τ then x < t (k + 1) ∧ good n (k + 1) τ u else good n k τ u := by
                dsimp only [good]
                rw [Fin.forall_fin_succ]
                simp only [Fin.cons_zero, Fin.cons_succ, Fin.not_lt_zero, false_and,
                  Finset.filter_false, Finset.card_empty, Nat.add_zero, hcount_before_cons]
                by_cases hx : x < τ
                · simp only [hx, if_true, true_implies, Nat.add_assoc]
                · simp only [hx, if_false, false_implies, true_and, Nat.zero_add]
              have hscan_cons (n k : ℕ) (τ x : ℝ) (u : Fin n → ℝ) (f : ℕ → ℝ) :
                  scan (n + 1) k τ f (Fin.cons (α := fun _ => ℝ) x u) =
                    (if τ ≤ x then (1 : ℝ) else 0) * scan n k τ f u +
                    (if x < min (t (k + 1)) τ then (1 : ℝ) else 0) * scan n (k + 1) τ f u := by
                dsimp only [scan]
                simp only [hgood_cons, hcount_cons]
                by_cases hx : x < τ
                · simp only [hx, if_true, not_le.mpr hx, if_false]
                  by_cases hxt : x < t (k + 1)
                  · have hxm : x < min (t (k + 1)) τ := lt_min hxt hx
                    simp only [hxt, hxm, if_true, true_and, zero_mul, zero_add, one_mul, Nat.add_assoc]
                  · have hxm : ¬ x < min (t (k + 1)) τ := fun h => hxt (lt_of_lt_of_le h (min_le_left _ _))
                    simp [hxt, hxm]
                · have hτx : τ ≤ x := le_of_not_gt hx
                  have hxm : ¬ x < min (t (k + 1)) τ := fun h => hx (lt_of_lt_of_le h (min_le_right _ _))
                  simp only [hx, if_false, hτx, if_true, hxm, Nat.zero_add, one_mul, zero_mul, add_zero]
              have hcons_integral (n : ℕ) (g : (Fin (n + 1) → ℝ) → ℝ) :
                  (∫ u, g u ∂arrivalLaw (n + 1)) =
                  ∫ z : ℝ × (Fin n → ℝ), g (Fin.cons (α := fun _ => ℝ) z.1 z.2)
                    ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (arrivalLaw n)) := by
                have hmp := measurePreserving_piFinSuccAbove
                  (fun _ : Fin (n + 1) => volume.restrict (Set.Icc (0 : ℝ) 1)) (0 : Fin (n + 1))
                simpa only [arrivalLaw, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
                  Fin.insertNth_zero, cast_eq, Fin.zero_succAbove, Equiv.coe_fn_mk] using (hmp.symm.integral_comp' g).symm
              have hmix_integral (n k : ℕ) (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
                  (g h : (Fin n → ℝ) → ℝ) (hg : Integrable g (arrivalLaw n)) (hh : Integrable h (arrivalLaw n)) :
                  (∫ z : ℝ × (Fin n → ℝ),
                    (if τ ≤ z.1 then (1 : ℝ) else 0) * g z.2 +
                    (if z.1 < min (t (k + 1)) τ then (1 : ℝ) else 0) * h z.2
                    ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (arrivalLaw n))) =
                  (1 - τ) * (∫ u, g u ∂arrivalLaw n) +
                    min (t (k + 1)) τ * (∫ u, h u ∂arrivalLaw n) := by
                let μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
                letI : IsProbabilityMeasure μ := ⟨by simp [μ]⟩
                letI : IsProbabilityMeasure (arrivalLaw n) := ⟨hlaw n⟩
                have hmin0 : 0 ≤ min (t (k + 1)) τ := le_min (ht0 _) hτ.1
                have hmin1 : min (t (k + 1)) τ ≤ 1 := (min_le_right _ _).trans hτ.2
                have hset1 : Set.Ici τ ∩ Set.Icc (0 : ℝ) 1 = Set.Icc τ 1 := by
                  ext x
                  constructor
                  · rintro ⟨hτx, hx0, hx1⟩; exact ⟨hτx, hx1⟩
                  · rintro ⟨hτx, hx1⟩; exact ⟨hτx, hτ.1.trans hτx, hx1⟩
                have hset2 : Set.Iio (min (t (k + 1)) τ) ∩ Set.Icc (0 : ℝ) 1 =
                    Set.Ico 0 (min (t (k + 1)) τ) := by
                  ext x
                  constructor
                  · rintro ⟨hxm, hx0, hx1⟩; exact ⟨hx0, hxm⟩
                  · rintro ⟨hx0, hxm⟩; exact ⟨hxm, hx0, hxm.le.trans hmin1⟩
                have hcoeff1 : (∫ x : ℝ, (if τ ≤ x then (1 : ℝ) else 0) ∂μ) = 1 - τ := by
                  change (∫ x : ℝ, (Set.Ici τ).indicator (fun _ => (1 : ℝ)) x ∂μ) = _
                  rw [integral_indicator_const _ measurableSet_Ici]
                  change (μ (Set.Ici τ)).toReal * 1 = _
                  rw [Measure.restrict_apply measurableSet_Ici, hset1, Real.volume_Icc,
                    ENNReal.toReal_ofReal (sub_nonneg.mpr hτ.2), mul_one]
                have hcoeff2 : (∫ x : ℝ, (if x < min (t (k + 1)) τ then (1 : ℝ) else 0) ∂μ) =
                    min (t (k + 1)) τ := by
                  change (∫ x : ℝ, (Set.Iio (min (t (k + 1)) τ)).indicator (fun _ => (1 : ℝ)) x ∂μ) = _
                  rw [integral_indicator_const _ measurableSet_Iio]
                  change (μ (Set.Iio (min (t (k + 1)) τ))).toReal * 1 = _
                  rw [Measure.restrict_apply measurableSet_Iio, hset2, Real.volume_Ico, sub_zero,
                    ENNReal.toReal_ofReal hmin0, mul_one]
                have hfi : Integrable (fun x : ℝ => if τ ≤ x then (1 : ℝ) else 0) μ :=
                  (integrable_const (1 : ℝ)).indicator measurableSet_Ici
                have hgi : Integrable (fun x : ℝ => if x < min (t (k + 1)) τ then (1 : ℝ) else 0) μ :=
                  (integrable_const (1 : ℝ)).indicator measurableSet_Iio
                rw [integral_add (hfi.mul_prod hg)
                  (hgi.mul_prod hh),
                  integral_prod_mul (fun x : ℝ => if τ ≤ x then (1 : ℝ) else 0) g,
                  integral_prod_mul (fun x : ℝ => if x < min (t (k + 1)) τ then (1 : ℝ) else 0)
                    h, hcoeff1, hcoeff2]
              have hscan_step (n k : ℕ) (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (f : ℕ → ℝ)
                  (hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1) :
                  (∫ u, scan (n + 1) k τ f u ∂arrivalLaw (n + 1)) =
                    (1 - τ) * (∫ u, scan n k τ f u ∂arrivalLaw n) +
                    min (t (k + 1)) τ * (∫ u, scan n (k + 1) τ f u ∂arrivalLaw n) := by
                rw [hcons_integral]
                simp_rw [hscan_cons]
                exact hmix_integral n k τ hτ _ _ (hscan_int n k τ f hf) (hscan_int n (k + 1) τ f hf)
              let P : ℕ → ℕ → ℝ → (ℕ → ℝ) → ℝ := fun n => Nat.rec (fun k _ f => f k)
                (fun _ q k τ f => (1 - τ) * q k τ f + min (t (k + 1)) τ * q (k + 1) τ f) n
              have hP0 (k : ℕ) (τ : ℝ) (f : ℕ → ℝ) : P 0 k τ f = f k := rfl
              have hPs (n k : ℕ) (τ : ℝ) (f : ℕ → ℝ) : P (n + 1) k τ f =
                  (1 - τ) * P n k τ f + min (t (k + 1)) τ * P n (k + 1) τ f := rfl
              have hscan_integral (n k : ℕ) (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (f : ℕ → ℝ)
                  (hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1) :
                  (∫ u, scan n k τ f u ∂arrivalLaw n) = P n k τ f := by
                induction n generalizing k with
                | zero => simp [scan, good, count, hP0, integral_const, Measure.real, hlaw]
                | succ n ih => rw [hscan_step n k τ hτ f hf, ih k, ih (k + 1), hPs]
              have hPS (n k : ℕ) (τ : ℝ) : P n k τ (fun _ => 1) = S n k τ := by
                induction n generalizing k with
                | zero => rfl
                | succ n ih => rw [hPs, hSs, ih k, ih (k + 1)]
              let before : (n : ℕ) → ℕ → ℝ → (Fin n → ℝ) → ℕ :=
                fun n m τ u => (Finset.univ.filter (fun b : Fin n => b.val < m ∧ u b < τ)).card
              let joint : (n m : ℕ) → ℕ → ℝ → (Fin (n + m) → ℝ) → ℝ :=
                fun n m k τ u => if good (n + m) k τ u ∧ t (k + 1 + before (n + m) m τ u) ≤ τ then 1 else 0
              have hbefore_meas (n m : ℕ) (τ : ℝ) : Measurable (before n m τ) := by
                dsimp only [before]
                simp_rw [Finset.card_filter]
                apply Finset.measurable_sum
                intro b hb
                exact Measurable.ite ((MeasurableSet.const (b.val < m)).inter
                  (measurableSet_lt (measurable_pi_apply b) measurable_const)) measurable_const measurable_const
              have hjoint_meas (n m k : ℕ) (τ : ℝ) : Measurable (joint n m k τ) := by
                apply Measurable.ite ((hgood_meas (n + m) k τ).inter ?_) measurable_const measurable_const
                exact measurableSet_le ((measurable_of_countable t).comp
                  (measurable_const.add (hbefore_meas (n + m) m τ))) measurable_const
              have hjoint_int (n m k : ℕ) (τ : ℝ) : Integrable (joint n m k τ) (arrivalLaw (n + m)) := by
                letI : IsProbabilityMeasure (arrivalLaw (n + m)) := ⟨hlaw _⟩
                apply (integrable_const (1 : ℝ)).mono' (hjoint_meas n m k τ).aestronglyMeasurable
                exact Filter.Eventually.of_forall fun u => by dsimp only [joint]; split <;> norm_num
              have hbefore_cons (n m : ℕ) (τ x : ℝ) (u : Fin (n + m) → ℝ) :
                  before (n + (m + 1)) (m + 1) τ (Fin.cons (α := fun _ => ℝ) x u) =
                    (if x < τ then 1 else 0) + before (n + m) m τ u := by
                simp only [Nat.add_succ, before, Finset.card_filter, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
                  Fin.val_zero, Fin.val_succ, Nat.zero_lt_succ, true_and, Nat.succ_lt_succ_iff]
              have hjoint_cons (n m k : ℕ) (τ x : ℝ) (u : Fin (n + m) → ℝ) :
                  joint n (m + 1) k τ (Fin.cons (α := fun _ => ℝ) x u) =
                    (if τ ≤ x then (1 : ℝ) else 0) * joint n m k τ u +
                    (if x < min (t (k + 1)) τ then (1 : ℝ) else 0) * joint n m (k + 1) τ u := by
                dsimp only [joint]
                simp only [hbefore_cons]
                simp only [Nat.add_succ, Nat.add_zero, hgood_cons]
                by_cases hx : x < τ
                · have hτx : ¬τ ≤ x := not_le.mpr hx
                  by_cases hxt : x < t (k + 1)
                  · have hxm : x < min (t (k + 1)) τ := lt_min hxt hx
                    simp only [hx, hτx, hxt, hxm, if_true, if_false, true_and,
                      zero_mul, zero_add, one_mul, Nat.add_assoc]
                    simp only [← Nat.add_assoc, Nat.add_one]
                  · have hxm : ¬x < min (t (k + 1)) τ := fun h => hxt (h.trans_le (min_le_left _ _))
                    simp [hx, hτx, hxt, hxm]
                · have hτx : τ ≤ x := le_of_not_gt hx
                  have hxm : ¬x < min (t (k + 1)) τ := fun h => hx (h.trans_le (min_le_right _ _))
                  simp only [hx, hτx, hxm, if_true, if_false, zero_mul, one_mul, add_zero,
                    Nat.zero_add]
              have hjoint_integral (n m k : ℕ) (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
                  (∫ u, joint n m k τ u ∂arrivalLaw (n + m)) =
                    P m k τ (fun r => if t (r + 1) ≤ τ then S n r τ else 0) := by
                induction m generalizing k with
                | zero =>
                  have heq : joint n 0 k τ = fun u => if t (k + 1) ≤ τ then scan n k τ (fun _ => 1) u else 0 := by
                    funext u
                    simp only [joint, before, Nat.not_lt_zero, false_and, Finset.filter_false,
                      Finset.card_empty, Nat.add_zero, scan]
                    by_cases hg : good n k τ u <;> by_cases hgk : t (k + 1) ≤ τ <;> simp [hg, hgk]
                  rw [heq, hP0]
                  split
                  · change (∫ u, scan n k τ (fun _ => 1) u ∂arrivalLaw n) = S n k τ
                    rw [hscan_integral n k τ hτ (fun _ => 1) (by intro r; norm_num), hPS]
                  · simp
                | succ m ih =>
                  have heq := hcons_integral (n + m) (joint n (m + 1) k τ)
                  simp only [Nat.add_succ, Nat.add_zero] at heq ⊢
                  rw [heq]
                  simp_rw [hjoint_cons]
                  rw [hmix_integral (n + m) k τ hτ _ _ (hjoint_int n m k τ) (hjoint_int n m (k + 1) τ),
                    ih k, ih (k + 1), hPs]
              have hcard_delete (M : ℕ) (a : Fin (M + 1)) (Q : Fin (M + 1) → Prop) [DecidablePred Q] (ha : ¬Q a) :
                  (Finset.univ.filter Q).card =
                    (Finset.univ.filter (fun b : Fin M => Q (a.succAbove b))).card := by
                rw [Finset.card_filter, Fin.sum_univ_succAbove _ a]
                simp only [ha, if_false, zero_add, add_zero, Finset.card_filter]
              have hdelete_choice (M : ℕ) (a : Fin (M + 1)) (τ : ℝ) (u : Fin M → ℝ)
                  (hne : ∀ b, u b ≠ τ) :
                  thresholdChoice (M + 1) p t (a.insertNth (α := fun _ => ℝ) τ u) = some a ↔
                    good M 0 τ u ∧ t (1 + before M a.val τ u) ≤ τ := by
                let v : Fin (M + 1) → ℝ := a.insertNth τ u
                have hva : v a = τ := Fin.insertNth_apply_same _ _ _
                have hvb (b : Fin M) : v (a.succAbove b) = u b := Fin.insertNth_apply_succAbove _ _ _ _
                have hvne : ∀ b, b ≠ a → v b ≠ v a := by
                  intro b hb
                  obtain ⟨c, rfl⟩ := Fin.exists_succAbove_eq_iff.mpr hb
                  simpa only [hvb, hva] using hne c
                have hcut (b : Fin M) :
                    (Finset.univ.filter (fun c : Fin (M + 1) => c < a.succAbove b ∧ v c < τ)).card =
                      (Finset.univ.filter (fun c : Fin M => c < b ∧ u c < τ)).card := by
                  rw [hcard_delete M a (fun c => c < a.succAbove b ∧ v c < τ) (by simp only [hva, lt_self_iff_false, and_false, not_false_eq_true])]
                  simp only [hvb, Fin.succAbove_lt_succAbove_iff]
                have hrank : clockRank v a = 1 + before M a.val τ u := by
                  unfold clockRank
                  rw [hcard_delete M a (fun b => b < a ∧ v b ≤ v a) (by simp)]
                  dsimp only [before]
                  congr 1
                  apply congrArg Finset.card
                  ext b
                  simp only [before, Finset.mem_filter, Finset.mem_univ, true_and, hvb, hva,
                    Fin.succAbove_lt_iff_castSucc_lt, Fin.lt_iff_val_lt_val, Fin.coe_castSucc,
                    le_iff_lt_or_eq, hne b, or_false]
                  exact and_congr (Fin.succAbove_lt_iff_castSucc_lt a b) Iff.rfl
                have hg : (∀ b, v b < τ → v b < t (1 +
                    (Finset.univ.filter (fun c : Fin (M + 1) => c < b ∧ v c < τ)).card)) ↔ good M 0 τ u := by
                  constructor
                  · intro h b hb
                    have hh := h (a.succAbove b) (by simpa only [hvb] using hb)
                    simpa only [hvb, hcut, good, Nat.zero_add] using hh
                  · intro h b hb
                    have hba : b ≠ a := by intro he; subst b; exact (lt_irrefl τ) (hva ▸ hb)
                    obtain ⟨c, rfl⟩ := Fin.exists_succAbove_eq_iff.mpr hba
                    have hh := h c (by simpa only [hvb] using hb)
                    simpa only [hvb, hcut, good, Nat.zero_add] using hh
                change thresholdChoice (M + 1) p t v = some a ↔ _
                rw [hchoice_nostop v a hvne, hva, hnostop, hrank, hg, and_comm]
              have hprob_real (N : ℕ) : selectionProbability N p t j =
                  ∫ u, (if ∃ a : Fin N, a.val + 1 = j ∧ thresholdChoice N p t u = some a
                    then (1 : ℝ) else 0) ∂arrivalLaw N := by
                unfold selectionProbability
                have hh := integral_toReal (μ := arrivalLaw N) (hind_meas N).aemeasurable
                  (Filter.Eventually.of_forall fun u => (by split <;> simp :
                    (if ∃ a : Fin N, a.val + 1 = j ∧ thresholdChoice N p t u = some a
                      then (1 : ENNReal) else 0) < ⊤))
                rw [← hh]
                apply integral_congr_ae
                exact Filter.Eventually.of_forall fun u => by
                  by_cases h : ∃ a : Fin N, a.val + 1 = j ∧ thresholdChoice N p t u = some a
                  · simp only [h, if_true, ENNReal.toReal_one]
                  · simp only [h, if_false, ENNReal.toReal_zero]
              have hPbounds (m k : ℕ) (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (f : ℕ → ℝ)
                  (hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1) : 0 ≤ P m k τ f ∧ P m k τ f ≤ 1 := by
                induction m generalizing k with
                | zero => exact hf k
                | succ m ih =>
                  rw [hPs]
                  have hk := ih k
                  have hks := ih (k + 1)
                  have ha0 := sub_nonneg.mpr hτ.2
                  have hb0 := le_min (ht0 (k + 1)) hτ.1
                  refine ⟨add_nonneg (mul_nonneg ha0 hk.1) (mul_nonneg hb0 hks.1), ?_⟩
                  calc
                    _ ≤ (1 - τ) * 1 + min (t (k + 1)) τ * 1 :=
                      add_le_add (mul_le_mul_of_nonneg_left hk.2 ha0) (mul_le_mul_of_nonneg_left hks.2 hb0)
                    _ ≤ 1 := by have := min_le_right (t (k + 1)) τ; linarith
              have hPlimit (m k : ℕ) (τ : ℝ) (f : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
                  (hf : ∀ r, Tendsto (fun n => f n r) atTop (𝓝 (g r))) :
                  Tendsto (fun n => P m k τ (f n)) atTop (𝓝 (P m k τ g)) := by
                induction m generalizing k with
                | zero => exact hf k
                | succ m ih =>
                  simpa only [hPs] using
                    (((tendsto_const_nhds (x := 1 - τ)).mul (ih k)).add
                      ((tendsto_const_nhds (x := min (t (k + 1)) τ)).mul (ih (k + 1))))
              have hPmeas (m k : ℕ) (f : ℝ → ℕ → ℝ) (hf : ∀ r, Measurable (fun τ => f τ r)) :
                  Measurable (fun τ => P m k τ (f τ)) := by
                induction m generalizing k with
                | zero => exact hf k
                | succ m ih =>
                  simp_rw [hPs]
                  exact ((measurable_const.sub measurable_id).mul (ih k)).add
                    ((measurable_const.min measurable_id).mul (ih (k + 1)))
              let D : ℕ → ℝ → ℝ := fun n τ => P (j - 1) 0 τ (fun r => if t (r + 1) ≤ τ then S n r τ else 0)
              let G : ℝ → ℝ := fun τ => P (j - 1) 0 τ (fun r => if t (r + 1) ≤ τ then ⨅ n, S n r τ else 0)
              have hDmeas (n : ℕ) : Measurable (D n) := by
                apply hPmeas
                intro r
                exact Measurable.ite (measurableSet_le measurable_const measurable_id)
                  (hScont n r).measurable measurable_const
              have hDconv (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
                  Tendsto (fun n => D n τ) atTop (𝓝 (G τ)) := by
                apply hPlimit
                intro r
                split
                · exact hSconv r τ hτ
                · exact tendsto_const_nhds
              have hDbounds (n : ℕ) (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ D n τ ∧ D n τ ≤ 1 := by
                apply hPbounds (j - 1) 0 τ hτ
                intro r
                split
                · exact hSbounds n r τ hτ
                · norm_num
              have hGbounds (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ G τ ∧ G τ ≤ 1 :=
                isClosed_Icc.mem_of_tendsto (hDconv τ hτ) (Filter.Eventually.of_forall fun n => hDbounds n τ hτ)
              let μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
              letI : IsProbabilityMeasure μ := ⟨by simp [μ]⟩
              have hDconv_ae : ∀ᵐ τ ∂μ, Tendsto (fun n => D n τ) atTop (𝓝 (G τ)) := by
                filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
                exact hDconv τ hτ
              have hGmeas : AEStronglyMeasurable G μ :=
                aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hDmeas n).aestronglyMeasurable) hDconv_ae
              have hGint : Integrable G μ := by
                apply (integrable_const (1 : ℝ)).mono' hGmeas
                filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
                rw [Real.norm_eq_abs, abs_of_nonneg (hGbounds τ hτ).1]
                exact (hGbounds τ hτ).2
              have hD_integral_conv : Tendsto (fun n => ∫ τ, D n τ ∂μ) atTop (𝓝 (∫ τ, G τ ∂μ)) := by
                apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
                  (fun n => (hDmeas n).aestronglyMeasurable) (integrable_const (1 : ℝ))
                · intro n
                  filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
                  rw [Real.norm_eq_abs, abs_of_nonneg (hDbounds n τ hτ).1]
                  exact (hDbounds n τ hτ).2
                · exact hDconv_ae
              have hprob_integral (n : ℕ) : selectionProbability (n + (j - 1) + 1) p t j = ∫ τ, D n τ ∂μ := by
                let M := n + (j - 1)
                letI : IsProbabilityMeasure (arrivalLaw M) := ⟨hlaw M⟩
                let a : Fin (M + 1) := ⟨j - 1, by dsimp only [M]; omega⟩
                have haj : a.val + 1 = j := by dsimp only [a]; omega
                have hevent (u : Fin (M + 1) → ℝ) :
                    (∃ b : Fin (M + 1), b.val + 1 = j ∧ thresholdChoice (M + 1) p t u = some b) ↔
                      thresholdChoice (M + 1) p t u = some a := by
                  constructor
                  · rintro ⟨b, hbj, hb⟩
                    have hba : b = a := Fin.ext (by omega)
                    simpa only [hba] using hb
                  · intro h; exact ⟨a, haj, h⟩
                let F : (Fin (M + 1) → ℝ) → ℝ := fun u => if thresholdChoice (M + 1) p t u = some a then 1 else 0
                have hFmeas : Measurable F := by
                  apply Measurable.ite ?_ measurable_const measurable_const
                  have hs : {u : Fin (M + 1) → ℝ | thresholdChoice (M + 1) p t u = some a} =
                      {u | ∃ b : Fin (M + 1), b.val + 1 = j ∧ thresholdChoice (M + 1) p t u = some b} := by
                    ext u; exact (hevent u).symm
                  rw [hs]; exact hevent_meas (M + 1)
                have hFint : Integrable F (arrivalLaw (M + 1)) := by
                  letI : IsProbabilityMeasure (arrivalLaw (M + 1)) := ⟨hlaw _⟩
                  apply (integrable_const (1 : ℝ)).mono' hFmeas.aestronglyMeasurable
                  exact Filter.Eventually.of_forall fun u => by dsimp only [F]; split <;> norm_num
                let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (M + 1) => ℝ) a
                have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (M + 1) => μ) a
                have hcomp_int : Integrable (fun z : ℝ × (Fin M → ℝ) => F (a.insertNth (α := fun _ => ℝ) z.1 z.2))
                    (μ.prod (arrivalLaw M)) := by
                  have hi := (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).mpr hFint
                  simpa only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
                    Fin.insertNthEquiv, Equiv.coe_fn_mk, arrivalLaw] using hi
                calc
                  selectionProbability (n + (j - 1) + 1) p t j = ∫ u, F u ∂arrivalLaw (M + 1) := by
                    rw [hprob_real]
                    apply integral_congr_ae
                    exact Filter.Eventually.of_forall fun u => by
                      change (if ∃ b : Fin (M + 1), b.val + 1 = j ∧ thresholdChoice (M + 1) p t u = some b
                        then (1 : ℝ) else 0) = F u
                      simp only [F, hevent u]
                  _ = ∫ z : ℝ × (Fin M → ℝ), F (a.insertNth (α := fun _ => ℝ) z.1 z.2)
                      ∂(μ.prod (arrivalLaw M)) := by
                    simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
                      Equiv.coe_fn_mk, arrivalLaw] using (hmp.symm.integral_comp' F).symm
                  _ = ∫ τ, ∫ u, F (a.insertNth (α := fun _ => ℝ) τ u) ∂arrivalLaw M ∂μ :=
                    integral_prod _ hcomp_int
                  _ = ∫ τ, D n τ ∂μ := by
                    apply integral_congr_ae
                    filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
                    have hinner : (∫ u, F (a.insertNth (α := fun _ => ℝ) τ u) ∂arrivalLaw M) =
                        ∫ u, joint n (j - 1) 0 τ u ∂arrivalLaw M := by
                      apply integral_congr_ae
                      have hall : ∀ᵐ u : Fin M → ℝ ∂arrivalLaw M, ∀ b, u b ≠ τ := by
                        apply ae_all_iff.mpr
                        intro b
                        exact Measure.ae_eval_ne (fun _ : Fin M => volume.restrict (Set.Icc (0 : ℝ) 1)) b τ
                      filter_upwards [hall] with u hu
                      have hc := hdelete_choice M a τ u hu
                      simp only [F, hc, joint, Nat.zero_add]
                      rfl
                    rw [hinner, hjoint_integral n (j - 1) 0 τ hτ]
              have hTs (k : ℕ) : thresholdProd t (k + 1) =
                  thresholdProd t k * t (k + 1) := by
                exact Finset.prod_Icc_succ_top (by omega) t
              have hSweighted (i : ℕ) (τ : ℝ) (hτ : τ ∈ Set.Ioc (0 : ℝ) 1)
                  (hlo : t i ≤ τ) (hhi : τ ≤ t (i + 1)) (k : ℕ) (hk : k ≤ i) :
                  thresholdProd t k * (⨅ n, S n k τ) =
                    thresholdProd t i / τ ^ i * τ ^ k := by
                have hτcc : τ ∈ Set.Icc (0 : ℝ) 1 := ⟨hτ.1.le, hτ.2⟩
                apply Nat.decreasingInduction (motive := fun k _ =>
                  thresholdProd t k * (⨅ n, S n k τ) =
                    thresholdProd t i / τ ^ i * τ ^ k) ?_ ?_ hk
                · intro k hki ih
                  have htk : t (k + 1) ≤ τ := (htmon hki).trans hlo
                  have hfixed := hSfixed k τ hτcc
                  rw [min_eq_left htk] at hfixed
                  apply mul_left_cancel₀ (ne_of_gt hτ.1)
                  calc
                    τ * (thresholdProd t k * (⨅ n, S n k τ)) =
                        thresholdProd t (k + 1) * (⨅ n, S n (k + 1) τ) := by
                      rw [hTs]
                      linear_combination thresholdProd t k * hfixed
                    _ = thresholdProd t i / τ ^ i * τ ^ (k + 1) := ih
                    _ = τ * (thresholdProd t i / τ ^ i * τ ^ k) := by
                      rw [pow_succ]; ring
                · have hone : (⨅ n, S n i τ) = 1 := by simp_rw [hSone _ i τ hhi]; simp
                  rw [hone, mul_one, div_mul_cancel₀ _ (pow_ne_zero _ (ne_of_gt hτ.1))]
              have hSgeometric (c τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
                  (hc : ∀ k, t k ≤ c) (n k : ℕ) : S n k τ ≤ (1 - τ + c) ^ n := by
                have hc0 : 0 ≤ c := (ht0 0).trans (hc 0)
                have hr0 : 0 ≤ 1 - τ + c := add_nonneg (sub_nonneg.mpr hτ.2) hc0
                induction n generalizing k with
                | zero => simp [hS0]
                | succ n ih =>
                  rw [hSs, pow_succ]
                  calc
                    _ ≤ (1 - τ) * (1 - τ + c) ^ n +
                        min (t (k + 1)) τ * (1 - τ + c) ^ n :=
                      add_le_add (mul_le_mul_of_nonneg_left (ih k) (sub_nonneg.mpr hτ.2))
                        (mul_le_mul_of_nonneg_left (ih (k + 1)) (le_min (ht0 _) hτ.1))
                    _ ≤ (1 - τ + c) ^ n * (1 - τ + c) := by
                      have hm : min (t (k + 1)) τ ≤ c := (min_le_left _ _).trans (hc _)
                      have hp := pow_nonneg hr0 n
                      nlinarith
              have hSabove (c τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
                  (hc : ∀ k, t k ≤ c) (hct : c < τ) (k : ℕ) :
                  Tendsto (fun n => S n k τ) atTop (𝓝 0) := by
                have hc0 : 0 ≤ c := (ht0 0).trans (hc 0)
                apply squeeze_zero (fun n => (hSbounds n k τ hτ).1) (hSgeometric c τ hτ hc · k)
                exact tendsto_pow_atTop_nhds_zero_of_lt_one
                  (add_nonneg (sub_nonneg.mpr hτ.2) hc0) (by linarith)
              have hPzero (m k : ℕ) (τ : ℝ) (f : ℕ → ℝ) (hf : ∀ r, k ≤ r → f r = 0) : P m k τ f = 0 := by
                induction m generalizing k with
                | zero => exact hf k le_rfl
                | succ m ih =>
                  rw [hPs, ih k hf, ih (k + 1) (fun r hr => hf r (by omega))]
                  ring
              have hQstep (m k : ℕ) (τ : ℝ) (f : ℕ → ℝ)
                  (hf : ∀ r, τ < t (r + 1) → f r = 0) :
                  thresholdProd t k * P (m + 1) k τ f =
                    (1 - τ) * (thresholdProd t k * P m k τ f) +
                    thresholdProd t (k + 1) * P m (k + 1) τ f := by
                by_cases hk : t (k + 1) ≤ τ
                · rw [hPs, min_eq_left hk, hTs]; ring
                · have hz : P m (k + 1) τ f = 0 := by
                    apply hPzero
                    intro r hr
                    exact hf r ((lt_of_not_ge hk).trans_le (htmon (by omega)))
                  rw [hPs, hz, hTs]; ring
              have hQsum (m k : ℕ) (τ : ℝ) (f : ℕ → ℝ)
                  (hf : ∀ r, τ < t (r + 1) → f r = 0) :
                  thresholdProd t k * P m k τ f =
                    ∑ r ∈ Finset.range (m + 1), (m.choose r : ℝ) *
                      ((1 - τ) ^ (m - r) * (thresholdProd t (k + r) * f (k + r))) := by
                induction m generalizing k with
                | zero => simp [hP0]
                | succ m ih =>
                  rw [hQstep m k τ f hf, ih k, ih (k + 1),
                    Finset.sum_choose_succ_mul (fun r s => (1 - τ) ^ s *
                      (thresholdProd t (k + r) * f (k + r))) m]
                  congr 1
                  · rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro r hr
                    have hrm : r ≤ m := by have := Finset.mem_range.mp hr; omega
                    rw [show m + 1 - r = (m - r) + 1 by omega, pow_succ]
                    ring
                  · apply Finset.sum_congr rfl
                    intro r hr
                    rw [show k + 1 + r = k + (r + 1) by omega]
              have hGinterval (i : ℕ) (hi : 1 ≤ i) (τ : ℝ) (hτ0 : 0 < τ)
                  (hlo : t i ≤ τ) (hhi : τ < t (i + 1)) : G τ = rankLimitIntegrand t j i τ := by
                have hτ1 : τ ≤ 1 := hhi.le.trans (ht1 _)
                let f : ℕ → ℝ := fun r => if t (r + 1) ≤ τ then ⨅ n, S n r τ else 0
                have hf : ∀ r, τ < t (r + 1) → f r = 0 := by intro r hr; simp only [f, not_le.mpr hr, if_false]
                have hexp := hQsum (j - 1) 0 τ f hf
                have hj' : j - 1 + 1 = j := by omega
                have hT0 : thresholdProd t 0 = 1 := by
                  simp [thresholdProd]
                simp only [hT0, one_mul, Nat.zero_add, hj'] at hexp
                let H : ℕ → ℝ := fun l => thresholdProd t i / τ ^ i *
                  ((j - 1).choose (l - 1) : ℝ) * (1 - τ) ^ (j - l) * τ ^ (l - 1)
                calc
                  G τ = ∑ r ∈ Finset.range j, if r < i then H (r + 1) else 0 := by
                    change P (j - 1) 0 τ f = _
                    rw [hexp]
                    apply Finset.sum_congr rfl
                    intro r hr
                    by_cases hri : r < i
                    · have htr : t (r + 1) ≤ τ := (htmon hri).trans hlo
                      simp only [f, htr, if_true, hri]
                      rw [hSweighted i τ ⟨hτ0, hτ1⟩ hlo hhi.le r (by omega)]
                      dsimp only [H]
                      simp only [Nat.add_sub_cancel]
                      rw [show j - 1 - r = j - (r + 1) by omega]
                      ring
                    · have htr : τ < t (r + 1) := hhi.trans_le (htmon (by omega))
                      simp only [f, not_le.mpr htr, if_false, hri, mul_zero]
                  _ = ∑ r ∈ (Finset.range j).filter (fun r => r < i), H (r + 1) := by rw [Finset.sum_filter]
                  _ = ∑ l ∈ Finset.Icc 1 (min j i), H l := by
                    apply Finset.sum_bij (fun r _ => r + 1)
                    · intro r hr
                      obtain ⟨hrj, hri⟩ := Finset.mem_filter.mp hr
                      have hrj' := Finset.mem_range.mp hrj
                      exact Finset.mem_Icc.mpr ⟨by omega, le_min (by omega) (by omega)⟩
                    · intro r hr s hs heq
                      omega
                    · intro l hl
                      obtain ⟨hl1, hl2⟩ := Finset.mem_Icc.mp hl
                      have hlj := hl2.trans (min_le_left j i)
                      have hli := hl2.trans (min_le_right j i)
                      refine ⟨l - 1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega⟩, by omega⟩
                    · intro r hr; rfl
                  _ = rankLimitIntegrand t j i τ := rfl
              have hGbelow (τ : ℝ) (hτ : τ < t 1) : G τ = 0 := by
                apply hPzero
                intro r hr
                have htr : τ < t (r + 1) := hτ.trans_le (htmon (by omega))
                simp only [not_le.mpr htr, if_false]
              let c : ℝ := sSup (Set.range t)
              have hcbdd : BddAbove (Set.range t) := ⟨1, by rintro _ ⟨k, rfl⟩; exact ht1 k⟩
              have hcle (k : ℕ) : t k ≤ c := le_csSup hcbdd ⟨k, rfl⟩
              have hGabove (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hcτ : c < τ) : G τ = 0 := by
                have hL (r : ℕ) : (⨅ n, S n r τ) = 0 :=
                  tendsto_nhds_unique (hSconv r τ hτ) (hSabove c τ hτ hcle hcτ r)
                apply hPzero
                intro r hr
                split <;> simp only [hL, if_true]
              let E : ℕ → Set ℝ := fun i => Set.Ioc (t (i + 1)) (t (i + 1 + 1))
              have hEmeas (i : ℕ) : MeasurableSet (E i) := measurableSet_Ioc
              have hEsub (i : ℕ) : E i ⊆ Set.Icc (0 : ℝ) 1 := by
                intro τ hτ
                exact ⟨(ht0 _).trans hτ.1.le, hτ.2.trans (ht1 _)⟩
              have hEdisj : Pairwise (Function.onFun Disjoint E) := by
                intro i k hik
                apply Set.disjoint_left.mpr
                intro τ hτi hτk
                rcases lt_or_gt_of_ne hik with hik | hki
                · have hle : t (i + 1 + 1) ≤ t (k + 1) := htmon (by omega)
                  exact (not_lt_of_ge (hτi.2.trans hle)) hτk.1
                · have hle : t (k + 1 + 1) ≤ t (i + 1) := htmon (by omega)
                  exact (not_lt_of_ge (hτk.2.trans hle)) hτi.1
              have hEcover (τ : ℝ) (hlo : t 1 < τ) (hhi : τ < c) : ∃ i, τ ∈ E i := by
                have hex : ∃ k : ℕ, τ ≤ t k := by
                  by_contra h
                  have hle : c ≤ τ := csSup_le (Set.range_nonempty t) (by
                    rintro _ ⟨k, rfl⟩
                    exact le_of_lt (lt_of_not_ge (fun hk => h ⟨k, hk⟩)))
                  exact (not_le_of_gt hhi) hle
                let k := Nat.find hex
                have hkτ : τ ≤ t k := Nat.find_spec hex
                have hk2 : 2 ≤ k := by
                  by_contra h
                  have hk1 : k ≤ 1 := by omega
                  exact (not_le_of_gt hlo) (hkτ.trans (htmon hk1))
                have hprev : t (k - 1) < τ :=
                  lt_of_not_ge (Nat.find_min hex (show k - 1 < Nat.find hex by dsimp only [k] at hk2 ⊢; omega))
                refine ⟨k - 2, ?_⟩
                change t (k - 2 + 1) < τ ∧ τ ≤ t (k - 2 + 1 + 1)
                rw [show k - 2 + 1 = k - 1 by omega, show k - 1 + 1 = k by omega]
                exact ⟨hprev, hkτ⟩
              have hGoff : ∀ᵐ τ ∂μ, τ ∉ ⋃ i, E i → G τ = 0 := by
                filter_upwards [ae_restrict_mem measurableSet_Icc, Measure.ae_ne μ (t 1), Measure.ae_ne μ c]
                  with τ hτ hne1 hnec
                intro hn
                by_cases hbelow : τ < t 1
                · exact hGbelow τ hbelow
                · have hlo : t 1 < τ := lt_of_le_of_ne (le_of_not_gt hbelow) (Ne.symm hne1)
                  by_cases hbefore : τ < c
                  · obtain ⟨i, hi⟩ := hEcover τ hlo hbefore
                    exact (hn (Set.mem_iUnion.mpr ⟨i, hi⟩)).elim
                  · exact hGabove τ hτ (lt_of_le_of_ne (le_of_not_gt hbefore) (Ne.symm hnec))
              have hEint (i : ℕ) : (∫ τ in E i, G τ ∂μ) = rankLimitTerm t j (i + 1) := by
                have hre : μ.restrict (E i) = volume.restrict (E i) :=
                  Measure.restrict_restrict_of_subset (hEsub i)
                change (∫ τ, G τ ∂μ.restrict (E i)) = _
                rw [hre]
                rw [rankLimitTerm, intervalIntegral.integral_of_le (htmon (Nat.le_succ (i + 1)))]
                apply integral_congr_ae
                filter_upwards [ae_restrict_mem (hEmeas i),
                  ae_restrict_of_ae (Measure.ae_ne volume (t (i + 1 + 1)))] with τ hτ hne
                exact hGinterval (i + 1) (by omega) τ ((ht0 _).trans_lt hτ.1) hτ.1.le
                  (lt_of_le_of_ne hτ.2 hne)
              have hGsum : (∫ τ, G τ ∂μ) = ∑' i : ℕ, rankLimitTerm t j (i + 1) := by
                rw [← setIntegral_eq_integral_of_ae_compl_eq_zero hGoff,
                  integral_iUnion hEmeas hEdisj hGint.integrableOn]
                exact tsum_congr hEint
              refine ⟨hint, hsum, ?_⟩
              apply (tendsto_add_atTop_iff_nat (j - 1)).mp
              simpa only [hprob_integral, hGsum] using hD_integral_conv
