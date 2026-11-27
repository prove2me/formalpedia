-- Prove2me | solution 1 for ReedGGN.Regulator.Supplement.proposition_4_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:44:01.361625+00:00
-- url     : https://prove2.me/submissions/23156067-d7a9-4e87-916f-4345cd64afab

import Mathlib
import Definitions.Def_ReedGGN_Regulator_Supplement_Drivers

open MeasureTheory ProbabilityTheory Filter Topology

open scoped NNReal ENNReal

open ReedGGN
open ReedGGN.Regulator
open ReedGGN.Regulator.Supplement

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ μ₀ : Measure ℝ) (q : QueueFamily Ω P μ μ₀) :
    WeakJ1 P P (fun n ω => one (mbar q n ω)) (fun _ => one (fun _ => 0)) := by
      classical
      let : IsProbabilityMeasure μ := q.service_law.1
      have hfreshlaw (i : ℕ) : IdentDistrib (q.fresh (i + 1)) id P μ := by
        refine ⟨(q.fresh_measurable _).aemeasurable, measurable_id.aemeasurable, ?_⟩
        simpa using q.fresh_dist i
      have hstrong (f : ℝ → ℝ) (hf : Measurable f) (hi : Integrable f μ) :
          ∀ᵐ ω ∂P, Tendsto
            (fun n : ℕ => (∑ i ∈ Finset.range n, f (q.fresh (i + 1) ω)) / n)
            atTop (𝓝 (∫ x, f x ∂μ)) := by
        have hdist (i : ℕ) : IdentDistrib (fun ω => f (q.fresh (i + 1) ω)) f P μ :=
          (hfreshlaw i).comp hf
        have hint : Integrable (fun ω => f (q.fresh (0 + 1) ω)) P :=
          (hdist 0).symm.integrable_snd hi
        have hpair : Pairwise (fun i j => IndepFun (fun ω => f (q.fresh (i + 1) ω))
            (fun ω => f (q.fresh (j + 1) ω)) P) := by
          intro i j hij
          exact (q.fresh_iid.indepFun hij).comp hf hf
        have hident (i : ℕ) : IdentDistrib (fun ω => f (q.fresh (i + 1) ω))
            (fun ω => f (q.fresh (0 + 1) ω)) P P :=
          (hdist i).trans (hdist 0).symm
        simpa only [(hdist 0).integral_eq] using
          strong_law_ae_real (fun i ω => f (q.fresh (i + 1) ω)) hint hpair hident
      have hnonneg : ∀ᵐ ω ∂P, ∀ i : ℕ, 0 ≤ q.fresh (i + 1) ω := by
        have hμnonneg : ∀ᵐ x ∂μ, (0 : ℝ) ≤ x := by
          rw [ae_iff]
          simp only [not_le]
          change μ (Set.Iio 0) = 0
          exact q.service_law.2.1
        exact ae_all_iff.mpr fun i => (hfreshlaw i).symm.ae_snd measurableSet_Ici hμnonneg
      have hfcfs : ∀ᵐ ω ∂P, ∀ n H : ℕ, IsFCFS (q.sample n ω H) := by
        exact ae_all_iff.mpr fun n => ae_all_iff.mpr fun H => q.fcfs n H
      have hmean : ∀ᵐ ω ∂P, Tendsto
          (fun n : ℕ => (∑ i ∈ Finset.range n, q.fresh (i + 1) ω) / n)
          atTop (𝓝 1) := by
        simpa only [id_eq, q.service_law.2.2.2] using
          hstrong id measurable_id q.service_law.2.2.1
      have hcount (α : Type) [LinearOrder α] [TopologicalSpace α]
          [TopologicalSpace.SeparableSpace α] [ClosedIicTopology α] :
          IsCountablyGenerated (atTop : Filter α) := by
        obtain (h | ⟨x, hx⟩) := Set.eq_empty_or_nonempty {x : α | IsTop x}
        · obtain ⟨s, hs, hd⟩ := TopologicalSpace.exists_countable_dense α
          have heq : (atTop : Filter α) = Filter.generate (Set.Ici '' s) := by
            refine atTop_eq_generate_of_not_bddAbove fun ⟨x, hx⟩ => ?_
            simp only [Set.eq_empty_iff_forall_notMem, IsTop, Set.mem_ofPred_eq,
              not_forall, not_le] at h
            obtain ⟨y, hy, hxy⟩ := hd.exists_mem_open isOpen_Ioi (h x)
            exact (hx hy).not_gt hxy
          rw [heq]
          exact ⟨_, hs.image _, rfl⟩
        · rw [atTop_eq_pure_of_isTop hx]
          infer_instance
      have henvelope (s : Set ℝ) (hs : s.Nonempty) :
          MeasurableSet (⋂ t : s, Set.Ioi (t : ℝ)) ∧
          μ (⋂ t : s, Set.Ioi (t : ℝ)) = ⨅ t : s, μ (Set.Ioi (t : ℝ)) ∧
          μ (⋃ t : s, Set.Ioi (t : ℝ)) = ⨆ t : s, μ (Set.Ioi (t : ℝ)) := by
        let : Nonempty s := hs.to_subtype
        let : IsCountablyGenerated (atTop : Filter s) := hcount s
        let : IsCountablyGenerated (atBot : Filter s) := hcount (OrderDual s)
        have hm : Antitone (fun t : s => Set.Ioi (t : ℝ)) := by
          intro a b hab
          exact Set.Ioi_subset_Ioi hab
        obtain ⟨v, hv, hlim⟩ := exists_seq_monotone_tendsto_atTop_atTop s
        have heq : (⋂ t : s, Set.Ioi (t : ℝ)) = ⋂ n : ℕ, Set.Ioi (v n : ℝ) := by
          apply Set.Subset.antisymm
          · exact Set.iInter_mono' fun n => ⟨v n, Set.Subset.rfl⟩
          · apply Set.iInter_mono'
            intro t
            obtain ⟨n, hn⟩ := (hlim.eventually_ge_atTop t).exists
            exact ⟨n, hm hn⟩
        refine ⟨?_, hm.measure_iInter (fun _ => measurableSet_Ioi.nullMeasurableSet)
          ⟨⟨hs.choose, hs.choose_spec⟩, measure_ne_top _ _⟩, hm.measure_iUnion⟩
        rw [heq]
        exact MeasurableSet.iInter (fun _ => measurableSet_Ioi)
      let C : ℕ → ℕ → Set ℝ := fun m b =>
        {t | (b : ℝ) / (m + 1 : ℝ) ≤ ReedGGN.SystemEq.G μ t ∧
          ReedGGN.SystemEq.G μ t ≤ (b + 1 : ℝ) / (m + 1 : ℝ)}
      let L : ℕ → ℕ → Set ℝ := fun m b =>
        if (C m b).Nonempty then ⋂ t : C m b, Set.Ioi (t : ℝ) else ∅
      let U : ℕ → ℕ → Set ℝ := fun m b => ⋃ t : C m b, Set.Ioi (t : ℝ)
      have hLm (m b : ℕ) : MeasurableSet (L m b) := by
        dsimp [L]
        split_ifs with h
        · exact (henvelope _ h).1
        · exact MeasurableSet.empty
      have hUm (m b : ℕ) : MeasurableSet (U m b) :=
        (isOpen_iUnion fun _ => isOpen_Ioi).measurableSet
      have hbracket (m b : ℕ) (t : ℝ) (ht : t ∈ C m b) :
          L m b ⊆ Set.Ioi t ∧ Set.Ioi t ⊆ U m b := by
        constructor
        · dsimp [L]
          rw [if_pos ⟨t, ht⟩]
          exact Set.iInter_subset (fun t : C m b => Set.Ioi (t : ℝ)) ⟨t, ht⟩
        · exact Set.subset_iUnion (fun t : C m b => Set.Ioi (t : ℝ)) ⟨t, ht⟩
      have hwidth (m b : ℕ) : μ.real (U m b) - μ.real (L m b) ≤ 1 / (m + 1 : ℝ) := by
        by_cases hs : (C m b).Nonempty
        · obtain ⟨hm, hlow, hupp⟩ := henvelope (C m b) hs
          have hu : μ (U m b) ≤ ENNReal.ofReal ((b + 1 : ℝ) / (m + 1 : ℝ)) := by
            change μ (⋃ t : C m b, Set.Ioi (t : ℝ)) ≤ _
            rw [hupp]
            refine iSup_le fun t => ?_
            apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).mpr
            exact t.2.2
          have hl : ENNReal.ofReal ((b : ℝ) / (m + 1 : ℝ)) ≤ μ (L m b) := by
            dsimp [L]
            rw [if_pos hs, hlow]
            refine le_iInf fun t => ?_
            apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr
            exact t.2.1
          have hu' := ENNReal.toReal_le_of_le_ofReal (by positivity) hu
          have hl' := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ (L m b))).mp hl
          change (μ (U m b)).toReal - (μ (L m b)).toReal ≤ _
          have heq : (b + 1 : ℝ) / (m + 1 : ℝ) - (b : ℝ) / (m + 1 : ℝ) =
              1 / (m + 1 : ℝ) := by ring
          linarith
        · have he : C m b = ∅ := Set.not_nonempty_iff_eq_empty.mp hs
          have hu : U m b = ∅ := by
            dsimp [U]
            apply Set.iUnion_eq_empty.mpr
            intro t
            exact (hs ⟨t, t.2⟩).elim
          simp only [L, if_neg hs, hu, measureReal_empty, sub_self]
          positivity
      have hbracket_slln : ∀ᵐ ω ∂P, ∀ m b : ℕ,
          Tendsto (fun k : ℕ => (∑ i ∈ Finset.range k,
            (L m b).indicator (fun _ => (1 : ℝ)) (q.fresh (i + 1) ω)) / k)
            atTop (𝓝 (μ.real (L m b))) ∧
          Tendsto (fun k : ℕ => (∑ i ∈ Finset.range k,
            (U m b).indicator (fun _ => (1 : ℝ)) (q.fresh (i + 1) ω)) / k)
            atTop (𝓝 (μ.real (U m b))) := by
        apply ae_all_iff.mpr
        intro m
        apply ae_all_iff.mpr
        intro b
        have hl := hstrong ((L m b).indicator (fun _ => (1 : ℝ)))
          (measurable_const.indicator (hLm m b))
          ((integrable_const (1 : ℝ)).indicator (hLm m b))
        have hu := hstrong ((U m b).indicator (fun _ => (1 : ℝ)))
          (measurable_const.indicator (hUm m b))
          ((integrable_const (1 : ℝ)).indicator (hUm m b))
        have hli : (∫ x, (L m b).indicator (fun _ => (1 : ℝ)) x ∂μ) = μ.real (L m b) :=
          integral_indicator_one (hLm m b)
        have hui : (∫ x, (U m b).indicator (fun _ => (1 : ℝ)) x ∂μ) = μ.real (U m b) :=
          integral_indicator_one (hUm m b)
        rw [hli] at hl
        rw [hui] at hu
        exact hl.and hu
      have hprefix (f : ℕ → ℝ) (a : ℝ)
          (ha : Tendsto (fun k : ℕ => (∑ i ∈ Finset.range k, f i) / k) atTop (𝓝 a))
          (ε : ℝ) (hε : 0 < ε) :
          ∃ D : ℝ, 0 ≤ D ∧ ∀ k : ℕ,
            |∑ i ∈ Finset.range k, (f i - a)| ≤ ε * k + D := by
        obtain ⟨K, hK⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp ha) ε hε)
        let D : ℝ := ∑ j ∈ Finset.range K, |∑ i ∈ Finset.range j, (f i - a)|
        have hD : 0 ≤ D := Finset.sum_nonneg fun j hj => abs_nonneg _
        refine ⟨D, hD, ?_⟩
        intro k
        by_cases hk0 : k = 0
        · subst k
          simpa using hD
        by_cases hk : k < K
        · have hsmall : |∑ i ∈ Finset.range k, (f i - a)| ≤ D := by
            dsimp [D]
            exact Finset.single_le_sum
              (fun j hj => abs_nonneg (∑ i ∈ Finset.range j, (f i - a)))
              (Finset.mem_range.mpr hk)
          have he : 0 ≤ ε * k := mul_nonneg hε.le (Nat.cast_nonneg _)
          linarith
        · have hkpos : (0 : ℝ) < k := by exact_mod_cast (Nat.pos_of_ne_zero hk0)
          have hlarge := hK k (by omega)
          rw [Real.dist_eq] at hlarge
          have heq : (∑ i ∈ Finset.range k, (f i - a)) / k =
              (∑ i ∈ Finset.range k, f i) / k - a := by
            simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            field_simp
          rw [← heq, abs_div, abs_of_pos hkpos] at hlarge
          have hmul := (div_lt_iff₀ hkpos).mp hlarge
          linarith
      have hinterval_partition (k : ℕ) (b : ℕ → ℕ) (hb : Monotone b) (r : ℕ) :
          ∃ a z : ℕ, a ≤ z ∧ z ≤ k ∧
            ((Finset.range k).filter fun i => b i = r) = Finset.Ico a z := by
        let s := (Finset.range k).filter fun i => b i = r
        by_cases hs : s.Nonempty
        · let a := s.min' hs
          let z := s.max' hs + 1
          have ha : a ∈ s := Finset.min'_mem _ _
          have hz : z - 1 ∈ s := by simpa only [z, Nat.add_sub_cancel] using Finset.max'_mem s hs
          have haz : a < z := by
            have h := Finset.le_max' s a ha
            dsimp [z]
            omega
          have hzk : z ≤ k := by
            have hm := (Finset.mem_filter.mp (Finset.max'_mem s hs)).1
            have := Finset.mem_range.mp hm
            dsimp [z]
            omega
          refine ⟨a, z, haz.le, hzk, ?_⟩
          apply Finset.ext
          intro i
          constructor
          · intro hi
            have hmin := Finset.min'_le s i hi
            have hmax := Finset.le_max' s i hi
            apply Finset.mem_Ico.mpr
            dsimp [a, z]
            omega
          · intro hi
            obtain ⟨hai, hiz⟩ := Finset.mem_Ico.mp hi
            have hi' : i ≤ z - 1 := by omega
            have hba : b a = r := (Finset.mem_filter.mp ha).2
            have hbz : b (z - 1) = r := (Finset.mem_filter.mp hz).2
            apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_range.mpr (by omega), le_antisymm ?_ ?_⟩
            · simpa only [hbz] using hb hi'
            · simpa only [hba] using hb hai
        · refine ⟨0, 0, le_rfl, Nat.zero_le _, ?_⟩
          simpa only [Finset.Ico_self] using Finset.not_nonempty_iff_eq_empty.mp hs
      have hG_nonneg (t : ℝ) : 0 ≤ ReedGGN.SystemEq.G μ t := ENNReal.toReal_nonneg
      have hG_le_one (t : ℝ) : ReedGGN.SystemEq.G μ t ≤ 1 := by
        simpa only [ReedGGN.SystemEq.G, ENNReal.toReal_one] using
          ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := μ) (s := Set.Ioi t))
      have hG_anti : Antitone (ReedGGN.SystemEq.G μ) := by
        intro a b hab
        exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Ioi_subset_Ioi hab))
      have hfinite_noise (η : ℕ → ℝ) (m k : ℕ) (d : ℝ)
          (hbound : ∀ b < m + 2, ∀ a z : ℕ, a ≤ z → z ≤ k →
            |∑ i ∈ Finset.Ico a z, ((L m b).indicator (fun _ => (1 : ℝ)) (η i) - μ.real (L m b))| ≤ d ∧
            |∑ i ∈ Finset.Ico a z, ((U m b).indicator (fun _ => (1 : ℝ)) (η i) - μ.real (U m b))| ≤ d)
          (u : ℕ → ℝ) (hu : Antitone u) :
          |∑ i ∈ Finset.range k,
            ((if u i < η i then (1 : ℝ) else 0) - ReedGGN.SystemEq.G μ (u i))| ≤
            (m + 2 : ℝ) * d + k / (m + 1 : ℝ) := by
        let bin : ℕ → ℕ := fun i => ⌊ReedGGN.SystemEq.G μ (u i) * (m + 1 : ℝ)⌋₊
        have hmpos : (0 : ℝ) < m + 1 := by positivity
        have hbin_mono : Monotone bin := by
          intro i j hij
          apply Nat.floor_mono
          exact mul_le_mul_of_nonneg_right (hG_anti (hu hij)) hmpos.le
        have hbin_bound (i : ℕ) : bin i < m + 2 := by
          have hle : bin i ≤ m + 1 := by
            apply Nat.floor_le_of_le
            push_cast
            nlinarith [hG_le_one (u i)]
          omega
        have hbinmem (i : ℕ) (hi : i ∈ Finset.range k) : bin i ∈ Finset.range (m + 2) :=
          Finset.mem_range.mpr (hbin_bound i)
        have hbin_C (i : ℕ) : u i ∈ C m (bin i) := by
          constructor
          · apply (div_le_iff₀ hmpos).mpr
            exact Nat.floor_le (mul_nonneg (hG_nonneg _) hmpos.le)
          · apply (le_div_iff₀ hmpos).mpr
            exact le_of_lt (Nat.lt_floor_add_one _)
        let v : ℕ → ℝ := fun i =>
          (if u i < η i then (1 : ℝ) else 0) - ReedGGN.SystemEq.G μ (u i)
        have hpoint (b i : ℕ) (hi : i ∈ (Finset.range k).filter fun j => bin j = b) :
            ((L m b).indicator (fun _ => (1 : ℝ)) (η i) - μ.real (L m b)) - 1 / (m + 1 : ℝ) ≤ v i ∧
            v i ≤ ((U m b).indicator (fun _ => (1 : ℝ)) (η i) - μ.real (U m b)) + 1 / (m + 1 : ℝ) := by
          have hib : bin i = b := (Finset.mem_filter.mp hi).2
          have hCi : u i ∈ C m b := by simpa only [hib] using hbin_C i
          obtain ⟨hl, hu'⟩ := hbracket m b (u i) hCi
          have hil := Set.indicator_le_indicator_of_subset hl
            (show (0 : ℝ → ℝ) ≤ fun _ => 1 from fun _ => zero_le_one) (η i)
          have hiu := Set.indicator_le_indicator_of_subset hu'
            (show (0 : ℝ → ℝ) ≤ fun _ => 1 from fun _ => zero_le_one) (η i)
          have heq : (Set.Ioi (u i)).indicator (fun _ => (1 : ℝ)) (η i) =
              if u i < η i then 1 else 0 := by simp only [Set.indicator, Set.mem_Ioi]
          rw [heq] at hil hiu
          have hml : μ.real (L m b) ≤ ReedGGN.SystemEq.G μ (u i) :=
            ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hl)
          have hmu : ReedGGN.SystemEq.G μ (u i) ≤ μ.real (U m b) :=
            ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hu')
          dsimp [v]
          constructor <;> linarith [hwidth m b]
        have hfiber (b : ℕ) (hb : b ∈ Finset.range (m + 2)) :
            |∑ i ∈ (Finset.range k).filter (fun j => bin j = b), v i| ≤
              d + (((Finset.range k).filter fun j => bin j = b).card : ℝ) / (m + 1 : ℝ) := by
          obtain ⟨a, z, haz, hzk, heq⟩ := hinterval_partition k bin hbin_mono b
          obtain ⟨hl, hu'⟩ := hbound b (Finset.mem_range.mp hb) a z haz hzk
          rw [← heq] at hl hu'
          have hlow := Finset.sum_le_sum (fun i hi => (hpoint b i hi).1)
          have hupp := Finset.sum_le_sum (fun i hi => (hpoint b i hi).2)
          simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
            nsmul_eq_mul] at hlow hupp
          simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hl hu'
          rw [abs_le] at hl hu' ⊢
          simp only [div_eq_mul_inv, one_mul] at hlow hupp ⊢
          constructor <;> linarith only [hl.1, hu'.2, hlow, hupp]
        have hcards : (∑ b ∈ Finset.range (m + 2),
            (((Finset.range k).filter fun i => bin i = b).card : ℝ)) = k := by
          simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_range] using
            Finset.sum_fiberwise_of_maps_to hbinmem (fun _ => (1 : ℝ))
        have hsum := Finset.sum_fiberwise_of_maps_to hbinmem v
        change |∑ i ∈ Finset.range k, v i| ≤ _
        rw [← hsum]
        calc
          _ ≤ ∑ b ∈ Finset.range (m + 2), |∑ i ∈ (Finset.range k).filter (fun j => bin j = b), v i| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ b ∈ Finset.range (m + 2),
              (d + (((Finset.range k).filter fun j => bin j = b).card : ℝ) / (m + 1 : ℝ)) :=
            Finset.sum_le_sum hfiber
          _ = _ := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
              ← Finset.sum_div, hcards]
            push_cast
            ring
      have hinterval_error (f : ℕ → ℝ) (ρ D : ℝ) (hρ : 0 ≤ ρ)
          (hf : ∀ k : ℕ, |∑ i ∈ Finset.range k, f i| ≤ ρ * k + D)
          (a z k : ℕ) (haz : a ≤ z) (hzk : z ≤ k) :
          |∑ i ∈ Finset.Ico a z, f i| ≤ 2 * ρ * k + 2 * D := by
        rw [Finset.sum_Ico_eq_sub f haz]
        calc
          _ ≤ |∑ i ∈ Finset.range z, f i| + |∑ i ∈ Finset.range a, f i| := abs_sub _ _
          _ ≤ (ρ * z + D) + (ρ * a + D) := add_le_add (hf z) (hf a)
          _ ≤ _ := by
            have hza : (a : ℝ) ≤ z := by exact_mod_cast haz
            have hzk' : (z : ℝ) ≤ k := by exact_mod_cast hzk
            nlinarith only [hza, hzk', hρ]
      have hnoise : ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
          ∃ D : ℝ, 0 ≤ D ∧ ∀ (k : ℕ) (u : ℕ → ℝ), Antitone u →
            |∑ i ∈ Finset.range k,
              ((if u i < q.fresh (i + 1) ω then (1 : ℝ) else 0) - ReedGGN.SystemEq.G μ (u i))| ≤
              ε * k + D := by
        filter_upwards [hbracket_slln] with ω hω
        intro ε hε
        obtain ⟨m, hm⟩ := exists_nat_one_div_lt (half_pos hε)
        let ρ : ℝ := ε / (4 * (m + 2 : ℝ))
        have hρ : 0 < ρ := by dsimp [ρ]; positivity
        have hc : ∀ b : Fin (m + 2), ∃ D : ℝ, 0 ≤ D ∧ ∀ k : ℕ,
            |∑ i ∈ Finset.range k,
              ((L m b).indicator (fun _ => (1 : ℝ)) (q.fresh (i + 1) ω) - μ.real (L m b))| ≤ ρ * k + D ∧
            |∑ i ∈ Finset.range k,
              ((U m b).indicator (fun _ => (1 : ℝ)) (q.fresh (i + 1) ω) - μ.real (U m b))| ≤ ρ * k + D := by
          intro b
          obtain ⟨D₁, hD₁, h₁⟩ := hprefix _ _ (hω m b).1 ρ hρ
          obtain ⟨D₂, hD₂, h₂⟩ := hprefix _ _ (hω m b).2 ρ hρ
          refine ⟨D₁ + D₂, add_nonneg hD₁ hD₂, ?_⟩
          intro k
          constructor <;> linarith [h₁ k, h₂ k]
        choose D hD hc using hc
        let A : ℝ := ∑ b : Fin (m + 2), D b
        have hA : 0 ≤ A := Finset.sum_nonneg fun b hb => hD b
        have hDA (b : Fin (m + 2)) : D b ≤ A := by
          exact Finset.single_le_sum (fun b hb => hD b) (Finset.mem_univ b)
        refine ⟨2 * (m + 2 : ℝ) * A, by positivity, ?_⟩
        intro k u hu
        have hbound : ∀ b < m + 2, ∀ a z : ℕ, a ≤ z → z ≤ k →
            |∑ i ∈ Finset.Ico a z,
              ((L m b).indicator (fun _ => (1 : ℝ)) (q.fresh (i + 1) ω) - μ.real (L m b))| ≤ 2 * ρ * k + 2 * A ∧
            |∑ i ∈ Finset.Ico a z,
              ((U m b).indicator (fun _ => (1 : ℝ)) (q.fresh (i + 1) ω) - μ.real (U m b))| ≤ 2 * ρ * k + 2 * A := by
          intro b hb a z haz hzk
          let b' : Fin (m + 2) := ⟨b, hb⟩
          have hl : ∀ k : ℕ, |∑ i ∈ Finset.range k,
              ((L m b).indicator (fun _ => (1 : ℝ)) (q.fresh (i + 1) ω) - μ.real (L m b))| ≤ ρ * k + A := by
            intro k
            exact (hc b' k).1.trans (by linarith [hDA b'])
          have hu' : ∀ k : ℕ, |∑ i ∈ Finset.range k,
              ((U m b).indicator (fun _ => (1 : ℝ)) (q.fresh (i + 1) ω) - μ.real (U m b))| ≤ ρ * k + A := by
            intro k
            exact (hc b' k).2.trans (by linarith [hDA b'])
          exact ⟨hinterval_error _ ρ A hρ.le hl a z k haz hzk,
            hinterval_error _ ρ A hρ.le hu' a z k haz hzk⟩
        have hres := hfinite_noise (fun i => q.fresh (i + 1) ω) m k
          (2 * ρ * k + 2 * A) hbound u hu
        have hρeq : 2 * (m + 2 : ℝ) * ρ = ε / 2 := by
          dsimp [ρ]
          field_simp
          ring
        have hδ : (k : ℝ) / (m + 1 : ℝ) ≤ ε / 2 * k := by
          have := mul_le_mul_of_nonneg_right hm.le (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
          simpa only [div_eq_mul_inv, one_mul, mul_comm] using this
        calc
          _ ≤ (m + 2 : ℝ) * (2 * ρ * k + 2 * A) + k / (m + 1 : ℝ) := hres
          _ = (2 * (m + 2 : ℝ) * ρ) * k + 2 * (m + 2 : ℝ) * A + k / (m + 1 : ℝ) := by ring
          _ ≤ ε * k + 2 * (m + 2 : ℝ) * A := by rw [hρeq]; linarith
      have hready_nonneg (p : ReedGGN.SystemEq.SamplePath) (j : ℕ) : 0 ≤ ready p j := by
        unfold ready
        split_ifs
        · rfl
        · simpa only [p.τ_zero] using p.τ_mono (Nat.zero_le (j + 1 - (p.Q₀ - p.N)))
      have hready_mono (p : ReedGGN.SystemEq.SamplePath) : Monotone (ready p) := by
        intro i j hij
        unfold ready
        split_ifs with hi hj hj
        · rfl
        · simpa only [ready, if_neg hj] using hready_nonneg p j
        · omega
        · exact p.τ_mono (by omega)
      have hentry_mono (p : ReedGGN.SystemEq.SamplePath) (hp : IsFCFS p) :
          Monotone (entry p) := by
        rcases hp with ⟨hN, hηt, hη, hNI, server, available, hinit, hmin, hent, hupd⟩
        apply monotone_nat_of_le_succ
        intro j
        rw [hent j, hent (j + 1)]
        apply max_le
        · exact (hready_mono p (Nat.le_succ j)).trans (le_max_left _ _)
        · have ha : available j (server j) ≤ available (j + 1) (server (j + 1)) := by
            rw [hupd]
            split_ifs with hs
            · exact (le_max_right _ _).trans (by rw [← hent j]; linarith [hη (j + 1)])
            · exact hmin j _
          exact ha.trans (le_max_right _ _)
      have hcapacity (p : ReedGGN.SystemEq.SamplePath) (hp : IsFCFS p)
          (T : ℝ) (hT : 0 ≤ T) (k : ℕ) (hk : ∀ j < k, entry p j ≤ T) :
          (∑ j ∈ Finset.range k, min (p.η (j + 1)) 1) ≤ (p.N : ℝ) * (T + 1) := by
        rcases hp with ⟨hN, hηt, hη, hNI, server, available, hinit, hmin, hent, hupd⟩
        have hstep (j : ℕ) (hj : j < k) :
            min (p.η (j + 1)) 1 ≤
              (∑ s : Fin p.N, min (available (j + 1) s) (T + 1)) -
              ∑ s : Fin p.N, min (available j s) (T + 1) := by
          have hstart : available j (server j) ≤ entry p j := by
            rw [hent]
            exact le_max_right _ _
          have ha : available j (server j) ≤ T + 1 := by linarith [hk j hj]
          have hb : entry p j + min (p.η (j + 1)) 1 ≤
              min (entry p j + p.η (j + 1)) (T + 1) := by
            apply le_min
            · linarith [min_le_left (p.η (j + 1)) 1]
            · linarith [min_le_right (p.η (j + 1)) 1, hk j hj]
          have hsum : (∑ s : Fin p.N, min (available (j + 1) s) (T + 1)) =
              (∑ s : Fin p.N, min (available j s) (T + 1)) +
                (min (entry p j + p.η (j + 1)) (T + 1) -
                  min (available j (server j)) (T + 1)) := by
            calc
              _ = ∑ s : Fin p.N, (min (available j s) (T + 1) +
                  if s = server j then
                    min (entry p j + p.η (j + 1)) (T + 1) -
                      min (available j s) (T + 1) else 0) := by
                apply Finset.sum_congr rfl
                intro s hs
                rw [hupd]
                split_ifs <;> ring
              _ = _ := by rw [Finset.sum_add_distrib]; simp
          rw [hsum, min_eq_left ha]
          linarith
        have hbound : (∑ j ∈ Finset.range k, min (p.η (j + 1)) 1) ≤
            ∑ s : Fin p.N, min (available k s) (T + 1) := by
          induction k with
          | zero =>
              simp only [Finset.range_zero, Finset.sum_empty]
              apply Finset.sum_nonneg
              intro s hs
              rw [hinit]
              split_ifs
              · exact le_min (hηt _) (by linarith)
              · exact le_min le_rfl (by linarith)
          | succ k ih =>
              have hi := ih (fun j hj => hk j (Nat.lt_succ_of_lt hj))
                (fun j hj => hstep j (Nat.lt_succ_of_lt hj))
              rw [Finset.sum_range_succ]
              linarith [hstep k (Nat.lt_succ_self k)]
        calc
          _ ≤ ∑ s : Fin p.N, min (available k s) (T + 1) := hbound
          _ ≤ ∑ _s : Fin p.N, (T + 1) := Finset.sum_le_sum (fun s hs => min_le_right _ _)
          _ = _ := by simp; ring
      let trunc : ℝ → ℝ := fun x => min (max x 0) 1
      have htrunc_meas : Measurable trunc :=
        (measurable_id.max measurable_const).min measurable_const
      have htrunc_nonneg (x : ℝ) : 0 ≤ trunc x := le_min (le_max_right _ _) zero_le_one
      have htrunc_int : Integrable trunc μ := by
        apply (integrable_const (1 : ℝ)).mono' htrunc_meas.aestronglyMeasurable
        exact Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (htrunc_nonneg x)]
          exact min_le_right _ _
      have hμnonneg : ∀ᵐ x ∂μ, (0 : ℝ) ≤ x := by
        rw [ae_iff]
        simp only [not_le]
        exact q.service_law.2.1
      have htrunc_pos : 0 < ∫ x, trunc x ∂μ := by
        have hle : 0 ≤ ∫ x, trunc x ∂μ := integral_nonneg htrunc_nonneg
        by_contra hnot
        have hz : (∫ x, trunc x ∂μ) = 0 := le_antisymm (le_of_not_gt hnot) hle
        have hae := (integral_eq_zero_iff_of_nonneg htrunc_nonneg htrunc_int).mp hz
        have hid : ∀ᵐ x ∂μ, x = (0 : ℝ) := by
          filter_upwards [hae, hμnonneg] with x hx hx0
          dsimp [trunc] at hx
          rw [max_eq_left hx0] at hx
          rcases min_eq_iff.mp hx with h | h
          · exact h.1
          · norm_num at h
        have hi : (∫ x, x ∂μ) = 0 := by
          calc
            _ = ∫ _x : ℝ, (0 : ℝ) ∂μ := integral_congr_ae hid
            _ = 0 := by simp
        linarith [q.service_law.2.2.2]
      have htrunc_slln := hstrong trunc htrunc_meas htrunc_int
      have hstart_bound : ∀ᵐ ω ∂P, ∀ T : ℝ, 0 ≤ T →
          ∃ B : ℝ, 0 < B ∧ ∀ n H k : ℕ,
            (∀ j < k, entry (q.sample n ω H) j ≤ T) →
            (k : ℝ) ≤ B * (n + 1 : ℕ) := by
        filter_upwards [htrunc_slln, hnonneg, hfcfs] with ω hlim hη hq
        intro T hT
        let c : ℝ := ∫ x, trunc x ∂μ
        have hc : 0 < c := htrunc_pos
        obtain ⟨K, hK⟩ := eventually_atTop.mp
          ((tendsto_order.mp hlim).1 (c / 2) (by dsimp [c]; linarith [htrunc_pos]))
        let B : ℝ := K + 1 + 2 * (T + 1) / c
        have hfrac : 0 ≤ 2 * (T + 1) / c := div_nonneg (by linarith) hc.le
        have hB : 0 < B := by dsimp [B]; positivity
        refine ⟨B, hB, ?_⟩
        intro n H k hk
        have hN : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        by_cases hsmall : k < K ∨ k = 0
        · have hks : (k : ℝ) ≤ K := by exact_mod_cast (by omega : k ≤ K)
          have hKB : (K : ℝ) ≤ B := by dsimp [B]; linarith
          nlinarith
        · have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
          have hkl : c / 2 < (∑ i ∈ Finset.range k, trunc (q.fresh (i + 1) ω)) / k :=
            hK k (by omega)
          have hlower : c / 2 * k < ∑ i ∈ Finset.range k, trunc (q.fresh (i + 1) ω) :=
            (lt_div_iff₀ hk0).mp hkl
          have hcap := hcapacity (q.sample n ω H) (hq n H) T hT k hk
          have heq : (∑ i ∈ Finset.range k, trunc (q.fresh (i + 1) ω)) =
              ∑ i ∈ Finset.range k, min ((q.sample n ω H).η (i + 1)) 1 := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [q.fresh_eq]
            simp only [trunc, max_eq_left (hη i)]
          rw [← heq, q.size] at hcap
          have hBc : B * c = (K + 1 : ℝ) * c + 2 * (T + 1) := by
            dsimp [B]
            field_simp
          have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
          have hBC : 2 * (T + 1) ≤ B * c := by nlinarith
          have hBCN := mul_le_mul_of_nonneg_right hBC (le_trans zero_le_one hN)
          apply (mul_le_mul_iff_left₀ hc).mp
          nlinarith
      have hIcc (f : ℕ → ℝ) (k : ℕ) :
          (∑ i ∈ Finset.Icc 1 k, f i) = ∑ j ∈ Finset.range k, f (j + 1) := by
        induction k with
        | zero => simp
        | succ k ih =>
            rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1), Finset.sum_range_succ, ih]
      have hM2range (p : ReedGGN.SystemEq.SamplePath) (t : ℝ) :
          ReedGGN.SystemEq.M2 μ p t = ∑ j ∈ Finset.range (p.Q₀ - p.N + p.A t),
            ((if t - entry p j < p.η (j + 1) then (1 : ℝ) else 0) -
              ReedGGN.SystemEq.G μ (t - entry p j)) := by
        unfold ReedGGN.SystemEq.M2
        rw [hIcc, hIcc, Finset.sum_range_add]
        congr 1
        · apply Finset.sum_congr rfl
          intro j hj
          have hj' : j < p.Q₀ - p.N := Finset.mem_range.mp hj
          simp only [entry, if_pos hj', sub_lt_iff_lt_add, add_comm]
        · apply Finset.sum_congr rfl
          intro j hj
          have hnot : ¬p.Q₀ - p.N + j < p.Q₀ - p.N := by omega
          have hind : p.Q₀ - p.N + j + 1 - (p.Q₀ - p.N) = j + 1 := by omega
          have hiη : p.Q₀ - p.N + j + 1 = p.Q₀ - p.N + (j + 1) := by omega
          simp only [entry, if_neg hnot, hiη, Nat.add_sub_cancel_left]
          simp only [sub_lt_iff_lt_add, sub_sub, add_comm, add_left_comm]
      have hG_neg (s : ℝ) (hs : s < 0) : ReedGGN.SystemEq.G μ s = 1 := by
        have hz : μ (Set.Iic s) = 0 := measure_mono_null
          (fun x hx => lt_of_le_of_lt hx hs) q.service_law.2.1
        unfold ReedGGN.SystemEq.G
        rw [← Set.compl_Iic, measure_compl measurableSet_Iic (measure_ne_top _ _)]
        simp only [measure_univ, hz, tsub_zero, ENNReal.toReal_one]
      have hM2started (p : ReedGGN.SystemEq.SamplePath) (hp : IsFCFS p) (t : ℝ) :
          ∃ k : ℕ, (∀ j < k, entry p j ≤ t) ∧
            ReedGGN.SystemEq.M2 μ p t = ∑ j ∈ Finset.range k,
              ((if t - entry p j < p.η (j + 1) then (1 : ℝ) else 0) -
                ReedGGN.SystemEq.G μ (t - entry p j)) := by
        let total := p.Q₀ - p.N + p.A t
        have hex : ∃ j : ℕ, j = total ∨ t < entry p j := ⟨total, Or.inl rfl⟩
        let k := Nat.find hex
        have hkt : k ≤ total := Nat.find_min' hex (Or.inl rfl)
        have hbefore (j : ℕ) (hj : j < k) : entry p j ≤ t := by
          exact le_of_not_gt (fun h => Nat.find_min hex hj (Or.inr h))
        refine ⟨k, hbefore, ?_⟩
        rw [hM2range]
        symm
        apply Finset.sum_subset (Finset.range_mono hkt)
        intro j hj hjk
        have hkj : k ≤ j := by simpa only [Finset.mem_range, not_lt] using hjk
        have hjt : j < total := Finset.mem_range.mp hj
        have ha : t < entry p j := by
          rcases Nat.find_spec hex with h | h
          · change k = total at h
            omega
          · exact h.trans_le (hentry_mono p hp hkj)
        have hs : t - entry p j < 0 := by linarith
        have hη : 0 ≤ p.η (j + 1) := hp.2.2.1 (j + 1)
        rw [if_pos (lt_of_lt_of_le hs hη), hG_neg _ hs]
        ring
      have huniform : ∀ᵐ ω ∂P,
          KurtzProtter91.Integrals.TendstoUniformlyOnBounded (fun n => mbar q n ω) (fun _ => 0) := by
        filter_upwards [hnoise, hstart_bound, hfcfs] with ω hnoiseω hstartω hfcfsω
        intro T
        rw [Metric.tendstoUniformlyOn_iff]
        intro ε hε
        obtain ⟨B, hB, hbound⟩ := hstartω T T.coe_nonneg
        obtain ⟨D, hD, hDcontrol⟩ := hnoiseω (ε / (2 * B)) (by positivity)
        obtain ⟨N, hN⟩ := exists_nat_gt (2 * D / ε)
        filter_upwards [eventually_ge_atTop N] with n hn
        intro t ht
        let p := localSample q n ω t
        have hp : IsFCFS p := hfcfsω n (⌈(t : ℝ)⌉₊ + 1)
        obtain ⟨k, hk, hM⟩ := hM2started p hp t
        have hkT : ∀ j < k, entry p j ≤ (T : ℝ) := by
          intro j hj
          exact (hk j hj).trans (by exact_mod_cast ht.2)
        have hkB : (k : ℝ) ≤ B * (n + 1 : ℕ) := hbound n _ k hkT
        have hanti : Antitone (fun j => (t : ℝ) - entry p j) := by
          intro i j hij
          linarith [hentry_mono p hp hij]
        have herr := hDcontrol k (fun j => (t : ℝ) - entry p j) hanti
        have hMeq : ReedGGN.SystemEq.M2 μ p t = ∑ j ∈ Finset.range k,
            ((if (t : ℝ) - entry p j < q.fresh (j + 1) ω then (1 : ℝ) else 0) -
              ReedGGN.SystemEq.G μ ((t : ℝ) - entry p j)) := by
          rw [hM]
          apply Finset.sum_congr rfl
          intro j hj
          rw [show p.η (j + 1) = q.fresh (j + 1) ω from q.fresh_eq _ _ _ _]
        rw [← hMeq] at herr
        have hnpos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
        have hDsmall : D < ε / 2 * (n + 1 : ℕ) := by
          have hN' : (2 * D / ε) < (n + 1 : ℕ) := by
            have hnn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
            push_cast
            linarith
          have := (div_lt_iff₀ hε).mp hN'
          nlinarith
        have hεB : ε / (2 * B) * B = ε / 2 := by field_simp
        have hmul := mul_le_mul_of_nonneg_left hkB (by positivity : 0 ≤ ε / (2 * B))
        have hfinal : |ReedGGN.SystemEq.M2 μ p t| < ε * (n + 1 : ℕ) := by
          calc
            _ ≤ ε / (2 * B) * k + D := herr
            _ ≤ ε / (2 * B) * (B * (n + 1 : ℕ)) + D := by linarith only [hmul]
            _ = ε / 2 * (n + 1 : ℕ) + D := by rw [← mul_assoc, hεB]
            _ < _ := by linarith
        rw [dist_comm]
        change dist (ReedGGN.SystemEq.M2 μ p t / (n + 1 : ℕ)) 0 < ε
        rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hnpos]
        exact (div_lt_iff₀ hnpos).mpr hfinal
      have hEval (f : ℕ → Ω → ℝ) (hf : ∀ i, Measurable (f i))
          (j : Ω → ℕ) (hj : Measurable j) : Measurable (fun ω => f (j ω) ω) := by
        have hm : Measurable (fun p : Ω × ℕ => f p.2 p.1) :=
          measurable_from_prod_countable_left hf
        exact hm.comp (measurable_id.prodMk hj)
      have hentry_meas (n H j : ℕ) : Measurable (fun ω => entry (q.sample n ω H) j) := by
        have hQ : Measurable (fun ω => (q.sample n ω H).Q₀) := by
          convert q.count_measurable n using 1
          funext ω
          exact q.initial_agrees n ω H
        have hN : Measurable (fun ω => (q.sample n ω H).N) := by
          simpa only [q.size] using (measurable_const : Measurable (fun _ : Ω => n + 1))
        have hc := hQ.sub hN
        have hj : Measurable (fun ω => j + 1 - ((q.sample n ω H).Q₀ - (q.sample n ω H).N)) :=
          measurable_const.sub hc
        have hτ := hEval (fun i ω => (q.sample n ω H).τ i) (q.arrival_measurable n H) _ hj
        have hw := hEval (fun i ω => (q.sample n ω H).w i) (q.wait_measurable n H) _ hj
        exact Measurable.ite (measurableSet_lt measurable_const hc)
          (q.initial_wait_measurable n H (j + 1)) (hτ.add hw)
      have hM2_meas (n H : ℕ) (t : ℝ≥0) (ht : (t : ℝ) ≤ H) :
          Measurable (fun ω => ReedGGN.SystemEq.M2 μ (q.sample n ω H) t) := by
        have hQ : Measurable (fun ω => (q.sample n ω H).Q₀) := by
          convert q.count_measurable n using 1
          funext ω
          exact q.initial_agrees n ω H
        have hN : Measurable (fun ω => (q.sample n ω H).N) := by
          simpa only [q.size] using (measurable_const : Measurable (fun _ : Ω => n + 1))
        have hA : Measurable (fun ω => (q.sample n ω H).A t) := by
          convert q.arrivals_measurable n t using 1
          funext ω
          exact q.horizon_agrees n ω H t ht
        have hK := (hQ.sub hN).add hA
        have hterm (j : ℕ) : Measurable (fun ω =>
            ((if (t : ℝ) - entry (q.sample n ω H) j < (q.sample n ω H).η (j + 1)
              then (1 : ℝ) else 0) -
                ReedGGN.SystemEq.G μ ((t : ℝ) - entry (q.sample n ω H) j))) := by
          have hη : Measurable (fun ω => (q.sample n ω H).η (j + 1)) := by
            simpa only [q.fresh_eq] using q.fresh_measurable (j + 1)
          have he : Measurable (fun ω => (t : ℝ) - entry (q.sample n ω H) j) :=
            measurable_const.sub (hentry_meas n H j)
          exact (Measurable.ite (measurableSet_lt he hη) measurable_const measurable_const).sub
            (hG_anti.measurable.comp he)
        simp_rw [hM2range]
        exact hEval (fun k ω => ∑ j ∈ Finset.range k,
          ((if (t : ℝ) - entry (q.sample n ω H) j < (q.sample n ω H).η (j + 1)
            then (1 : ℝ) else 0) - ReedGGN.SystemEq.G μ ((t : ℝ) - entry (q.sample n ω H) j)))
          (fun k => Finset.measurable_sum _ (fun j hj => hterm j)) _ hK
      have hmbar_meas (n : ℕ) : Measurable (fun ω => one (mbar q n ω)) := by
        apply Measurable.prodMk measurable_const
        apply measurable_pi_iff.mpr
        intro i
        apply measurable_pi_iff.mpr
        intro t
        apply Measurable.div_const
        apply hM2_meas
        have ht := Nat.le_ceil (t : ℝ)
        push_cast
        linarith
      have hτcount (p : ReedGGN.SystemEq.SamplePath) (t : ℝ) (i : ℕ) (hi : 1 ≤ i) :
          i ≤ p.A t ↔ p.τ i ≤ t := by
        let S := {j : ℕ // 1 ≤ j ∧ p.τ j ≤ t}
        let : Finite S := (p.τ_finite t).to_subtype
        constructor
        · intro hia
          by_contra hnot
          have hti : t < p.τ i := lt_of_not_ge hnot
          have hjbound (j : S) : j.val < i := by
            by_contra hj
            have := p.τ_mono (le_of_not_gt hj)
            linarith [j.2.2]
          let f : S → Fin (i - 1) := fun j => ⟨j.val - 1, by have := hjbound j; have := j.2.1; omega⟩
          have hf : Function.Injective f := by
            intro a b hab
            have hab' := congrArg Fin.val hab
            apply Subtype.ext
            dsimp [f] at hab'
            have ha := a.2.1
            have hb := b.2.1
            omega
          have hc := Nat.card_le_card_of_injective f hf
          have hc' : p.A t ≤ i - 1 := by simpa only [ReedGGN.SystemEq.SamplePath.A, S, Nat.card_fin] using hc
          omega
        · intro hit
          let f : Fin i → S := fun j => ⟨j.val + 1, by omega,
            (p.τ_mono (by omega)).trans hit⟩
          have hf : Function.Injective f := by
            intro a b hab
            have hab' := congrArg Subtype.val hab
            apply Fin.ext
            dsimp [f] at hab'
            omega
          have hc := Nat.card_le_card_of_injective f hf
          simpa only [ReedGGN.SystemEq.SamplePath.A, S, Nat.card_fin] using hc
      have hA_mono (p : ReedGGN.SystemEq.SamplePath) : Monotone p.A := by
        intro s t hst
        by_cases hzero : p.A s = 0
        · rw [hzero]; exact Nat.zero_le _
        · apply (hτcount p t (p.A s) (by omega)).mpr
          exact ((hτcount p s (p.A s) (by omega)).mp le_rfl).trans hst
      have hτ_agree (p p' : ReedGGN.SystemEq.SamplePath) (T : ℝ)
          (hA : ∀ s : ℝ, 0 ≤ s → s ≤ T → p.A s = p'.A s)
          (i : ℕ) (hi : 1 ≤ i) (hiT : i ≤ p.A T) : p.τ i = p'.τ i := by
        have hiτ : p.τ i ≤ T := (hτcount p T i hi).mp hiT
        have hτ0 : 0 ≤ p.τ i := by simpa only [p.τ_zero] using p.τ_mono (Nat.zero_le i)
        have hτ0' : 0 ≤ p'.τ i := by simpa only [p'.τ_zero] using p'.τ_mono (Nat.zero_le i)
        have hia : i ≤ p.A (p.τ i) := (hτcount p _ i hi).mpr le_rfl
        rw [hA _ hτ0 hiτ] at hia
        have hle : p'.τ i ≤ p.τ i := (hτcount p' _ i hi).mp hia
        have hia' : i ≤ p'.A (p'.τ i) := (hτcount p' _ i hi).mpr le_rfl
        rw [← hA _ hτ0' (hle.trans hiτ)] at hia'
        exact le_antisymm ((hτcount p _ i hi).mp hia') hle
      have hminimum_equal (a b : ℕ) (f : Fin a → ℝ) (g : Fin b → ℝ)
          (s : Fin a) (r : Fin b) (hf : ∀ i, f s ≤ f i) (hg : ∀ i, g r ≤ g i)
          (hbag : (∑ i : Fin a, ({f i} : Multiset ℝ)) = ∑ i : Fin b, ({g i} : Multiset ℝ)) :
          f s = g r := by
        have hmem : f s ∈ ∑ i : Fin a, ({f i} : Multiset ℝ) := by
          exact Multiset.mem_sum.mpr ⟨s, Finset.mem_univ _, by simp⟩
        rw [hbag] at hmem
        obtain ⟨i, hi, he⟩ := Multiset.mem_sum.mp hmem
        have he' : f s = g i := Multiset.mem_singleton.mp he
        have hmem' : g r ∈ ∑ i : Fin b, ({g i} : Multiset ℝ) := by
          exact Multiset.mem_sum.mpr ⟨r, Finset.mem_univ _, by simp⟩
        rw [← hbag] at hmem'
        obtain ⟨j, hj, he2⟩ := Multiset.mem_sum.mp hmem'
        have he3 : g r = f j := Multiset.mem_singleton.mp he2
        linarith [hf j, hg i]
      have hbag_update (a : ℕ) (f g : Fin a → ℝ) (s : Fin a) (v : ℝ)
          (hg : ∀ i, g i = if i = s then v else f i) :
          (∑ i : Fin a, ({g i} : Multiset ℝ)) + {f s} =
            (∑ i : Fin a, ({f i} : Multiset ℝ)) + {v} := by
        have hrest : (∑ i ∈ Finset.univ.erase s, ({g i} : Multiset ℝ)) =
            ∑ i ∈ Finset.univ.erase s, ({f i} : Multiset ℝ) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hg, if_neg (Finset.mem_erase.mp hi).1]
        rw [← Finset.add_sum_erase Finset.univ (fun i => ({g i} : Multiset ℝ)) (Finset.mem_univ s),
          ← Finset.add_sum_erase Finset.univ (fun i => ({f i} : Multiset ℝ)) (Finset.mem_univ s),
          hrest, hg s, if_pos rfl]
        ac_rfl
      have hschedule_unique (a b K : ℕ) (f : ℕ → Fin a → ℝ) (g : ℕ → Fin b → ℝ)
          (sf : ℕ → Fin a) (sg : ℕ → Fin b) (rf rg ef eg η : ℕ → ℝ)
          (hfmin : ∀ j i, f j (sf j) ≤ f j i) (hgmin : ∀ j i, g j (sg j) ≤ g j i)
          (hef : ∀ j, ef j = max (rf j) (f j (sf j)))
          (heg : ∀ j, eg j = max (rg j) (g j (sg j)))
          (hfupdate : ∀ j i, f (j + 1) i = if i = sf j then ef j + η j else f j i)
          (hgupdate : ∀ j i, g (j + 1) i = if i = sg j then eg j + η j else g j i)
          (hinit : (∑ i : Fin a, ({f 0 i} : Multiset ℝ)) = ∑ i : Fin b, ({g 0 i} : Multiset ℝ))
          (hready : ∀ j < K, rf j = rg j) : ∀ j < K, ef j = eg j := by
        have hbags : ∀ j : ℕ, j ≤ K →
            (∑ i : Fin a, ({f j i} : Multiset ℝ)) = ∑ i : Fin b, ({g j i} : Multiset ℝ) := by
          intro j
          induction j with
          | zero => intro hj; exact hinit
          | succ j ih =>
              intro hj
              have hbag := ih (by omega)
              have hmin := hminimum_equal a b (f j) (g j) (sf j) (sg j) (hfmin j) (hgmin j) hbag
              have he : ef j = eg j := by rw [hef, heg, hready j (by omega), hmin]
              have hfu := hbag_update a (f j) (f (j + 1)) (sf j) (ef j + η j) (hfupdate j)
              have hgu := hbag_update b (g j) (g (j + 1)) (sg j) (eg j + η j) (hgupdate j)
              apply add_right_cancel (b := ({f j (sf j)} : Multiset ℝ))
              rw [hfu, hmin, hgu, ← hbag, ← he]
        intro j hj
        have hmin := hminimum_equal a b (f j) (g j) (sf j) (sg j) (hfmin j) (hgmin j) (hbags j hj.le)
        rw [hef, heg, hready j hj, hmin]
      have hM2_agree (n : ℕ) (ω : Ω) (H H' : ℕ) (t : ℝ≥0)
          (ht : (t : ℝ) ≤ H) (ht' : (t : ℝ) ≤ H')
          (hp : IsFCFS (q.sample n ω H)) (hp' : IsFCFS (q.sample n ω H')) :
          ReedGGN.SystemEq.M2 μ (q.sample n ω H) t =
            ReedGGN.SystemEq.M2 μ (q.sample n ω H') t := by
        let p := q.sample n ω H
        let p' := q.sample n ω H'
        have hN : p.N = p'.N := (q.size n ω H).trans (q.size n ω H').symm
        have hQ : p.Q₀ = p'.Q₀ := (q.initial_agrees n ω H).trans (q.initial_agrees n ω H').symm
        have hη (j : ℕ) : p.η j = p'.η j := (q.fresh_eq n ω H j).trans (q.fresh_eq n ω H' j).symm
        have hηt (j : ℕ) : p.ηt j = p'.ηt j := (q.residual_eq n ω H j).trans (q.residual_eq n ω H' j).symm
        have hA (s : ℝ) (hs0 : 0 ≤ s) (hst : s ≤ t) : p.A s = p'.A s := by
          calc
            _ = q.arrivals n ω ⟨s, hs0⟩ := q.horizon_agrees n ω H ⟨s, hs0⟩ (hst.trans ht)
            _ = _ := (q.horizon_agrees n ω H' ⟨s, hs0⟩ (hst.trans ht')).symm
        let K := p.Q₀ - p.N + p.A t
        have hcut : p'.Q₀ - p'.N = p.Q₀ - p.N := by rw [← hQ, ← hN]
        have hready : ∀ j < K, ready p j = ready p' j := by
          intro j hj
          dsimp [ready]
          rw [hcut]
          split_ifs with hjcut
          · rfl
          · exact hτ_agree p p' t hA _ (by omega) (by dsimp [K] at hj; omega)
        rcases hp with ⟨hNp, hηtp, hηp, hNIp, server, available, hinit, hmin, hent, hupd⟩
        rcases hp' with ⟨hNp', hηtp', hηp', hNIp', server', available', hinit', hmin', hent', hupd'⟩
        have hbag : (∑ i : Fin p.N, ({available 0 i} : Multiset ℝ)) =
            ∑ i : Fin p'.N, ({available' 0 i} : Multiset ℝ) := by
          apply Fintype.sum_equiv (Fin.castOrderIso hN).toEquiv
          intro i
          apply congrArg (fun x : ℝ => ({x} : Multiset ℝ))
          rw [hinit, hinit']
          have hv : ((Fin.castOrderIso hN).toEquiv i).val = i.val := rfl
          rw [hv, ← hQ, ← hN]
          split_ifs
          · exact hηt _
          · rfl
        have hentryeq := hschedule_unique p.N p'.N K available available' server server'
          (ready p) (ready p') (entry p) (entry p') (fun j => p.η (j + 1))
          hmin hmin' hent hent' hupd
          (by intro j i; simpa only [hη] using hupd' j i) hbag hready
        have htotal : p.Q₀ - p.N + p.A t = p'.Q₀ - p'.N + p'.A t := by
          rw [hQ, hN, hA t t.coe_nonneg le_rfl]
        change ReedGGN.SystemEq.M2 μ p t = ReedGGN.SystemEq.M2 μ p' t
        rw [hM2range, hM2range, ← htotal]
        apply Finset.sum_congr rfl
        intro j hj
        rw [hentryeq j (Finset.mem_range.mp hj), hη]
      have hM2_extend (p : ReedGGN.SystemEq.SamplePath) (hp : IsFCFS p)
          (T t : ℝ) (htT : t ≤ T) :
          ReedGGN.SystemEq.M2 μ p t = ∑ j ∈ Finset.range (p.Q₀ - p.N + p.A T),
            ((if t - entry p j < p.η (j + 1) then (1 : ℝ) else 0) -
              ReedGGN.SystemEq.G μ (t - entry p j)) := by
        rw [hM2range]
        apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_left (hA_mono p htT) _))
        intro j hj hjt
        have hjcut : p.Q₀ - p.N ≤ j := by
          have := Finset.mem_range.mp hj
          have := (show p.Q₀ - p.N + p.A t ≤ j by simpa only [Finset.mem_range, not_lt] using hjt)
          omega
        have hjindex : p.A t < j + 1 - (p.Q₀ - p.N) := by
          have := (show p.Q₀ - p.N + p.A t ≤ j by simpa only [Finset.mem_range, not_lt] using hjt)
          omega
        have hτ : t < p.τ (j + 1 - (p.Q₀ - p.N)) := by
          apply lt_of_not_ge
          intro hnot
          have := (hτcount p t _ (by omega)).mpr hnot
          omega
        have hentry : t < entry p j := by
          have he := hp.2.2.2.2
          obtain ⟨server, available, hinit, hmin, hent, hupd⟩ := he
          rw [hent]
          apply hτ.trans_le
          simp only [ready, if_neg (by omega : ¬j < p.Q₀ - p.N)]
          exact le_max_left _ _
        have hneg : t - entry p j < 0 := by linarith
        have hη := hp.2.2.1 (j + 1)
        rw [if_pos (hneg.trans_le hη), hG_neg _ hneg]
        ring
      have hG_cdf (x : ℝ) : ReedGGN.SystemEq.G μ x = 1 - ProbabilityTheory.cdf μ x := by
        rw [ProbabilityTheory.cdf_eq_real]
        change μ.real (Set.Ioi x) = 1 - μ.real (Set.Iic x)
        rw [← Set.compl_Iic, measureReal_compl measurableSet_Iic]
        simp
      have hindicator_cadlag (c : ℝ) :
          KurtzProtter91.Integrals.IsCadlag (fun t : ℝ≥0 => if (t : ℝ) < c then (1 : ℝ) else 0) := by
        have hanti : Antitone (fun t : ℝ≥0 => if (t : ℝ) < c then (1 : ℝ) else 0) := by
          intro s t hst
          have hst' : (s : ℝ) ≤ t := hst
          change (if (t : ℝ) < c then (1 : ℝ) else 0) ≤
            (if (s : ℝ) < c then (1 : ℝ) else 0)
          split_ifs <;> norm_num; linarith
        constructor
        · intro t
          by_cases ht : (t : ℝ) < c
          · have hnb : ∀ᶠ s : ℝ≥0 in 𝓝 t, (s : ℝ) < c :=
              (isOpen_Iio.preimage NNReal.continuous_coe).mem_nhds ht
            apply continuousWithinAt_const.congr_of_eventuallyEq
              (f := fun _ : ℝ≥0 => (1 : ℝ))
            · filter_upwards [hnb.filter_mono nhdsWithin_le_nhds] with s hs
              simp only [if_pos hs]
            · simp only [if_pos ht]
          · apply continuousWithinAt_const.congr_of_eventuallyEq
              (f := fun _ : ℝ≥0 => (0 : ℝ))
            · filter_upwards [self_mem_nhdsWithin] with s hs
              have hs' : ¬(s : ℝ) < c := by
                have hst : (t : ℝ) ≤ s := hs
                linarith
              simp only [if_neg hs']
            · simp only [if_neg ht]
        · intro t ht
          exact ⟨_, hanti.tendsto_leftLim t⟩
      have htail_cadlag (a : ℝ) :
          KurtzProtter91.Integrals.IsCadlag (fun t : ℝ≥0 => ReedGGN.SystemEq.G μ ((t : ℝ) - a)) := by
        have hanti : Antitone (fun t : ℝ≥0 => ReedGGN.SystemEq.G μ ((t : ℝ) - a)) := by
          intro s t hst
          exact hG_anti (sub_le_sub_right (show (s : ℝ) ≤ t from hst) a)
        constructor
        · intro t
          have hcdf := (ProbabilityTheory.cdf μ).right_continuous ((t : ℝ) - a)
          have hcont : ContinuousWithinAt (fun s : ℝ≥0 => (s : ℝ) - a) (Set.Ici t) t :=
            NNReal.continuous_coe.continuousWithinAt.sub continuousWithinAt_const
          have hmap : Set.MapsTo (fun s : ℝ≥0 => (s : ℝ) - a) (Set.Ici t) (Set.Ici ((t : ℝ) - a)) := by
            intro s hs
            exact sub_le_sub_right (show (t : ℝ) ≤ s from hs) a
          have hccomp : ContinuousWithinAt
              (fun s : ℝ≥0 => ProbabilityTheory.cdf μ ((s : ℝ) - a)) (Set.Ici t) t :=
            ContinuousWithinAt.comp (f := fun s : ℝ≥0 => (s : ℝ) - a) hcdf hcont hmap
          have h : ContinuousWithinAt
              (fun s : ℝ≥0 => 1 - ProbabilityTheory.cdf μ ((s : ℝ) - a)) (Set.Ici t) t :=
            continuousWithinAt_const.sub hccomp
          simpa only [hG_cdf] using h
        · intro t ht
          exact ⟨_, hanti.tendsto_leftLim t⟩
      have hcadlag_sub (f g : RPath) (hf : KurtzProtter91.Integrals.IsCadlag f)
          (hg : KurtzProtter91.Integrals.IsCadlag g) :
          KurtzProtter91.Integrals.IsCadlag (fun t => f t - g t) := by
        refine ⟨fun t => (hf.1 t).sub (hg.1 t), ?_⟩
        intro t ht
        obtain ⟨a, ha⟩ := hf.2 t ht
        obtain ⟨b, hb⟩ := hg.2 t ht
        exact ⟨a - b, ha.sub hb⟩
      have hcadlag_add (f g : RPath) (hf : KurtzProtter91.Integrals.IsCadlag f)
          (hg : KurtzProtter91.Integrals.IsCadlag g) :
          KurtzProtter91.Integrals.IsCadlag (fun t => f t + g t) := by
        refine ⟨fun t => (hf.1 t).add (hg.1 t), ?_⟩
        intro t ht
        obtain ⟨a, ha⟩ := hf.2 t ht
        obtain ⟨b, hb⟩ := hg.2 t ht
        exact ⟨a + b, ha.add hb⟩
      have hcadlag_zero : KurtzProtter91.Integrals.IsCadlag (fun _ : ℝ≥0 => (0 : ℝ)) :=
        ⟨fun _ => continuousWithinAt_const, fun _ _ => ⟨0, tendsto_const_nhds⟩⟩
      have hcadlag_div (f : RPath) (hf : KurtzProtter91.Integrals.IsCadlag f) (c : ℝ) :
          KurtzProtter91.Integrals.IsCadlag (fun t => f t / c) := by
        refine ⟨fun t => ?_, ?_⟩
        · have h := (hf.1 t).mul (continuousWithinAt_const (b := c⁻¹))
          convert h using 1
          funext s
          exact div_eq_mul_inv (f s) c
        intro t ht
        obtain ⟨a, ha⟩ := hf.2 t ht
        exact ⟨a / c, by simpa only [div_eq_mul_inv] using ha.mul (tendsto_const_nhds (x := c⁻¹))⟩
      have hcadlag_sum (s : Finset ℕ) (f : ℕ → RPath)
          (hf : ∀ j ∈ s, KurtzProtter91.Integrals.IsCadlag (f j)) :
          KurtzProtter91.Integrals.IsCadlag (fun t => ∑ j ∈ s, f j t) := by
        induction s using Finset.induction_on with
        | empty => simpa only [Finset.sum_empty] using hcadlag_zero
        | @insert j s hjs ih =>
            simp only [Finset.sum_insert hjs]
            exact hcadlag_add _ _ (hf j (Finset.mem_insert_self _ _))
              (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))
      have hterm_cadlag (a b : ℝ) : KurtzProtter91.Integrals.IsCadlag
          (fun t : ℝ≥0 => (if (t : ℝ) - a < b then (1 : ℝ) else 0) -
            ReedGGN.SystemEq.G μ ((t : ℝ) - a)) := by
        simpa only [sub_lt_iff_lt_add, add_comm] using
          hcadlag_sub _ _ (hindicator_cadlag (a + b)) (htail_cadlag a)
      have hcadlag_local (f : RPath)
          (hlocal : ∀ t : ℝ≥0, ∃ g : RPath, KurtzProtter91.Integrals.IsCadlag g ∧ f =ᶠ[𝓝 t] g) :
          KurtzProtter91.Integrals.IsCadlag f := by
        constructor
        · intro t
          obtain ⟨g, hg, he⟩ := hlocal t
          exact (hg.1 t).congr_of_eventuallyEq (he.filter_mono nhdsWithin_le_nhds) he.eq_of_nhds
        · intro t ht
          obtain ⟨g, hg, he⟩ := hlocal t
          obtain ⟨a, ha⟩ := hg.2 t ht
          exact ⟨a, ha.congr' (he.symm.filter_mono nhdsWithin_le_nhds)⟩
      have hM2_cadlag (p : ReedGGN.SystemEq.SamplePath) (hp : IsFCFS p) :
          KurtzProtter91.Integrals.IsCadlag (fun t : ℝ≥0 => ReedGGN.SystemEq.M2 μ p t) := by
        apply hcadlag_local
        intro t
        let T : ℝ := t + 1
        let g : RPath := fun s => ∑ j ∈ Finset.range (p.Q₀ - p.N + p.A T),
          ((if (s : ℝ) - entry p j < p.η (j + 1) then (1 : ℝ) else 0) -
            ReedGGN.SystemEq.G μ ((s : ℝ) - entry p j))
        refine ⟨g, hcadlag_sum _ _ (fun j hj => hterm_cadlag _ _), ?_⟩
        have htt : (t : ℝ) < T := by dsimp [T]; linarith
        have hnb : ∀ᶠ s : ℝ≥0 in 𝓝 t, (s : ℝ) < T :=
          (isOpen_Iio.preimage NNReal.continuous_coe).mem_nhds htt
        filter_upwards [hnb] with s hs
        exact hM2_extend p hp T s hs.le
      have hmbar_cadlag : ∀ᵐ ω ∂P, ∀ n : ℕ, KurtzProtter91.Integrals.IsCadlag (mbar q n ω) := by
        filter_upwards [hfcfs] with ω hω
        intro n
        apply hcadlag_local
        intro t
        let H : ℕ := ⌈(t : ℝ)⌉₊ + 1
        have htH : (t : ℝ) < H := by
          have := Nat.le_ceil (t : ℝ)
          dsimp [H]
          push_cast
          linarith
        let g : RPath := fun s => ReedGGN.SystemEq.M2 μ (q.sample n ω H) s / (n + 1 : ℕ)
        refine ⟨g, hcadlag_div _ (hM2_cadlag _ (hω n H)) _, ?_⟩
        have hnb : ∀ᶠ s : ℝ≥0 in 𝓝 t, (s : ℝ) < H :=
          (isOpen_Iio.preimage NNReal.continuous_coe).mem_nhds htH
        filter_upwards [hnb] with s hs
        apply congrArg (fun x : ℝ => x / (n + 1 : ℕ))
        apply hM2_agree n ω (⌈(s : ℝ)⌉₊ + 1) H s _ hs.le (hω n _) (hω n _)
        have := Nat.le_ceil (s : ℝ)
        push_cast
        linarith
      refine ⟨?_, Filter.Eventually.of_forall (fun _ _ => hcadlag_zero), ?_⟩
      · intro n
        filter_upwards [hmbar_cadlag] with ω hω
        exact fun _ => hω n
      · refine ⟨Ω, inferInstance, P, (fun n ω => one (mbar q n ω)),
          (fun _ : Ω => one (fun _ => 0)), inferInstance, ?_, ?_, ?_⟩
        · exact fun n => IdentDistrib.refl (hmbar_meas n).aemeasurable
        · exact IdentDistrib.refl measurable_const.aemeasurable
        · filter_upwards [hmbar_cadlag, huniform] with ω hc hu
          refine ⟨tendsto_const_nhds, ?_⟩
          intro i
          refine ⟨hc, hcadlag_zero, (fun _ => id), ?_, ?_, ?_⟩
          · intro n
            exact ⟨continuous_id, strictMono_id, Function.surjective_id⟩
          · exact hu
          · intro T
            rw [Metric.tendstoUniformlyOn_iff]
            intro ε hε
            exact Filter.Eventually.of_forall fun n t ht => by simpa using hε
