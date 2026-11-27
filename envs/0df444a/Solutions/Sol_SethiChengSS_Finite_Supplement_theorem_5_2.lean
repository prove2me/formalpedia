-- Prove2me | solution 1 for SethiChengSS.Finite.Supplement.theorem_5_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:45:39.764642+00:00
-- url     : https://prove2.me/submissions/a22e83bd-e579-4c47-b218-29f784761c96

import Mathlib
import Definitions.Def_SethiChengSS_Finite_Supplement_Capacity

open SethiChengSS
open SethiChengSS.Finite
open SethiChengSS.Finite.Supplement

open MeasureTheory Filter Topology
open scoped ENNReal

/-- Theorem 5.2 and the service-quantile interpretation immediately preceding it.
No (4.1), (4.2), positive unit cost, or global K-convexity is assumed. -/
theorem solution {L : ℕ} (D : Data L) (T : ServiceData) (N : ℕ)
    (hD : Standing D) (hT : ServiceFeasible D T N) :
    (∀ n < N, ∀ i q, 0 < q → q < 1 →
      {t : ℝ | q ≤ demandCDF D n i t}.Nonempty ∧
      BddBelow {t : ℝ | q ≤ demandCDF D n i t} ∧
      demandCDF D n i (demandQuantile D n i q) = q) ∧
    (∀ n < N, ∀ i y,
      (serviceFailure D T n i y ≤ ENNReal.ofReal T.β ↔ serviceA D T n i ≤ y)) ∧
    (∀ n ≤ N, ∀ i, LowerSemicontinuousOn (capV D T N n i) (Set.Iic T.B)) ∧
    (∀ n < N, ∀ i j y, y ≤ T.B →
      Integrable (fun z => capV D T N (n + 1) j (y - z) * D.φ n i z)
        (volume.restrict (Set.Ioi 0))) ∧
    (∀ n < N, ∀ i x, x ≤ T.B →
      (capLevels D T n i x).Nonempty ∧
      BddBelow (capObjective D n (capV D T N (n + 1)) i x '' capLevels D T n i x) ∧
      capH D T N n i x =
        ((sInf (capObjective D n (capV D T N (n + 1)) i x '' capLevels D T n i x) : ℝ) : EReal) ∧
      (capV D T N n i x : EReal) =
        ((D.f n i x - D.c n i * x : ℝ) : EReal) + capH D T N n i x) ∧
    ∃ û : ℕ → Fin L → ℝ → ℝ,
      ∀ n < N, InB0 (û n) ∧ ∀ i x, x ≤ T.B →
        capAction D T n i x (û n i x) ∧
        capV D T N n i x = D.f n i x + orderCost D n i (û n i x) +
          F D n (capV D T N (n + 1)) i (x + û n i x) ∧
        ∀ u : ℝ, capAction D T n i x u →
          orderCost D n i (û n i x) + F D n (capV D T N (n + 1)) i (x + û n i x) ≤
          orderCost D n i u + F D n (capV D T N (n + 1)) i (x + u) := by
            -- distribution facts
            have hCDF : ∀ n i, (∀ t, demandCDF D n i t = ∫ z in Set.Iic t, D.φ n i z) ∧
                Integrable (D.φ n i) ∧ Continuous (demandCDF D n i) ∧ Monotone (demandCDF D n i) ∧
                (∀ t, t < 0 → demandCDF D n i t = 0) ∧
                (∀ q < 1, ∃ t, q ≤ demandCDF D n i t) := by
              intro n i
              have hint : Integrable (D.φ n i) := by
                apply Integrable.of_integral_ne_zero; rw [hD.φ_int]; norm_num
              have h1 : ∀ t, demandCDF D n i t = ∫ z in Set.Iic t, D.φ n i z := by
                intro t
                unfold demandCDF
                symm
                apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Iic
                · intro x hx; exact hx.2
                · intro x hx
                  apply hD.φ_neg
                  simp only [Set.mem_diff, Set.mem_Iic, Set.mem_Icc, not_and, not_le] at hx
                  by_contra h; push_neg at h; linarith [hx.2 h]
              have h2 : ∀ t, demandCDF D n i t = demandCDF D n i 0 + ∫ z in (0:ℝ)..t, D.φ n i z := by
                intro t
                rw [h1, h1, ← intervalIntegral.integral_Iic_sub_Iic hint.integrableOn hint.integrableOn]
                ring
              have hcont : Continuous (demandCDF D n i) := by
                have : (demandCDF D n i) = fun t => demandCDF D n i 0 + ∫ z in (0:ℝ)..t, D.φ n i z := by
                  funext t; exact h2 t
                rw [this]
                exact continuous_const.add
                  (intervalIntegral.continuous_primitive (fun a b => hint.intervalIntegrable) 0)
              have hmono : Monotone (demandCDF D n i) := by
                intro a b hab
                rw [h1, h1]
                apply setIntegral_mono_set hint.integrableOn
                · exact Filter.Eventually.of_forall (fun z => hD.φ_nonneg n i z)
                · exact Filter.Eventually.of_forall (Set.Iic_subset_Iic.mpr hab)
              have hneg : ∀ t, t < 0 → demandCDF D n i t = 0 := by
                intro t ht
                unfold demandCDF
                rw [Set.Icc_eq_empty (by linarith)]
                simp
              refine ⟨h1, hint, hcont, hmono, hneg, ?_⟩
              intro q hq
              have hlim : Tendsto (fun k : ℕ => ∫ z in Set.Iic (k:ℝ), D.φ n i z) atTop
                  (𝓝 (∫ z in ⋃ k : ℕ, Set.Iic (k:ℝ), D.φ n i z)) := by
                apply tendsto_setIntegral_of_monotone (fun k => measurableSet_Iic)
                · intro a b hab; exact Set.Iic_subset_Iic.mpr (by exact_mod_cast hab)
                · exact hint.integrableOn
              have hU : (⋃ k : ℕ, Set.Iic (k:ℝ)) = Set.univ := by
                ext z; simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_univ, iff_true]
                obtain ⟨k, hk⟩ := exists_nat_ge z; exact ⟨k, hk⟩
              rw [hU, Measure.restrict_univ, hD.φ_int] at hlim
              obtain ⟨k, hk⟩ := (hlim.eventually (lt_mem_nhds hq)).exists
              exact ⟨k, by rw [h1]; exact hk.le⟩
            have hQ : ∀ n i q, 0 < q → q < 1 →
                {t : ℝ | q ≤ demandCDF D n i t}.Nonempty ∧
                BddBelow {t : ℝ | q ≤ demandCDF D n i t} ∧
                demandCDF D n i (demandQuantile D n i q) = q ∧
                (∀ t, q ≤ demandCDF D n i t ↔ demandQuantile D n i q ≤ t) := by
              intro n i q hq0 hq1
              obtain ⟨_, _, hcont, hmono, hneg, hex⟩ := hCDF n i
              have hne : {t : ℝ | q ≤ demandCDF D n i t}.Nonempty := hex q hq1
              have hbdd : BddBelow {t : ℝ | q ≤ demandCDF D n i t} := by
                refine ⟨0, fun t ht => ?_⟩
                by_contra h; push_neg at h
                simp only [Set.mem_setOf_eq] at ht
                rw [hneg t h] at ht; linarith
              have hclosed : IsClosed {t : ℝ | q ≤ demandCDF D n i t} :=
                isClosed_le continuous_const hcont
              have hmem := hclosed.csInf_mem hne hbdd
              have hiff : ∀ t, q ≤ demandCDF D n i t ↔ demandQuantile D n i q ≤ t := by
                intro t
                constructor
                · intro ht; exact csInf_le hbdd ht
                · intro ht; exact le_trans hmem (hmono ht)
              refine ⟨hne, hbdd, ?_, hiff⟩
              apply le_antisymm _ hmem
              by_contra hlt; push_neg at hlt
              -- Q > 0 hence left continuity gives smaller point in the set
              set Q := demandQuantile D n i q
              have hev : ∀ᶠ t in 𝓝 Q, q < demandCDF D n i t := hcont.continuousAt.eventually (lt_mem_nhds hlt)
              obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
              have := hball (y := Q - ε/2) (by rw [Real.dist_eq]; rw [abs_of_neg (by linarith)]; linarith)
              have := (hiff (Q - ε/2)).mp this.le
              linarith
            have hSF : ∀ n i y, serviceFailure D T n i y =
                ENNReal.ofReal (1 - demandCDF D n i (y - T.Cmin)) := by
              intro n i y
              obtain ⟨h1, hint, _, _, _, _⟩ := hCDF n i
              unfold serviceFailure
              have hset : {z : ℝ | y - z ≤ T.Cmin} = Set.Ici (y - T.Cmin) := by
                ext z; simp only [Set.mem_setOf_eq, Set.mem_Ici]; constructor <;> intro h <;> linarith
              rw [hset, lintegral_indicator measurableSet_Ici,
                ← ofReal_integral_eq_lintegral_ofReal hint.integrableOn
                  (Filter.Eventually.of_forall (fun z => hD.φ_nonneg n i z))]
              congr 1
              have := integral_add_compl (μ := volume) (f := D.φ n i) (measurableSet_Ici (a := y - T.Cmin)) hint
              rw [Set.compl_Ici, hD.φ_int, ← integral_Iic_eq_integral_Iio, ← h1] at this
              linarith
            refine ⟨fun n _ i q hq0 hq1 => ⟨(hQ n i q hq0 hq1).1, (hQ n i q hq0 hq1).2.1,
              (hQ n i q hq0 hq1).2.2.1⟩, ?_, ?_⟩
            · intro n hn i y
              obtain ⟨hβ0, hβ1, _⟩ := hT
              rw [hSF, ENNReal.ofReal_le_ofReal_iff hβ0.le]
              have := (hQ n i (1 - T.β) (by linarith) (by linarith)).2.2.2 (y - T.Cmin)
              unfold serviceA
              constructor
              · intro h; have := this.mp (by linarith); linarith
              · intro h; have := this.mpr (by linarith); linarith
            obtain ⟨hβ0, hβ1, hAB⟩ := hT
            have hbaire : ∀ u : ℝ → ℝ, (∀ x, 0 ≤ u x) → LowerSemicontinuous u →
                ∃ g : ℕ → ℝ → ℝ, (∀ k, Continuous (g k)) ∧ (∀ k x, 0 ≤ g k x) ∧
                  ∀ x, Tendsto (fun k => g k x) atTop (𝓝 (u x)) := by
              intro u hu0 hul
              have hbdd : ∀ (k : ℕ) (x : ℝ), BddBelow (Set.range fun y => u y + (k:ℝ) * |x - y|) := by
                intro k x
                refine ⟨0, ?_⟩
                rintro _ ⟨y, rfl⟩
                have := hu0 y
                positivity
              refine ⟨fun k x => ⨅ y, (u y + (k:ℝ) * |x - y|), ?_, ?_, ?_⟩
              · intro k
                apply LipschitzWith.continuous (K := ⟨(k:ℝ), by positivity⟩)
                apply LipschitzWith.of_le_add_mul
                intro x x'
                have : (⨅ y, (u y + (k:ℝ) * |x - y|)) - (k:ℝ) * dist x x' ≤ ⨅ y, (u y + (k:ℝ) * |x' - y|) := by
                  apply le_ciInf
                  intro y
                  have h1 := ciInf_le (hbdd k x) y
                  have h2 : |x - y| ≤ |x' - y| + dist x x' := by
                    rw [Real.dist_eq]
                    calc |x - y| = |(x' - y) + (x - x')| := by ring_nf
                      _ ≤ |x' - y| + |x - x'| := abs_add_le _ _
                  have h3 : (k:ℝ) * |x - y| ≤ (k:ℝ) * |x' - y| + (k:ℝ) * dist x x' := by
                    rw [← mul_add]; exact mul_le_mul_of_nonneg_left h2 (by positivity)
                  linarith
                change _ ≤ _ + (k:ℝ) * _
                linarith
              · intro k x
                apply le_ciInf
                intro y
                have := hu0 y
                positivity
              · intro x
                rw [tendsto_order]
                constructor
                · intro a ha
                  obtain ⟨a', haa', ha'⟩ := exists_between ha
                  have hev := hul x a' ha'
                  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
                  obtain ⟨k0, hk0⟩ := exists_nat_ge (a' / δ)
                  rw [eventually_atTop]
                  refine ⟨k0, fun k hk => ?_⟩
                  have hk' : (k0:ℝ) ≤ k := by exact_mod_cast hk
                  apply lt_of_lt_of_le haa'
                  apply le_ciInf
                  intro y
                  by_cases hy : dist y x < δ
                  · have := hball hy
                    have : 0 ≤ (k:ℝ) * |x - y| := by positivity
                    linarith
                  · push_neg at hy
                    rw [Real.dist_eq, abs_sub_comm] at hy
                    have h1 : a' ≤ (k:ℝ) * δ := by
                      rw [div_le_iff₀ hδ] at hk0
                      nlinarith
                    have h2 : (k:ℝ) * δ ≤ (k:ℝ) * |x - y| := mul_le_mul_of_nonneg_left hy (by positivity)
                    have := hu0 y
                    linarith
                · intro a ha
                  refine Eventually.of_forall (fun k => lt_of_le_of_lt ?_ ha)
                  have := ciInf_le (hbdd k x) x
                  simpa using this
            -- generic one-dimensional minimization with a Baire-one selection
            have hmin : ∀ (K A B : ℝ) (z : ℝ → ℝ), 0 ≤ K → A ≤ B → LowerSemicontinuousOn z (Set.Iic B) →
                ∃ ysel : ℝ → ℝ, (∀ x ≤ B, max x A ≤ ysel x ∧ ysel x ≤ B ∧ ∀ y, max x A ≤ y → y ≤ B →
                    K * delta (ysel x - x) + z (ysel x) ≤ K * delta (y - x) + z y) ∧
                  LowerSemicontinuousOn (fun x => K * delta (ysel x - x) + z (ysel x)) (Set.Iic B) ∧
                  ∃ g : ℕ → ℝ → ℝ, (∀ k, Continuous (g k)) ∧ (∀ k x, 0 ≤ g k x) ∧
                    ∀ x, Tendsto (fun k => g k x) atTop (𝓝 (if x ≤ B then ysel x - x else 0)) := by
              intro K A B z hK hAB hz
              classical
              have hd1 : ∀ u, 0 < u → delta u = 1 := fun u hu => by unfold delta; rw [if_pos hu]
              have hd0 : delta 0 = 0 := by unfold delta; simp
              obtain ⟨I, hIm⟩ : ∃ I : ℝ → Set ℝ, ∀ x y, y ∈ I x ↔ max x A ≤ y ∧ y ≤ B :=
                ⟨fun x => Set.Icc (max x A) B, fun x y => Iff.rfl⟩
              have hIeq : ∀ x, I x = Set.Icc (max x A) B := fun x => by ext y; rw [hIm]; rfl
              have hex : ∀ x ≤ B, ∃ w ∈ I x, ∀ y ∈ I x, z w ≤ z y := by
                intro x hx
                obtain ⟨a, ha, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn (s := I x) (f := z)
                  ⟨B, (hIm x B).mpr ⟨max_le hx hAB, le_rfl⟩⟩ (by rw [hIeq]; exact isCompact_Icc)
                  (hz.mono (fun y hy => ((hIm x y).mp hy).2))
                exact ⟨a, ha, fun y hy => hmin hy⟩
              obtain ⟨Am, hAmm⟩ : ∃ Am : ℝ → Set ℝ, ∀ x y, y ∈ Am x ↔ (y ∈ I x ∧ ∀ y' ∈ I x, z y ≤ z y') :=
                ⟨fun x => {y | y ∈ I x ∧ ∀ y' ∈ I x, z y ≤ z y'}, fun x y => Iff.rfl⟩
              obtain ⟨w, hw⟩ : ∃ w : ℝ → ℝ, ∀ x, (Am x).Nonempty → w x ∈ Am x ∧
                  ∀ x', Am x' = Am x → w x' = w x :=
                ⟨fun x => if h : (Am x).Nonempty then h.some else 0, fun x hne =>
                  ⟨by simp only [dif_pos hne]; exact hne.some_mem, fun x' h => by simp only [h]⟩⟩
              have hwmem : ∀ x ≤ B, w x ∈ I x ∧ ∀ y ∈ I x, z (w x) ≤ z y := by
                intro x hx
                obtain ⟨a, ha, hmin⟩ := hex x hx
                exact (hAmm x (w x)).mp (hw x ⟨a, (hAmm x a).mpr ⟨ha, hmin⟩⟩).1
              have hwI : ∀ x ≤ B, ∀ x', Am x' = Am x → w x' = w x := by
                intro x hx
                obtain ⟨a, ha, hmin⟩ := hex x hx
                exact (hw x ⟨a, (hAmm x a).mpr ⟨ha, hmin⟩⟩).2
              have hwlow : ∀ x ≤ B, max x A ≤ w x ∧ w x ≤ B := fun x hx => (hIm x _).mp (hwmem x hx).1
              obtain ⟨ysel, hys⟩ : ∃ ysel : ℝ → ℝ, ∀ x, ((x < A ∨ K + z (w x) < z x) → ysel x = w x) ∧
                  (¬ (x < A ∨ K + z (w x) < z x) → ysel x = x) :=
                ⟨fun x => if (x < A ∨ K + z (w x) < z x) then w x else x,
                  fun x => ⟨fun h => if_pos h, fun h => if_neg h⟩⟩
              -- values
              have hOv : ∀ x ≤ B, (x < A ∨ K + z (w x) < z x) → x < w x ∧ ysel x = w x ∧
                  K * delta (ysel x - x) + z (ysel x) = K + z (w x) := by
                intro x hx ho
                have hxw : x < w x := by
                  have h1 := hwlow x hx
                  rcases ho with h | h
                  · linarith [le_max_right x A]
                  · rcases (le_max_left x A).trans h1.1 |>.lt_or_eq with h2 | h2
                    · exact h2
                    · rw [← h2] at h; linarith
                refine ⟨hxw, (hys x).1 ho, ?_⟩
                rw [(hys x).1 ho, hd1 _ (by linarith)]; ring
              have hNv : ∀ x, ¬ (x < A ∨ K + z (w x) < z x) → A ≤ x ∧ z x ≤ K + z (w x) ∧ ysel x = x ∧
                  K * delta (ysel x - x) + z (ysel x) = z x := by
                intro x ho
                push_neg at ho
                refine ⟨ho.1, ho.2, (hys x).2 (by push_neg; exact ho), ?_⟩
                rw [(hys x).2 (by push_neg; exact ho), sub_self, hd0]; ring
              -- key local lemma
              have hKL : ∀ x0 ≤ B, (x0 < A ∨ K + z (w x0) < z x0) →
                  ∀ᶠ x in 𝓝 x0, x ≤ B ∧ (x < A ∨ K + z (w x) < z x) ∧ w x = w x0 := by
                intro x0 hx0 ho
                by_cases hlt : x0 < A
                · filter_upwards [Iio_mem_nhds hlt] with x hx
                  have hx' : (x:ℝ) < A := hx
                  refine ⟨by linarith, Or.inl hx', ?_⟩
                  apply hwI x0 hx0
                  have : I x = I x0 := by rw [hIeq, hIeq, max_eq_right hx'.le, max_eq_right hlt.le]
                  ext y; rw [hAmm, hAmm, this]
                · push_neg at hlt
                  have h : K + z (w x0) < z x0 := ho.resolve_left (not_lt.mpr hlt)
                  have hx0B : x0 < B := by
                    rcases hx0.lt_or_eq with h1 | h1
                    · exact h1
                    · exfalso
                      have h2 := hwlow x0 hx0
                      have : w x0 = x0 := le_antisymm (h1 ▸ h2.2) ((le_max_left _ _).trans h2.1)
                      rw [this] at h; linarith
                  have hev := hz x0 hx0 _ h
                  rw [nhdsWithin_eq_nhds.mpr (Iic_mem_nhds hx0B)] at hev
                  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
                  filter_upwards [Metric.ball_mem_nhds x0 hδ, Iio_mem_nhds hx0B] with x hxδ hxB
                  have hxB' : x ≤ B := le_of_lt hxB
                  rw [Metric.mem_ball, Real.dist_eq] at hxδ
                  have hclaim : ∀ y, z y ≤ z (w x0) → (y ∈ I x ↔ y ∈ I x0) := by
                    intro y hy
                    have hfar : δ ≤ |y - x0| := by
                      by_contra hc; push_neg at hc
                      have := hball (show dist y x0 < δ by rw [Real.dist_eq]; exact hc)
                      linarith
                    rw [hIm, hIm]
                    rw [abs_lt] at hxδ
                    constructor
                    · rintro ⟨h1, h2⟩
                      refine ⟨?_, h2⟩
                      have hyx : x ≤ y := (le_max_left _ _).trans h1
                      have : x0 < y := by
                        rcases le_or_gt y x0 with h3 | h3
                        · exfalso; rw [abs_of_nonpos (by linarith)] at hfar; linarith
                        · exact h3
                      exact max_le this.le ((le_max_right _ _).trans h1)
                    · rintro ⟨h1, h2⟩
                      refine ⟨?_, h2⟩
                      have hyx : x0 ≤ y := (le_max_left _ _).trans h1
                      rw [abs_of_nonneg (by linarith)] at hfar
                      exact max_le (by linarith) ((le_max_right _ _).trans h1)
                  have hw0x : w x0 ∈ I x := (hclaim (w x0) le_rfl).mpr (hwmem x0 hx0).1
                  have hmin : ∀ y' ∈ I x, z (w x0) ≤ z y' := by
                    intro y' hy'
                    by_cases hc : z y' ≤ z (w x0)
                    · exact (hwmem x0 hx0).2 y' ((hclaim y' hc).mp hy')
                    · push_neg at hc; exact hc.le
                  have hAmeq : Am x = Am x0 := by
                    ext y
                    rw [hAmm, hAmm]
                    constructor
                    · rintro ⟨h1, h2⟩
                      have hy : z y ≤ z (w x0) := h2 (w x0) hw0x
                      exact ⟨(hclaim y hy).mp h1, fun y' hy' => hy.trans ((hwmem x0 hx0).2 y' hy')⟩
                    · rintro ⟨h1, h2⟩
                      have hy : z y ≤ z (w x0) := h2 (w x0) (hwmem x0 hx0).1
                      exact ⟨(hclaim y hy).mpr h1, fun y' hy' => hy.trans (hmin y' hy')⟩
                  have hwx : w x = w x0 := hwI x0 hx0 x hAmeq
                  refine ⟨hxB', Or.inr ?_, hwx⟩
                  rw [hwx]
                  exact hball (by rw [Real.dist_eq]; exact hxδ)
              have hMl : ∀ x0 ≤ B, ∀ s < z (w x0), ∀ᶠ x in 𝓝[Set.Iic B] x0, s < z (w x) := by
                intro x0 hx0 s hs
                by_cases hlt : x0 < A
                · apply nhdsWithin_le_nhds
                  filter_upwards [Iio_mem_nhds hlt] with x hx
                  have hx' : (x:ℝ) < A := hx
                  have : I x = I x0 := by rw [hIeq, hIeq, max_eq_right hx'.le, max_eq_right hlt.le]
                  rw [hwI x0 hx0 x (by ext y; rw [hAmm, hAmm, this])]
                  exact hs
                · push_neg at hlt
                  have hzx0 : z (w x0) ≤ z x0 :=
                    (hwmem x0 hx0).2 x0 ((hIm x0 x0).mpr ⟨max_le le_rfl hlt, hx0⟩)
                  have hev := hz x0 hx0 s (by linarith)
                  rw [eventually_nhdsWithin_iff] at hev ⊢
                  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
                  filter_upwards [Metric.ball_mem_nhds x0 hδ] with x hxδ hxB
                  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hxδ
                  have h1 := hwlow x hxB
                  by_cases hc : x0 ≤ w x
                  · exact lt_of_lt_of_le hs ((hwmem x0 hx0).2 _
                      ((hIm x0 _).mpr ⟨max_le hc ((le_max_right _ _).trans h1.1), h1.2⟩))
                  · push_neg at hc
                    refine hball ?_ h1.2
                    rw [Real.dist_eq, abs_lt]
                    constructor <;> linarith [(le_max_left x A).trans h1.1]
              have hm : LowerSemicontinuousOn (fun x => K * delta (ysel x - x) + z (ysel x)) (Set.Iic B) := by
                intro x0 hx0 t ht
                by_cases ho : x0 < A ∨ K + z (w x0) < z x0
                · have hval := (hOv x0 hx0 ho).2.2
                  apply nhdsWithin_le_nhds
                  filter_upwards [hKL x0 hx0 ho] with x ⟨hxB, hox, hwx⟩
                  beta_reduce at ht ⊢
                  rw [(hOv x hxB hox).2.2, hwx]; rw [hval] at ht; exact ht
                · obtain ⟨hA, hzx, _, hval⟩ := hNv x0 ho
                  beta_reduce at ht; rw [hval] at ht
                  filter_upwards [hz x0 hx0 t ht, hMl x0 hx0 (t - K) (by linarith), self_mem_nhdsWithin]
                    with x h1 h2 hxB
                  by_cases hox : x < A ∨ K + z (w x) < z x
                  · beta_reduce; rw [(hOv x hxB hox).2.2]; linarith
                  · beta_reduce; rw [(hNv x hox).2.2.2]; exact h1
              refine ⟨ysel, ?_, hm, ?_⟩
              · intro x hx
                by_cases ho : x < A ∨ K + z (w x) < z x
                · obtain ⟨hxw, hy, hval⟩ := hOv x hx ho
                  refine ⟨by rw [hy]; exact (hwlow x hx).1, by rw [hy]; exact (hwlow x hx).2,
                    fun y hy1 hy2 => ?_⟩
                  rw [hval]
                  rcases (le_max_left x A).trans hy1 |>.lt_or_eq with h1 | h1
                  · rw [hd1 _ (by linarith)]
                    have := (hwmem x hx).2 y ((hIm x y).mpr ⟨hy1, hy2⟩); linarith
                  · rw [← h1, sub_self, hd0]
                    rw [← h1] at hy1
                    rcases ho with h | h
                    · linarith [le_max_right x A]
                    · linarith
                · obtain ⟨hA, hzx, hy, hval⟩ := hNv x ho
                  refine ⟨by rw [hy, max_eq_left hA], by rw [hy]; exact hx, fun y hy1 hy2 => ?_⟩
                  rw [hval]
                  rcases (le_max_left x A).trans hy1 |>.lt_or_eq with h1 | h1
                  · rw [hd1 _ (by linarith)]
                    have := (hwmem x hx).2 y ((hIm x y).mpr ⟨hy1, hy2⟩); linarith
                  · rw [← h1, sub_self, hd0]; linarith
              · have hu0 : ∀ x, 0 ≤ (if x ≤ B then ysel x - x else 0) := by
                  intro x
                  by_cases hx : x ≤ B
                  · rw [if_pos hx]
                    by_cases ho : x < A ∨ K + z (w x) < z x
                    · rw [(hOv x hx ho).2.1]; linarith [(hOv x hx ho).1]
                    · rw [(hNv x ho).2.2.1]; simp
                  · rw [if_neg hx]
                apply hbaire _ hu0
                intro x0 t ht
                by_cases ht0 : t < 0
                · exact Eventually.of_forall (fun x => lt_of_lt_of_le ht0 (hu0 x))
                · push_neg at ht0
                  beta_reduce at ht
                  have hx0B : x0 ≤ B := by
                    by_contra hc; rw [if_neg hc] at ht; linarith
                  rw [if_pos hx0B] at ht
                  have ho : x0 < A ∨ K + z (w x0) < z x0 := by
                    by_contra hc; rw [(hNv x0 hc).2.2.1] at ht; linarith
                  rw [(hOv x0 hx0B ho).2.1] at ht
                  have hcont : Continuous (fun x : ℝ => w x0 - x) := continuous_const.sub continuous_id
                  have hc : ∀ᶠ x in 𝓝 x0, t < w x0 - x := hcont.continuousAt.eventually (lt_mem_nhds ht)
                  filter_upwards [hKL x0 hx0B ho, hc] with x ⟨hxB, hox, hwx⟩ hx
                  beta_reduce
                  rw [if_pos hxB, (hOv x hxB hox).2.1, hwx]; exact hx
            -- properties of the next-stage value used by the operator F
            have hFprop : ∀ n < N, (∀ j, (∀ x ≤ T.B, 0 ≤ capV D T N (n + 1) j x) ∧
                  LowerSemicontinuousOn (capV D T N (n + 1) j) (Set.Iic T.B) ∧
                  ∃ C, ∀ x ≤ T.B, capV D T N (n + 1) j x ≤ C * (1 + |x|)) →
                (∀ i j y, y ≤ T.B → Integrable (fun z => capV D T N (n + 1) j (y - z) * D.φ n i z)
                  (volume.restrict (Set.Ioi 0))) ∧
                (∀ i, LowerSemicontinuousOn (F D n (capV D T N (n + 1)) i) (Set.Iic T.B)) ∧
                (∀ i y, y ≤ T.B → 0 ≤ F D n (capV D T N (n + 1)) i y) ∧
                (∃ C, ∀ i y, y ≤ T.B → F D n (capV D T N (n + 1)) i y ≤ C * (1 + |y|)) := by
              intro n _ hv
              generalize capV D T N (n + 1) = v at hv ⊢
              generalize T.B = B at hv ⊢
              choose hv0 hvl C hC using hv
              set w : Fin L → ℝ → ℝ := fun j x => v j (min x B) with hw
              have hwl : ∀ j, LowerSemicontinuous (w j) := by
                intro j
                rw [← lowerSemicontinuousOn_univ_iff]
                exact (hvl j).comp (continuous_id.min continuous_const).continuousOn
                  (fun x _ => min_le_right x B)
              have hwm : ∀ j, Measurable (w j) := fun j => (hwl j).measurable
              have hvw : ∀ j y z, y ≤ B → 0 < z → v j (y - z) = w j (y - z) := by
                intro j y z hy hz
                simp only [hw]; rw [min_eq_left (by linarith)]
              have hint : ∀ i, Integrable (D.φ n i) := by
                intro i; apply Integrable.of_integral_ne_zero; rw [hD.φ_int]; norm_num
              have hbound : ∀ i j y z, y ≤ B → 0 < z →
                  ‖v j (y - z) * D.φ n i z‖ ≤ |C j| * (1 + |y|) * D.φ n i z + |C j| * (z * D.φ n i z) := by
                intro i j y z hy hz
                have h0 := hv0 j (y - z) (by linarith)
                have h1 := hC j (y - z) (by linarith)
                have hp := hD.φ_nonneg n i z
                rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0, abs_of_nonneg hp]
                have h2 : |y - z| ≤ |y| + z := by
                  calc |y - z| ≤ |y| + |z| := abs_sub _ _
                    _ = |y| + z := by rw [abs_of_pos hz]
                have h3 : v j (y - z) ≤ |C j| * (1 + |y| + z) := by
                  calc v j (y - z) ≤ C j * (1 + |y - z|) := h1
                    _ ≤ |C j| * (1 + |y - z|) := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
                    _ ≤ |C j| * (1 + |y| + z) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
                have := mul_le_mul_of_nonneg_right h3 hp
                nlinarith
              have hI : ∀ i j y, y ≤ B → Integrable (fun z => v j (y - z) * D.φ n i z)
                  (volume.restrict (Set.Ioi 0)) := by
                intro i j y hy
                have hg : Integrable (fun z => |C j| * (1 + |y|) * D.φ n i z + |C j| * (z * D.φ n i z))
                    (volume.restrict (Set.Ioi 0)) :=
                  (((hint i).const_mul _).add ((hD.mean_integrable n i).const_mul _)).restrict
                have hm : AEStronglyMeasurable (fun z => v j (y - z) * D.φ n i z)
                    (volume.restrict (Set.Ioi 0)) := by
                  have : Measurable (fun z => w j (y - z) * D.φ n i z) :=
                    ((hwm j).comp (measurable_const.sub measurable_id)).mul (hD.φ_meas n i)
                  refine this.aestronglyMeasurable.congr ?_
                  rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioi]
                  exact Eventually.of_forall (fun z hz => by simp only [hvw j y z hy hz])
                refine Integrable.mono' hg hm ?_
                rw [ae_restrict_iff' measurableSet_Ioi]
                exact Eventually.of_forall (fun z hz => hbound i j y z hy hz)
              have hnn : ∀ i y, y ≤ B → 0 ≤ F D n v i y := by
                intro i y hy
                unfold F
                apply Finset.sum_nonneg
                intro j _
                apply mul_nonneg (hD.P_nonneg i j)
                apply setIntegral_nonneg measurableSet_Ioi
                intro z hz
                exact mul_nonneg (hv0 j _ (by simp at hz; linarith)) (hD.φ_nonneg n i z)
              refine ⟨hI, ?_, hnn, ?_⟩
              · intro i
                have hIj : ∀ j, LowerSemicontinuousOn (fun y => ∫ z in Set.Ioi 0, v j (y - z) * D.φ n i z)
                    (Set.Iic B) := by
                  intro j
                  set G : ℝ → ℝ≥0∞ := fun y => ∫⁻ z in Set.Ioi 0, ENNReal.ofReal (w j (y - z) * D.φ n i z)
                    with hG
                  have hpt : ∀ z, LowerSemicontinuous (fun y => ENNReal.ofReal (w j (y - z) * D.φ n i z)) := by
                    intro z
                    have h1 : LowerSemicontinuousOn (fun y => w j (y - z)) Set.univ :=
                      LowerSemicontinuousOn.comp (f := w j) (g := fun y => y - z)
                        (lowerSemicontinuousOn_univ_iff.mpr (hwl j))
                        (continuous_id.sub continuous_const).continuousOn (Set.mapsTo_univ _ _)
                    have h2 := (ENNReal.continuous_ofReal.comp (continuous_id.mul continuous_const)).comp_lowerSemicontinuousOn
                      h1 (fun a b hab => ENNReal.ofReal_le_ofReal
                        (mul_le_mul_of_nonneg_right hab (hD.φ_nonneg n i z)))
                    rw [lowerSemicontinuousOn_univ_iff] at h2
                    exact h2
                  have hGl : LowerSemicontinuous G := by
                    rw [← lowerSemicontinuousOn_univ_iff]
                    intro y0 _
                    apply lowerSemicontinuousWithinAt_iff_le_liminf.mpr
                    rw [nhdsWithin_univ]
                    calc G y0 ≤ ∫⁻ z in Set.Ioi 0, liminf (fun y => ENNReal.ofReal (w j (y - z) * D.φ n i z))
                          (𝓝 y0) := by
                          apply lintegral_mono
                          intro z
                          have := (lowerSemicontinuousOn_univ_iff.mpr (hpt z)) y0 (Set.mem_univ _)
                          have := lowerSemicontinuousWithinAt_iff_le_liminf.mp this
                          rw [nhdsWithin_univ] at this
                          exact this
                      _ ≤ liminf G (𝓝 y0) := by
                          apply lintegral_liminf_le
                          intro y
                          exact ENNReal.measurable_ofReal.comp
                            (((hwm j).comp (measurable_const.sub measurable_id)).mul (hD.φ_meas n i))
                  have hIG : ∀ y ≤ B, (∫ z in Set.Ioi 0, v j (y - z) * D.φ n i z) = (G y).toReal ∧ G y ≠ ⊤ := by
                    intro y hy
                    have heq : (fun z => v j (y - z) * D.φ n i z) =ᵐ[volume.restrict (Set.Ioi 0)]
                        (fun z => w j (y - z) * D.φ n i z) := by
                      rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioi]
                      exact Eventually.of_forall (fun z hz => by simp only [hvw j y z hy hz])
                    have hIw := (hI i j y hy).congr heq
                    have hnn' : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)] (fun z => w j (y - z) * D.φ n i z) := by
                      rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
                      exact Eventually.of_forall (fun z hz => by
                        rw [← hvw j y z hy hz]
                        exact mul_nonneg (hv0 j _ (by simp at hz; linarith)) (hD.φ_nonneg n i z))
                    refine ⟨?_, ?_⟩
                    · rw [integral_congr_ae heq, integral_eq_lintegral_of_nonneg_ae hnn' hIw.1]
                    · exact (hasFiniteIntegral_iff_ofReal hnn').mp hIw.2 |>.ne
                  intro y0 hy0 t ht
                  by_cases ht0 : t < 0
                  · filter_upwards [self_mem_nhdsWithin] with y hy
                    exact lt_of_lt_of_le ht0 (setIntegral_nonneg measurableSet_Ioi (fun z hz =>
                      mul_nonneg (hv0 j _ (by simp at hz hy; linarith)) (hD.φ_nonneg n i z)))
                  push_neg at ht0
                  have ht' : t < ∫ z in Set.Ioi 0, v j (y0 - z) * D.φ n i z := ht
                  rw [(hIG y0 hy0).1] at ht'
                  have h1 : ENNReal.ofReal t < G y0 :=
                    (ENNReal.ofReal_lt_iff_lt_toReal ht0 (hIG y0 hy0).2).mpr ht'
                  have h2 := hGl y0 _ h1
                  filter_upwards [nhdsWithin_le_nhds h2, self_mem_nhdsWithin] with y hy hyB
                  show t < ∫ z in Set.Ioi 0, v j (y - z) * D.φ n i z
                  rw [(hIG y hyB).1]
                  exact (ENNReal.ofReal_lt_iff_lt_toReal ht0 (hIG y hyB).2).mp hy
                unfold F
                apply lowerSemicontinuousOn_sum
                intro j _
                exact (continuous_const.mul continuous_id).comp_lowerSemicontinuousOn (hIj j)
                  (fun a b hab => mul_le_mul_of_nonneg_left hab (hD.P_nonneg i j))
              · set C0 := ∑ j, |C j|
                have hmean : ∀ i, ∫ z in Set.Ioi 0, (z * D.φ n i z) ≤ |D.M| := by
                  intro i
                  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
                  · exact (hD.mean_le n i).trans (le_abs_self _)
                  · intro z hz
                    simp only [Set.mem_Ioi, not_lt] at hz
                    rcases hz.lt_or_eq with h | h
                    · rw [hD.φ_neg n i z h, mul_zero]
                    · rw [h, zero_mul]
                have hmass : ∀ i, ∫ z in Set.Ioi 0, D.φ n i z ≤ 1 := by
                  intro i
                  rw [← hD.φ_int n i]
                  exact setIntegral_le_integral (hint i) (Eventually.of_forall (fun z => hD.φ_nonneg n i z))
                refine ⟨C0 + C0 * |D.M|, fun i y hy => ?_⟩
                unfold F
                have hj : ∀ j, ∫ z in Set.Ioi 0, v j (y - z) * D.φ n i z ≤ C0 * (1 + |y|) + C0 * |D.M| := by
                  intro j
                  have hCj : |C j| ≤ C0 := Finset.single_le_sum (f := fun j => |C j|)
                    (fun j _ => abs_nonneg _) (Finset.mem_univ j)
                  have hg : Integrable (fun z => |C j| * (1 + |y|) * D.φ n i z + |C j| * (z * D.φ n i z))
                      (volume.restrict (Set.Ioi 0)) :=
                    (((hint i).const_mul _).add ((hD.mean_integrable n i).const_mul _)).restrict
                  calc ∫ z in Set.Ioi 0, v j (y - z) * D.φ n i z
                      ≤ ∫ z in Set.Ioi 0, (|C j| * (1 + |y|) * D.φ n i z + |C j| * (z * D.φ n i z)) := by
                        apply setIntegral_mono_on (hI i j y hy) hg measurableSet_Ioi
                        intro z hz
                        exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans
                          (hbound i j y z hy hz))
                    _ = |C j| * (1 + |y|) * (∫ z in Set.Ioi 0, D.φ n i z) +
                          |C j| * ∫ z in Set.Ioi 0, (z * D.φ n i z) := by
                        rw [integral_add (((hint i).const_mul _).restrict)
                          (((hD.mean_integrable n i).const_mul _).restrict),
                          integral_const_mul, integral_const_mul]
                    _ ≤ C0 * (1 + |y|) + C0 * |D.M| := by
                        have h1 := hmass i
                        have h2 := hmean i
                        have h3 : 0 ≤ ∫ z in Set.Ioi 0, D.φ n i z :=
                          setIntegral_nonneg measurableSet_Ioi (fun z _ => hD.φ_nonneg n i z)
                        have h4 : 0 ≤ |C j| := abs_nonneg _
                        have h5 : 0 ≤ 1 + |y| := by positivity
                        have e1 : |C j| * (1 + |y|) * (∫ z in Set.Ioi 0, D.φ n i z) ≤ C0 * (1 + |y|) := by
                          calc |C j| * (1 + |y|) * (∫ z in Set.Ioi 0, D.φ n i z) ≤ |C j| * (1 + |y|) * 1 :=
                                mul_le_mul_of_nonneg_left h1 (by positivity)
                            _ ≤ C0 * (1 + |y|) := by nlinarith
                        have e2 : |C j| * ∫ z in Set.Ioi 0, (z * D.φ n i z) ≤ C0 * |D.M| := by
                          calc |C j| * ∫ z in Set.Ioi 0, (z * D.φ n i z) ≤ |C j| * |D.M| :=
                                mul_le_mul_of_nonneg_left h2 h4
                            _ ≤ C0 * |D.M| := mul_le_mul_of_nonneg_right hCj (abs_nonneg _)
                        linarith
                calc ∑ j, D.P i j * ∫ z in Set.Ioi 0, v j (y - z) * D.φ n i z
                    ≤ ∑ j, D.P i j * (C0 * (1 + |y|) + C0 * |D.M|) :=
                      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hj j) (hD.P_nonneg i j))
                  _ = C0 * (1 + |y|) + C0 * |D.M| := by rw [← Finset.sum_mul, hD.P_sum, one_mul]
                  _ ≤ (C0 + C0 * |D.M|) * (1 + |y|) := by
                      have : 0 ≤ C0 * |D.M| := mul_nonneg (Finset.sum_nonneg (fun j _ => abs_nonneg _))
                        (abs_nonneg _)
                      have : 0 ≤ |y| := abs_nonneg y
                      nlinarith
            have hcapV : ∀ n < N, ∀ i x, capV D T N n i x = D.f n i x - D.c n i * x +
                sInf (capObjective D n (capV D T N (n + 1)) i x '' capLevels D T n i x) := by
              intro n hn i x
              unfold capV
              obtain ⟨m, hm⟩ : ∃ m, N - n = m + 1 := ⟨N - n - 1, by omega⟩
              have h2 : N - (n + 1) = m := by omega
              have h3 : N - (m + 1) = n := by omega
              rw [hm, h2]
              simp only [capAux, h3]
            -- the induction
            have hP : ∀ k, ∀ n, N - n = k → n ≤ N → ∀ j, (∀ x ≤ T.B, 0 ≤ capV D T N n j x) ∧
                  LowerSemicontinuousOn (capV D T N n j) (Set.Iic T.B) ∧
                  ∃ C, ∀ x ≤ T.B, capV D T N n j x ≤ C * (1 + |x|) := by
              intro k
              induction k with
              | zero =>
                intro n hk hn j
                have hnN : n = N := by omega
                have hV : capV D T N n j = D.f n j := by
                  unfold capV; rw [hk, hnN]; rfl
                rw [hV]
                refine ⟨fun x _ => hD.f_nonneg n j x, ?_, ⟨D.C, fun x _ => hD.f_growth n j x⟩⟩
                have hc : Continuous (D.f n j) := by
                  rw [← continuousOn_univ]; exact (hD.f_convex n j).continuousOn isOpen_univ
                exact hc.continuousOn.lowerSemicontinuousOn
              | succ k ih =>
                intro n hk hn j
                have hnN : n < N := by omega
                have hF := hFprop n hnN (ih (n + 1) (by omega) (by omega))
                have hz : LowerSemicontinuousOn (fun y => D.c n j * y + F D n (capV D T N (n + 1)) j y)
                    (Set.Iic T.B) :=
                  ((continuous_const.mul continuous_id).continuousOn.lowerSemicontinuousOn).add (hF.2.1 j)
                obtain ⟨ysel, h1, h2, _⟩ := hmin (D.K n j) (serviceA D T n j) T.B _ (hD.K_nonneg n j)
                  (hAB n hnN j) hz
                have hEq : ∀ x ≤ T.B, capV D T N n j x = D.f n j x - D.c n j * x +
                    (D.K n j * delta (ysel x - x) + (D.c n j * ysel x + F D n (capV D T N (n + 1)) j (ysel x))) := by
                  intro x hx
                  obtain ⟨g1, g2, g3⟩ := h1 x hx
                  have hmem : ysel x ∈ capLevels D T n j x :=
                    ⟨le_trans (le_max_left _ _) g1, le_trans (le_max_right _ _) g1, g2⟩
                  have hl : IsLeast (capObjective D n (capV D T N (n + 1)) j x '' capLevels D T n j x)
                      (capObjective D n (capV D T N (n + 1)) j x (ysel x)) := by
                    refine ⟨⟨ysel x, hmem, rfl⟩, ?_⟩
                    rintro _ ⟨y, ⟨hy1, hy2, hy3⟩, rfl⟩
                    have := g3 y (max_le hy1 hy2) hy3
                    unfold capObjective; linarith
                  rw [hcapV n hnN j x, hl.csInf_eq]; unfold capObjective; ring
                have hdelta : ∀ u, 0 ≤ delta u ∧ delta u ≤ 1 := by
                  intro u; unfold delta; split_ifs <;> norm_num
                refine ⟨?_, ?_, ?_⟩
                · intro x hx
                  rw [hEq x hx]
                  obtain ⟨g1, g2, _⟩ := h1 x hx
                  have := hF.2.2.1 j (ysel x) g2
                  have := hD.f_nonneg n j x
                  have := mul_nonneg (hD.K_nonneg n j) (hdelta (ysel x - x)).1
                  have := mul_le_mul_of_nonneg_left (le_trans (le_max_left _ _) g1) (hD.c_nonneg n j)
                  linarith
                · have hc : Continuous (D.f n j) := by
                    rw [← continuousOn_univ]; exact (hD.f_convex n j).continuousOn isOpen_univ
                  have hc2 : Continuous (fun x => D.f n j x - D.c n j * x) :=
                    hc.sub (continuous_const.mul continuous_id)
                  have hl := (hc2.continuousOn.lowerSemicontinuousOn (s := Set.Iic T.B)).add h2
                  intro x hx t ht
                  rw [hEq x hx] at ht
                  have := hl x hx t (by simpa using ht)
                  filter_upwards [this, self_mem_nhdsWithin] with x' hx' hx'm
                  rw [hEq x' hx'm]; simpa using hx'
                · obtain ⟨CF, hCF⟩ := hF.2.2.2
                  refine ⟨D.C + D.K n j + 2 * D.c n j + D.c n j * |serviceA D T n j| +
                      |CF| * (1 + |serviceA D T n j|), fun x hx => ?_⟩
                  have hle : capV D T N n j x ≤ D.f n j x - D.c n j * x +
                      (D.K n j * delta (max x (serviceA D T n j) - x) + (D.c n j * max x (serviceA D T n j) +
                        F D n (capV D T N (n + 1)) j (max x (serviceA D T n j)))) := by
                    rw [hEq x hx]
                    have := (h1 x hx).2.2 (max x (serviceA D T n j)) le_rfl (max_le hx (hAB n hnN j))
                    linarith
                  set A := serviceA D T n j
                  have hmx : max x A ≤ |x| + |A| := by
                    rcases le_total x A with h | h
                    · rw [max_eq_right h]; linarith [le_abs_self A, abs_nonneg x]
                    · rw [max_eq_left h]; linarith [le_abs_self x, abs_nonneg A]
                  have hamx : |max x A| ≤ |x| + |A| := by
                    rcases le_total x A with h | h
                    · rw [max_eq_right h]; linarith [abs_nonneg x]
                    · rw [max_eq_left h]; linarith [abs_nonneg A]
                  have hFb := hCF j (max x A) (max_le hx (hAB n hnN j))
                  have hFb2 : CF * (1 + |max x A|) ≤ |CF| * (1 + |x| + |A|) := by
                    calc CF * (1 + |max x A|) ≤ |CF| * (1 + |max x A|) :=
                          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
                      _ ≤ |CF| * (1 + |x| + |A|) :=
                          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
                  have hfg := hD.f_growth n j x
                  have hd := (hdelta (max x A - x)).2
                  have hK := hD.K_nonneg n j
                  have hc := hD.c_nonneg n j
                  have hKd : D.K n j * delta (max x A - x) ≤ D.K n j := by nlinarith
                  have hcx : D.c n j * (max x A - x) ≤ D.c n j * (2 * |x| + |A|) := by
                    apply mul_le_mul_of_nonneg_left _ hc
                    linarith [neg_abs_le x]
                  have hx0 := abs_nonneg x
                  have hA0 := abs_nonneg A
                  have hCF0 := abs_nonneg CF
                  have e1 := mul_nonneg hK hx0
                  have e2 := mul_nonneg (mul_nonneg hc hA0) hx0
                  have e3 := mul_nonneg (mul_nonneg hCF0 hA0) hx0
                  have hcx' : D.c n j * (max x A - x) = D.c n j * max x A - D.c n j * x := by ring
                  have hCx : D.C * (1 + |x|) = D.C + D.C * |x| := by ring
                  have hCF' : |CF| * (1 + |x| + |A|) = |CF| + |CF| * |x| + |CF| * |A| := by ring
                  have hcx2 : D.c n j * (2 * |x| + |A|) = 2 * D.c n j * |x| + D.c n j * |A| := by ring
                  have hgoal : (D.C + D.K n j + 2 * D.c n j + D.c n j * |A| + |CF| * (1 + |A|)) * (1 + |x|) =
                      D.C + D.C * |x| + D.K n j + D.K n j * |x| + 2 * D.c n j + 2 * D.c n j * |x| +
                      D.c n j * |A| + D.c n j * |A| * |x| + |CF| + |CF| * |A| + |CF| * |x| + |CF| * |A| * |x| := by
                    ring
                  rw [hgoal]
                  linarith
            have hPn : ∀ n ≤ N, ∀ j, (∀ x ≤ T.B, 0 ≤ capV D T N n j x) ∧
                  LowerSemicontinuousOn (capV D T N n j) (Set.Iic T.B) ∧
                  ∃ C, ∀ x ≤ T.B, capV D T N n j x ≤ C * (1 + |x|) := fun n hn => hP (N - n) n rfl hn
            have hsel : ∀ n i, ∃ ysel : ℝ → ℝ, n < N →
                ((∀ x ≤ T.B, max x (serviceA D T n i) ≤ ysel x ∧ ysel x ≤ T.B ∧
                  ∀ y, max x (serviceA D T n i) ≤ y → y ≤ T.B →
                    D.K n i * delta (ysel x - x) + (D.c n i * ysel x + F D n (capV D T N (n + 1)) i (ysel x)) ≤
                    D.K n i * delta (y - x) + (D.c n i * y + F D n (capV D T N (n + 1)) i y)) ∧
                  ∃ g : ℕ → ℝ → ℝ, (∀ k, Continuous (g k)) ∧ (∀ k x, 0 ≤ g k x) ∧
                    ∀ x, Tendsto (fun k => g k x) atTop (𝓝 (if x ≤ T.B then ysel x - x else 0))) := by
              intro n i
              by_cases hn : n < N
              · have hF := hFprop n hn (hPn (n + 1) (by omega))
                have hz : LowerSemicontinuousOn (fun y => D.c n i * y + F D n (capV D T N (n + 1)) i y)
                    (Set.Iic T.B) :=
                  ((continuous_const.mul continuous_id).continuousOn.lowerSemicontinuousOn).add (hF.2.1 i)
                obtain ⟨ysel, h1, _, h3⟩ := hmin (D.K n i) (serviceA D T n i) T.B _ (hD.K_nonneg n i)
                  (hAB n hn i) hz
                exact ⟨ysel, fun _ => ⟨h1, h3⟩⟩
              · exact ⟨id, fun h => absurd h hn⟩
            choose Y hY using hsel
            have hobj : ∀ n i x y, capObjective D n (capV D T N (n + 1)) i x y =
                D.K n i * delta (y - x) + (D.c n i * y + F D n (capV D T N (n + 1)) i y) := by
              intro n i x y; unfold capObjective; ring
            have hleast : ∀ n < N, ∀ i x, x ≤ T.B →
                Y n i x ∈ capLevels D T n i x ∧
                IsLeast (capObjective D n (capV D T N (n + 1)) i x '' capLevels D T n i x)
                  (capObjective D n (capV D T N (n + 1)) i x (Y n i x)) := by
              intro n hn i x hx
              obtain ⟨h1, h2, h3⟩ := (hY n i hn).1 x hx
              have hmem : Y n i x ∈ capLevels D T n i x :=
                ⟨le_trans (le_max_left _ _) h1, le_trans (le_max_right _ _) h1, h2⟩
              refine ⟨hmem, ⟨⟨Y n i x, hmem, rfl⟩, ?_⟩⟩
              rintro _ ⟨y, ⟨hy1, hy2, hy3⟩, rfl⟩
              rw [hobj, hobj]
              exact h3 y (max_le hy1 hy2) hy3
            refine ⟨fun n hn i => (hPn n hn i).2.1,
              fun n hn => (hFprop n hn (hPn (n + 1) (by omega))).1, ?_, ?_⟩
            · intro n hn i x hx
              obtain ⟨hmem, hl⟩ := hleast n hn i x hx
              have hH : capH D T N n i x =
                  ((capObjective D n (capV D T N (n + 1)) i x (Y n i x) : ℝ) : EReal) := by
                apply le_antisymm
                · exact iInf_le_of_le ⟨Y n i x, hmem⟩ le_rfl
                · apply le_iInf
                  intro y
                  exact EReal.coe_le_coe_iff.mpr (hl.2 ⟨y.1, y.2, rfl⟩)
              refine ⟨⟨_, hmem⟩, hl.bddBelow, ?_, ?_⟩
              · rw [hH, hl.csInf_eq]
              · rw [hH, hcapV n hn i x, hl.csInf_eq]
                push_cast; ring
            · refine ⟨fun n i x => if x ≤ T.B then Y n i x - x else 0, ?_⟩
              intro n hn
              have hg := fun i => (hY n i hn).2
              choose g hgc hg0 hgt using hg
              refine ⟨⟨?_, fun k i => g i k, fun k i => hgc i k, fun k i x => hg0 i k x,
                fun i x => hgt i x⟩, ?_⟩
              · intro i x
                by_cases hx : x ≤ T.B
                · simp only [hx, if_true]
                  linarith [le_trans (le_max_left _ _) ((hY n i hn).1 x hx).1]
                · simp [hx]
              · intro i x hx
                simp only [hx, if_true]
                obtain ⟨h1, h2, h3⟩ := (hY n i hn).1 x hx
                have hxY : x + (Y n i x - x) = Y n i x := by ring
                refine ⟨⟨by linarith [le_trans (le_max_left _ _) h1], by
                  rw [hxY]; exact le_trans (le_max_right _ _) h1, by rw [hxY]; exact h2⟩, ?_, ?_⟩
                · rw [hxY, hcapV n hn i x, (hleast n hn i x hx).2.csInf_eq, hobj]
                  unfold orderCost; ring
                · intro u ⟨hu0, hu1, hu2⟩
                  have := h3 (x + u) (max_le (by linarith) hu1) hu2
                  rw [hxY]
                  unfold orderCost
                  have hxu : x + u - x = u := by ring
                  rw [hxu] at this
                  linarith
