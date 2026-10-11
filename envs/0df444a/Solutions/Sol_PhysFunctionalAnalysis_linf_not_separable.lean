-- Prove2me | solution 1 for PhysFunctionalAnalysis.linf_not_separable
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:59:39.364984+00:00
-- url     : https://prove2.me/submissions/bb939943-5590-49a8-b4d7-d5624d2bdee0

-- Generated from PhysFunctionalAnalysis.lean — solution of PhysFunctionalAnalysis.linf_not_separable
import Mathlib
import Definitions.Def_PhysFunctionalAnalysis
import Definitions.Def_PhysMeasureBasis
import Definitions.Def_ChapterA4
open PhysFunctionalAnalysis



open MeasureTheory Set
open scoped ENNReal lp

noncomputable section


open PhysMeasureBasis

set_option maxHeartbeats 1000000 in
theorem solution :
    ¬ TopologicalSpace.SeparableSpace (Lp ℝ ⊤ unitMeasure) := by

  intro h
  obtain ⟨D, hD_countable, hD_dense⟩ : ∃ D : Set (Lp ℝ ⊤ unitMeasure), D.Countable ∧ Dense D := by
    grind +splitIndPred;
  -- For $t \in (0,1]$, let $u_t := \text{indicatorConstLp} \top (\text{measurableSet_Ioc})
  -- (\text{finiteness}) (1:ℝ)$ for the set $Ioc 0 t$.
  set u : ℝ → Lp ℝ ⊤ unitMeasure := fun t => MeasureTheory.MemLp.toLp (Set.indicator (Set.Ioc 0 t)
    fun _ => 1) (MeasureTheory.memLp_const (1 : ℝ) |>.indicator (measurableSet_Ioc));
  -- For $0 < s < t \leq 1$, $\|u_t - u_s\| = 1$: the difference is a.e. the indicator of $Ioc s t$,
  -- and the $L^\infty$ norm of the indicator of a positive-measure set with value 1 equals 1.
  have h_dist : ∀ s t : ℝ, 0 < s → s < t → t ≤ 1 → dist (u t) (u s) = 1 := by
    intros s t hs ht ht1
    have h_diff : ∀ᵐ x ∂unitMeasure, (u t - u s) x = if x ∈ Set.Ioc s t then 1 else 0 := by
      have h_diff : ∀ᵐ x ∂unitMeasure, (u t - u s) x = (Set.indicator (Set.Ioc 0 t) (fun _ => 1 : ℝ
        → ℝ) - Set.indicator (Set.Ioc 0 s) (fun _ => 1 : ℝ → ℝ)) x := by
        have h_diff : ∀ᵐ x ∂unitMeasure, (u t - u s) x = (u t) x - (u s) x := by
          exact MeasureTheory.Lp.coeFn_sub _ _;
        filter_upwards [ h_diff, MeasureTheory.MemLp.coeFn_toLp ( MeasureTheory.memLp_const ( 1 : ℝ
          ) |>.indicator ( measurableSet_Ioc ) : MeasureTheory.MemLp ( Set.indicator ( Set.Ioc 0 t )
          fun _ => 1 : ℝ → ℝ ) ⊤ unitMeasure ), MeasureTheory.MemLp.coeFn_toLp (
          MeasureTheory.memLp_const ( 1 : ℝ ) |>.indicator ( measurableSet_Ioc ) :
          MeasureTheory.MemLp ( Set.indicator ( Set.Ioc 0 s ) fun _ => 1 : ℝ → ℝ ) ⊤ unitMeasure ) ]
          with x hx₁ hx₂ hx₃
        aesop
      filter_upwards [ h_diff ] with x hx ; split_ifs <;> simp_all +decide [ Set.indicator ] ;
      · grind;
      · grind;
    -- The L^∞ norm of the indicator of a positive-measure set with value 1 equals 1.
    have h_norm : eLpNorm (fun x => if x ∈ Set.Ioc s t then 1 else 0 : ℝ → ℝ) ⊤ unitMeasure = 1
      := by
      refine le_antisymm ?_ ?_ <;> norm_num [ eLpNormEssSup ];
      · refine csInf_le ?_ ?_ <;> norm_num;
        exact Filter.eventually_inf_principal.mpr
          ( Filter.Eventually.of_forall fun x hx => by split_ifs <;> norm_num );
      · refine le_csInf ?_ ?_ <;> norm_num;
        · refine ⟨ 1, ?_ ⟩ ; norm_num [ Filter.eventually_inf_principal ];
          exact Filter.Eventually.of_forall fun x hx₁ hx₂ => by split_ifs <;> norm_num;
        · intro b hb
          contrapose! hb
          simp_all +decide only [AddSubgroupClass.coe_sub, mem_Ioc, measurableSet_Icc,
            ae_restrict_eq, Filter.eventually_inf_principal, mem_Icc, and_imp]
          rw [ Filter.Frequently, Filter.eventually_inf_principal ];
          rw [ MeasureTheory.ae_iff ] ; norm_num;
          refine ne_of_gt (lt_of_lt_of_le ?_
            (MeasureTheory.measure_mono (s := Set.Ioc s t) ?_))
          · simp +decide [ ht ];
          · exact fun x hx => ⟨ by linarith [ hx.1 ], by linarith [ hx.2 ],
              by rw [ if_pos ⟨ hx.1, hx.2 ⟩ ] ; simpa using hb ⟩;
    rw [ dist_eq_norm, Lp.norm_def ];
    rw [ eLpNorm_congr_ae h_diff ] ; aesop;
  -- From a countable dense set $D$, for each $t$ pick $d_t \in D$ with $\dist (u t) (d t) < 1/2$;
  -- the assignment $t \mapsto d t$ is injective on $(0,1]$.
  obtain ⟨d, hd⟩ : ∃ d : ℝ → Lp ℝ ⊤ unitMeasure, (∀ t : ℝ, 0 < t → t ≤ 1 → d t ∈ D ∧ dist (u t) (d
    t) < 1 / 2) ∧ (∀ s t : ℝ, 0 < s → s < t → t ≤ 1 → d s ≠ d t) := by
    have h_inj : ∀ t : ℝ, 0 < t → t ≤ 1 → ∃ d_t ∈ D, dist (u t) d_t < 1 / 2 := by
      exact fun t ht₁ ht₂ => by
        rcases Metric.mem_closure_iff.mp ( hD_dense ( u t ) ) ( 1 / 2 ) ( by norm_num ) with ⟨ d,
                                                                            hd₁, hd₂ ⟩
        exact ⟨ d, hd₁, hd₂ ⟩
    choose! d hd using h_inj;
    refine ⟨ d, hd, fun s t hs ht ht' hst => ?_ ⟩;
    have := h_dist s t hs ht ht'
    have := hd s hs ( by linarith )
    have := hd t ( by linarith ) ht'
    simp_all +decide [ dist_comm ]
    have := dist_triangle_left ( u s ) ( u t ) ( d t )
    norm_num at *
    linarith [ h_dist s t hs ht ht' ]
  -- Hence $(0,1]$ injects into countable $D$, so $(Ioc (0:ℝ) 1)$ is countable.
  have h_countable : Set.Countable (Set.Ioc (0 : ℝ) 1) := by
    have h_inj : Set.InjOn d (Set.Ioc (0 : ℝ) 1) := by
      exact fun x hx y hy hxy => le_antisymm ( le_of_not_gt fun h => hd.2 _ _ hy.1 h hx.2 hxy.symm )
        ( le_of_not_gt fun h => hd.2 _ _ hx.1 h hy.2 hxy );
    exact Set.MapsTo.countable_of_injOn ( fun x hx => hd.1 x hx.1 hx.2 |>.1 ) h_inj hD_countable;
  exact absurd h_countable ( by exact fun h => absurd ( h.measure_zero <|
                               MeasureTheory.MeasureSpace.volume ) ( by norm_num ) )
