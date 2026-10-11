-- Prove2me | solution 1 for PhysFunctionalAnalysis.polynomial_dense_L2
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:59:42.583553+00:00
-- url     : https://prove2.me/submissions/fd586a08-950b-42a1-857f-1821fff69441

-- Generated from PhysFunctionalAnalysis.lean — solution of PhysFunctionalAnalysis.polynomial_dense_L2
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
    Dense {f : Lp ℝ 2 unitMeasure | ∃ P : Polynomial ℝ,
           f =ᵐ[unitMeasure] fun x => P.eval x} := by

  intro f
  have h_dense : ∀ ε > 0, ∃ g : Lp ℝ 2 unitMeasure, ‖f - g‖ < ε ∧ ∃ P : Polynomial ℝ, g
    =ᵐ[unitMeasure] fun x => P.eval x := by
    intro ε ε_pos;
    -- By the density of continuous functions in L², there exists a continuous function g such that
    -- ‖f - g‖ < ε/2.
    have dens : ∀ f : Lp ℝ 2 unitMeasure, ∀ ε > 0, ∃ g : Lp ℝ 2 unitMeasure, ‖f - g‖ < ε ∧ ∃
        g_cont : C(ℝ, ℝ), g =ᵐ[unitMeasure] fun x => g_cont x := by
      intro f ε ε_pos;
      have := @BoundedContinuousFunction.toLp_denseRange;
      specialize this ℝ unitMeasure ( p := 2 ) ℝ;
      have := this ( by norm_num );
      have := this.exists_dist_lt f ε_pos;
      obtain ⟨ g, hg ⟩ := this;
      have hg' : ‖f - BoundedContinuousFunction.toLp 2 unitMeasure ℝ g‖ < ε := by
        rwa [dist_eq_norm] at hg
      refine ⟨_, hg', g.toContinuousMap, ?_⟩;
      exact BoundedContinuousFunction.coeFn_toLp 2 unitMeasure ℝ g;
    obtain ⟨g, hg⟩ := dens f ( ε / 2 ) ( half_pos ε_pos );
    obtain ⟨ g_cont, hg_cont ⟩ := hg.2
    obtain ⟨ P, hP ⟩ : ∃ P : Polynomial ℝ, ∀ x ∈ Set.Icc (0 : ℝ) 1, |g_cont x - P.eval x| < ε / 4
      := by
      have h_weierstrass : ∃ P : Polynomial ℝ, ∀ x ∈ Set.Icc (0 : ℝ) 1, |P.eval x - g_cont x| < ε /
        4 := by
        apply_rules [ exists_polynomial_near_of_continuousOn, g_cont.continuous.continuousOn ]
        linarith
      simpa only [ abs_sub_comm ] using h_weierstrass
    use (MemLp.toLp (fun x => P.eval x) (by
    have h_poly_integrable : MeasureTheory.Integrable (fun x => P.eval x ^ 2) unitMeasure := by
      exact Continuous.integrableOn_Icc ( by exact P.continuous.pow 2 ) |> fun h => h.mono_set <|
                                            Set.Icc_subset_Icc le_rfl le_rfl;
    rw [ memLp_two_iff_integrable_sq ]
    · aesop
    · exact P.continuous.aestronglyMeasurable));
    have h_norm : ‖g - (MemLp.toLp (fun x => P.eval x) (by
    have h_poly_integrable : MeasureTheory.Integrable (fun x => P.eval x ^ 2) unitMeasure := by
      exact Continuous.integrableOn_Icc ( by exact P.continuous.pow 2 ) |> fun h => h.mono_set <|
                                            Set.Icc_subset_Icc le_rfl le_rfl;
    rw [ memLp_two_iff_integrable_sq ]
    · aesop
    · exact P.continuous.aestronglyMeasurable))‖ ≤ ENNReal.toReal (ENNReal.ofReal (ε / 4)) := by
      refine ENNReal.toReal_mono ?_ ?_;
      · norm_num;
      · rw [ eLpNorm_congr_ae ];
        rotate_left;
        · exact MeasureTheory.Lp.coeFn_sub _ _ |> fun h =>
            h.trans ( Filter.EventuallyEq.sub hg_cont ( MeasureTheory.MemLp.coeFn_toLp _ ) )
        rw [ eLpNorm_eq_lintegral_rpow_enorm_toReal ] <;> norm_num;
        refine le_trans (ENNReal.rpow_le_rpow
          (MeasureTheory.lintegral_mono_ae
            (g := fun _ => ENNReal.ofReal (ε / 4) ^ 2) ?_) (by norm_num)) ?_;
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with x hx using
            pow_le_pow_left₀ ( by positivity )
              ( by simpa [ Real.enorm_eq_ofReal_abs ] using
                    ENNReal.ofReal_le_ofReal ( le_of_lt ( hP x hx ) ) ) _;
        · norm_num [ ← ENNReal.ofReal_pow, ε_pos.le ];
          rw [ ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul ] ; norm_num;
    refine ⟨?_, P, MeasureTheory.MemLp.coeFn_toLp _⟩
    · rw [ show f - MemLp.toLp ( fun x => Polynomial.eval x P ) _
            = ( f - g ) + ( g - MemLp.toLp ( fun x => Polynomial.eval x P ) _ ) by abel1 ]
      refine lt_of_le_of_lt ( norm_add_le _ _ ) ?_
      rw [ ENNReal.toReal_ofReal ( by positivity ) ] at h_norm
      linarith
  rw [ Metric.mem_closure_iff ];
  exact fun ε hε => by
    rcases h_dense ε hε with ⟨ g, hg₁, P, hg₂ ⟩
    exact ⟨ g, ⟨ P, hg₂ ⟩, by simpa [ dist_eq_norm ] using hg₁ ⟩
