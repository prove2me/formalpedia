-- Prove2me | solution 1 for PhysFunctionalAnalysis.exists_atomless_sphere_measure
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:59:49.838247+00:00
-- url     : https://prove2.me/submissions/6dfeac35-6207-47a8-9015-409eb9f1e861

-- Generated from PhysFunctionalAnalysis.lean — solution of PhysFunctionalAnalysis.exists_atomless_sphere_measure
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
theorem solution (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (e₀ e₁ : E) (h : Orthonormal ℝ ![e₀, e₁]) :
    ∃ μ : Measure E, IsProbabilityMeasure μ ∧
      (∀ x, μ {x} = 0) ∧
      ∀ᵐ v ∂μ, ‖v‖ = 1 := by

  -- Define the function φ : ℝ → E by φ(t) = cos(πt/2) • e₀ + sin(πt/2) • e₁.
  let φ : ℝ → E := fun t => Real.cos (Real.pi * t / 2) • e₀ + Real.sin (Real.pi * t / 2) • e₁;
  refine ⟨ MeasureTheory.Measure.map φ unitMeasure, ?_, ?_, ?_ ⟩;
  · constructor;
    rw [ Measure.map_apply ] <;> norm_num;
    fun_prop;
  · intro x
    have h_preimage : MeasureTheory.volume (φ ⁻¹' {x} ∩ Set.Icc 0 1) = 0 := by
      have h_preimage : ∀ t₁ t₂ : ℝ, t₁ ∈ Set.Icc 0 1 → t₂ ∈ Set.Icc 0 1 → φ t₁ = φ t₂ → t₁ = t₂
        := by
        intro t₁ t₂ ht₁ ht₂ h_eq
        have h_cos : Real.cos (Real.pi * t₁ / 2) = Real.cos (Real.pi * t₂ / 2) := by
          apply_fun ( fun x => inner ℝ x e₀ ) at h_eq;
          simp +zetaDelta at *;
          simp_all +decide [ inner_add_left, inner_smul_left ];
          simp_all +decide [ real_inner_comm ]
        have h_sin : Real.sin (Real.pi * t₁ / 2) = Real.sin (Real.pi * t₂ / 2) := by
          simp +zetaDelta only [Nat.succ_eq_add_one, Nat.reduceAdd, orthonormal_vecCons_iff,
            Matrix.cons_val_fin_one, forall_const, IsEmpty.forall_iff, Orthonormal.of_isEmpty,
            and_self, and_true, mem_Icc] at *;
          replace h_eq := congr_arg ( fun x => inner ℝ x e₁ ) h_eq
          simp_all +decide [ inner_add_left, inner_smul_left ]
        exact Eq.symm ( by apply_fun Real.arccos at h_cos; rw [ Real.arccos_cos, Real.arccos_cos ]
                          at h_cos <;> nlinarith [ Real.pi_pos, ht₁.1, ht₁.2, ht₂.1, ht₂.2 ] );
      exact Set.Subsingleton.measure_zero
        ( fun t₁ ht₁ t₂ ht₂ => h_preimage t₁ t₂ ht₁.2 ht₂.2 <| by aesop )
        MeasureTheory.MeasureSpace.volume;
    rw [ MeasureTheory.Measure.map_apply_of_aemeasurable ];
    · unfold unitMeasure; aesop;
    · fun_prop;
    · exact MeasurableSingletonClass.measurableSet_singleton x;
  · rw [ MeasureTheory.ae_map_iff ];
    · refine Filter.Eventually.of_forall fun t => ?_;
      have := norm_add_sq_real ( Real.cos ( Real.pi * t / 2 ) • e₀ ) ( Real.sin ( Real.pi * t / 2 )
        • e₁ )
      simp_all +decide only [Nat.succ_eq_add_one, Nat.reduceAdd, orthonormal_vecCons_iff,
        Matrix.cons_val_fin_one, forall_const, IsEmpty.forall_iff, Orthonormal.of_isEmpty,
        and_self, and_true, norm_smul, Real.norm_eq_abs, mul_one, sq_abs, inner_smul_right,
        inner_smul_left, Real.ringHom_apply, mul_zero, add_zero, Real.cos_sq_add_sin_sq,
        sq_eq_one_iff]
      exact this.resolve_right ( by linarith [ norm_nonneg ( Real.cos ( Real.pi * t / 2 ) • e₀ +
                                   Real.sin ( Real.pi * t / 2 ) • e₁ ) ] );
    · fun_prop;
    · exact measurableSet_eq_fun ( measurable_norm ) measurable_const
