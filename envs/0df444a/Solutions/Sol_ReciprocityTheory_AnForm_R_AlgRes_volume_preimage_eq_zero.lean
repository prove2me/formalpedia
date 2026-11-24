-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.AlgRes.volume_preimage_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:55.68865+00:00
-- url     : https://prove2.me/submissions/e80ea566-b77b-4f7e-bea7-f72b85f3740f

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsAtlas
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SNCstep
import Theorems.Thm_ReciprocityTheory_AnForm_R_AlgRes_isOpen_nonvan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial ReciprocityTheory.AnForm.M
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.AnForm.R
namespace AlgRes
theorem _root_.solution {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}
    (R : AlgRes ι P D e) (A : FinHolAtlas e R.M) (hA : R.IsGoodAtlas A) (j : Fin A.n) :
    MeasureTheory.volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹'
      {x | ∃ i, x ∈ R.src i ∧ (fun q => eval (R.coord i x) (R.lift i q)) ∈ conePts D}) = 0 := by
  classical
  have hset : (A.chart j).target ∩ (A.chart j).symm ⁻¹'
      {x | ∃ i, x ∈ R.src i ∧ (fun q => eval (R.coord i x) (R.lift i q)) ∈ conePts D} =
      ⋃ i, ((A.chart j).target ∩ (A.chart j).symm ⁻¹'
        {x | x ∈ R.src i ∧ (fun q => eval (R.coord i x) (R.lift i q)) ∈ conePts D}) := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨h1, i, h2⟩; exact ⟨i, h1, h2⟩
    · rintro ⟨i, h1, h2⟩; exact ⟨h1, i, h2⟩
  have hyp : ∀ l : Fin e, MeasureTheory.volume {w : Fin e → ℂ | w l = 0} = 0 := by
    intro l
    have : {w : Fin e → ℂ | w l = 0} =
        Set.univ.pi (Function.update (fun _ => (Set.univ : Set ℂ)) l {0}) := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_univ_pi]
      constructor
      · intro hw k
        by_cases hk : k = l
        · subst hk; simp [hw]
        · simp [Function.update_of_ne hk]
      · intro hw; simpa using hw l
    rw [this, MeasureTheory.volume_pi_pi]
    exact Finset.prod_eq_zero (Finset.mem_univ l) (by simp)
  rw [hset]
  refine MeasureTheory.measure_iUnion_null fun i => ?_
  apply MeasureTheory.measure_null_of_locally_null
  rintro y0 ⟨hy0t, hy0s, -⟩
  obtain ⟨ψ, hψc, hxψ, hψs, hψe⟩ := hA.2 i _ hy0s (R.sncAt i _ hy0s).r (R.sncAt i _ hy0s).span_eq
    _ (R.isOpen_nonvan i (R.sncAt i _ hy0s).h) ⟨hy0s, (R.sncAt i _ hy0s).eval_h⟩
  set d := R.sncAt i _ hy0s with hd
  have hU : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target ψ.open_source
  refine ⟨_, inter_mem_nhdsWithin _ (hU.mem_nhds ⟨hy0t, hxψ⟩), ?_⟩
  have hN : MeasureTheory.volume ((ψ.target ∩ ψ.symm ⁻¹' (A.chart j).source) ∩
      {w : Fin e → ℂ | ∏ l ∈ d.J, w l = 0}) = 0 := by
    refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_iUnion_null hyp)
    rintro w ⟨-, hw⟩
    obtain ⟨l, -, hl⟩ := Finset.prod_eq_zero_iff.1 hw
    exact Set.mem_iUnion.2 ⟨l, hl⟩
  have hg : DifferentiableOn ℝ ((A.chart j) ∘ ψ.symm)
      ((ψ.target ∩ ψ.symm ⁻¹' (A.chart j).source) ∩ {w : Fin e → ℂ | ∏ l ∈ d.J, w l = 0}) :=
    fun w hw => (((hψc j).2 w hw.1).differentiableAt.restrictScalars ℝ).differentiableWithinAt
  refine MeasureTheory.measure_mono_null ?_
    (MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero _ hg hN)
  rintro y ⟨⟨hyt, hys, hyD⟩, -, hyψ⟩
  refine ⟨ψ ((A.chart j).symm y), ⟨⟨ψ.map_source hyψ, ?_⟩, ?_⟩, ?_⟩
  · rw [Set.mem_preimage, ψ.left_inv hyψ]; exact (A.chart j).map_target hyt
  · have hbd := (R.zero_bd i _ hys).2 hyD _ d.mem_bd
    rw [map_mul, map_prod] at hbd
    have h0 := (mul_eq_zero.1 hbd).resolve_left (hψs hyψ).1.2
    simp only [Set.mem_ofPred_eq, hψe _ hyψ]
    exact h0
  · simp only [Function.comp_apply, ψ.left_inv hyψ, (A.chart j).right_inv hyt]
end AlgRes
end ReciprocityTheory.AnForm.R
