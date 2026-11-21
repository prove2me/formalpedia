-- Prove2me | solution 1 for RiemannMasullo.rapidDecaySequence_weighted_l1_map
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T02:54:51.281476+00:00
-- url     : https://prove2.me/submissions/c05fef5b-69d1-42c5-8627-02870302f9ad

-- New supporting theorem for the lattice sequence topology of Appendix D.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L574-L588
import Definitions.Def_RiemannMasullo_RapidDecaySequenceTopology
import Theorems.Thm_RiemannMasullo_rapidDecaySequence_withSeminorms
import Mathlib
open RiemannMasullo
open scoped ENNReal NNReal

theorem solution (r j : ℕ) :
    let W := fun a : Fin r → ℤ =>
      (1 + ‖(WithLp.toLp 2 (fun i ↦ (a i : ℝ)) : EuclideanSpace ℝ (Fin r))‖)^j
    ∃ L : RapidDecaySequence r →L[ℂ] lp (fun _ : Fin r → ℤ => ℂ) 1,
      (∀ s a, L s a = (W a : ℂ)*s a) ∧ ∀ s, ‖L s‖ = rapidDecaySequenceSeminorm j s := by
  classical
  dsimp only
  let W (a : Fin r → ℤ) : ℝ≥0 :=
    (1 + ‖(WithLp.toLp 2 (fun i ↦ (a i : ℝ)) : EuclideanSpace ℝ (Fin r))‖₊)^j
  let v (s : RapidDecaySequence r) (a : Fin r → ℤ) : ℂ := (W a : ℝ)*s a
  have hn (s : RapidDecaySequence r) (a : Fin r → ℤ) :
      ‖v s a‖₊ = W a * ‖s a‖₊ := by
    simp [v,nnnorm_mul]
  have he (s : RapidDecaySequence r) : (∑' a, (‖v s a‖₊ : ℝ≥0∞)) = rapidDecaySequenceBound j s.val := by
    unfold rapidDecaySequenceBound
    apply tsum_congr
    intro a
    simp [hn,W,ENNReal.coe_mul,ENNReal.coe_pow,ENNReal.coe_add]
  have hmem (s : RapidDecaySequence r) : Memℓp (v s) 1 := by
    apply (memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)).mpr
    have hh := ENNReal.tsum_coe_ne_top_iff_summable_coe.mp ((he s).trans_lt (s.property j)).ne
    simpa using hh
  let T : RapidDecaySequence r →ₗ[ℂ] lp (fun _ : Fin r → ℤ => ℂ) 1 :=
    { toFun := fun s => ⟨v s, hmem s⟩
      map_add' := fun s t => by
        ext a
        change (_:ℂ) * (s a+t a) = _ * s a + _ * t a
        exact mul_add _ _ _
      map_smul' := fun c s => by
        ext a
        change (_:ℂ) * (c * s a) = c * (_ * s a)
        exact mul_left_comm _ _ _ }
  have hnorm (s : RapidDecaySequence r) : ‖T s‖ = rapidDecaySequenceSeminorm j s := by
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1:ℝ≥0∞).toReal)]
    change _ = (rapidDecaySequenceBound j s.val).toReal
    rw [← he s,ENNReal.tsum_toReal_eq (fun _ => ENNReal.coe_ne_top)]
    simp [T]
  have hc : Continuous T := by
    apply Seminorm.cont_withSeminorms_normedSpace _ rapidDecaySequence_withSeminorms T
    refine ⟨{j},1,?_⟩
    intro s
    simp [hnorm,Seminorm.comp_apply]
    exact Finset.le_sup (f:=rapidDecaySequenceSeminorm (r:=r)) (Finset.mem_singleton_self j) s
  refine ⟨⟨T,hc⟩,?_,hnorm⟩
  intro s a
  change ((W a:ℝ):ℂ)*s a = _
  simp [W]
