-- Prove2me | solution 1 for RiemannMasullo.rapidDecaySequence_isFrechet
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T03:05:05.222973+00:00
-- url     : https://prove2.me/submissions/02fe098d-22b5-4750-9d42-5534fb68b72d

-- New proof of an upstream statement in mccorvie/riemann-masullo.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L600-L600
import Theorems.Thm_RiemannMasullo_rapidDecaySequence_weighted_l1_map
import Theorems.Thm_RiemannMasullo_rapidDecaySequence_withSeminorms
import Mathlib
import Definitions.Def_RiemannMasullo_AppC_Nets_and_Bounded_Lifts
import Definitions.Def_RiemannMasullo_RapidDecaySequenceTopology
open Filter Topology
open scoped ENNReal NNReal
open RiemannMasullo
variable {r : ℕ}
theorem solution : IsFrechetTVS (RapidDecaySequence r) := by
  classical
  let W (j : ℕ) (a : Fin r → ℤ) : ℝ≥0 :=
    (1 + ‖(WithLp.toLp 2 (fun i ↦ (a i : ℝ)) : EuclideanSpace ℝ (Fin r))‖₊)^j
  choose L hL hn using (rapidDecaySequence_weighted_l1_map r)
  have hcoord (j) (s : RapidDecaySequence r) (a) :
      L j s a = ((W j a:ℝ):ℂ) * s a := by simpa [W] using hL j s a
  have hzero (s : RapidDecaySequence r) (a) : L 0 s a = s a := by simp [hcoord,W]
  have hp := rapidDecaySequence_withSeminorms (r:=r)
  letI : FirstCountableTopology (RapidDecaySequence r) := hp.firstCountableTopology
  letI : (uniformity (RapidDecaySequence r)).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  letI : T1Space (RapidDecaySequence r) := hp.T1_of_separating (by
    intro s hs
    refine ⟨0,?_⟩
    intro h
    have hh : L 0 s = 0 := norm_eq_zero.mp ((hn 0 s).trans h)
    apply hs
    apply Subtype.ext
    funext a
    change s a = 0
    rw [←hzero s a,hh]
    rfl)
  refine ⟨inferInstance,hp.toPolynormableSpace,inferInstance,?_⟩
  change CompleteSpace (RapidDecaySequence r)
  apply UniformSpace.complete_of_cauchySeq_tendsto
  intro u hu
  have hex (j : ℕ) := cauchySeq_tendsto_of_complete ((L j).uniformContinuous.comp_cauchySeq hu)
  choose v hv using hex
  have heval (j : ℕ) (a : Fin r → ℤ) :
      Tendsto (fun n => L j (u n) a) atTop (𝓝 (v j a)) :=
    ((lp.evalCLM ℂ (fun _ : Fin r → ℤ => ℂ) 1 a).continuous.tendsto _).comp (hv j)
  have hcompat (j : ℕ) (a : Fin r → ℤ) : v j a = ((W j a:ℝ):ℂ)*v 0 a := by
    apply tendsto_nhds_unique (heval j a)
    have h := (tendsto_const_nhds (x:=((W j a:ℝ):ℂ)) (f:=atTop (α:=ℕ))).mul (heval 0 a)
    simp only [hzero] at h
    simpa only [hcoord] using h
  have hmem : (fun a => v 0 a) ∈ rapidDecaySequenceSubmodule r := by
    intro j
    have hseq := (memℓp_gen_iff (by norm_num : 0 < (1:ℝ≥0∞).toReal)).mp (v j).property
    have hs : Summable (fun a => ((‖v j a‖₊ : ℝ≥0):ℝ)) := by simpa using hseq
    have hfin := ENNReal.tsum_coe_ne_top_iff_summable_coe.mpr hs
    apply lt_top_iff_ne_top.mpr
    have heq : rapidDecaySequenceBound j (fun a => v 0 a) =
        ∑' a, (‖v j a‖₊ : ℝ≥0∞) := by
      unfold rapidDecaySequenceBound
      apply tsum_congr
      intro a
      have hw : ‖((W j a:ℝ):ℂ)‖₊ = W j a := by simp
      rw [hcompat j a,nnnorm_mul,hw,ENNReal.coe_mul]
      simp [W,ENNReal.coe_pow,ENNReal.coe_add]
    rwa [heq]
  let s : RapidDecaySequence r :=
    (⟨fun a => v 0 a,hmem⟩ : rapidDecaySequenceSubmodule r)
  have hvj (j : ℕ) : L j s = v j := by
    ext a
    exact (hcoord j s a).trans (hcompat j a).symm
  refine ⟨s,(hp.tendsto_nhds u s).mpr ?_⟩
  intro j ε hε
  have hb := (Metric.tendsto_nhds.mp (hv j)) ε hε
  filter_upwards [hb] with n h
  apply (hn j (u n - s)).symm.trans_lt
  rw [map_sub, hvj]
  simpa only [Function.comp_apply, dist_eq_norm] using h
