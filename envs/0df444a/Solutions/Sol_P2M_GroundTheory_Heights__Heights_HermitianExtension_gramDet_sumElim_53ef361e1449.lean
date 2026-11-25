-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermitianExtension_gramDet_sumElim_53ef361e1449
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:44:37.378562+00:00
-- url     : https://prove2.me/submissions/299fc6e3-4144-432c-b6e0-01588fa44744

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeExact
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_span_fibreVec_cf563df73035
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_lTensor_complex_smul_450d1267bf4b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_det_gram_im_04e273c56d14
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_det_gram_sumElim_66edcb621772
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianExtension_proj_incl_940321fee341

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Heights₂.Heights.HermitianExtension
variable {E' E E'' : HermitianBundle K} (X : HermitianExtension E' E E'')
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
namespace GroundTheory.Heights₂.Heights.HermitianExtension
theorem _root_.solution (σ : K →+* ℂ) {s' : m → E'.carrier} {s'' : n → E''.carrier}
    {u : n → E.carrier} (hu : ∀ j, X.proj (u j) = s'' j) (hs' : LinearIndependent (𝓞 K) s')
    (hcard' : Fintype.card m = Module.finrank (𝓞 K) E'.carrier) :
    gramDet E.metric σ (Sum.elim (fun i ↦ X.incl (s' i)) u) =
      gramDet E'.metric σ s' * gramDet E''.metric σ s'' := by
  let a : m → FibreSpace E.metric σ := fun i ↦ fibreVec E.metric σ (X.incl (s' i))
  let b : n → FibreSpace E.metric σ := fun j ↦ fibreVec E.metric σ (u j)
  let W := Submodule.span ℂ (Set.range a)
  have : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.finite_range a)
  have : CompleteSpace W := FiniteDimensional.complete ℂ W
  have hdec : ∀ j, ∃ p ∈ W, ∃ q ∈ Wᗮ, b j = p + q := fun j ↦ W.exists_add_mem_mem_orthogonal (b j)
  choose p hpW q hqW hb using hdec
  have hc : ∀ j, ∃ c : m → ℂ, ∑ i, c i • a i = p j :=
    fun j ↦ (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hpW j)
  choose c hc using hc
  have hq : ∀ j, q j = b j - ∑ i, (Matrix.of fun i j ↦ c j i) i j • a i := by
    intro j
    simp only [Matrix.of_apply, hc, hb j]
    abel
  have horth : ∀ i j, inner ℂ (a i) (q j) = 0 := fun i j ↦
    Submodule.inner_right_of_mem_orthogonal (K := W) (Submodule.subset_span (Set.mem_range_self i))
      (hqW j)
  have hfam : (fun k ↦ fibreVec E.metric σ (Sum.elim (fun i ↦ X.incl (s' i)) u k)) =
      Sum.elim a b := by
    funext k
    rcases k with i | j <;> rfl

  let L : FibreSpace E'.metric σ →ₗ[ℂ] FibreSpace E.metric σ :=
    { toFun := fun x ↦ X.incl.lTensor (ComplexAt σ) x
      map_add' := map_add _
      map_smul' := lTensor_complex_smul σ X.incl }
  let P : FibreSpace E.metric σ →ₗ[ℂ] FibreSpace E''.metric σ :=
    { toFun := fun x ↦ X.proj.lTensor (ComplexAt σ) x
      map_add' := map_add _
      map_smul' := lTensor_complex_smul σ X.proj }
  have hga : gram ℂ a = gram ℂ (fun i ↦ fibreVec E'.metric σ (s' i)) := by
    ext i k
    exact X.incl_isometric σ (1 ⊗ₜ s' i) (1 ⊗ₜ s' k)
  have hLW : ∀ w : Fibre σ E'.carrier, L (FibreSpace.equiv E'.metric σ w) ∈ W := by
    intro w
    have hw := Submodule.mem_map_of_mem (f := L) (mem_span_fibreVec E'.metric σ hs' hcard' w)
    rw [Submodule.map_span, ← Set.range_comp] at hw
    exact hw
  have hperp : ∀ j (w : Fibre σ E'.carrier),
      (E.metric.form σ).inner (X.incl.lTensor (ComplexAt σ) w) (q j) = 0 :=
    fun j w ↦ Submodule.inner_right_of_mem_orthogonal (hLW w) (hqW j)
  have hP : ∀ j, P (q j) = fibreVec E''.metric σ (s'' j) := by
    intro j
    rw [hq j, map_sub, map_sum]
    have h0 : ∀ i, P (a i) = 0 := fun i ↦ by
      change X.proj.lTensor (ComplexAt σ) ((1 : ComplexAt σ) ⊗ₜ X.incl (s' i)) = 0
      rw [LinearMap.lTensor_tmul, proj_incl, tmul_zero]
    simp only [map_smul, h0, smul_zero, Finset.sum_const_zero, sub_zero]
    change X.proj.lTensor (ComplexAt σ) ((1 : ComplexAt σ) ⊗ₜ u j) = _
    rw [LinearMap.lTensor_tmul, hu]
    rfl
  have hgq : gram ℂ q = gram ℂ (fun j ↦ fibreVec E''.metric σ (s'' j)) := by
    ext j k
    rw [gram_apply, gram_apply, ← hP j, ← hP k]
    exact (X.proj_coisometric σ (q j) (q k) (hperp j) (hperp k)).symm
  simp only [gramDet]
  rw [hfam, det_gram_sumElim a b q _ hq horth, hga, hgq, Complex.mul_re, det_gram_im,
    det_gram_im, mul_zero, sub_zero]
end GroundTheory.Heights₂.Heights.HermitianExtension
