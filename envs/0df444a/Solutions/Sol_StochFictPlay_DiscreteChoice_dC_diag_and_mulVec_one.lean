-- Prove2me | solution 1 for StochFictPlay.DiscreteChoice.dC_diag_and_mulVec_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T16:27:10.783284+00:00
-- url     : https://prove2.me/submissions/bbd311a8-f810-4478-809c-512e6905bfb6

import Mathlib
import Definitions.Def_StochFictPlay_DiscreteChoice_ChoiceProb

set_option autoImplicit false

open MeasureTheory

namespace StochFictPlay.DiscreteChoice.P2MAuxED44

theorem tie_null {n : ℕ} (j k : Fin n) (hjk : k ≠ j) (c : ℝ) :
    (volume : Measure (Fin n → ℝ)) {e | e k - e j = c} = 0 := by
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k -
    LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j
  have hL : ∀ e, L e = e k - e j := fun e => rfl
  have hne : LinearMap.ker L ≠ ⊤ := by
    intro h
    have hmem : (Pi.single k (1:ℝ) : Fin n → ℝ) ∈ LinearMap.ker L := h ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, hL] at hmem
    simp [Pi.single_apply, Ne.symm hjk] at hmem
  have h0 := Measure.addHaar_submodule (volume : Measure (Fin n → ℝ)) _ hne
  have hset : {e : Fin n → ℝ | e k - e j = c} =
      (fun e => e + (-(c • Pi.single k (1:ℝ)))) ⁻¹' (LinearMap.ker L : Set (Fin n → ℝ)) := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe, LinearMap.mem_ker, hL]
    simp [Pi.single_apply, Ne.symm hjk]
    constructor <;> intro h <;> linarith
  rw [hset, measure_preimage_add_right]
  exact h0

theorem sum_choiceProb {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : IsStrictlyPositiveDensity f)
    (π : Fin n → ℝ) (i0 : Fin n) : ∑ j, choiceProb f π j = 1 := by
  have huniv : noiseLaw f Set.univ = 1 := by
    rw [noiseLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hf.lintegral_eq_one
  have hac : noiseLaw f ≪ volume := withDensity_absolutelyContinuous _ _
  let A : Fin n → Set (Fin n → ℝ) := fun i => {e | ∀ j, j ≠ i → π j + e j < π i + e i}
  have hAm : ∀ i, MeasurableSet (A i) := by
    intro i
    have hAi : A i = ⋂ j, ⋂ (_ : j ≠ i), {e : Fin n → ℝ | π j + e j < π i + e i} := by
      ext e; simp [A]
    rw [hAi]
    refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_
    exact measurableSet_lt (by fun_prop) (by fun_prop)
  have hdisj : Pairwise (Function.onFun Disjoint A) := by
    intro a b hab
    rw [Function.onFun, Set.disjoint_left]
    intro e ha hb
    have h1 := ha b (Ne.symm hab)
    have h2 := hb a hab
    linarith
  have hcompl : noiseLaw f (⋃ i, A i)ᶜ = 0 := by
    apply hac
    apply measure_mono_null
      (t := ⋃ j, ⋃ k, {e : Fin n → ℝ | k ≠ j ∧ e k - e j = π j - π k})
    · intro e he
      simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at he
      obtain ⟨j, -, hj⟩ :=
        Finset.exists_max_image Finset.univ (fun m => π m + e m) ⟨i0, Finset.mem_univ _⟩
      have hej := he j
      simp only [A, Set.mem_ofPred_eq, not_forall, not_lt] at hej
      obtain ⟨k, hkj, hk⟩ := hej
      have hk2 := hj k (Finset.mem_univ _)
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
      exact ⟨j, k, hkj, by linarith⟩
    · refine measure_iUnion_null fun j => measure_iUnion_null fun k => ?_
      by_cases hkj : k = j
      · simp [hkj]
      · exact measure_mono_null (fun e he => he.2) (tie_null j k hkj _)
  have hU : noiseLaw f (⋃ i, A i) = 1 := by
    have := measure_add_measure_compl (μ := noiseLaw f) (MeasurableSet.iUnion hAm)
    rw [hcompl, add_zero, huniv] at this
    exact this
  have hsum : ∑ j, noiseLaw f (A j) = 1 := by
    have := measure_iUnion (μ := noiseLaw f) hdisj hAm
    rw [tsum_fintype] at this
    rw [← this, hU]
  have hfin : ∀ j ∈ (Finset.univ : Finset (Fin n)), noiseLaw f (A j) ≠ ⊤ := by
    intro j _
    refine ne_top_of_le_ne_top ?_ (measure_mono (Set.subset_univ (A j)))
    rw [huniv]; exact ENNReal.one_ne_top
  show ∑ j, (noiseLaw f (A j)).toReal = 1
  rw [← ENNReal.toReal_sum hfin, hsum, ENNReal.toReal_one]

theorem choiceProb_shift {n : ℕ} (f : (Fin n → ℝ) → ℝ) (π : Fin n → ℝ) (t : ℝ) :
    choiceProb f (π + t • fun _ => (1:ℝ)) = choiceProb f π := by
  funext i
  unfold choiceProb
  congr 2
  ext e
  simp only [Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
  constructor
  · intro h j hj
    have := h j hj
    linarith
  · intro h j hj
    have := h j hj
    linarith

end StochFictPlay.DiscreteChoice.P2MAuxED44

open StochFictPlay.DiscreteChoice in
theorem solution {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : IsStrictlyPositiveDensity f)
    (hC : ContDiff ℝ 1 (choiceProb f)) (π : Fin n → ℝ) :
    (∀ i : Fin n, fderiv ℝ (choiceProb f) π (Pi.single i 1) i =
        -∑ j ∈ Finset.univ.erase i, fderiv ℝ (choiceProb f) π (Pi.single i 1) j) ∧
      fderiv ℝ (choiceProb f) π (fun _ => 1) = 0 := by
  have hd : DifferentiableAt ℝ (choiceProb f) π :=
    (hC.differentiable (by norm_num)).differentiableAt
  have hD : HasFDerivAt (choiceProb f) (fderiv ℝ (choiceProb f) π) π := hd.hasFDerivAt
  refine ⟨fun i => ?_, ?_⟩
  · let S : (Fin n → ℝ) →L[ℝ] ℝ := ∑ j, ContinuousLinearMap.proj j
    have hS : ∀ x : Fin n → ℝ, S x = ∑ j, x j := by
      intro x; simp [S]
    have h1 : HasFDerivAt (fun x => S (choiceProb f x)) (S.comp (fderiv ℝ (choiceProb f) π)) π :=
      S.hasFDerivAt.comp π hD
    have h2 : HasFDerivAt (fun x => S (choiceProb f x)) (0 : (Fin n → ℝ) →L[ℝ] ℝ) π := by
      have hconst : (fun x => S (choiceProb f x)) = fun _ => (1:ℝ) := by
        funext x
        rw [hS]
        exact StochFictPlay.DiscreteChoice.P2MAuxED44.sum_choiceProb f hf x i
      rw [hconst]
      exact hasFDerivAt_const _ _
    have h3 := h1.unique h2
    have h4 : S (fderiv ℝ (choiceProb f) π (Pi.single i 1)) = 0 := by
      have := congrArg (fun L => L (Pi.single i (1:ℝ))) h3
      simpa using this
    rw [hS, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at h4
    linarith
  · have hp : HasDerivAt (fun t : ℝ => π + t • fun _ => (1:ℝ)) (fun _ => (1:ℝ)) 0 := by
      have := ((hasDerivAt_id (0:ℝ)).smul_const (fun _ => (1:ℝ))).const_add π
      simpa using this
    have hD' : HasFDerivAt (choiceProb f) (fderiv ℝ (choiceProb f) π)
        (π + (0:ℝ) • fun _ => (1:ℝ)) := by
      rw [zero_smul, add_zero]; exact hD
    have hg := hD'.comp_hasDerivAt (0:ℝ) hp
    have hc : HasDerivAt (fun t : ℝ => choiceProb f (π + t • fun _ => (1:ℝ))) 0 0 := by
      simp only [StochFictPlay.DiscreteChoice.P2MAuxED44.choiceProb_shift]
      exact hasDerivAt_const _ _
    exact hg.unique hc
