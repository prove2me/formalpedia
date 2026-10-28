-- Prove2me | solution 1 for OAI.YauCounterexamples.finite_near_far_sign_probability
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:17:03.911142+00:00
-- url     : https://prove2.me/submissions/48eedd11-5ab2-48a4-8743-840efe9ed36f

import Mathlib
import Definitions.Def_OAIQ070A003
import Definitions.Def_OAIQ070A004
import Theorems.Thm_OAI_YauCounterexamples_common_near_wave_sign_probability

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_GeneratedCutoffWaveEndpointRatio
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal RealInnerProductSpace

variable {I : Type*} [Fintype I]

lemma complexValueVector_inner (z w : I → ℂ) :
    ⟪complexValueVector z,complexValueVector w⟫ = ∑ i, ((starRingEnd ℂ (z i))*w i).re := by
  simp only [PiLp.inner_apply,complexValueVector,Fintype.sum_sum_type,
    RCLike.inner_apply,Complex.mul_re,Complex.conj_re,Complex.conj_im,
    neg_mul,sub_neg_eq_add,Finset.sum_add_distrib, Sum.elim_inl, Sum.elim_inr]
  simp only [starRingEnd_apply, star_trivial]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

lemma complexValueVector_norm_sq (z : I → ℂ) :
    ‖complexValueVector z‖^2 = ∑ i, ‖z i‖^2 := by
  rw [←real_inner_self_eq_norm_sq,complexValueVector_inner]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im,neg_mul,sub_neg_eq_add,
    Complex.sq_norm]
  rw [Complex.normSq_apply]

omit [Fintype I] in
lemma complexValueVector_sub (z w : I → ℂ) :
    complexValueVector (fun i => z i-w i) = complexValueVector z-complexValueVector w := by
  ext i
  cases i <;> rfl

omit [Fintype I] in
lemma complexValueVector_real_smul (a : ℝ) (z : I → ℂ) :
    complexValueVector (fun i => (a : ℂ)*z i) = a • complexValueVector z := by
  ext i
  cases i <;> simp [complexValueVector,Complex.mul_re,Complex.mul_im]

lemma complexValueVector_rotated_norm (z : I → ℂ) (θ : I → ℝ) :
    ‖complexValueVector (rotatedWaveValues z θ)‖ = ‖complexValueVector z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [complexValueVector_norm_sq,complexValueVector_norm_sq]
  apply Finset.sum_congr rfl
  intro i _
  simp [rotatedWaveValues,Complex.norm_exp]

end



section
open Set Filter
open scoped Topology RealInnerProductSpace

variable {I : Type*} [Fintype I]
lemma complexValueVector_relative_error (z w : I → ℂ) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ i, ‖z i-w i‖ ≤ δ*‖z i‖) :
    ‖complexValueVector z-complexValueVector w‖ ≤ δ*‖complexValueVector z‖ := by
  rw [←complexValueVector_sub]
  have hs : ‖complexValueVector (fun i => z i-w i)‖^2 ≤ δ^2*‖complexValueVector z‖^2 := by
    rw [complexValueVector_norm_sq,complexValueVector_norm_sq,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hh := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hδ (norm_nonneg _))).mpr (h i)
    simpa only [mul_pow] using hh
  nlinarith [norm_nonneg (complexValueVector (fun i => z i-w i)),
    mul_nonneg hδ (norm_nonneg (complexValueVector z))]
end



open Set Filter
open scoped Topology ContDiff


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_LocalizedPacketSignProbability
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal RealInnerProductSpace
section NearFarVectors
variable {I : Type} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma complexValueVector_norm_le_sum (v : I → ℂ) :
    ‖complexValueVector v‖ ≤ ∑ i, ‖v i‖ := by
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg (s := (Finset.univ : Finset I))
    (f := fun i => ‖v i‖) (fun _ _ => norm_nonneg _)
  rw [←complexValueVector_norm_sq] at hs
  nlinarith [norm_nonneg (complexValueVector v),Finset.sum_nonneg (s := Finset.univ) (f := fun i => ‖v i‖)
    (fun _ _ => norm_nonneg _)]

omit [DecidableEq I] in
lemma complexValueVector_component_le (v : I → ℂ) (i : I) :
    ‖v i‖ ≤ ‖complexValueVector v‖ := by
  have hs := Finset.single_le_sum (f := fun j => ‖v j‖^2) (s := Finset.univ)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  rw [←complexValueVector_norm_sq] at hs
  nlinarith [norm_nonneg (v i),norm_nonneg (complexValueVector v)]

lemma maskComplex_far_error (s : Finset I) (v : I → ℂ) {τ : ℝ} (hτ : 0 ≤ τ)
    (hfar : ∀ i ∉ s, ‖v i‖ ≤ τ) :
    ‖complexValueVector (maskComplex s v)-complexValueVector v‖ ≤ (Fintype.card I : ℝ)*τ := by
  rw [←complexValueVector_sub]
  apply (complexValueVector_norm_le_sum _).trans
  calc
    _ ≤ ∑ _i : I, τ := Finset.sum_le_sum (fun i _ => by
      by_cases hi : i ∈ s
      · simp [maskComplex,hi,hτ]
      · simpa only [maskComplex,if_neg hi,zero_sub,norm_neg] using hfar i hi)
    _ = _ := by simp

lemma maskComplex_norm_ge (s : Finset I) (v : I → ℂ) {A : ℝ}
    (h : ∃ i ∈ s, A ≤ ‖v i‖) : A ≤ ‖complexValueVector (maskComplex s v)‖ := by
  obtain ⟨i,hi,hA⟩ := h
  exact hA.trans (by simpa only [maskComplex,if_pos hi] using
    complexValueVector_component_le (maskComplex s v) i)

lemma masked_endpoint_vector_error (s : Finset I) (v w : I → ℂ) (α : ℝ) (hα : 0 < α)
    (θ : I → ℝ) {ε τ : ℝ} (hε : 0 ≤ ε) (hτ : 0 ≤ τ)
    (hnear : ∀ i ∈ s, ‖(α : ℂ)*Complex.exp ((θ i : ℂ)*Complex.I)*v i-w i‖ ≤
      ε*‖(α : ℂ)*Complex.exp ((θ i : ℂ)*Complex.I)*v i‖)
    (hfar : ∀ i ∉ s, ‖w i‖ ≤ τ) :
    let z := maskComplex s v
    let b := fun i => (α : ℂ)*rotatedWaveValues z θ i
    ‖complexValueVector b-complexValueVector w‖ ≤
      ε*‖complexValueVector b‖+(Fintype.card I : ℝ)*τ := by
  dsimp only
  let b := fun i => (α : ℂ)*rotatedWaveValues (maskComplex s v) θ i
  have hh : ‖complexValueVector b-complexValueVector (maskComplex s w)‖ ≤
      ε*‖complexValueVector b‖ := by
    apply complexValueVector_relative_error _ _ hε
    intro i
    by_cases hi : i ∈ s
    · simpa only [b,rotatedWaveValues,maskComplex,if_pos hi,mul_assoc,
        norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hα] using hnear i hi
    · simp [b,rotatedWaveValues,maskComplex,hi]
  have ht := norm_add_le (complexValueVector b-complexValueVector (maskComplex s w))
    (complexValueVector (maskComplex s w)-complexValueVector w)
  rw [sub_add_sub_cancel] at ht
  exact ht.trans (add_le_add hh (maskComplex_far_error s w hτ hfar))

lemma masked_rotated_norm (s : Finset I) (v : I → ℂ) {α : ℝ} (hα : 0 < α)
    (θ : I → ℝ) :
    ‖complexValueVector (fun i => (α : ℂ)*rotatedWaveValues (maskComplex s v) θ i)‖ =
      α*‖complexValueVector (maskComplex s v)‖ := by
  rw [complexValueVector_real_smul,norm_smul,Real.norm_eq_abs,abs_of_pos hα,
    complexValueVector_rotated_norm]

end NearFarVectors

theorem finite_near_far_sign_probability_oai {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ p > 0, ∀ (I : Type) [Fintype I] [DecidableEq I]
      (s : Finset I) (v : I → ℂ) (w : Fin 3 → I → ℂ) (α : Fin 3 → ℝ)
      (θ : I → Fin 3 → ℝ) (m : ℝ) (m' : Fin 3 → ℝ) (A ε δ τ₀ : ℝ) (τ : Fin 3 → ℝ),
      0 < A → 0 ≤ ε → ε ≤ δ → 0 ≤ τ₀ → (∀ j, 0 ≤ τ j) →
      (∃ i ∈ s, A ≤ ‖v i‖) → (∀ j, 0 < α j) → δ ≤ 1/16 → δ ≤ κ/96 →
      (∀ i ∈ s, ∀ j, |θ i j| ≤ 1) → (∀ i ∈ s, κ ≤ ∑ j, (θ i j)^2) →
      (∀ i ∉ s, ‖v i‖ ≤ τ₀) → (Fintype.card I : ℝ)*τ₀ ≤ δ*A →
      (∀ j, (Fintype.card I : ℝ)*τ j ≤ (δ-ε)*α j*A) →
      (∀ j i, i ∈ s →
        ‖(α j : ℂ)*Complex.exp ((θ i j : ℂ)*Complex.I)*v i-w j i‖ ≤
          ε*‖(α j : ℂ)*Complex.exp ((θ i j : ℂ)*Complex.I)*v i‖) →
      (∀ j i, i ∉ s → ‖w j i‖ ≤ τ j) →
      |m/‖complexValueVector v‖| ≤ 1 → (∀ j, |m' j/‖complexValueVector (w j)‖| ≤ 1) →
      ∃ j, ENNReal.ofReal p ≤ (Measure.pi (fun _ : I => stdGaussian ℂ))
        {γ | (m+complexGaussianRealValue v γ)*(m' j+complexGaussianRealValue (w j) γ) < 0} := by
  obtain ⟨p,hp,hprob⟩ := common_near_wave_sign_probability hκ hκ1
  refine ⟨p,hp,?_⟩
  intro I _ _ s v w α θ m m' A ε δ τ₀ τ hA hε hεδ hτ₀ hτ hlarge hα hδ1 hδκ hθ heng hfar hbasebudget hendbudget hnear hfar' hm hm'
  let z := maskComplex s v
  have hAz : A ≤ ‖complexValueVector z‖ := maskComplex_norm_ge s v hlarge
  have hz : complexValueVector z ≠ 0 := norm_pos_iff.mp (hA.trans_le hAz)
  obtain ⟨i₀,hi₀,_hlarge⟩ := hlarge
  let θ' := fun i j => if i ∈ s then θ i j else θ i₀ j
  have hθ' (i j) : |θ' i j| ≤ 1 := by
    dsimp [θ']; split_ifs with hi
    · exact hθ i hi j
    · exact hθ i₀ hi₀ j
  have heng' (i) : κ ≤ ∑ j, (θ' i j)^2 := by
    by_cases hi : i ∈ s
    · simpa only [θ',if_pos hi] using heng i hi
    · simpa only [θ',if_neg hi] using heng i₀ hi₀
  have hδ : 0 ≤ δ := hε.trans hεδ
  have hbase : ‖complexValueVector z-complexValueVector v‖ ≤ δ*‖complexValueVector z‖ :=
    (maskComplex_far_error s v hτ₀ hfar).trans (hbasebudget.trans
      (mul_le_mul_of_nonneg_left hAz hδ))
  have hend (j) :
      ‖complexValueVector (fun i => (α j : ℂ)*rotatedWaveValues z (fun i => θ' i j) i)
        -complexValueVector (w j)‖ ≤
      δ*‖complexValueVector (fun i => (α j : ℂ)*rotatedWaveValues z (fun i => θ' i j) i)‖ := by
    have hh := masked_endpoint_vector_error s v (w j) (α j) (hα j) (fun i => θ' i j)
      hε (hτ j) (fun i hi => by simpa only [θ',if_pos hi] using hnear j i hi) (hfar' j)
    dsimp only at hh
    change _ ≤ _ at hh
    refine hh.trans ?_
    have hnorm := masked_rotated_norm s v (hα j) (fun i => θ' i j)
    change ‖complexValueVector (fun i => (α j : ℂ)*rotatedWaveValues z (fun i => θ' i j) i)‖ =
      α j*‖complexValueVector z‖ at hnorm
    rw [hnorm]
    have hb := (hendbudget j).trans (mul_le_mul_of_nonneg_left hAz
      (mul_nonneg (sub_nonneg.mpr hεδ) (hα j).le))
    nlinarith
  exact hprob I z v w α θ' m m' δ hz hα hδ1 hδκ hθ' heng' hbase hend hm hm'
end



open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal RealInnerProductSpace

end YauCounterexamples
end

end OAI
end

theorem solution : type_of% @OAI.YauCounterexamples.finite_near_far_sign_probability_oai := @OAI.YauCounterexamples.finite_near_far_sign_probability_oai
