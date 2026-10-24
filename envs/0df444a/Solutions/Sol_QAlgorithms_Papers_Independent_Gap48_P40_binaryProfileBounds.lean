-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P40.binaryProfileBounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T02:21:06.002338+00:00
-- url     : https://prove2.me/submissions/9d3bf017-0d69-46c7-90e4-6952d8b6d482

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.L2Operator

open Filter MeasureTheory Asymptotics

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

namespace X7C20

open Polynomial in
lemma X7_cfc_diag {X : Type*} [Fintype X] [DecidableEq X] (d : X → ℝ) (f : ℝ → ℝ) :
    cfc f (Matrix.diagonal (fun i => (d i : ℂ))) = Matrix.diagonal (fun i => (f (d i) : ℂ)) := by
  set A := Matrix.diagonal (fun i => (d i : ℂ)) with hA
  have hsa : IsSelfAdjoint A := by
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, hA, Matrix.diagonal_conjTranspose]
    congr 1; funext i; simp
  set S : Finset ℝ := Finset.univ.image d
  let p : ℝ[X] := Lagrange.interpolate S id f
  have hp : ∀ i, p.eval (d i) = f (d i) := by
    intro i
    have := Lagrange.eval_interpolate_at_node (s := S) (v := id) (r := f) (i := d i)
      (Set.injOn_id _) (Finset.mem_image_of_mem d (Finset.mem_univ i))
    exact this
  have hspec : ∀ x ∈ spectrum ℝ A, ∃ i, d i = x := by
    intro x hx
    rw [← spectrum.preimage_algebraMap ℂ, Set.mem_preimage, hA, spectrum_diagonal,
      Set.mem_range] at hx
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, by rw [Complex.coe_algebraMap] at hi; exact_mod_cast hi⟩
  have h1 : cfc f A = cfc p.eval A := by
    apply cfc_congr
    intro x hx
    obtain ⟨i, rfl⟩ := hspec x hx
    exact (hp i).symm
  rw [h1, cfc_polynomial p A]
  rw [hA, show Matrix.diagonal (fun i => (d i : ℂ)) =
    Matrix.diagonalAlgHom ℝ (fun i => (d i : ℂ)) from rfl, Polynomial.aeval_algHom_apply]
  rw [show Matrix.diagonal (fun i => (f (d i) : ℂ)) =
    Matrix.diagonalAlgHom ℝ (fun i => (f (d i) : ℂ)) from rfl]
  congr 1
  funext i
  rw [Polynomial.aeval_pi_apply₂]
  rw [show ((d i : ℝ) : ℂ) = algebraMap ℝ ℂ (d i) from rfl, Polynomial.aeval_algebraMap_apply,
    Polynomial.aeval_def, Algebra.algebraMap_self, ← Polynomial.eval, hp]
  rfl

/-- the explicit binary relative entropy -/
def F (x r : ℝ) : ℝ :=
  (r + x) * Real.log (r + x) - (r + x) * Real.log r +
    ((1 - r - x) * Real.log (1 - r - x) - (1 - r - x) * Real.log (1 - r))

lemma relEnt_eq (x r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    relativeEntropy (Matrix.diagonal ![((r + x : ℝ) : ℂ), ((1 - r - x : ℝ) : ℂ)])
      (Matrix.diagonal ![(r : ℂ), ((1 - r : ℝ) : ℂ)]) = ((F x r : ℝ) : EReal) := by
  have e1 : (![((r + x : ℝ) : ℂ), ((1 - r - x : ℝ) : ℂ)] : Fin 2 → ℂ)
      = fun i => ((![r + x, 1 - r - x] i : ℝ) : ℂ) := by
    funext i; fin_cases i <;> simp
  have e2 : (![(r : ℂ), ((1 - r : ℝ) : ℂ)] : Fin 2 → ℂ)
      = fun i => ((![r, 1 - r] i : ℝ) : ℂ) := by
    funext i; fin_cases i <;> simp
  rw [e1, e2]
  unfold QAlgorithms.Papers.Independent.Dependency50.P21.relativeEntropy
  rw [if_pos]
  · rw [X7_cfc_diag, X7_cfc_diag, Matrix.diagonal_mul_diagonal, Matrix.trace_sub,
      Matrix.trace_diagonal, Matrix.trace_diagonal]
    congr 1
    simp only [Fin.sum_univ_two, Complex.sub_re, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im]
    simp [F]
    ring
  · intro v hv
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
    have hv0 : v = 0 := by
      funext i
      have := congrFun hv i
      rw [Matrix.mulVec_diagonal] at this
      fin_cases i
      · simpa [hr.ne'] using this
      · have : (1 - r : ℂ) ≠ 0 := by
          rw [← Complex.ofReal_one, ← Complex.ofReal_sub]; exact_mod_cast (by linarith : (1 - r) ≠ 0)
        simp_all
    rw [hv0, Matrix.mulVec_zero]


lemma pinsker (x r : ℝ) (hx : 0 ≤ x) (hr : 0 < r) (h1 : r + x < 1) : 2 * x ^ 2 ≤ F x r := by
  let h : ℝ → ℝ := fun q => (r + x) * Real.log (r + x) - (r + x) * Real.log q +
    ((1 - r - x) * Real.log (1 - r - x) - (1 - r - x) * Real.log (1 - q)) - 2 * (r + x - q) ^ 2
  have hderiv : ∀ q, 0 < q → q < 1 →
      HasDerivAt h (-((r + x) / q) + (1 - r - x) / (1 - q) + 4 * (r + x - q)) q := by
    intro q hq hq1
    have d1 := (Real.hasDerivAt_log hq.ne').const_mul (r + x)
    have d2 := (((hasDerivAt_id q).const_sub 1).log (by simp; linarith)).const_mul (1 - r - x)
    have d3 := (((hasDerivAt_id q).const_sub (r + x)).pow 2).const_mul 2
    have := (((hasDerivAt_const q ((r + x) * Real.log (r + x))).sub d1).add
      ((hasDerivAt_const q ((1 - r - x) * Real.log (1 - r - x))).sub d2)).sub d3
    refine this.congr_deriv ?_
    have : (1 - q) ≠ 0 := by linarith
    simp only [id]
    field_simp
    ring
  have hanti : AntitoneOn h (Set.Icc r (r + x)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc r (r + x))
    · intro q hq
      exact (hderiv q (by linarith [hq.1]) (by linarith [hq.2])).continuousAt.continuousWithinAt
    · rw [interior_Icc]; intro q hq
      exact (hderiv q (by linarith [hq.1]) (by linarith [hq.2])).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]; intro q hq
      have hq0 : 0 < q := by linarith [hq.1]
      have hq1 : 0 < 1 - q := by linarith [hq.2]
      rw [(hderiv q hq0 (by linarith)).deriv]
      have key : -((r + x) / q) + (1 - r - x) / (1 - q) + 4 * (r + x - q) =
          -((r + x - q) * (2 * q - 1) ^ 2) / (q * (1 - q)) := by
        field_simp; ring
      rw [key]
      apply div_nonpos_of_nonpos_of_nonneg
      · have : 0 ≤ r + x - q := by linarith [hq.2]
        nlinarith [sq_nonneg (2 * q - 1)]
      · positivity
  have hle := hanti ⟨le_refl r, by linarith⟩ ⟨by linarith, le_refl (r + x)⟩ (by linarith)
  have hp : h (r + x) = 0 := by
    simp only [h]
    rw [show (1 : ℝ) - (r + x) = 1 - r - x by ring]
    ring
  have hr' : h r = F x r - 2 * x ^ 2 := by
    simp only [h, F]; ring
  linarith

lemma F_zero (r : ℝ) : F 0 r = 0 := by simp [F]

lemma F_lower (x r : ℝ) (hx : 0 < x) (hx1 : x < 1) (hr : 0 < r) (hr1 : r < 1 - x) :
    -x * Real.log (1 - x) - 1 ≤ F x r := by
  have hA : -Real.log (1 - x) ≤ Real.log (r + x) - Real.log r := by
    have h1 : r ≤ (r + x) * (1 - x) := by nlinarith
    have h2 := Real.log_le_log hr h1
    rw [Real.log_mul (by linarith) (by linarith)] at h2
    linarith
  have hB : 0 ≤ -Real.log (1 - x) := by
    have := Real.log_nonpos (by linarith : (0:ℝ) ≤ 1 - x) (by linarith)
    linarith
  have hC : (1 - r - x) - 1 ≤ (1 - r - x) * Real.log (1 - r - x) := by
    have hu : 0 < 1 - r - x := by linarith
    have := Real.one_sub_inv_le_log_of_pos hu
    have h3 : (1 - r - x) * (1 - (1 - r - x)⁻¹) = (1 - r - x) - 1 := by
      field_simp
    nlinarith
  have hD : (1 - r - x) * Real.log (1 - r) ≤ 0 := by
    have := Real.log_nonpos (by linarith : (0:ℝ) ≤ 1 - r) (by linarith)
    have hu : 0 ≤ 1 - r - x := by linarith
    nlinarith
  have hE : x * (-Real.log (1 - x)) ≤ (r + x) * (Real.log (r + x) - Real.log r) := by
    nlinarith
  unfold F
  nlinarith

lemma F_mid (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    F x ((1 - x) / 2) ≤ x * (2 * x / (1 - x)) := by
  have e1 : (1 - x) / 2 + x = (1 + x) / 2 := by ring
  have e2 : 1 - (1 - x) / 2 - x = (1 - x) / 2 := by ring
  have e3 : 1 - (1 - x) / 2 = (1 + x) / 2 := by ring
  unfold F
  rw [e1, e2, e3]
  have hL : Real.log ((1 + x) / 2) - Real.log ((1 - x) / 2) ≤ 2 * x / (1 - x) := by
    rw [← Real.log_div (by linarith) (by linarith)]
    have := Real.log_le_sub_one_of_pos (by positivity : 0 < ((1 + x) / 2) / ((1 - x) / 2))
    have hne : (1 - x) ≠ 0 := by linarith
    have h4 : ((1 + x) / 2) / ((1 - x) / 2) - 1 = 2 * x / (1 - x) := by
      field_simp; ring
    linarith
  have : (1 + x) / 2 * Real.log ((1 + x) / 2) - (1 + x) / 2 * Real.log ((1 - x) / 2) +
      ((1 - x) / 2 * Real.log ((1 - x) / 2) - (1 - x) / 2 * Real.log ((1 + x) / 2)) =
      x * (Real.log ((1 + x) / 2) - Real.log ((1 - x) / 2)) := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_left hL hx.le

lemma F_tendsto (x : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) :
    Tendsto (F x) (𝓝 (1 - x)) (𝓝 (-Real.log (1 - x))) := by
  rcases hx.eq_or_lt with rfl | hx0
  · have : F 0 = fun _ => 0 := funext F_zero
    rw [this]
    simp only [sub_zero, Real.log_one, neg_zero]
    exact tendsto_const_nhds
  · have hc : ContinuousAt (F x) (1 - x) := by
      unfold F
      have m1 : Continuous fun r : ℝ => (r + x) * Real.log (r + x) :=
        Real.continuous_mul_log.comp (continuous_id.add continuous_const)
      have m2 : Continuous fun r : ℝ => (1 - r - x) * Real.log (1 - r - x) :=
        Real.continuous_mul_log.comp ((continuous_const.sub continuous_id).sub continuous_const)
      apply ContinuousAt.add
      · apply ContinuousAt.sub m1.continuousAt
        apply ContinuousAt.mul (continuous_id.add continuous_const).continuousAt
        exact Real.continuousAt_log (by linarith)
      · apply ContinuousAt.sub m2.continuousAt
        apply ContinuousAt.mul ((continuous_const.sub continuous_id).sub continuous_const).continuousAt
        apply ContinuousAt.comp (g := Real.log) (Real.continuousAt_log (by linarith))
        exact (continuous_const.sub continuous_id).continuousAt
    have hv : F x (1 - x) = -Real.log (1 - x) := by
      unfold F
      rw [show 1 - x + x = 1 by ring, show 1 - (1 - x) - x = 0 by ring,
        show 1 - (1 - x) = x by ring]
      simp
    rw [← hv]
    exact hc.tendsto

end X7C20

open QAlgorithms.Papers.Independent.Information100.P50 (IsUINorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

open QAlgorithms.Papers.Independent.Gap48.P40 X7C20 in
theorem solution :
    (∀ x : ℝ, 0 ≤ x → x < 1 →
      ((2 * x ^ 2 : ℝ) : EReal) ≤ binaryProfile x ∧
        binaryProfile x ≤ ((-Real.log (1 - x) : ℝ) : EReal) ∧
        Tendsto (fun r : ℝ => relativeEntropy (Matrix.diagonal ![((r + x : ℝ) : ℂ), ((1 - r - x : ℝ) : ℂ)])
      (Matrix.diagonal ![(r : ℂ), ((1 - r : ℝ) : ℂ)]))
          (nhdsWithin (1 - x) (Set.Ioo 0 (1 - x)))
          (nhds ((-Real.log (1 - x) : ℝ) : EReal))) ∧
    Tendsto binaryProfile (nhdsWithin 1 (Set.Iio 1)) (nhds ⊤) ∧
    binaryProfile 1 = ⊤ ∧
    (∀ C : ℝ, (∀ x : ℝ, 0 < x → x < 1 →
      ((C * x ^ 2 : ℝ) : EReal) ≤ binaryProfile x) → C ≤ 2) := by
  -- membership of explicit values in the defining set
  have hmem : ∀ x r : ℝ, 0 ≤ x → 0 < r → r < 1 - x →
      binaryProfile x ≤ ((F x r : ℝ) : EReal) := by
    intro x r hx hr hr1
    rw [← relEnt_eq x r hr (by linarith)]
    exact sInf_le ⟨r, hr, hr1, rfl⟩
  have hlow : ∀ x : ℝ, ∀ b : ℝ, 0 ≤ x → (∀ r : ℝ, 0 < r → r < 1 - x → b ≤ F x r) →
      ((b : ℝ) : EReal) ≤ binaryProfile x := by
    intro x b hx hb
    apply le_sInf
    rintro v ⟨r, hr, hr1, rfl⟩
    rw [relEnt_eq x r hr (by linarith)]
    exact_mod_cast hb r hr hr1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx hx1
    have hT : Tendsto (fun r : ℝ => relativeEntropy
        (Matrix.diagonal ![((r + x : ℝ) : ℂ), ((1 - r - x : ℝ) : ℂ)])
        (Matrix.diagonal ![(r : ℂ), ((1 - r : ℝ) : ℂ)]))
        (nhdsWithin (1 - x) (Set.Ioo 0 (1 - x)))
        (nhds ((-Real.log (1 - x) : ℝ) : EReal)) := by
      have h1 : Tendsto (fun r => ((F x r : ℝ) : EReal)) (nhdsWithin (1 - x) (Set.Ioo 0 (1 - x)))
          (nhds ((-Real.log (1 - x) : ℝ) : EReal)) :=
        (continuous_coe_real_ereal.tendsto _).comp
          ((F_tendsto x hx hx1).mono_left nhdsWithin_le_nhds)
      refine h1.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r hr
      rw [relEnt_eq x r hr.1 (by linarith [hr.2])]
    refine ⟨hlow x _ hx (fun r hr hr1 => pinsker x r hx hr (by linarith)), ?_, hT⟩
    have hne : (nhdsWithin (1 - x) (Set.Ioo 0 (1 - x))).NeBot := by
      rw [nhdsWithin_Ioo_eq_nhdsLT (by linarith)]
      infer_instance
    apply ge_of_tendsto hT
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact sInf_le ⟨r, hr.1, hr.2, rfl⟩
  · rw [EReal.tendsto_nhds_top_iff_real]
    intro M
    have h1 : Tendsto (fun x : ℝ => 1 - x) (nhdsWithin 1 (Set.Iio 1)) (nhdsWithin 0 (Set.Ioi 0)) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have h0 : Tendsto (fun x : ℝ => 1 - x) (nhds 1) (nhds 0) := by
          have := (continuous_sub_left (1:ℝ)).tendsto (1 : ℝ)
          simpa using this
        exact h0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx
        simp only [Set.mem_Ioi, sub_pos]; exact hx
    have h2 : Tendsto (fun x : ℝ => -Real.log (1 - x)) (nhdsWithin 1 (Set.Iio 1)) atTop :=
      tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp h1)
    have h3 : Tendsto (fun x : ℝ => x) (nhdsWithin 1 (Set.Iio 1)) (nhds 1) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have h4 : Tendsto (fun x : ℝ => x * -Real.log (1 - x) + (-1)) (nhdsWithin 1 (Set.Iio 1)) atTop :=
      tendsto_atTop_add_const_right _ _ (h3.pos_mul_atTop one_pos h2)
    filter_upwards [h4.eventually_gt_atTop M, Ioo_mem_nhdsLT (by norm_num : (0:ℝ) < 1)]
      with x hxM hx
    calc ((M : ℝ) : EReal) < ((x * -Real.log (1 - x) + (-1) : ℝ) : EReal) := by exact_mod_cast hxM
      _ ≤ binaryProfile x := by
        apply hlow x _ hx.1.le
        intro r hr hr1
        have := F_lower x r hx.1 hx.2 hr hr1
        linarith
  · unfold binaryProfile
    have hE : {v : EReal | ∃ r : ℝ, 0 < r ∧ r < 1 - 1 ∧ v = relativeEntropy
        (Matrix.diagonal ![((r + 1 : ℝ) : ℂ), ((1 - r - 1 : ℝ) : ℂ)])
        (Matrix.diagonal ![(r : ℂ), ((1 - r : ℝ) : ℂ)])} = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr ?_
      rintro v ⟨r, hr, hr1, -⟩
      linarith
    rw [hE, sInf_empty]
  · intro C hC
    by_contra hlt
    push_neg at hlt
    set x := (C - 2) / (2 * C) with hxdef
    have hCpos : 0 < C := by linarith
    have hx0 : 0 < x := by rw [hxdef]; apply div_pos <;> linarith
    have hx1 : x < 1 / 2 := by
      rw [hxdef, div_lt_iff₀ (by linarith)]; linarith
    have hA := hC x hx0 (by linarith)
    have hB := hmem x ((1 - x) / 2) hx0.le (by linarith) (by linarith)
    have hR : C * x ^ 2 ≤ x * (2 * x / (1 - x)) := by
      have := hA.trans hB
      have h' : C * x ^ 2 ≤ F x ((1 - x) / 2) := by exact_mod_cast this
      exact h'.trans (F_mid x hx0 (by linarith))
    have hpos : 0 < 1 - x := by linarith
    have h5 : C * x ^ 2 * (1 - x) ≤ 2 * x ^ 2 := by
      have := mul_le_mul_of_nonneg_right hR hpos.le
      have e : x * (2 * x / (1 - x)) * (1 - x) = 2 * x ^ 2 := by field_simp
      linarith
    have h6 : C * (1 - x) ≤ 2 := by
      have hx2 : 0 < x ^ 2 := by positivity
      nlinarith
    have h7 : C * (1 - x) = (C + 2) / 2 := by
      rw [hxdef]; field_simp; ring
    linarith
