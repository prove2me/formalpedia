-- Prove2me | solution 1 for WassInvCov.Shrinkage.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-21T23:26:28.314332+00:00
-- url     : https://prove2.me/submissions/108b736d-f48e-4cc1-82fc-5559fbed47a7

import Mathlib
import Definitions.Def_WassInvCov_Shrinkage_Setting

open MeasureTheory ProbabilityTheory Matrix
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace

namespace WassShrinkageProof

noncomputable def diagInBasis {p : ℕ} (v : Fin p → EuclideanSpace ℝ (Fin p))
    (d : Fin p → ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  ∑ i, d i • Matrix.vecMulVec (v i).ofLp (v i).ofLp

end WassShrinkageProof

open scoped BigOperators
open WassInvCov.Shrinkage

namespace WassShrinkageProof

noncomputable def scalarPart (t : ℝ) : ℝ := (Real.sqrt (t ^ 2 + 4 * t) - t) / 2

lemma scalarPart_properties {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ scalarPart t ∧ scalarPart t < 1 ∧
      (scalarPart t) ^ 2 = t * (1 - scalarPart t) := by
  have hrad : 0 ≤ t ^ 2 + 4 * t := by positivity
  have hs := Real.sq_sqrt hrad
  have hn := Real.sqrt_nonneg (t ^ 2 + 4 * t)
  dsimp [scalarPart]
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

lemma scalarPart_mono : MonotoneOn scalarPart (Set.Ici 0) := by
  intro t ht u hu htu
  obtain ⟨ht0, ht1, hte⟩ := scalarPart_properties ht
  obtain ⟨hu0, hu1, hue⟩ := scalarPart_properties hu
  by_contra h
  have hlt : scalarPart u < scalarPart t := lt_of_not_ge h
  have hmul : t * (1 - scalarPart t) ≤ u * (1 - scalarPart u) :=
    mul_le_mul htu (by linarith) (by linarith) hu
  nlinarith

lemma scalarPart_zero_iff {t : ℝ} (ht : 0 ≤ t) : scalarPart t = 0 ↔ t = 0 := by
  constructor
  · intro h
    have := (scalarPart_properties ht).2.2
    simpa [h] using this.symm
  · rintro rfl
    simp [scalarPart]

lemma phi_eq {p : ℕ} (ρ : ℝ) (lam : Fin p → ℝ) (γ : ℝ) :
    phi16b ρ lam γ = ρ ^ 2 * γ + (∑ i, scalarPart (lam i * γ)) - p := by
  have hf (i : Fin p) : scalarPart (lam i * γ) =
      (Real.sqrt (lam i ^ 2 * γ ^ 2 + 4 * lam i * γ) - lam i * γ) / 2 := by
    unfold scalarPart
    congr 3
    ring
  simp_rw [hf]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.sum_mul]
  unfold phi16b
  ring

lemma phi_strict {p : ℕ} {ρ : ℝ} (hρ : 0 < ρ) {lam : Fin p → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) : StrictMonoOn (phi16b ρ lam) (Set.Ici 0) := by
  intro a ha b hb hab
  rw [phi_eq, phi_eq]
  have hs : (∑ i, scalarPart (lam i * a)) ≤ ∑ i, scalarPart (lam i * b) := by
    apply Finset.sum_le_sum
    intro i _
    exact scalarPart_mono (mul_nonneg (hlam i) ha) (mul_nonneg (hlam i) hb)
      (mul_le_mul_of_nonneg_left hab.le (hlam i))
  have hm : ρ ^ 2 * a < ρ ^ 2 * b := mul_lt_mul_of_pos_left hab (sq_pos_of_pos hρ)
  linarith

lemma unique_positive_root {p : ℕ} (hp : 0 < p) {ρ : ℝ} (hρ : 0 < ρ)
    {lam : Fin p → ℝ} (hlam : ∀ i, 0 ≤ lam i) :
    ∃! γ : ℝ, 0 < γ ∧ phi16b ρ lam γ = 0 := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hr : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have hb : 0 ≤ (p : ℝ) / ρ ^ 2 := le_of_lt (div_pos hp' hr)
  have hc : Continuous (phi16b ρ lam) := by unfold phi16b; fun_prop
  have hzero : phi16b ρ lam 0 = -(p : ℝ) := by simp [phi16b]
  have hupper : 0 ≤ phi16b ρ lam ((p : ℝ) / ρ ^ 2) := by
    rw [phi_eq, mul_div_cancel₀ _ (ne_of_gt hr)]
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) =>
      (scalarPart_properties (mul_nonneg (hlam i) hb)).1)
    linarith
  obtain ⟨γ, hγ, heq⟩ := intermediate_value_Icc hb hc.continuousOn
    (show 0 ∈ Set.Icc (phi16b ρ lam 0) (phi16b ρ lam ((p : ℝ) / ρ ^ 2)) from
      ⟨by rw [hzero]; linarith, hupper⟩)
  have hgpos : 0 < γ := by
    by_contra h
    have : γ = 0 := le_antisymm (le_of_not_gt h) hγ.1
    subst γ
    rw [hzero] at heq
    linarith
  refine ⟨γ, ⟨hgpos, heq⟩, ?_⟩
  intro y hy
  exact (phi_strict hρ hlam).injOn hy.1.le hgpos.le (hy.2.trans heq.symm)

lemma x_eq {p : ℕ} (lam : Fin p → ℝ) (γ : ℝ) (i : Fin p) :
    x16a lam γ i = γ * (1 - scalarPart (lam i * γ)) := by
  simp only [x16a, scalarPart, mul_pow]
  congr 2
  ring

lemma x_pos {p : ℕ} {lam : Fin p → ℝ} {γ : ℝ}
    (hlam : ∀ i, 0 ≤ lam i) (hγ : 0 < γ) (i : Fin p) : 0 < x16a lam γ i := by
  rw [x_eq]
  exact mul_pos hγ (sub_pos.mpr (scalarPart_properties (mul_nonneg (hlam i) hγ.le)).2.1)

lemma x_le_gamma {p : ℕ} {lam : Fin p → ℝ} {γ : ℝ}
    (hlam : ∀ i, 0 ≤ lam i) (hγ : 0 < γ) (i : Fin p) : x16a lam γ i ≤ γ := by
  rw [x_eq]
  have := (scalarPart_properties (mul_nonneg (hlam i) hγ.le)).1
  nlinarith

lemma x_eq_gamma_iff {p : ℕ} {lam : Fin p → ℝ} {γ : ℝ}
    (hlam : ∀ i, 0 ≤ lam i) (hγ : 0 < γ) (i : Fin p) :
    x16a lam γ i = γ ↔ lam i = 0 := by
  rw [x_eq]
  have hz := scalarPart_zero_iff (mul_nonneg (hlam i) hγ.le)
  constructor
  · intro h
    have : scalarPart (lam i * γ) = 0 := by nlinarith
    have := hz.mp this
    exact (mul_eq_zero.mp this).resolve_right hγ.ne'
  · intro h
    simp [h, scalarPart]

lemma x_identity {p : ℕ} {lam : Fin p → ℝ} {γ : ℝ}
    (hlam : ∀ i, 0 ≤ lam i) (hγ : 0 < γ) (i : Fin p) :
    γ ^ 2 * x16a lam γ i * lam i = (γ - x16a lam γ i) ^ 2 := by
  have h := (scalarPart_properties (mul_nonneg (hlam i) hγ.le)).2.2
  rw [x_eq]
  nlinarith [congrArg (fun z : ℝ => γ ^ 2 * z) h]

lemma x_sum {p : ℕ} {lam : Fin p → ℝ} {γ ρ : ℝ}
    (hphi : phi16b ρ lam γ = 0) : (∑ i, x16a lam γ i) = ρ ^ 2 * γ ^ 2 := by
  rw [phi_eq] at hphi
  simp only [x_eq, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  nlinarith [congrArg (fun z : ℝ => γ * z) hphi]

lemma sqrt_identity {p : ℕ} {lam : Fin p → ℝ} {γ : ℝ}
    (hlam : ∀ i, 0 ≤ lam i) (hγ : 0 < γ) (i : Fin p) :
    Real.sqrt (lam i) = (γ - x16a lam γ i) / (γ * Real.sqrt (x16a lam γ i)) := by
  have hx := x_pos hlam hγ i
  have hle := x_le_gamma hlam hγ i
  have hi := x_identity hlam hγ i
  have hsx := Real.sq_sqrt hx.le
  have hsl := Real.sq_sqrt (hlam i)
  have hsxp := Real.sqrt_pos.mpr hx
  have hslp := Real.sqrt_nonneg (lam i)
  apply (eq_div_iff (mul_pos hγ hsxp).ne').mpr
  have hsq : (Real.sqrt (lam i) * (γ * Real.sqrt (x16a lam γ i))) ^ 2 =
      (γ - x16a lam γ i) ^ 2 := by
    calc
      _ = γ ^ 2 * (Real.sqrt (x16a lam γ i)) ^ 2 * (Real.sqrt (lam i)) ^ 2 := by ring
      _ = _ := by rw [hsx, hsl, hi]
  nlinarith [mul_nonneg hslp (mul_pos hγ hsxp).le]

end WassShrinkageProof

open Matrix
open scoped BigOperators RealInnerProductSpace
open WassMMSE.Sandwich

namespace WassShrinkageProof

noncomputable def eigenColumns {p : ℕ} (v : Fin p → EuclideanSpace ℝ (Fin p)) :
    Matrix (Fin p) (Fin p) ℝ := fun i j => v j i

lemma columns_orthogonal {p : ℕ} {v : Fin p → EuclideanSpace ℝ (Fin p)}
    (hv : Orthonormal ℝ v) : (eigenColumns v)ᵀ * eigenColumns v = 1 := by
  ext i j
  have h := (orthonormal_iff_ite.mp hv) i j
  simpa [Matrix.mul_apply, eigenColumns, PiLp.inner_apply, Matrix.one_apply, mul_comm] using h

lemma columns_orthogonal' {p : ℕ} {v : Fin p → EuclideanSpace ℝ (Fin p)}
    (hv : Orthonormal ℝ v) : eigenColumns v * (eigenColumns v)ᵀ = 1 :=
  mul_eq_one_comm.mp (columns_orthogonal hv)

lemma diag_factor {p : ℕ} (v : Fin p → EuclideanSpace ℝ (Fin p)) (d : Fin p → ℝ) :
    diagInBasis v d = eigenColumns v * Matrix.diagonal d * (eigenColumns v)ᵀ := by
  ext i j
  rw [Matrix.mul_apply]
  simp [diagInBasis, Matrix.mul_diagonal, eigenColumns, Matrix.sum_apply, Matrix.vecMulVec_apply, mul_assoc, mul_comm]

lemma diag_mul {p : ℕ} {v : Fin p → EuclideanSpace ℝ (Fin p)}
    (hv : Orthonormal ℝ v) (a b : Fin p → ℝ) :
    diagInBasis v a * diagInBasis v b = diagInBasis v (fun i => a i * b i) := by
  simp only [diag_factor]
  calc
    _ = eigenColumns v * Matrix.diagonal a *
        ((eigenColumns v)ᵀ * eigenColumns v) * Matrix.diagonal b * (eigenColumns v)ᵀ := by
          simp only [Matrix.mul_assoc]
    _ = _ := by rw [columns_orthogonal hv]; simp [Matrix.mul_assoc]

lemma diag_one {p : ℕ} {v : Fin p → EuclideanSpace ℝ (Fin p)}
    (hv : Orthonormal ℝ v) : diagInBasis v (fun _ => 1) = 1 := by
  simpa [diag_factor] using columns_orthogonal' hv

lemma diag_transpose {p : ℕ} (v : Fin p → EuclideanSpace ℝ (Fin p)) (d : Fin p → ℝ) :
    (diagInBasis v d)ᵀ = diagInBasis v d := by
  ext i j
  simp [diagInBasis, Matrix.sum_apply, Matrix.vecMulVec_apply, mul_comm]

lemma diag_add {p : ℕ} (v : Fin p → EuclideanSpace ℝ (Fin p)) (a b : Fin p → ℝ) :
    diagInBasis v (a + b) = diagInBasis v a + diagInBasis v b := by
  simp [diagInBasis, add_smul, Finset.sum_add_distrib]

lemma diag_sub {p : ℕ} (v : Fin p → EuclideanSpace ℝ (Fin p)) (a b : Fin p → ℝ) :
    diagInBasis v (a - b) = diagInBasis v a - diagInBasis v b := by
  simp [diagInBasis, sub_smul, Finset.sum_sub_distrib]

lemma diag_smul {p : ℕ} (v : Fin p → EuclideanSpace ℝ (Fin p)) (c : ℝ) (a : Fin p → ℝ) :
    diagInBasis v (c • a) = c • diagInBasis v a := by
  simp [diagInBasis, Finset.smul_sum, smul_smul]

lemma diag_psd {p : ℕ} (v : Fin p → EuclideanSpace ℝ (Fin p)) {d : Fin p → ℝ}
    (hd : ∀ i, 0 ≤ d i) : (diagInBasis v d).PosSemidef := by
  rw [diag_factor]
  simpa using (Matrix.PosSemidef.diagonal hd).mul_mul_conjTranspose_same (eigenColumns v)

lemma diag_pd {p : ℕ} {v : Fin p → EuclideanSpace ℝ (Fin p)}
    (hv : Orthonormal ℝ v) {d : Fin p → ℝ} (hd : ∀ i, 0 < d i) :
    (diagInBasis v d).PosDef := by
  rw [diag_factor]
  apply (show (Matrix.diagonal d).PosDef from Matrix.PosDef.diagonal hd).mul_mul_conjTranspose_same
  intro x y hxy
  have h := congrArg (fun z => z ᵥ* (eigenColumns v)ᵀ) hxy
  simpa only [Matrix.vecMul_vecMul, columns_orthogonal' hv, Matrix.vecMul_one] using h

noncomputable def givenBasis {p : ℕ} {v : Fin p → EuclideanSpace ℝ (Fin p)}
    (hv : Orthonormal ℝ v) : OrthonormalBasis (Fin p) ℝ (EuclideanSpace ℝ (Fin p)) :=
  (basisOfLinearIndependentOfCardEqFinrank' v hv.linearIndependent (by simp)).toOrthonormalBasis
    (by simpa using hv)

lemma givenBasis_apply {p : ℕ} {v : Fin p → EuclideanSpace ℝ (Fin p)}
    (hv : Orthonormal ℝ v) (i : Fin p) : givenBasis hv i = v i := by
  simp [givenBasis, Module.Basis.coe_toOrthonormalBasis]

lemma coordinate_sq_sum {p : ℕ} {v : Fin p → EuclideanSpace ℝ (Fin p)}
    (hv : Orthonormal ℝ v) (z : EuclideanSpace ℝ (Fin p)) :
    (∑ i, ⟪v i, z⟫ ^ 2) = ‖z‖ ^ 2 := by
  simpa only [givenBasis_apply] using (givenBasis hv).sum_sq_inner_right z

lemma frob_outer {p : ℕ} (z : EuclideanSpace ℝ (Fin p)) (X : Matrix (Fin p) (Fin p) ℝ) :
    frob (vecMulVec z.ofLp z.ofLp) X = z.ofLp ⬝ᵥ (X *ᵥ z.ofLp) := by
  simp only [frob, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma diag_qform {p : ℕ} (v : Fin p → EuclideanSpace ℝ (Fin p)) (d : Fin p → ℝ)
    (z : EuclideanSpace ℝ (Fin p)) :
    frob (vecMulVec z.ofLp z.ofLp) (diagInBasis v d) = ∑ i, d i * ⟪v i, z⟫ ^ 2 := by
  rw [frob_outer]
  simp only [diagInBasis, Matrix.sum_mulVec, dotProduct_sum, Matrix.smul_mulVec,
    dotProduct_smul, Matrix.vecMulVec_mulVec, dotProduct_smul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  rw [dotProduct_comm (v i).ofLp z.ofLp]
  simp only [op_smul_eq_mul]
  ring

lemma diag_trace {p : ℕ} {v : Fin p → EuclideanSpace ℝ (Fin p)}
    (hv : Orthonormal ℝ v) (d : Fin p → ℝ) : (diagInBasis v d).trace = ∑ i, d i := by
  rw [diag_factor, Matrix.trace_mul_cycle]
  simp [columns_orthogonal hv]

lemma diag_frob {p : ℕ} {v : Fin p → EuclideanSpace ℝ (Fin p)}
    (hv : Orthonormal ℝ v) (a b : Fin p → ℝ) :
    frob (diagInBasis v a) (diagInBasis v b) = ∑ i, a i * b i := by
  rw [frob, diag_transpose, diag_mul hv, diag_trace hv]

lemma lambda_nonneg {p : ℕ} {Sh : Matrix (Fin p) (Fin p) ℝ}
    (hSh : Sh.PosSemidef) {lam : Fin p → ℝ} {v : Fin p → EuclideanSpace ℝ (Fin p)}
    (hv : Orthonormal ℝ v) (hdecomp : Sh = diagInBasis v lam) : ∀ i, 0 ≤ lam i := by
  intro i
  have h := hSh.dotProduct_mulVec_nonneg (v i).ofLp
  simp only [star_trivial] at h
  rw [hdecomp, ← frob_outer, diag_qform] at h
  simpa [orthonormal_iff_ite.mp hv] using h

end WassShrinkageProof

open Matrix
open scoped BigOperators
open WassMMSE.Sandwich

namespace WassShrinkageProof

lemma logdet_lt_trace_sub {p : ℕ} {C : Matrix (Fin p) (Fin p) ℝ}
    (hC : C.PosDef) (hne : C ≠ 1) : Real.log C.det < C.trace - p := by
  have hex : ∃ i, hC.1.eigenvalues i ≠ 1 := by
    by_contra! h
    apply hne
    rw [hC.1.spectral_theorem]
    have he : (RCLike.ofReal ∘ hC.1.eigenvalues) = (fun _ : Fin p => (1 : ℝ)) := by
      funext i
      simp [h i]
    rw [he]
    simp
  have hs : (∑ i, Real.log (hC.1.eigenvalues i)) < ∑ i, (hC.1.eigenvalues i - 1) := by
    apply Finset.sum_lt_sum
    · intro i _
      exact Real.log_le_sub_one_of_pos (hC.eigenvalues_pos i)
    · obtain ⟨i, hi⟩ := hex
      exact ⟨i, Finset.mem_univ _, Real.log_lt_sub_one_of_pos (hC.eigenvalues_pos i) hi⟩
  rw [hC.1.det_eq_prod_eigenvalues, Real.log_prod (by intro i _; exact ne_of_gt (hC.eigenvalues_pos i))]
  simpa [hC.1.trace_eq_sum_eigenvalues, Finset.sum_sub_distrib] using hs

lemma strict_logdet_bound {p : ℕ} {v : Fin p → EuclideanSpace ℝ (Fin p)}
    (hv : Orthonormal ℝ v) {d : Fin p → ℝ} (hd : ∀ i, 0 < d i)
    {X : Matrix (Fin p) (Fin p) ℝ} (hX : X.PosDef) (hne : X ≠ diagInBasis v d) :
    -Real.log (diagInBasis v d).det + (p : ℝ) <
      -Real.log X.det + frob (diagInBasis v (fun i => (d i)⁻¹)) X := by
  let P := diagInBasis v (fun i => Real.sqrt (d i))
  let R := diagInBasis v (fun i => (Real.sqrt (d i))⁻¹)
  have hs (i) : 0 < Real.sqrt (d i) := Real.sqrt_pos.2 (hd i)
  have hPR : P * R = 1 := by
    dsimp [P, R]
    rw [diag_mul hv]
    simpa [ne_of_gt (hs _)] using diag_one hv
  have hRP : R * P = 1 := mul_eq_one_comm.mp hPR
  have hPP : P * P = diagInBasis v d := by
    dsimp [P]
    rw [diag_mul hv]
    congr 1
    funext i
    nlinarith [Real.sq_sqrt (le_of_lt (hd i))]
  have hRR : R * R = diagInBasis v (fun i => (d i)⁻¹) := by
    dsimp [R]
    rw [diag_mul hv]
    congr 1
    funext i
    rw [← _root_.mul_inv_rev]
    congr 1
    nlinarith [Real.sq_sqrt (le_of_lt (hd i))]
  have hRt : Rᵀ = R := diag_transpose _ _
  have hRinj : Function.Injective R.mulVec := by
    intro x y hxy
    have h := congrArg (fun z => P *ᵥ z) hxy
    simpa only [Matrix.mulVec_mulVec, hPR, Matrix.one_mulVec] using h
  let C := R * X * R
  have hC : C.PosDef := by
    simpa [C, hRt] using hX.conjTranspose_mul_mul_same hRinj
  have hPCP : P * C * P = X := by
    dsimp [C]
    calc
      _ = (P * R) * X * (R * P) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hPR, hRP, Matrix.one_mul, Matrix.mul_one]
  have hneC : C ≠ 1 := by
    intro h
    apply hne
    rw [h, Matrix.mul_one, hPP] at hPCP
    exact hPCP.symm
  have htr : C.trace = frob (diagInBasis v (fun i => (d i)⁻¹)) X := by
    dsimp [C]
    rw [Matrix.trace_mul_cycle]
    rw [hRR, frob, diag_transpose]
  have hD := diag_pd hv hd
  have hdet : C.det * (diagInBasis v d).det = X.det := by
    have h := congrArg Matrix.det hPCP
    have hpp := congrArg Matrix.det hPP
    simp only [Matrix.det_mul] at h hpp
    rw [← hpp]
    calc
      _ = P.det * C.det * P.det := by ring
      _ = _ := h
  have hlog : Real.log X.det = Real.log C.det + Real.log (diagInBasis v d).det := by
    rw [← hdet, Real.log_mul (ne_of_gt hC.det_pos) (ne_of_gt hD.det_pos)]
  have h := logdet_lt_trace_sub hC hneC
  rw [htr] at h
  linarith

end WassShrinkageProof

open MeasureTheory ProbabilityTheory Matrix WassMMSE.Sandwich
open scoped BigOperators RealInnerProductSpace

namespace WassShrinkageProof

variable {p : ℕ}

lemma frob_entries (A B : Matrix (Fin p) (Fin p) ℝ) :
    frob A B = ∑ i, ∑ j, A i j * B i j := by
  simp only [frob, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

lemma frob_vec (X : Matrix (Fin p) (Fin p) ℝ)
    (z : EuclideanSpace ℝ (Fin p)) :
    frob (vecMulVec z.ofLp z.ofLp) X = ∑ i, ∑ j, z i * z j * X i j := by
  simp only [frob_entries, Matrix.vecMulVec_apply]

lemma gaussian_inner_memLp (S : Matrix (Fin p) (Fin p) ℝ)
    (u : EuclideanSpace ℝ (Fin p)) :
    MemLp (fun z => ⟪u, z⟫) 2 (multivariateGaussian 0 S) := by
  exact IsGaussian.memLp_two_id.continuousLinearMap_comp (innerSL ℝ u)

lemma gaussian_inner_integrable (S : Matrix (Fin p) (Fin p) ℝ)
    (u w : EuclideanSpace ℝ (Fin p)) :
    Integrable (fun z => ⟪u, z⟫ * ⟪w, z⟫) (multivariateGaussian 0 S) :=
  (gaussian_inner_memLp S u).integrable_mul (gaussian_inner_memLp S w)

lemma gaussian_inner_product (S : Matrix (Fin p) (Fin p) ℝ) (hS : S.PosSemidef)
    (u w : EuclideanSpace ℝ (Fin p)) :
    (∫ z, ⟪u, z⟫ * ⟪w, z⟫ ∂multivariateGaussian 0 S) = u.ofLp ⬝ᵥ S *ᵥ w.ofLp := by
  have h := covarianceBilin_multivariateGaussian (μ := 0) hS u w
  rw [covarianceBilin_apply IsGaussian.memLp_two_id] at h
  simpa using h

lemma gaussian_coord_integrable (S : Matrix (Fin p) (Fin p) ℝ) (i j : Fin p) :
    Integrable (fun z : EuclideanSpace ℝ (Fin p) => z i * z j)
      (multivariateGaussian 0 S) := by
  simpa [PiLp.inner_apply] using gaussian_inner_integrable S (EuclideanSpace.basisFun (Fin p) ℝ i)
    (EuclideanSpace.basisFun (Fin p) ℝ j)

lemma gaussian_coord_product (S : Matrix (Fin p) (Fin p) ℝ) (hS : S.PosSemidef)
    (i j : Fin p) :
    (∫ z : EuclideanSpace ℝ (Fin p), z i * z j ∂multivariateGaussian 0 S) = S i j := by
  simpa [PiLp.inner_apply] using gaussian_inner_product S hS (EuclideanSpace.basisFun (Fin p) ℝ i)
    (EuclideanSpace.basisFun (Fin p) ℝ j)

lemma gaussian_integrable_qform (S X : Matrix (Fin p) (Fin p) ℝ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin p) => frob (vecMulVec z.ofLp z.ofLp) X)
      (multivariateGaussian 0 S) := by
  simp only [frob_vec]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (gaussian_coord_integrable S i j).mul_const (X i j)

lemma gaussian_integral_qform (S X : Matrix (Fin p) (Fin p) ℝ) (hS : S.PosSemidef) :
    (∫ z : EuclideanSpace ℝ (Fin p), frob (vecMulVec z.ofLp z.ofLp) X
      ∂multivariateGaussian 0 S) = frob S X := by
  simp_rw [frob_vec]
  rw [frob_entries]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [integral_mul_const, gaussian_coord_product S hS i j]
    · exact fun j _ => (gaussian_coord_integrable S i j).mul_const (X i j)
  · exact fun i _ => integrable_finsetSum _ fun j _ =>
      (gaussian_coord_integrable S i j).mul_const (X i j)

lemma gaussian_inner_sq_integrable (S : Matrix (Fin p) (Fin p) ℝ)
    (u : EuclideanSpace ℝ (Fin p)) :
    Integrable (fun z => ⟪u, z⟫ ^ 2) (multivariateGaussian 0 S) := by
  simpa only [pow_two] using gaussian_inner_integrable S u u

lemma gaussian_inner_sq (S : Matrix (Fin p) (Fin p) ℝ) (hS : S.PosSemidef)
    (u : EuclideanSpace ℝ (Fin p)) :
    (∫ z, ⟪u, z⟫ ^ 2 ∂multivariateGaussian 0 S) = u.ofLp ⬝ᵥ S *ᵥ u.ofLp := by
  simpa only [pow_two] using gaussian_inner_product S hS u u

lemma gaussian_zero_coordinate (S : Matrix (Fin p) (Fin p) ℝ) (hS : S.PosSemidef)
    (u : EuclideanSpace ℝ (Fin p)) (hu : u.ofLp ⬝ᵥ S *ᵥ u.ofLp = 0) :
    ∀ᵐ z ∂multivariateGaussian 0 S, ⟪u, z⟫ = 0 := by
  have he : (∫ z, ⟪u, z⟫ ^ 2 ∂multivariateGaussian 0 S) = 0 :=
    (gaussian_inner_sq S hS u).trans hu
  have hz := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall fun z => sq_nonneg ⟪u, z⟫)
    (gaussian_inner_sq_integrable S u)).mp he
  filter_upwards [hz] with z hz
  simpa only [Pi.zero_apply, sq_eq_zero_iff] using hz

lemma frob_vec_inner (X : Matrix (Fin p) (Fin p) ℝ)
    (z : EuclideanSpace ℝ (Fin p)) :
    frob (vecMulVec z.ofLp z.ofLp) X = ⟪z, (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin p)) X z⟫ := by
  rw [frob_vec, inner_toEuclideanCLM]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma qform_transpose_mul (M : Matrix (Fin p) (Fin p) ℝ)
    (z : EuclideanSpace ℝ (Fin p)) :
    frob (vecMulVec z.ofLp z.ofLp) (Mᵀ * M) = ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin p)) M z‖ ^ 2 := by
  have ht : (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin p)) Mᵀ = ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin p)) M).adjoint := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      ContinuousLinearMap.star_eq_adjoint] using (map_star (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin p)) M)
  rw [frob_vec_inner, map_mul]
  change ⟪z, (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin p)) Mᵀ ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin p)) M z)⟫ = _
  rw [ht, ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]

lemma std_integrable_normsq (M : Matrix (Fin p) (Fin p) ℝ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin p) => ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin p)) M z‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin p))) := by
  simpa only [qform_transpose_mul, multivariateGaussian_zero_one] using
    gaussian_integrable_qform (1 : Matrix (Fin p) (Fin p) ℝ) (Mᵀ * M)

lemma std_integral_normsq (M : Matrix (Fin p) (Fin p) ℝ) :
    (∫ z : EuclideanSpace ℝ (Fin p), ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin p)) M z‖ ^ 2
      ∂stdGaussian (EuclideanSpace ℝ (Fin p))) = frob M M := by
  have h := gaussian_integral_qform (1 : Matrix (Fin p) (Fin p) ℝ)
    (Mᵀ * M) Matrix.PosSemidef.one
  simp only [qform_transpose_mul, multivariateGaussian_zero_one] at h
  simpa only [frob, Matrix.transpose_one, Matrix.one_mul] using h

end WassShrinkageProof

open MeasureTheory ProbabilityTheory Matrix WassMMSE.Sandwich
open scoped BigOperators RealInnerProductSpace ENNReal MatrixOrder

namespace WassShrinkageProof

variable {p : ℕ}

noncomputable def couplingCost
    (π : Measure (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin p))) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ 2) ∂π

noncomputable def transportInf (Q Q' : Measure (EuclideanSpace ℝ (Fin p))) : ℝ≥0∞ :=
  ⨅ (π : Measure (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin p)))
    (_ : π.map Prod.fst = Q ∧ π.map Prod.snd = Q'), couplingCost π

lemma wasserstein_eq_half (Q Q' : Measure (EuclideanSpace ℝ (Fin p))) :
    WassersteinDRO.Gelbrich.wassersteinDistance 2 Q Q' = transportInf Q Q' ^ (1 / 2 : ℝ) := by
  simp only [WassersteinDRO.Gelbrich.wassersteinDistance, transportInf, couplingCost,
    Real.rpow_two]

lemma transportInf_le_of_wasserstein_le (Q Q' : Measure (EuclideanSpace ℝ (Fin p)))
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : WassersteinDRO.Gelbrich.wassersteinDistance 2 Q Q' ≤ ENNReal.ofReal ρ) :
    transportInf Q Q' ≤ ENNReal.ofReal (ρ ^ 2) := by
  rw [wasserstein_eq_half] at h
  have hh := ENNReal.rpow_le_rpow h (show (0 : ℝ) ≤ 2 by norm_num)
  rw [← ENNReal.rpow_mul] at hh
  norm_num at hh
  simpa only [ENNReal.ofReal_pow hρ] using hh

lemma wasserstein_le_of_cost (Q Q' : Measure (EuclideanSpace ℝ (Fin p)))
    (π : Measure (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin p)))
    (hπ : π.map Prod.fst = Q ∧ π.map Prod.snd = Q') {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hc : couplingCost π ≤ ENNReal.ofReal (ρ ^ 2)) :
    WassersteinDRO.Gelbrich.wassersteinDistance 2 Q Q' ≤ ENNReal.ofReal ρ := by
  have hcost : transportInf Q Q' ≤ ENNReal.ofReal (ρ ^ 2) :=
    (iInf_le_of_le π (iInf_le_of_le hπ le_rfl)).trans hc
  rw [wasserstein_eq_half]
  have hh := ENNReal.rpow_le_rpow hcost (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  rw [ENNReal.ofReal_pow hρ, ← ENNReal.rpow_two, ← ENNReal.rpow_mul] at hh
  norm_num at hh ⊢
  exact hh

noncomputable def gaussianJoint (R T : Matrix (Fin p) (Fin p) ℝ) :
    Measure (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin p)) :=
  (stdGaussian (EuclideanSpace ℝ (Fin p))).map
    (fun g => ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin p)) R g, (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin p)) T g))

lemma gaussianJoint_fst (R T : Matrix (Fin p) (Fin p) ℝ) (hR : R.PosSemidef) :
    (gaussianJoint R T).map Prod.fst = multivariateGaussian 0 (R * R) := by
  rw [gaussianJoint, Measure.map_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def, multivariateGaussian, CFC.sqrt_mul_self R hR.nonneg, zero_add]

lemma gaussianJoint_snd (R T : Matrix (Fin p) (Fin p) ℝ) (hT : T.PosSemidef) :
    (gaussianJoint R T).map Prod.snd = multivariateGaussian 0 (T * T) := by
  rw [gaussianJoint, Measure.map_map (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def, multivariateGaussian, CFC.sqrt_mul_self T hT.nonneg, zero_add]

lemma gaussianJoint_cost (R T : Matrix (Fin p) (Fin p) ℝ) :
    couplingCost (gaussianJoint R T) = ENNReal.ofReal (frob (R - T) (R - T)) := by
  rw [couplingCost, gaussianJoint, lintegral_map (by fun_prop) (by fun_prop)]
  have he (g : EuclideanSpace ℝ (Fin p)) :
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin p)) R g - (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin p)) T g = (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin p)) (R - T) g := by
    simp only [map_sub, _root_.sub_apply]
  simp only [he]
  rw [← ofReal_integral_eq_lintegral_ofReal (std_integrable_normsq (R - T))
    (Filter.Eventually.of_forall fun z => sq_nonneg ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin p)) (R - T) z‖),
    std_integral_normsq]

lemma gaussian_wasserstein_le (R T : Matrix (Fin p) (Fin p) ℝ)
    (hR : R.PosSemidef) (hT : T.PosSemidef) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hc : frob (R - T) (R - T) ≤ ρ ^ 2) :
    WassersteinDRO.Gelbrich.wassersteinDistance 2
      (multivariateGaussian 0 (R * R)) (multivariateGaussian 0 (T * T)) ≤ ENNReal.ofReal ρ := by
  apply wasserstein_le_of_cost _ _ (gaussianJoint R T)
    ⟨gaussianJoint_fst R T hR, gaussianJoint_snd R T hT⟩ hρ
  rw [gaussianJoint_cost]
  exact ENNReal.ofReal_le_ofReal hc

end WassShrinkageProof

open MeasureTheory ProbabilityTheory Matrix WassMMSE.Sandwich WassInvCov.Shrinkage
open scoped BigOperators RealInnerProductSpace ENNReal MatrixOrder

namespace WassShrinkageProof

variable {p : ℕ}

noncomputable def penalty (lam : Fin p → ℝ) (γ : ℝ) (i : Fin p) : ℝ :=
  if lam i = 0 then 0 else γ * x16a lam γ i / (γ - x16a lam γ i)

lemma penalty_nonneg {lam : Fin p → ℝ} {γ : ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (hγ : 0 < γ) (i : Fin p) : 0 ≤ penalty lam γ i := by
  unfold penalty
  split_ifs
  · rfl
  · exact div_nonneg (mul_nonneg hγ.le (x_pos hlam hγ i).le)
      (sub_nonneg.mpr (x_le_gamma hlam hγ i))

lemma penalty_mul {lam : Fin p → ℝ} {γ : ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (hγ : 0 < γ) (i : Fin p) :
    penalty lam γ i * lam i = (γ - x16a lam γ i) / γ := by
  by_cases hz : lam i = 0
  · simp [penalty, hz, (x_eq_gamma_iff hlam hγ i).mpr hz]
  · have hx : x16a lam γ i < γ := lt_of_le_of_ne (x_le_gamma hlam hγ i)
      (fun h => hz ((x_eq_gamma_iff hlam hγ i).mp h))
    rw [penalty, if_neg hz]
    have hi := x_identity hlam hγ i
    field_simp [hγ.ne', (sub_pos.mpr hx).ne']
    nlinarith [hi]

lemma completed_square {a γ : ℝ} (ha : a < γ) (z y : ℝ) :
    a * z ^ 2 ≤ γ * (z - y) ^ 2 + (γ * a / (γ - a)) * y ^ 2 := by
  have hd : 0 < γ - a := sub_pos.mpr ha
  have he : γ * (z - y) ^ 2 + (γ * a / (γ - a)) * y ^ 2 - a * z ^ 2 =
      ((γ - a) * z - γ * y) ^ 2 / (γ - a) := by
    field_simp [hd.ne']
    ring
  have hn := div_nonneg (sq_nonneg ((γ - a) * z - γ * y)) hd.le
  linarith

lemma coordinate_upper {lam : Fin p → ℝ} {γ : ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (hγ : 0 < γ) (i : Fin p) (z y : ℝ) (hy : lam i = 0 → y = 0) :
    x16a lam γ i * z ^ 2 ≤ γ * (z - y) ^ 2 + penalty lam γ i * y ^ 2 := by
  by_cases hz : lam i = 0
  · simp [hy hz, (x_eq_gamma_iff hlam hγ i).mpr hz]
  · rw [penalty, if_neg hz]
    exact completed_square (lt_of_le_of_ne (x_le_gamma hlam hγ i)
      (fun h => hz ((x_eq_gamma_iff hlam hγ i).mp h))) z y

lemma gaussian_diagonal_variance {Sh : Matrix (Fin p) (Fin p) ℝ} (hSh : Sh.PosSemidef)
    {lam : Fin p → ℝ} {v : Fin p → EuclideanSpace ℝ (Fin p)} (hv : Orthonormal ℝ v)
    (hdecomp : Sh = diagInBasis v lam) (i : Fin p) :
    (∫ y, ⟪v i, y⟫ ^ 2 ∂multivariateGaussian 0 Sh) = lam i := by
  rw [gaussian_inner_sq Sh hSh, hdecomp, ← frob_outer, diag_qform]
  simp [orthonormal_iff_ite.mp hv]

lemma gaussian_diagonal_zero {Sh : Matrix (Fin p) (Fin p) ℝ} (hSh : Sh.PosSemidef)
    {lam : Fin p → ℝ} {v : Fin p → EuclideanSpace ℝ (Fin p)} (hv : Orthonormal ℝ v)
    (hdecomp : Sh = diagInBasis v lam) :
    ∀ᵐ y ∂multivariateGaussian 0 Sh, ∀ i, lam i = 0 → ⟪v i, y⟫ = 0 := by
  rw [Filter.eventually_all]
  intro i
  by_cases hi : lam i = 0
  · have hz : (v i).ofLp ⬝ᵥ (Sh *ᵥ (v i).ofLp) = 0 := by
      rw [hdecomp, ← frob_outer, diag_qform]
      simpa [orthonormal_iff_ite.mp hv] using hi
    filter_upwards [gaussian_zero_coordinate Sh hSh (v i) hz] with y hy
    exact fun _ => hy
  · exact Filter.Eventually.of_forall fun _ h => (hi h).elim

lemma coupling_upper {Sh S : Matrix (Fin p) (Fin p) ℝ} (hSh : Sh.PosSemidef)
    (hS : S.PosSemidef) {lam : Fin p → ℝ} {v : Fin p → EuclideanSpace ℝ (Fin p)}
    (hv : Orthonormal ℝ v) (hdecomp : Sh = diagInBasis v lam) {γ : ℝ} (hγ : 0 < γ)
    (π : Measure (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin p)))
    (hπ : π.map Prod.fst = multivariateGaussian 0 S ∧
      π.map Prod.snd = multivariateGaussian 0 Sh) :
    ENNReal.ofReal (frob S (diagInBasis v (x16a lam γ))) ≤
      ENNReal.ofReal γ * couplingCost π + ENNReal.ofReal (∑ i, penalty lam γ i * lam i) := by
  have hlam := lambda_nonneg hSh hv hdecomp
  let X := diagInBasis v (x16a lam γ)
  let r := fun y : EuclideanSpace ℝ (Fin p) => ∑ i, penalty lam γ i * ⟪v i, y⟫ ^ 2
  have hrnon (y) : 0 ≤ r y :=
    Finset.sum_nonneg fun i _ => mul_nonneg (penalty_nonneg hlam hγ i) (sq_nonneg _)
  have hrint : Integrable r (multivariateGaussian 0 Sh) := by
    apply integrable_finsetSum
    intro i _
    exact (gaussian_inner_sq_integrable Sh (v i)).const_mul _
  have hrval : (∫ y, r y ∂multivariateGaussian 0 Sh) = ∑ i, penalty lam γ i * lam i := by
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [integral_const_mul, gaussian_diagonal_variance hSh hv hdecomp]
    · intro i _
      exact (gaussian_inner_sq_integrable Sh (v i)).const_mul _
  have hz := gaussian_diagonal_zero hSh hv hdecomp
  rw [← hπ.2] at hz
  have hzπ := ae_of_ae_map measurable_snd.aemeasurable hz
  have hpoint : ∀ᵐ z ∂π, frob (vecMulVec z.1.ofLp z.1.ofLp) X ≤
      γ * ‖z.1 - z.2‖ ^ 2 + r z.2 := by
    filter_upwards [hzπ] with z hz
    dsimp [X, r]
    rw [diag_qform, ← coordinate_sq_sum hv, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    simpa only [inner_sub_right] using coordinate_upper hlam hγ i
      ⟪v i, z.1⟫ ⟪v i, z.2⟫ (hz i)
  have hleft : (∫⁻ z, ENNReal.ofReal (frob (vecMulVec z.1.ofLp z.1.ofLp) X) ∂π) =
      ENNReal.ofReal (frob S X) := by
    rw [← lintegral_map (μ := π)
      (f := fun z : EuclideanSpace ℝ (Fin p) => ENNReal.ofReal (frob (vecMulVec z.ofLp z.ofLp) X))
      (by simp only [frob_vec]; fun_prop) measurable_fst, hπ.1,
      ← ofReal_integral_eq_lintegral_ofReal (gaussian_integrable_qform S X)]
    · rw [gaussian_integral_qform S X hS]
    · exact Filter.Eventually.of_forall fun z => by
        change 0 ≤ frob (vecMulVec z.ofLp z.ofLp) X
        rw [frob_outer]
        simpa only [star_trivial] using
          (diag_psd v fun i => (x_pos hlam hγ i).le).dotProduct_mulVec_nonneg z.ofLp
  have hright : (∫⁻ z, ENNReal.ofReal (r z.2) ∂π) =
      ENNReal.ofReal (∑ i, penalty lam γ i * lam i) := by
    rw [← lintegral_map (μ := π)
      (f := fun z : EuclideanSpace ℝ (Fin p) => ENNReal.ofReal (r z))
      (by dsimp [r]; fun_prop) measurable_snd, hπ.2,
      ← ofReal_integral_eq_lintegral_ofReal hrint (Filter.Eventually.of_forall hrnon), hrval]
  have hh := lintegral_mono_ae (hpoint.mono fun z hz => ENNReal.ofReal_le_ofReal hz)
  have he (z : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin p)) :
      ENNReal.ofReal (γ * ‖z.1 - z.2‖ ^ 2 + r z.2) =
        ENNReal.ofReal γ * ENNReal.ofReal (‖z.1 - z.2‖ ^ 2) + ENNReal.ofReal (r z.2) := by
    rw [ENNReal.ofReal_add (mul_nonneg hγ.le (sq_nonneg _)) (hrnon _),
      ENNReal.ofReal_mul hγ.le]
  simp_rw [he] at hh
  rw [hleft, lintegral_add_left (by fun_prop), lintegral_const_mul _ (by fun_prop), hright] at hh
  exact hh

lemma gaussian_risk_upper {ρ : ℝ} {Sh S : Matrix (Fin p) (Fin p) ℝ}
    (hSh : Sh.PosSemidef) (hS : S.PosSemidef) {lam : Fin p → ℝ}
    {v : Fin p → EuclideanSpace ℝ (Fin p)} (hv : Orthonormal ℝ v)
    (hdecomp : Sh = diagInBasis v lam) {γ : ℝ} (hγ : 0 < γ)
    (hphi : phi16b ρ lam γ = 0) (hρ : 0 ≤ ρ)
    (hW : WassersteinDRO.Gelbrich.wassersteinDistance 2
      (multivariateGaussian 0 S) (multivariateGaussian 0 Sh) ≤ ENNReal.ofReal ρ) :
    frob S (diagInBasis v (x16a lam γ)) ≤ p := by
  have hlam := lambda_nonneg hSh hv hdecomp
  let K := ∑ i, penalty lam γ i * lam i
  have hK : 0 ≤ K := Finset.sum_nonneg fun i _ =>
    mul_nonneg (penalty_nonneg hlam hγ i) (hlam i)
  have hKeq : γ * ρ ^ 2 + K = p := by
    dsimp [K]
    simp_rw [penalty_mul hlam hγ]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, x_sum hphi]
    field_simp [hγ.ne']
    ring
  have hh : ENNReal.ofReal (frob S (diagInBasis v (x16a lam γ))) ≤
      ENNReal.ofReal γ * transportInf (multivariateGaussian 0 S) (multivariateGaussian 0 Sh) +
        ENNReal.ofReal K := by
    simp_rw [transportInf, ENNReal.mul_iInf_of_ne (ENNReal.ofReal_ne_zero_iff.mpr hγ)
      ENNReal.ofReal_ne_top, ENNReal.iInf_add]
    exact le_iInf fun π => le_iInf fun hπ => coupling_upper hSh hS hv hdecomp hγ π hπ
  have hc := transportInf_le_of_wasserstein_le _ _ hρ hW
  have hb : ENNReal.ofReal γ * transportInf (multivariateGaussian 0 S) (multivariateGaussian 0 Sh) +
      ENNReal.ofReal K ≤ ENNReal.ofReal (p : ℝ) := by
    calc
      _ ≤ ENNReal.ofReal γ * ENNReal.ofReal (ρ ^ 2) + ENNReal.ofReal K := by gcongr
      _ = _ := by rw [← ENNReal.ofReal_mul hγ.le,
        ← ENNReal.ofReal_add (mul_nonneg hγ.le (sq_nonneg _)) hK, hKeq]
  exact (ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg p)).mp (hh.trans hb)

lemma worst_estimator_upper {ρ : ℝ} (hρ : 0 ≤ ρ) {Sh : Matrix (Fin p) (Fin p) ℝ}
    (hSh : Sh.PosSemidef) {lam : Fin p → ℝ} {v : Fin p → EuclideanSpace ℝ (Fin p)}
    (hv : Orthonormal ℝ v) (hdecomp : Sh = diagInBasis v lam) {γ : ℝ} (hγ : 0 < γ)
    (hphi : phi16b ρ lam γ = 0) :
    worstCaseExp ρ Sh (shrinkageEstimator lam v γ) ≤ (p : EReal) := by
  apply iSup_le
  intro Q
  apply iSup_le
  rintro ⟨S, hS, rfl, hW⟩
  rw [gaussian_integral_qform S _ hS]
  exact EReal.coe_le_coe_iff.mpr (gaussian_risk_upper hSh hS hv hdecomp hγ hphi hρ hW)

end WassShrinkageProof

open MeasureTheory ProbabilityTheory Matrix WassMMSE.Sandwich WassInvCov.Shrinkage
open scoped BigOperators RealInnerProductSpace ENNReal MatrixOrder

namespace WassShrinkageProof

lemma saddle_bounds {p : ℕ} (_hp : 0 < p) {ρ : ℝ} (hρ : 0 < ρ)
    {Sh : Matrix (Fin p) (Fin p) ℝ} (hSh : Sh.PosSemidef)
    {lam : Fin p → ℝ} {v : Fin p → EuclideanSpace ℝ (Fin p)} (hv : Orthonormal ℝ v)
    (hdecomp : Sh = ∑ i, lam i • Matrix.vecMulVec (v i).ofLp (v i).ofLp)
    {γ : ℝ} (hγ : 0 < γ) (hphi : phi16b ρ lam γ = 0) :
    worstCaseExp ρ Sh (shrinkageEstimator lam v γ) = (p : EReal) ∧
    ∀ X, (frob (diagInBasis v (fun i => (x16a lam γ i)⁻¹)) X : EReal) ≤
      worstCaseExp ρ Sh X := by
  have hlam := lambda_nonneg hSh hv hdecomp
  have hx := x_pos hlam hγ
  let S := diagInBasis v (fun i => (x16a lam γ i)⁻¹)
  let R := diagInBasis v (fun i => (Real.sqrt (x16a lam γ i))⁻¹)
  let T := diagInBasis v (fun i => Real.sqrt (lam i))
  have hS : S.PosSemidef := diag_psd v fun i => inv_nonneg.mpr (hx i).le
  have hR : R.PosSemidef := diag_psd v fun i => inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hT : T.PosSemidef := diag_psd v fun i => Real.sqrt_nonneg _
  have hRR : R * R = S := by
    dsimp [R, S]
    rw [diag_mul hv]
    congr 1
    funext i
    rw [← _root_.mul_inv_rev]
    congr 1
    nlinarith [Real.sq_sqrt (hx i).le]
  have hTT : T * T = Sh := by
    change _ = diagInBasis v lam at hdecomp
    rw [hdecomp]
    dsimp [T]
    rw [diag_mul hv]
    congr 1
    funext i
    nlinarith [Real.sq_sqrt (hlam i)]
  have hdiff (i : Fin p) :
      (Real.sqrt (x16a lam γ i))⁻¹ - Real.sqrt (lam i) = Real.sqrt (x16a lam γ i) / γ := by
    rw [sqrt_identity hlam hγ i]
    have hs := Real.sqrt_pos.mpr (hx i)
    field_simp [hγ.ne', hs.ne']
    nlinarith [Real.sq_sqrt (hx i).le]
  have hcost : frob (R - T) (R - T) = ρ ^ 2 := by
    dsimp [R, T]
    rw [← diag_sub, diag_frob hv]
    simp only [Pi.sub_apply]
    simp_rw [hdiff, ← pow_two, div_pow, Real.sq_sqrt (hx _).le]
    rw [← Finset.sum_div, x_sum hphi]
    exact mul_div_cancel_right₀ _ (pow_ne_zero 2 hγ.ne')
  have hfeas : multivariateGaussian 0 S ∈ ambiguitySet ρ Sh := by
    refine ⟨S, hS, rfl, ?_⟩
    rw [← hRR, ← hTT]
    exact gaussian_wasserstein_le R T hR hT hρ.le hcost.le
  have hlower (X : Matrix (Fin p) (Fin p) ℝ) :
      (frob S X : EReal) ≤ worstCaseExp ρ Sh X := by
    have h : ((∫ z, frob (vecMulVec z.ofLp z.ofLp) X ∂multivariateGaussian 0 S : ℝ) : EReal) ≤
        worstCaseExp ρ Sh X :=
      le_iSup_of_le (multivariateGaussian 0 S) (le_iSup_of_le hfeas le_rfl)
    rw [gaussian_integral_qform S X hS] at h
    exact h
  refine ⟨le_antisymm (worst_estimator_upper hρ.le hSh hv hdecomp hγ hphi) ?_, hlower⟩
  have h := hlower (shrinkageEstimator lam v γ)
  have he : frob S (shrinkageEstimator lam v γ) = (p : ℝ) := by
    change frob (diagInBasis v _) (diagInBasis v _) = _
    rw [diag_frob hv]
    simp [ne_of_gt (hx _)]
  simpa only [he, EReal.coe_natCast] using h

end WassShrinkageProof

open MeasureTheory ProbabilityTheory Matrix

namespace WassInvCov.Shrinkage

/-- Theorem 3.1, p. 12 (arXiv:1805.07194v1). Without sparsity information (`𝒳 = 𝕊^p_{++}`), for
`ρ > 0` and `Σ̂ ⪰ 0` with an orthonormal eigendecomposition `Σ̂ = Σᵢ λᵢ vᵢ vᵢᵀ`, equation (16b) has a
unique positive solution `γ⋆`, and `X⋆ = Σᵢ x⋆ᵢ vᵢ vᵢᵀ` with `x⋆ᵢ` from (16a) is the unique minimizer
of (5). The hypothesis `0 < p` is added (for `p = 0`, (16b) has no positive solution). -/
theorem theorem_3_1 {p : ℕ} (hp : 0 < p) (ρ : ℝ) (hρ : 0 < ρ) (Sh : Matrix (Fin p) (Fin p) ℝ)
    (hSh : Sh.PosSemidef) (lam : Fin p → ℝ) (v : Fin p → EuclideanSpace ℝ (Fin p))
    (hv : Orthonormal ℝ v)
    (hdecomp : Sh = ∑ i, lam i • Matrix.vecMulVec (v i).ofLp (v i).ofLp) :
    (∃! γ : ℝ, 0 < γ ∧ phi16b ρ lam γ = 0) ∧
    ∀ γs : ℝ, 0 < γs → phi16b ρ lam γs = 0 →
      (shrinkageEstimator lam v γs).PosDef ∧
      IsMinOn (robustObjective ρ Sh) {X | X.PosDef} (shrinkageEstimator lam v γs) ∧
      ∀ X : Matrix (Fin p) (Fin p) ℝ, X.PosDef →
        IsMinOn (robustObjective ρ Sh) {X | X.PosDef} X → X = shrinkageEstimator lam v γs := by
  have hlam : ∀ i, 0 ≤ lam i := WassShrinkageProof.lambda_nonneg hSh hv hdecomp
  refine ⟨WassShrinkageProof.unique_positive_root hp hρ hlam, ?_⟩
  intro γs hγ hphi
  have hx := WassShrinkageProof.x_pos hlam hγ
  have hD : (shrinkageEstimator lam v γs).PosDef := WassShrinkageProof.diag_pd hv hx
  obtain ⟨hcost, hlower⟩ := WassShrinkageProof.saddle_bounds hp hρ hSh hv hdecomp hγ hphi
  have hstrict (X : Matrix (Fin p) (Fin p) ℝ) (hX : X.PosDef)
      (hne : X ≠ shrinkageEstimator lam v γs) :
      robustObjective ρ Sh (shrinkageEstimator lam v γs) < robustObjective ρ Sh X := by
    have h := WassShrinkageProof.strict_logdet_bound hv hx hX hne
    have he : ((-Real.log (shrinkageEstimator lam v γs).det + (p : ℝ) : ℝ) : EReal) <
        ((-Real.log X.det + WassMMSE.Sandwich.frob
          (WassShrinkageProof.diagInBasis v (fun i => (x16a lam γs i)⁻¹)) X : ℝ) : EReal) :=
      EReal.coe_lt_coe_iff.mpr h
    have hb := add_le_add (le_refl ((-Real.log X.det : ℝ) : EReal)) (hlower X)
    simp only [EReal.coe_add, EReal.coe_natCast] at he
    simpa only [robustObjective, hcost] using lt_of_lt_of_le he hb
  refine ⟨hD, ?_, ?_⟩
  · intro X hX
    change robustObjective ρ Sh (shrinkageEstimator lam v γs) ≤ robustObjective ρ Sh X
    by_cases he : X = shrinkageEstimator lam v γs
    · subst X
      exact le_rfl
    · exact (hstrict X hX he).le
  · intro X hX hmin
    by_contra he
    exact (not_le_of_gt (hstrict X hX he)) (hmin hD)

end WassInvCov.Shrinkage

open WassInvCov.Shrinkage

theorem solution {p : ℕ} (hp : 0 < p) (ρ : ℝ) (hρ : 0 < ρ) (Sh : Matrix (Fin p) (Fin p) ℝ)
    (hSh : Sh.PosSemidef) (lam : Fin p → ℝ) (v : Fin p → EuclideanSpace ℝ (Fin p))
    (hv : Orthonormal ℝ v)
    (hdecomp : Sh = ∑ i, lam i • Matrix.vecMulVec (v i).ofLp (v i).ofLp) :
    (∃! γ : ℝ, 0 < γ ∧ phi16b ρ lam γ = 0) ∧
    ∀ γs : ℝ, 0 < γs → phi16b ρ lam γs = 0 →
      (shrinkageEstimator lam v γs).PosDef ∧
      IsMinOn (robustObjective ρ Sh) {X | X.PosDef} (shrinkageEstimator lam v γs) ∧
      ∀ X : Matrix (Fin p) (Fin p) ℝ, X.PosDef →
        IsMinOn (robustObjective ρ Sh) {X | X.PosDef} X → X = shrinkageEstimator lam v γs := by
  exact WassInvCov.Shrinkage.theorem_3_1 hp ρ hρ Sh hSh lam v hv hdecomp
