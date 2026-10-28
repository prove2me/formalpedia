-- Prove2me | solution 1 for SynDigits.Ridge.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-26T06:32:19.95971+00:00
-- url     : https://prove2.me/submissions/4d9a8122-8f31-45c4-8db7-a1ab26f26179

import Definitions.Def_GaussianMatrix_basic
import Definitions.Def_SynDigits_Ridge_Model
import Init
import Mathlib



section
namespace Queelius.Ridge
open Matrix GaussianMatrix SynDigits.Ridge
open scoped Matrix.Norms.L2Operator

theorem vnorm_eq_norm {k : ℕ} (x : Fin k → ℝ) :
    vnorm x=‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin k))‖ := by
  simp [vnorm,EuclideanSpace.norm_eq,dotProduct,Real.norm_eq_abs,sq_abs,pow_two]

theorem vnorm_nonneg {k : ℕ} (x : Fin k → ℝ) : 0 ≤ vnorm x := by
  rw [vnorm_eq_norm]
  exact norm_nonneg _

theorem vnorm_add_le {k : ℕ} (x y : Fin k → ℝ) : vnorm (x+y) ≤ vnorm x+vnorm y := by
  simp only [vnorm_eq_norm]
  exact norm_add_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin k)) (WithLp.toLp 2 y)

theorem vnorm_sub_le {k : ℕ} (x y : Fin k → ℝ) : vnorm (x-y) ≤ vnorm x+vnorm y := by
  simp only [vnorm_eq_norm]
  exact norm_sub_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin k)) (WithLp.toLp 2 y)

theorem vnorm_smul {k : ℕ} (a : ℝ) (x : Fin k → ℝ) : vnorm (a • x)=|a| * vnorm x := by
  simp only [vnorm_eq_norm]
  exact norm_smul a (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin k))

theorem vnorm_mulVec {n m : ℕ} (Y : Matrix (Fin n) (Fin m) ℝ) (x : Fin m → ℝ) :
    vnorm (Y *ᵥ x) ≤ specNorm Y*vnorm x := by
  simp only [vnorm_eq_norm,specNorm]
  exact Y.l2_opNorm_mulVec (WithLp.toLp 2 x)

end Queelius.Ridge

end

section
namespace Queelius.Ridge
open Matrix GaussianMatrix SynDigits.Ridge

theorem prediction_decomposition {n m : ℕ} (Y : Matrix (Fin n) (Fin m) ℝ)
    (y : Fin n → ℝ) (beta reference : Fin m → ℝ) :
    Y *ᵥ beta-y=Y *ᵥ (beta-reference)-(y-Y *ᵥ reference) := by
  rw [mulVec_sub]
  abel

theorem prediction_error_bound {n m : ℕ} (Y : Matrix (Fin n) (Fin m) ℝ)
    (y : Fin n → ℝ) (beta reference : Fin m → ℝ) :
    vnorm (Y *ᵥ beta-y) ≤ specNorm Y*vnorm (beta-reference)+vnorm (y-Y *ᵥ reference) := by
  rw [prediction_decomposition Y y beta reference]
  exact (vnorm_sub_le (Y *ᵥ (beta-reference)) (y-Y *ᵥ reference)).trans
    (_root_.add_le_add (vnorm_mulVec Y (beta-reference)) le_rfl)

end Queelius.Ridge
open Matrix GaussianMatrix SynDigits.Ridge

theorem residual_solution {n m : ℕ} (Y Yt : Matrix (Fin n) (Fin m) ℝ) (ytv Yv : Fin n → ℝ)
    (Sig : Matrix (Fin m) (Fin m) ℝ) (gam : Fin m → ℝ) (lam : ℝ) :
    ridgePredict Y Yt ytv lam - Yv
        = Y *ᵥ (ridgeFit Yt ytv lam - betaStar Sig gam lam) - resid Y Yv Sig gam lam ∧
      vnorm (ridgePredict Y Yt ytv lam - Yv)
        ≤ specNorm Y * vnorm (ridgeFit Yt ytv lam - betaStar Sig gam lam)
          + vnorm (resid Y Yv Sig gam lam) :=
  ⟨Queelius.Ridge.prediction_decomposition Y Yv (ridgeFit Yt ytv lam) (betaStar Sig gam lam),
    Queelius.Ridge.prediction_error_bound Y Yv (ridgeFit Yt ytv lam) (betaStar Sig gam lam)⟩

end

section
namespace Queelius.Ridge
open Matrix GaussianMatrix SynDigits.Ridge
open scoped Matrix.Norms.L2Operator
variable {m : ℕ}

theorem sMin_le_unit (S : Matrix (Fin m) (Fin m) ℝ) (x : Fin m → ℝ)
    (hx : x ⬝ᵥ x=1) : sMin S ≤ vnorm (S *ᵥ x) := by
  have hb : BddBelow (Set.range (fun z : {z : Fin m → ℝ // z ⬝ᵥ z=1} =>
      Real.sqrt ((S *ᵥ z.1) ⬝ᵥ (S *ᵥ z.1)))) :=
    ⟨0,by rintro y ⟨z,rfl⟩; exact Real.sqrt_nonneg _⟩
  exact ciInf_le hb ⟨x,hx⟩

theorem sMin_le_eigenvalue (S : Matrix (Fin m) (Fin m) ℝ) (hS : S.PosSemidef)
    (i : Fin m) : sMin S ≤ hS.isHermitian.eigenvalues i := by
  let x : Fin m → ℝ := ⇑(hS.isHermitian.eigenvectorBasis i)
  have hn : vnorm x=1 := by
    simpa [x,vnorm_eq_norm] using hS.isHermitian.eigenvectorBasis.orthonormal.1 i
  have hsq : vnorm x ^ 2=x ⬝ᵥ x := by
    apply Real.sq_sqrt
    exact Finset.sum_nonneg (fun j _ => mul_self_nonneg (x j))
  have hx : x ⬝ᵥ x=1 := by rw [hn] at hsq; norm_num at hsq; exact hsq.symm
  have he : S *ᵥ x=hS.isHermitian.eigenvalues i • x := hS.isHermitian.mulVec_eigenvectorBasis i
  have hb := sMin_le_unit S x hx
  rw [he,vnorm_smul,abs_of_nonneg (hS.eigenvalues_nonneg i),hn,mul_one] at hb
  exact hb

theorem shifted_diagonalization (S : Matrix (Fin m) (Fin m) ℝ) (hS : S.IsHermitian) (lam : ℝ) :
    S+lam • (1 : Matrix (Fin m) (Fin m) ℝ) =
      Unitary.conjStarAlgAut ℝ _ hS.eigenvectorUnitary
        (diagonal (fun i => hS.eigenvalues i+lam)) := by
  have hd : diagonal (fun i => hS.eigenvalues i+lam) =
      diagonal hS.eigenvalues+lam • (1 : Matrix (Fin m) (Fin m) ℝ) := by
    ext i j
    by_cases h : i=j <;> simp [diagonal,h]
  rw [hd,map_add,map_smul,map_one]
  congr 1
  simpa using hS.spectral_theorem

theorem conjugate_inverse (U : Matrix.unitaryGroup (Fin m) ℝ) (d : Fin m → ℝ)
    (hd : ∀ i,d i ≠ 0) :
    (Unitary.conjStarAlgAut ℝ _ U (diagonal d))⁻¹ =
      Unitary.conjStarAlgAut ℝ _ U (diagonal (fun i => (d i)⁻¹)) := by
  apply Matrix.inv_eq_right_inv
  rw [← map_mul]
  have he : diagonal d * diagonal (fun i => (d i)⁻¹) = (1 : Matrix (Fin m) (Fin m) ℝ) := by
    rw [diagonal_mul_diagonal]
    ext i j
    by_cases h : i=j <;> simp [diagonal,Matrix.one_apply,h,hd]
  rw [he,map_one]

theorem norm_conjugate (U : Matrix.unitaryGroup (Fin m) ℝ) (B : Matrix (Fin m) (Fin m) ℝ) :
    ‖Unitary.conjStarAlgAut ℝ _ U B‖=‖B‖ := by
  rw [Unitary.conjStarAlgAut_apply]
  simpa only [← Unitary.coe_star] using
    (CStarRing.norm_mul_coe_unitary ((U : Matrix (Fin m) (Fin m) ℝ)*B) (star U)).trans
      (CStarRing.norm_coe_unitary_mul U B)

theorem shifted_inverse_bound (S : Matrix (Fin m) (Fin m) ℝ) (hS : S.PosSemidef)
    (lam : ℝ) (hpos : 0 < sMin S+lam) :
    specNorm (S+lam • (1 : Matrix (Fin m) (Fin m) ℝ))⁻¹ ≤ 1/(sMin S+lam) := by
  have hbound : ∀ i,sMin S+lam ≤ hS.isHermitian.eigenvalues i+lam :=
    fun i => _root_.add_le_add (sMin_le_eigenvalue S hS i) (le_refl lam)
  have hp : ∀ i,0 < hS.isHermitian.eigenvalues i+lam := fun i => hpos.trans_le (hbound i)
  rw [shifted_diagonalization S hS.isHermitian lam,
    conjugate_inverse _ _ (fun i => ne_of_gt (hp i))]
  unfold specNorm
  rw [norm_conjugate,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro i
  rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (hp i))]
  simpa only [one_div] using one_div_le_one_div_of_le hpos (hbound i)

theorem shifted_mul_inv (S : Matrix (Fin m) (Fin m) ℝ) (hS : S.PosSemidef)
    (lam : ℝ) (hpos : 0 < sMin S+lam) :
    (S+lam • (1 : Matrix (Fin m) (Fin m) ℝ)) *
      (S+lam • (1 : Matrix (Fin m) (Fin m) ℝ))⁻¹=1 := by
  have hp : ∀ i,0 < hS.isHermitian.eigenvalues i+lam := fun i =>
    hpos.trans_le (_root_.add_le_add (sMin_le_eigenvalue S hS i) (le_refl lam))
  rw [shifted_diagonalization S hS.isHermitian lam,
    conjugate_inverse _ _ (fun i => ne_of_gt (hp i)),← map_mul,diagonal_mul_diagonal]
  have he : diagonal (fun i => (hS.isHermitian.eigenvalues i+lam) *
      (hS.isHermitian.eigenvalues i+lam)⁻¹) = (1 : Matrix (Fin m) (Fin m) ℝ) := by
    ext i j
    by_cases h : i=j <;> simp [diagonal,Matrix.one_apply,h,fun i => ne_of_gt (hp i)]
  rw [he,map_one]

end Queelius.Ridge

end

section
namespace Queelius.Ridge
open Matrix GaussianMatrix SynDigits.Ridge

theorem structural_residual {n m d : ℕ} (U : Matrix (Fin n) (Fin d) ℝ)
    (V : Matrix (Fin m) (Fin d) ℝ) (Eps Y : Matrix (Fin n) (Fin m) ℝ) (v e : Fin d → ℝ)
    (Ev Yv : Fin n → ℝ) (b beta : Fin m → ℝ)
    (hY : Y=U*Vᵀ+Eps) (hYv : Yv=U*ᵥv+Ev) (hv : v=Vᵀ*ᵥb+e) :
    Yv-Y*ᵥbeta=U*ᵥe+(Ev-Eps*ᵥb)+Y*ᵥ(b-beta) := by
  simp only [hY,hYv,hv,add_mulVec,mulVec_add,mulVec_sub,mulVec_mulVec]
  abel

theorem structural_residual_bound {n m d : ℕ} (U : Matrix (Fin n) (Fin d) ℝ)
    (V : Matrix (Fin m) (Fin d) ℝ) (Eps Y : Matrix (Fin n) (Fin m) ℝ) (v e : Fin d → ℝ)
    (Ev Yv : Fin n → ℝ) (b beta : Fin m → ℝ)
    (hY : Y=U*Vᵀ+Eps) (hYv : Yv=U*ᵥv+Ev) (hv : v=Vᵀ*ᵥb+e) :
    vnorm (Yv-Y*ᵥbeta) ≤ vnorm (U*ᵥe)+vnorm (Ev-Eps*ᵥb)+specNorm Y*vnorm (b-beta) := by
  rw [structural_residual U V Eps Y v e Ev Yv b beta hY hYv hv]
  exact (vnorm_add_le (U *ᵥ e+(Ev-Eps *ᵥ b)) (Y *ᵥ (b-beta))).trans
    (_root_.add_le_add (vnorm_add_le (U *ᵥ e) (Ev-Eps *ᵥ b)) (vnorm_mulVec Y (b-beta)))

theorem structural_complete {n m d : ℕ} (U : Matrix (Fin n) (Fin d) ℝ)
    (V : Matrix (Fin m) (Fin d) ℝ) (Eps Y : Matrix (Fin n) (Fin m) ℝ) (v e : Fin d → ℝ)
    (Ev Yv : Fin n → ℝ) (b : Fin m → ℝ) (Sig : Matrix (Fin m) (Fin m) ℝ) (gam : Fin m → ℝ)
    (lam : ℝ)
    (hY : Y = U * Vᵀ + Eps) (hYv : Yv = U *ᵥ v + Ev) (hv : v = Vᵀ *ᵥ b + e) :
    resid Y Yv Sig gam lam = U *ᵥ e + (Ev - Eps *ᵥ b) + Y *ᵥ (b - betaStar Sig gam lam) ∧
      vnorm (resid Y Yv Sig gam lam)
        ≤ vnorm (U *ᵥ e) + vnorm (Ev - Eps *ᵥ b)
          + specNorm Y * vnorm (b - betaStar Sig gam lam) :=
  ⟨structural_residual U V Eps Y v e Ev Yv b (betaStar Sig gam lam) hY hYv hv,
    structural_residual_bound U V Eps Y v e Ev Yv b (betaStar Sig gam lam) hY hYv hv⟩

end Queelius.Ridge

end

section
namespace Queelius.Ridge
open Matrix GaussianMatrix SynDigits.Ridge
open scoped Matrix.Norms.L2Operator
variable {n m : ℕ}

theorem sampleCov_psd (Yt : Matrix (Fin n) (Fin m) ℝ) : (sampleCov Yt).PosSemidef := by
  have h : (Ytᵀ*Yt).PosSemidef := by simpa using posSemidef_conjTranspose_mul_self Yt
  exact h.smul (by positivity : 0 ≤ 1/(n:ℝ))

theorem ridge_normal (S : Matrix (Fin m) (Fin m) ℝ) (g : Fin m → ℝ) (lam : ℝ)
    (hS : S.PosSemidef) (hpos : 0 < sMin S+lam) :
    (S+lam • (1 : Matrix (Fin m) (Fin m) ℝ)) *ᵥ ridgeCoef S g lam=g := by
  unfold ridgeCoef
  rw [mulVec_mulVec,shifted_mul_inv S hS lam hpos,one_mulVec]

theorem inverse_solve_bound (S : Matrix (Fin m) (Fin m) ℝ) (lam : ℝ)
    (hS : S.PosSemidef) (hpos : 0 < sMin S+lam) (x y : Fin m → ℝ)
    (he : (S+lam • (1 : Matrix (Fin m) (Fin m) ℝ)) *ᵥ x=y) :
    vnorm x ≤ 1/(sMin S+lam)*vnorm y := by
  have hleft := mul_eq_one_comm.mp (shifted_mul_inv S hS lam hpos)
  have hx : x=(S+lam • (1 : Matrix (Fin m) (Fin m) ℝ))⁻¹ *ᵥ y := by
    rw [← he,mulVec_mulVec,hleft,one_mulVec]
  rw [hx]
  exact (vnorm_mulVec _ y).trans
    (mul_le_mul_of_nonneg_right (shifted_inverse_bound S hS lam hpos) (vnorm_nonneg y))

theorem coefficient_decomposition (A B : Matrix (Fin m) (Fin m) ℝ)
    (x y g h : Fin m → ℝ) (lam : ℝ)
    (hx : (A+lam • (1 : Matrix (Fin m) (Fin m) ℝ)) *ᵥ x=g)
    (hy : (B+lam • (1 : Matrix (Fin m) (Fin m) ℝ)) *ᵥ y=h) :
    (A+lam • (1 : Matrix (Fin m) (Fin m) ℝ)) *ᵥ (x-y) = (B-A) *ᵥ y+(g-h) := by
  rw [mulVec_sub,hx,← hy]
  simp only [add_mulVec,sub_mulVec,smul_mulVec,one_mulVec]
  abel

theorem norm_reverse_sub (A B : Matrix (Fin m) (Fin m) ℝ) : specNorm (B-A)=specNorm (A-B) :=
  norm_sub_rev B A

theorem coefficient_complete (Yt : Matrix (Fin n) (Fin m) ℝ) (ytv : Fin n → ℝ)
    (Sig : Matrix (Fin m) (Fin m) ℝ) (gam : Fin m → ℝ) (lam : ℝ)
    (hSig : Sig.PosSemidef) (hposHat : 0 < sMin (sampleCov Yt)+lam)
    (hpos : 0 < sMin Sig+lam) :
    (sampleCov Yt+lam • (1 : Matrix (Fin m) (Fin m) ℝ)) *ᵥ ridgeFit Yt ytv lam = sampleCross Yt ytv ∧
    (Sig+lam • (1 : Matrix (Fin m) (Fin m) ℝ)) *ᵥ betaStar Sig gam lam = gam ∧
    (sampleCov Yt+lam • (1 : Matrix (Fin m) (Fin m) ℝ)) *ᵥ (ridgeFit Yt ytv lam-betaStar Sig gam lam) =
      (Sig-sampleCov Yt) *ᵥ betaStar Sig gam lam+(sampleCross Yt ytv-gam) ∧
    vnorm (ridgeFit Yt ytv lam-betaStar Sig gam lam) ≤
      1/(sMin (sampleCov Yt)+lam) * (specNorm (sampleCov Yt-Sig)*vnorm (betaStar Sig gam lam)+
        vnorm (sampleCross Yt ytv-gam)) := by
  have hh := ridge_normal (sampleCov Yt) (sampleCross Yt ytv) lam (sampleCov_psd Yt) hposHat
  have hs := ridge_normal Sig gam lam hSig hpos
  have he := coefficient_decomposition (sampleCov Yt) Sig (ridgeFit Yt ytv lam)
    (betaStar Sig gam lam) (sampleCross Yt ytv) gam lam hh hs
  refine ⟨hh,hs,he,?_⟩
  apply (inverse_solve_bound (sampleCov Yt) lam (sampleCov_psd Yt) hposHat _ _ he).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (vnorm_add_le _ _).trans
  have hb := vnorm_mulVec (Sig-sampleCov Yt) (betaStar Sig gam lam)
  rw [norm_reverse_sub] at hb
  exact _root_.add_le_add hb le_rfl

theorem population_complete (Sig : Matrix (Fin m) (Fin m) ℝ) (gam b : Fin m → ℝ) (lam : ℝ)
    (hSig : Sig.PosSemidef) (hlam : 0 ≤ lam) (hpos : 0 < sMin Sig+lam) :
    (Sig+lam • (1 : Matrix (Fin m) (Fin m) ℝ)) *ᵥ (betaStar Sig gam lam-b) =
      (gam-Sig *ᵥ b)-lam • b ∧
    vnorm (betaStar Sig gam lam-b) ≤
      1/(sMin Sig+lam)*(vnorm (gam-Sig *ᵥ b)+lam*vnorm b) := by
  have he : (Sig+lam • (1 : Matrix (Fin m) (Fin m) ℝ)) *ᵥ (betaStar Sig gam lam-b) =
      (gam-Sig *ᵥ b)-lam • b := by
    rw [mulVec_sub,betaStar,ridge_normal Sig gam lam hSig hpos,add_mulVec,smul_mulVec,one_mulVec]
    abel
  refine ⟨he,?_⟩
  apply (inverse_solve_bound Sig lam hSig hpos _ _ he).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [vnorm_smul,abs_of_nonneg hlam] using vnorm_sub_le (gam-Sig *ᵥ b) (lam • b)

end Queelius.Ridge
open Matrix GaussianMatrix SynDigits.Ridge
theorem coefficient_solution {n m : ℕ} (Yt : Matrix (Fin n) (Fin m) ℝ) (ytv : Fin n → ℝ)
    (Sig : Matrix (Fin m) (Fin m) ℝ) (gam : Fin m → ℝ) (lam : ℝ)
    (hSig : Sig.PosSemidef) (hposHat : 0 < sMin (sampleCov Yt)+lam)
    (hpos : 0 < sMin Sig+lam) :
    (sampleCov Yt+lam • (1 : Matrix (Fin m) (Fin m) ℝ)) *ᵥ ridgeFit Yt ytv lam = sampleCross Yt ytv ∧
    (Sig+lam • (1 : Matrix (Fin m) (Fin m) ℝ)) *ᵥ betaStar Sig gam lam = gam ∧
    (sampleCov Yt+lam • (1 : Matrix (Fin m) (Fin m) ℝ)) *ᵥ (ridgeFit Yt ytv lam-betaStar Sig gam lam) =
      (Sig-sampleCov Yt) *ᵥ betaStar Sig gam lam+(sampleCross Yt ytv-gam) ∧
    vnorm (ridgeFit Yt ytv lam-betaStar Sig gam lam) ≤
      1/(sMin (sampleCov Yt)+lam) * (specNorm (sampleCov Yt-Sig)*vnorm (betaStar Sig gam lam)+
        vnorm (sampleCross Yt ytv-gam)) :=
  Queelius.Ridge.coefficient_complete Yt ytv Sig gam lam hSig hposHat hpos

end

section
namespace Queelius.Ridge.Controls
open Matrix GaussianMatrix SynDigits.Ridge

theorem two_coordinate_norm : vnorm ![(1:ℝ),1]=Real.sqrt 2 := by
  norm_num [vnorm,dotProduct,Fin.sum_univ_two]

theorem zero_dimension_norm (x : Fin 0 → ℝ) : vnorm x=0 := by
  simp [vnorm,dotProduct]

theorem zero_twin_response {n m : ℕ} (Yt : Matrix (Fin n) (Fin m) ℝ) (lam : ℝ) :
    ridgeFit Yt 0 lam=0 := by
  simp [ridgeFit,ridgeCoef,sampleCross]

theorem singular_coef_zero {m : ℕ} (g : Fin m → ℝ) :
    ridgeCoef (0 : Matrix (Fin m) (Fin m) ℝ) g 0=0 := by
  simp [ridgeCoef]

theorem singular_normal_equation_fails :
    (0 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ ridgeCoef 0 (fun _ => (1:ℝ)) 0 ≠ (fun _ => (1:ℝ)) := by
  intro h
  have hh := congrFun h 0
  norm_num at hh

theorem equal_coefficients_exact_error {n m : ℕ} (Y : Matrix (Fin n) (Fin m) ℝ)
    (y : Fin n → ℝ) (beta : Fin m → ℝ) : vnorm (Y *ᵥ beta-y)=vnorm (y-Y *ᵥ beta) := by
  simp only [vnorm_eq_norm]
  exact norm_sub_rev (WithLp.toLp 2 (Y *ᵥ beta) : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 y)

end Queelius.Ridge.Controls

end

section
namespace Queelius.Ridge
open Matrix GaussianMatrix SynDigits.Ridge
open scoped Matrix.Norms.L2Operator

theorem sMin_scalar_identity {m : ℕ} (hm : 0 < m) (a : ℝ) :
    sMin (a • (1 : Matrix (Fin m) (Fin m) ℝ))=|a| := by
  have hx : (Pi.single (⟨0,hm⟩ : Fin m) (1:ℝ)) ⬝ᵥ Pi.single (⟨0,hm⟩ : Fin m) (1:ℝ)=1 := by simp
  letI : Nonempty {x : Fin m → ℝ // x ⬝ᵥ x=1} := ⟨⟨_,hx⟩⟩
  unfold sMin
  have he : ∀ x : {x : Fin m → ℝ // x ⬝ᵥ x=1},
      Real.sqrt (((a • (1 : Matrix (Fin m) (Fin m) ℝ)) *ᵥ x.1) ⬝ᵥ
        ((a • (1 : Matrix (Fin m) (Fin m) ℝ)) *ᵥ x.1))=|a| := by
    intro x
    change vnorm ((a • (1 : Matrix (Fin m) (Fin m) ℝ)) *ᵥ x.1)=|a|
    rw [smul_mulVec,one_mulVec,vnorm_smul]
    simp [vnorm,x.property]
  simp_rw [he]
  simp

namespace Controls

theorem no_observations_covariance {m : ℕ} (Yt : Matrix (Fin 0) (Fin m) ℝ) : sampleCov Yt=0 := by
  simp [sampleCov]

theorem indefinite_shift_singular :
    0 < sMin ((-1:ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))+1 ∧
    (-1:ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)+1 • (1 : Matrix (Fin 1) (Fin 1) ℝ)=0 := by
  rw [sMin_scalar_identity (by omega)]
  norm_num

theorem admissible_negative_regularization :
    0 < sMin ((2:ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))+(-1) ∧
    specNorm (((2:ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))+(-1:ℝ) • 1)⁻¹=1 := by
  rw [sMin_scalar_identity (by omega)]
  constructor
  · norm_num
  · have he : (2:ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)+(-1:ℝ) • 1=1 := by module
    rw [he]
    simp [specNorm]

theorem zero_features_coefficient_error {n : ℕ} (Yt : Matrix (Fin n) (Fin 0) ℝ)
    (ytv : Fin n → ℝ) (Sig : Matrix (Fin 0) (Fin 0) ℝ) (gam : Fin 0 → ℝ) (lam : ℝ) :
    vnorm (ridgeFit Yt ytv lam-betaStar Sig gam lam)=0 := by
  simp [vnorm,dotProduct]

end Controls
end Queelius.Ridge

end

section
namespace Queelius.Ridge
open Matrix GaussianMatrix SynDigits.Ridge
open scoped Matrix.Norms.L2Operator

theorem vnorm_sub_rev {m : ℕ} (x y : Fin m → ℝ) : vnorm (x-y)=vnorm (y-x) := by
  simp only [vnorm_eq_norm]
  exact norm_sub_rev (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin m)) (WithLp.toLp 2 y)

theorem root_complete {n m d : ℕ} (U : Matrix (Fin n) (Fin d) ℝ)
    (V : Matrix (Fin m) (Fin d) ℝ) (Eps Y : Matrix (Fin n) (Fin m) ℝ) (v e : Fin d → ℝ)
    (Ev Yv : Fin n → ℝ) (b : Fin m → ℝ) (Yt : Matrix (Fin n) (Fin m) ℝ) (ytv : Fin n → ℝ)
    (Sig : Matrix (Fin m) (Fin m) ℝ) (gam : Fin m → ℝ) (lam : ℝ)
    (hY : Y=U*Vᵀ+Eps) (hYv : Yv=U*ᵥ v+Ev) (hv : v=Vᵀ*ᵥ b+e)
    (hSig : Sig.PosSemidef) (hlam : 0 ≤ lam)
    (hposHat : 0 < sMin (sampleCov Yt)+lam) (hpos : 0 < sMin Sig+lam) :
    vnorm (ridgePredict Y Yt ytv lam-Yv) ≤ vnorm (resid Y Yv Sig gam lam)+
      specNorm Y/(sMin (sampleCov Yt)+lam) *
        (specNorm (sampleCov Yt-Sig)*vnorm (betaStar Sig gam lam)+vnorm (sampleCross Yt ytv-gam)) ∧
    vnorm (resid Y Yv Sig gam lam) ≤ vnorm (U*ᵥ e)+vnorm (Ev-Eps*ᵥ b)+
      specNorm Y/(sMin Sig+lam) * (lam*vnorm b+vnorm (gam-Sig*ᵥ b)) := by
  have hnorm : 0 ≤ specNorm Y := norm_nonneg Y
  have hc := (coefficient_complete Yt ytv Sig gam lam hSig hposHat hpos).2.2.2
  have hp := (population_complete Sig gam b lam hSig hlam hpos).2
  constructor
  · calc
      _ ≤ specNorm Y*vnorm (ridgeFit Yt ytv lam-betaStar Sig gam lam)+vnorm (resid Y Yv Sig gam lam) :=
        prediction_error_bound Y Yv (ridgeFit Yt ytv lam) (betaStar Sig gam lam)
      _ ≤ specNorm Y*(1/(sMin (sampleCov Yt)+lam) *
          (specNorm (sampleCov Yt-Sig)*vnorm (betaStar Sig gam lam)+vnorm (sampleCross Yt ytv-gam)))+
          vnorm (resid Y Yv Sig gam lam) :=
        _root_.add_le_add (mul_le_mul_of_nonneg_left hc hnorm) le_rfl
      _ = _ := by ring
  · have hs := structural_residual_bound U V Eps Y v e Ev Yv b (betaStar Sig gam lam) hY hYv hv
    rw [vnorm_sub_rev b] at hs
    calc
      _ ≤ vnorm (U*ᵥ e)+vnorm (Ev-Eps*ᵥ b)+specNorm Y*vnorm (betaStar Sig gam lam-b) := hs
      _ ≤ vnorm (U*ᵥ e)+vnorm (Ev-Eps*ᵥ b)+specNorm Y*
          (1/(sMin Sig+lam)*(vnorm (gam-Sig*ᵥ b)+lam*vnorm b)) :=
        _root_.add_le_add le_rfl (mul_le_mul_of_nonneg_left hp hnorm)
      _ = _ := by ring

end Queelius.Ridge

open Matrix GaussianMatrix SynDigits.Ridge
theorem solution {n m d : ℕ} (U : Matrix (Fin n) (Fin d) ℝ)
    (V : Matrix (Fin m) (Fin d) ℝ) (Eps Y : Matrix (Fin n) (Fin m) ℝ) (v e : Fin d → ℝ)
    (Ev Yv : Fin n → ℝ) (b : Fin m → ℝ) (Yt : Matrix (Fin n) (Fin m) ℝ) (ytv : Fin n → ℝ)
    (Sig : Matrix (Fin m) (Fin m) ℝ) (gam : Fin m → ℝ) (lam : ℝ)
    (hY : Y=U*Vᵀ+Eps) (hYv : Yv=U*ᵥ v+Ev) (hv : v=Vᵀ*ᵥ b+e)
    (hSig : Sig.PosSemidef) (hlam : 0 ≤ lam)
    (hposHat : 0 < sMin (sampleCov Yt)+lam) (hpos : 0 < sMin Sig+lam) :
    vnorm (ridgePredict Y Yt ytv lam-Yv) ≤ vnorm (resid Y Yv Sig gam lam)+
      specNorm Y/(sMin (sampleCov Yt)+lam) *
        (specNorm (sampleCov Yt-Sig)*vnorm (betaStar Sig gam lam)+vnorm (sampleCross Yt ytv-gam)) ∧
    vnorm (resid Y Yv Sig gam lam) ≤ vnorm (U*ᵥ e)+vnorm (Ev-Eps*ᵥ b)+
      specNorm Y/(sMin Sig+lam) * (lam*vnorm b+vnorm (gam-Sig*ᵥ b)) :=
  Queelius.Ridge.root_complete U V Eps Y v e Ev Yv b Yt ytv Sig gam lam hY hYv hv hSig hlam hposHat hpos

end
