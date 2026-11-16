-- Prove2me | solution 1 for WildeQIT.Recover.hirschman_two_one
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-16T01:02:49.136738+00:00
-- url     : https://prove2.me/submissions/4507f585-3af4-43c0-8083-ca326a93564b

import Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P21_hirschmanDensities
import Theorems.Thm_WildeQIT_Purification_exists_unitary_eq_mul_of_mul_conjTranspose_eq
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.Ring
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.DiffContOnCl
import Theorems.Thm_WildeQIT_Recover_theorem_12_2_2
import Mathlib.Data.EReal.Inv

noncomputable section
open Matrix Unitary
open scoped ComplexOrder ComplexConjugate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RecoveryMatrixSVD
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Square SVD tied to the exact Gram spectral calculus; no rank assumption. -/
theorem gram_svd (A : Matrix n n ℂ) :
    ∃ (U V : unitary (Matrix n n ℂ)) (s : n → ℝ),
      (∀ i, 0 ≤ s i) ∧
      A=(U : Matrix n n ℂ)*diagonal (fun i => (s i : ℂ))*(V : Matrix n n ℂ) ∧
      (∀ f : ℝ → ℝ, cfc f (Aᴴ*A) =
        (V : Matrix n n ℂ)ᴴ*diagonal (fun i => (f (s i^2) : ℂ))*(V : Matrix n n ℂ)) := by
  classical
  let hG := posSemidef_conjTranspose_mul_self A
  let Q := hG.isHermitian.eigenvectorUnitary
  let s : n → ℝ := fun i => Real.sqrt (hG.isHermitian.eigenvalues i)
  have hs (i : n) : 0 ≤ s i := Real.sqrt_nonneg _
  have hsq (i : n) : s i^2 = hG.isHermitian.eigenvalues i := Real.sq_sqrt (hG.eigenvalues_nonneg i)
  let D : Matrix n n ℂ := diagonal (fun i => (s i : ℂ))
  let B : Matrix n n ℂ := D*(Q : Matrix n n ℂ)ᴴ
  have hD : Dᴴ=D := by simp [D,diagonal_conjTranspose]
  have hB : Bᴴ*B=Aᴴ*A := by
    dsimp [B]
    rw [conjTranspose_mul,conjTranspose_conjTranspose,hD]
    rw [Matrix.mul_assoc,← Matrix.mul_assoc D D]
    have hd : D*D=diagonal (fun i => (hG.isHermitian.eigenvalues i : ℂ)) := by
      dsimp [D]
      rw [diagonal_mul_diagonal]
      congr 1
      funext i
      exact_mod_cast (show s i*s i=hG.isHermitian.eigenvalues i by simpa only [pow_two] using hsq i)
    rw [hd]
    rw [← Matrix.mul_assoc]
    exact hG.isHermitian.spectral_theorem.symm
  obtain ⟨W,hW,hh⟩ := WildeQIT.Purification.exists_unitary_eq_mul_of_mul_conjTranspose_eq Aᴴ Bᴴ
    (by simpa only [conjTranspose_conjTranspose] using hB.symm)
  let U : unitary (Matrix n n ℂ) := star ⟨W,hW⟩
  let V : unitary (Matrix n n ℂ) := star Q
  refine ⟨U,V,s,hs,?_,?_⟩
  · have hh' := congrArg conjTranspose hh
    simpa only [U,V,B,conjTranspose_conjTranspose,conjTranspose_mul,
      Unitary.coe_star,Matrix.star_eq_conjTranspose,Matrix.mul_assoc] using hh'
  · intro f
    rw [hG.isHermitian.cfc_eq,Matrix.IsHermitian.cfc,conjStarAlgAut_apply]
    dsimp [V,Q]
    simp only [Unitary.coe_star,Matrix.star_eq_conjTranspose,conjTranspose_conjTranspose]
    congr 2
    ext i j
    simp [diagonal_apply,hsq]

end RecoveryMatrixSVD

noncomputable section
open Matrix Unitary
open QAlgorithms.Papers.Independent.Information100.P50
open scoped ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RecoverySchatten
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma trace_gram_cfc (A : Matrix n n ℂ) (V : unitary (Matrix n n ℂ)) (s : n → ℝ)
    (hcalc : ∀ f : ℝ → ℝ, cfc f (Aᴴ*A) =
      (V : Matrix n n ℂ)ᴴ*diagonal (fun i => (f (s i^2) : ℂ))*(V : Matrix n n ℂ))
    (f : ℝ → ℝ) : (cfc f (Aᴴ*A)).trace.re=∑ i, f (s i^2) := by
  rw [hcalc,trace_mul_cycle]
  have hVV : (V : Matrix n n ℂ)*(V : Matrix n n ℂ)ᴴ=1 := Unitary.coe_mul_star_self V
  rw [hVV,Matrix.one_mul,trace_diagonal]
  simp

lemma schatten_finite (A : Matrix n n ℂ) (V : unitary (Matrix n n ℂ)) (s : n → ℝ)
    (hs : ∀ i, 0 ≤ s i)
    (hcalc : ∀ f : ℝ → ℝ, cfc f (Aᴴ*A) =
      (V : Matrix n n ℂ)ᴴ*diagonal (fun i => (f (s i^2) : ℂ))*(V : Matrix n n ℂ))
    (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    schattenNorm p A = (∑ i, (s i)^p.toReal)^(1/p.toReal) := by
  rw [schattenNorm,if_neg hp,trace_gram_cfc A V s hcalc]
  simp only [Real.rpow_eq_pow]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← Real.rpow_natCast,← Real.rpow_mul (hs i)]
  congr 1
  ring

lemma schatten_two (A : Matrix n n ℂ) :
    schattenNorm 2 A = Real.sqrt ((Aᴴ*A).trace.re) := by
  rw [schattenNorm,if_neg (by simp),ENNReal.toReal_ofNat]
  simp only [Real.rpow_eq_pow]
  norm_num only [show (2 : ℝ)/2=1 by norm_num,Real.rpow_one]
  change (cfc id (Aᴴ*A)).trace.re^(1/2 : ℝ)=Real.sqrt ((Aᴴ*A).trace.re)
  have hG : IsSelfAdjoint (Aᴴ*A) := (posSemidef_conjTranspose_mul_self A).isHermitian
  rw [cfc_id ℝ (Aᴴ*A)]
  exact (Real.sqrt_eq_rpow _).symm

lemma schatten_one_svd (A : Matrix n n ℂ) (V : unitary (Matrix n n ℂ)) (s : n → ℝ)
    (hs : ∀ i, 0 ≤ s i)
    (hcalc : ∀ f : ℝ → ℝ, cfc f (Aᴴ*A) =
      (V : Matrix n n ℂ)ᴴ*diagonal (fun i => (f (s i^2) : ℂ))*(V : Matrix n n ℂ)) :
    schattenNorm 1 A = ∑ i, s i := by
  rw [schatten_finite A V s hs hcalc 1 (by simp)]
  simp

lemma schatten_one_nonneg (A : Matrix n n ℂ) : 0 ≤ schattenNorm 1 A := by
  obtain ⟨U,V,s,hs,_,hcalc⟩ := RecoveryMatrixSVD.gram_svd A
  rw [schatten_one_svd A V s hs hcalc]
  exact Finset.sum_nonneg fun i _ => hs i

end RecoverySchatten

noncomputable section
open Matrix Unitary
open QAlgorithms.Papers.Independent.Information100.P50
open scoped ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RecoveryTraceBounds
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma entry_le_opNorm (A : Matrix n n ℂ) (i j : n) : ‖A i j‖ ≤ ‖A‖ := by
  let e : EuclideanSpace ℂ n := EuclideanSpace.single j 1
  have hh := (PiLp.norm_apply_le ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) A) e) i).trans
    ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) A).le_opNorm e)
  have he : ‖e‖=1 := by simp [e]
  have hval : ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) A) e) i = A i j := by
    change (A *ᵥ Pi.single j (1 : ℂ)) i = A i j
    simp
  rw [hval,Matrix.l2_opNorm_toEuclideanCLM,he,mul_one] at hh
  exact hh

lemma gram_trace (A : Matrix n n ℂ) : (Aᴴ*A).trace.re=∑ i, ∑ j, ‖A i j‖^2 := by
  change (∑ i, ∑ j, star (A j i)*A j i).re=∑ i, ∑ j, ‖A i j‖^2
  simp only [Complex.re_sum]
  have hterm (z : ℂ) : (star z*z).re=‖z‖^2 := by
    change (conj z*z).re=‖z‖^2
    rw [← Complex.normSq_eq_conj_mul_self,Complex.ofReal_re,Complex.normSq_eq_norm_sq]
  simp_rw [hterm]
  exact Finset.sum_comm

lemma trace_diagonal_mul (X : Matrix n n ℂ) (s : n → ℂ) :
    (X*diagonal s).trace=∑ i, X i i*s i := by
  simp [Matrix.trace,Matrix.diag]

lemma trace_op_trace_bound (X A : Matrix n n ℂ) :
    ‖(X*A).trace‖ ≤ ‖X‖*schattenNorm 1 A := by
  obtain ⟨U,V,s,hs,hA,hcalc⟩ := RecoveryMatrixSVD.gram_svd A
  rw [RecoverySchatten.schatten_one_svd A V s hs hcalc]
  have ht : (X*A).trace = ((V : Matrix n n ℂ)*X*(U : Matrix n n ℂ)*diagonal (fun i => (s i : ℂ))).trace := by
    rw [hA,← Matrix.mul_assoc,trace_mul_cycle]
    simp only [Matrix.mul_assoc]
  rw [ht,trace_diagonal_mul]
  calc
    _ ≤ ∑ i, ‖((V : Matrix n n ℂ)*X*(U : Matrix n n ℂ)) i i*(s i : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖X‖*s i := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hs i)]
      apply mul_le_mul_of_nonneg_right _ (hs i)
      exact (entry_le_opNorm _ i i).trans_eq (by
        rw [CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul])
    _ = _ := (Finset.mul_sum _ _ _).symm

lemma trace_hilbert_schmidt_bound (X A : Matrix n n ℂ) :
    ‖(X*A).trace‖ ≤ schattenNorm 2 X*schattenNorm 2 A := by
  rw [RecoverySchatten.schatten_two,RecoverySchatten.schatten_two,gram_trace,gram_trace]
  have ht : (X*A).trace = ∑ p : n×n, X p.1 p.2*A p.2 p.1 := by
    simp [Matrix.trace,Matrix.diag,Matrix.mul_apply,Fintype.sum_prod_type]
  rw [ht]
  calc
    _ ≤ ∑ p : n×n, ‖X p.1 p.2*A p.2 p.1‖ := norm_sum_le _ _
    _ = ∑ p : n×n, ‖X p.1 p.2‖*‖A p.2 p.1‖ := by simp only [norm_mul]
    _ ≤ Real.sqrt (∑ p : n×n, ‖X p.1 p.2‖^2)*Real.sqrt (∑ p : n×n, ‖A p.2 p.1‖^2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = _ := by simp only [Fintype.sum_prod_type]; rw [Finset.sum_comm (f := fun i j => ‖A j i‖^2)]

end RecoveryTraceBounds

noncomputable section
open Matrix Unitary
open QAlgorithms.Papers.Independent.Information100.P50
open scoped ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RecoveryDualFamily

def coeff (d : ℝ) (z : ℂ) : ℂ :=
  if d=0 then 0 else Complex.exp (((1-z)/2)*(Real.log d : ℂ))

lemma coeff_differentiable (d : ℝ) : Differentiable ℂ (coeff d) := by
  unfold coeff
  by_cases hd : d=0
  · simp only [if_pos hd]
    exact differentiable_const _
  · simp only [if_neg hd]
    fun_prop

lemma coeff_norm_exp {d : ℝ} (hd : d ≠ 0) (z : ℂ) :
    ‖coeff d z‖=Real.exp (((1-z.re)/2)*Real.log d) := by
  rw [coeff,if_neg hd,Complex.norm_exp]
  congr 1
  norm_num [Complex.mul_re,Complex.div_re]

lemma coeff_norm_le_one {d : ℝ} (hd : 0 ≤ d) (hd1 : d ≤ 1) {z : ℂ}
    (hz : z.re ≤ 1) : ‖coeff d z‖ ≤ 1 := by
  by_cases hdz : d=0
  · simp [coeff,hdz]
  · rw [coeff_norm_exp hdz,Real.exp_le_one_iff]
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (Real.log_nonpos hd hd1)

lemma coeff_norm_sq_it {d : ℝ} (hd : 0 ≤ d) (t : ℝ) :
    ‖coeff d ((t : ℂ)*Complex.I)‖^2=d := by
  by_cases hdz : d=0
  · simp [coeff,hdz]
  · rw [coeff_norm_exp hdz]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
      mul_zero,zero_mul,sub_zero,one_div]
    rw [pow_two,← Real.exp_add]
    convert Real.exp_log (lt_of_le_of_ne hd (Ne.symm hdz)) using 1 <;> ring

lemma coeff_real {d : ℝ} (hd : 0 ≤ d) {θ : ℝ} (hθ : θ < 1) :
    coeff d θ=(d^((1-θ)/2) : ℝ) := by
  by_cases hdz : d=0
  · simp [coeff,hdz,Real.zero_rpow (show (1-θ)/2 ≠ 0 by linarith)]
  · have hp : 0 < d := lt_of_le_of_ne hd (Ne.symm hdz)
    rw [coeff,if_neg hdz,Real.rpow_def_of_pos hp]
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring

variable {n : Type*} [Fintype n] [DecidableEq n]

def diagonalCLM : (n → ℂ) →L[ℂ] Matrix n n ℂ :=
  (Matrix.diagonalLinearMap n ℂ ℂ).toContinuousLinearMap

def traceCLM : Matrix n n ℂ →L[ℂ] ℂ :=
  (Matrix.traceLinearMap n ℂ ℂ).toContinuousLinearMap

def family (U V : unitary (Matrix n n ℂ)) (d : n → ℝ) (z : ℂ) : Matrix n n ℂ :=
  (V : Matrix n n ℂ)ᴴ*diagonal (fun i => coeff (d i) z)*(U : Matrix n n ℂ)ᴴ

lemma family_differentiable (U V : unitary (Matrix n n ℂ)) (d : n → ℝ) :
    Differentiable ℂ (family U V d) := by
  have h : Differentiable ℂ (fun z => (diagonalCLM (n := n)) (fun i => coeff (d i) z)) :=
    (diagonalCLM (n := n)).differentiable.comp (differentiable_pi.mpr fun i => coeff_differentiable (d i))
  exact (h.const_mul (V : Matrix n n ℂ)ᴴ).mul_const (U : Matrix n n ℂ)ᴴ

lemma family_opNorm_le (U V : unitary (Matrix n n ℂ)) (d : n → ℝ)
    (hd : ∀ i, 0 ≤ d i) (h1 : ∀ i, d i ≤ 1) {z : ℂ} (hz : z.re ≤ 1) :
    ‖family U V d z‖ ≤ 1 := by
  unfold family
  change ‖((star V : unitary (Matrix n n ℂ)) : Matrix n n ℂ)*diagonal (fun i => coeff (d i) z)*
    ((star U : unitary (Matrix n n ℂ)) : Matrix n n ℂ)‖ ≤ 1
  rw [CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul,Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun i => coeff_norm_le_one (hd i) (h1 i) hz)

lemma family_two_it (U V : unitary (Matrix n n ℂ)) (d : n → ℝ)
    (hd : ∀ i, 0 ≤ d i) (hsum : ∑ i, d i=1) (t : ℝ) :
    schattenNorm 2 (family U V d ((t : ℂ)*Complex.I))=1 := by
  let D : Matrix n n ℂ := diagonal (fun i => coeff (d i) ((t : ℂ)*Complex.I))
  have hv : (V : Matrix n n ℂ)*(V : Matrix n n ℂ)ᴴ=1 := Unitary.coe_mul_star_self V
  have hu : (U : Matrix n n ℂ)ᴴ*(U : Matrix n n ℂ)=1 := Unitary.coe_star_mul_self U
  have hh : ((family U V d ((t : ℂ)*Complex.I))ᴴ*family U V d ((t : ℂ)*Complex.I)).trace=(Dᴴ*D).trace := by
    change (((V : Matrix n n ℂ)ᴴ*D*(U : Matrix n n ℂ)ᴴ)ᴴ*((V : Matrix n n ℂ)ᴴ*D*(U : Matrix n n ℂ)ᴴ)).trace=_
    simp only [conjTranspose_mul,conjTranspose_conjTranspose,Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (V : Matrix n n ℂ) (V : Matrix n n ℂ)ᴴ,hv,Matrix.one_mul]
    rw [← Matrix.mul_assoc,trace_mul_cycle]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U : Matrix n n ℂ)ᴴ (U : Matrix n n ℂ),hu,Matrix.one_mul]
    exact trace_mul_comm _ _
  rw [RecoverySchatten.schatten_two,hh,RecoveryTraceBounds.gram_trace]
  have he : (∑ i, ∑ j, ‖D i j‖^2)=∑ i, d i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · simpa only [D,diagonal_apply_eq] using coeff_norm_sq_it (hd i) t
    · intro j _ hji
      simp [D,diagonal_apply,Ne.symm hji]
    · simp
  rw [he,hsum]
  norm_num

end RecoveryDualFamily

noncomputable section
open Matrix Unitary
open QAlgorithms.Papers.Independent.Information100.P50
open scoped ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RecoveryDualDensity
variable {n : Type*} [Fintype n] [DecidableEq n]

def density (s : n → ℝ) (p : ℝ) (i : n) : ℝ := (s i)^p/(∑ j, (s j)^p)

lemma density_nonneg (s : n → ℝ) (p : ℝ) (hs : ∀ i, 0 ≤ s i) (i : n) :
    0 ≤ density s p i := div_nonneg (Real.rpow_nonneg (hs i) _)
      (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (hs j) _)

lemma density_sum (s : n → ℝ) (p : ℝ) (hT : 0 < ∑ j, (s j)^p) :
    ∑ i, density s p i=1 := by
  unfold density
  rw [← Finset.sum_div,div_self hT.ne']

lemma density_le_one (s : n → ℝ) (p : ℝ) (hs : ∀ i, 0 ≤ s i)
    (hT : 0 < ∑ j, (s j)^p) (i : n) : density s p i ≤ 1 := by
  unfold density
  apply (div_le_one hT).mpr
  exact Finset.single_le_sum (fun j _ => Real.rpow_nonneg (hs j) _) (Finset.mem_univ i)

lemma density_weighted_sum (s : n → ℝ) (p q : ℝ) (hs : ∀ i, 0 ≤ s i)
    (hp : 0 < p) (hq : 0 < q) (hpq : p*q+1=p) (hT : 0 < ∑ j, (s j)^p) :
    (∑ i, (density s p i)^q*s i) = (∑ i, (s i)^p)^(1-q) := by
  let T := ∑ i, (s i)^p
  have hi (i : n) : (density s p i)^q*s i=(s i)^p/T^q := by
    by_cases hz : s i=0
    · simp [density,hz,Real.zero_rpow hp.ne',Real.zero_rpow hq.ne']
    · have hpos : 0 < s i := lt_of_le_of_ne (hs i) (Ne.symm hz)
      unfold density
      rw [Real.div_rpow (Real.rpow_nonneg (hs i) p) hT.le,← Real.rpow_mul (hs i)]
      rw [div_mul_eq_mul_div]
      have he : (s i)^(p*q)*s i=(s i)^p := by
        calc
          _=(s i)^(p*q)*(s i)^1 := by rw [Real.rpow_one]
          _=(s i)^(p*q+1) := (Real.rpow_add hpos _ _).symm
          _=_ := by rw [hpq]
      rw [he]
  simp_rw [hi]
  rw [← Finset.sum_div]
  change T/T^q=T^(1-q)
  rw [Real.rpow_sub hT,Real.rpow_one]

lemma power_sum_pos_of_svd (A : Matrix n n ℂ) (U V : unitary (Matrix n n ℂ)) (s : n → ℝ)
    (hs : ∀ i, 0 ≤ s i) (hA : A=(U : Matrix n n ℂ)*diagonal (fun i => (s i : ℂ))*(V : Matrix n n ℂ))
    (hne : A ≠ 0) {p : ℝ} (hp : 0 < p) : 0 < ∑ i, (s i)^p := by
  have hex : ∃ i, 0 < s i := by
    by_contra! hh
    have hz : ∀ i, s i=0 := fun i => le_antisymm (hh i) (hs i)
    apply hne
    rw [hA]
    simp [hz]
  obtain ⟨i,hi⟩ := hex
  exact lt_of_lt_of_le (Real.rpow_pos_of_pos hi p)
    (Finset.single_le_sum (fun j _ => Real.rpow_nonneg (hs j) p) (Finset.mem_univ i))

end RecoveryDualDensity

noncomputable section
open Matrix Unitary Set Filter
open QAlgorithms.Papers.Independent.Information100.P50
open RecoveryDualFamily RecoveryDualDensity
open scoped ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RecoveryScalarization
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma norm_trace_le (A : Matrix n n ℂ) : ‖A.trace‖ ≤ (Fintype.card n : ℝ)*‖A‖ := by
  calc
    _ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
    _ ≤ ∑ i : n, ‖A‖ := Finset.sum_le_sum fun i _ => RecoveryTraceBounds.entry_le_opNorm A i i
    _ = _ := by simp [nsmul_eq_mul]

def scalar (U V : unitary (Matrix n n ℂ)) (d : n → ℝ) (G : ℂ → Matrix n n ℂ) (z : ℂ) : ℂ :=
  (family U V d z * G z).trace

lemma scalar_differentiableOn (U V : unitary (Matrix n n ℂ)) (d : n → ℝ) (G : ℂ → Matrix n n ℂ)
    {S : Set ℂ} (hG : DifferentiableOn ℂ G S) : DifferentiableOn ℂ (scalar U V d G) S := by
  exact (traceCLM (n := n)).differentiable.comp_differentiableOn
    ((family_differentiable U V d).differentiableOn.mul hG)

lemma scalar_continuousOn (U V : unitary (Matrix n n ℂ)) (d : n → ℝ) (G : ℂ → Matrix n n ℂ)
    {S : Set ℂ} (hG : ContinuousOn G S) : ContinuousOn (scalar U V d G) S := by
  exact (traceCLM (n := n)).continuous.comp_continuousOn
    ((family_differentiable U V d).continuous.continuousOn.mul hG)

lemma scalar_bounded (U V : unitary (Matrix n n ℂ)) (d : n → ℝ) (G : ℂ → Matrix n n ℂ)
    (hd : ∀ i, 0 ≤ d i) (h1 : ∀ i, d i ≤ 1)
    (hG : Bornology.IsBounded (G '' {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1})) :
    Bornology.IsBounded ((scalar U V d G) '' {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1}) := by
  obtain ⟨B,hB⟩ := hG.exists_norm_le
  let M := max 1 B
  have hM : 0 ≤ M := le_trans zero_le_one (le_max_left _ _)
  apply (isBounded_iff_forall_norm_le).mpr
  refine ⟨(Fintype.card n : ℝ)*M,?_⟩
  rintro w ⟨z,hz,rfl⟩
  have hnormG : ‖G z‖ ≤ M := (hB _ ⟨z,hz,rfl⟩).trans (le_max_right _ _)
  change ‖(family U V d z * G z).trace‖ ≤ _
  calc
    _ ≤ (Fintype.card n : ℝ)*‖family U V d z * G z‖ := norm_trace_le _
    _ ≤ (Fintype.card n : ℝ)*(‖family U V d z‖*‖G z‖) :=
      mul_le_mul_of_nonneg_left (norm_mul_le _ _) (Nat.cast_nonneg _)
    _ ≤ (Fintype.card n : ℝ)*(1*M) := mul_le_mul_of_nonneg_left
      (mul_le_mul (family_opNorm_le U V d hd h1 hz.2) hnormG (norm_nonneg _) zero_le_one) (Nat.cast_nonneg _)
    _ = _ := by rw [one_mul]

lemma scalar_left_bound (U V : unitary (Matrix n n ℂ)) (d : n → ℝ) (G : ℂ → Matrix n n ℂ)
    (hd : ∀ i, 0 ≤ d i) (hsum : ∑ i, d i=1) (t : ℝ) :
    ‖scalar U V d G ((t : ℂ)*Complex.I)‖ ≤ schattenNorm 2 (G ((t : ℂ)*Complex.I)) := by
  have h := RecoveryTraceBounds.trace_hilbert_schmidt_bound
    (family U V d ((t : ℂ)*Complex.I)) (G ((t : ℂ)*Complex.I))
  rwa [family_two_it U V d hd hsum,one_mul] at h

lemma scalar_right_bound (U V : unitary (Matrix n n ℂ)) (d : n → ℝ) (G : ℂ → Matrix n n ℂ)
    (hd : ∀ i, 0 ≤ d i) (h1 : ∀ i, d i ≤ 1) (t : ℝ) :
    ‖scalar U V d G (1+(t : ℂ)*Complex.I)‖ ≤ schattenNorm 1 (G (1+(t : ℂ)*Complex.I)) := by
  apply (RecoveryTraceBounds.trace_op_trace_bound _ _).trans
  have hh := mul_le_mul_of_nonneg_right
    (family_opNorm_le U V d hd h1 (z := 1+(t : ℂ)*Complex.I) (by simp))
    (RecoverySchatten.schatten_one_nonneg (G (1+(t : ℂ)*Complex.I)))
  simpa only [one_mul] using hh

lemma family_trace_real (U V : unitary (Matrix n n ℂ)) (s d : n → ℝ) (hd : ∀ i, 0 ≤ d i)
    {θ : ℝ} (hθ : θ < 1) :
    (family U V d θ * ((U : Matrix n n ℂ)*diagonal (fun i => (s i : ℂ))*(V : Matrix n n ℂ))).trace =
      (∑ i, (d i)^((1-θ)/2)*s i : ℝ) := by
  have hu : (U : Matrix n n ℂ)ᴴ*(U : Matrix n n ℂ)=1 := Unitary.coe_star_mul_self U
  have hv : (V : Matrix n n ℂ)*(V : Matrix n n ℂ)ᴴ=1 := Unitary.coe_mul_star_self V
  unfold family
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (U : Matrix n n ℂ)ᴴ (U : Matrix n n ℂ),hu,Matrix.one_mul]
  simp only [← Matrix.mul_assoc]
  rw [trace_mul_cycle]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (V : Matrix n n ℂ) (V : Matrix n n ℂ)ᴴ,hv,Matrix.one_mul,
    diagonal_mul_diagonal,trace_diagonal]
  simp_rw [coeff_real (hd _) hθ]
  norm_cast

end RecoveryScalarization

noncomputable section
open Matrix Unitary Set Filter MeasureTheory
open QAlgorithms.Papers.Independent.Information100.P50
open QAlgorithms.Papers.Independent.Dependency50.P21
open RecoveryDualFamily RecoveryDualDensity RecoveryScalarization
open scoped Topology ComplexOrder ComplexConjugate ENNReal Matrix.Norms.L2Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RecoveryInterpolation
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma extendedLog_mono {a b : ℝ} (h : a ≤ b) : extendedLog a ≤ extendedLog b := by
  simpa only [ENNReal.log_ofReal,extendedLog] using ENNReal.log_monotone (ENNReal.ofReal_le_ofReal h)

lemma upperLogIntegral_mono {u v : ℝ → EReal} (h : ∀ t, u t ≤ v t) :
    upperLogIntegral u ≤ upperLogIntegral v := by
  apply EReal.sub_le_sub
  · exact_mod_cast lintegral_mono (fun t => EReal.toENNReal_le_toENNReal (h t))
  · exact_mod_cast (lintegral_mono (μ := volume)
      (fun t => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (h t))))

lemma schatten_zero (p : ℝ) (hp : 0 < p) :
    schattenNorm (ENNReal.ofReal p) (0 : Matrix n n ℂ)=0 := by
  rw [schattenNorm,if_neg ENNReal.ofReal_ne_top,ENNReal.toReal_ofReal hp.le]
  simp only [Real.rpow_eq_pow,Matrix.conjTranspose_zero,Matrix.mul_zero]
  rw [cfc_apply_zero]
  simp only [Real.zero_rpow (show p/2 ≠ 0 by positivity),map_zero,trace_zero,Complex.zero_re]
  exact Real.zero_rpow (one_div_pos.mpr hp).ne'

/-- The Schatten 2-to-1 Stein–Hirschman specialization used in quantitative recoverability. -/
theorem two_one (G : ℂ → Matrix n n ℂ)
    (hbounded : Bornology.IsBounded (G '' {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1}))
    (hholomorphic : DifferentiableOn ℂ G {z : ℂ | 0 < z.re ∧ z.re < 1})
    (hcontinuous : ContinuousOn G {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1})
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    extendedLog (schattenNorm (ENNReal.ofReal (2/(1+θ))) (G θ)) ≤
      upperLogIntegral (fun t =>
        (alphaDensity θ t : EReal)*extendedLog ((schattenNorm 2 (G ((t : ℂ)*Complex.I)))^(1-θ)) +
        (betaDensity θ t : EReal)*extendedLog ((schattenNorm 1 (G (1+(t : ℂ)*Complex.I)))^θ)) := by
  let P := 2/(1+θ)
  let Q := (1-θ)/2
  have hplus : 0 < 1+θ := by linarith
  have hP : 0 < P := div_pos (by norm_num) hplus
  have hQ : 0 < Q := by dsimp [Q]; linarith
  by_cases hzero : G θ=0
  · rw [hzero,schatten_zero P hP]
    simp only [extendedLog,le_refl,if_true]
    exact bot_le
  · obtain ⟨U,V,s,hs,hA,hcalc⟩ := RecoveryMatrixSVD.gram_svd (G θ)
    have hT : 0 < ∑ i, (s i)^P := power_sum_pos_of_svd (G θ) U V s hs hA hzero hP
    have hPQ : P*Q+1=P := by dsimp [P,Q]; field_simp [hplus.ne']; ring
    have hInv : 1-Q=1/P := by dsimp [P,Q]; field_simp [hplus.ne']; ring
    let d := density s P
    have hd : ∀ i, 0 ≤ d i := density_nonneg s P hs
    have hd1 : ∀ i, d i ≤ 1 := density_le_one s P hs hT
    have hds : ∑ i, d i=1 := density_sum s P hT
    let F := scalar U V d G
    have hFbounded : Bornology.IsBounded (F '' {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1}) :=
      scalar_bounded U V d G hd hd1 hbounded
    have hcl : closure {z : ℂ | 0 < z.re ∧ z.re < 1} = {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1} := by
      change closure (Complex.re ⁻¹' Ioo 0 1) = Complex.re ⁻¹' Icc 0 1
      rw [Complex.closure_preimage_re,closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)]
    have hF : DiffContOnCl ℂ F {z : ℂ | 0 < z.re ∧ z.re < 1} := by
      refine ⟨scalar_differentiableOn U V d G hholomorphic,?_⟩
      rw [hcl]
      exact scalar_continuousOn U V d G hcontinuous
    have hcenter : F θ=((∑ i, (s i)^P)^(1/P) : ℝ) := by
      change (family U V d θ * G θ).trace=_
      rw [hA,family_trace_real U V s d hd hθ1]
      change ((∑ i, (density s P i)^Q*s i : ℝ) : ℂ)=_
      rw [density_weighted_sum s P Q hs hP hQ hPQ hT,hInv]
    have hnorm : ‖F θ‖=schattenNorm (ENNReal.ofReal P) (G θ) := by
      rw [hcenter,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hT.le _),
        RecoverySchatten.schatten_finite (G θ) V s hs hcalc _ ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hP.le]
    have hh := WildeQIT.Recover.theorem_12_2_2 F hFbounded hF θ hθ0 hθ1
    rw [hnorm] at hh
    apply hh.trans
    apply upperLogIntegral_mono
    intro t
    have ha := (hirschmanDensities.1 θ hθ0 hθ1).1 t
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ (EReal.coe_nonneg.mpr ha.1)
      apply extendedLog_mono
      exact Real.rpow_le_rpow (norm_nonneg _)
        (scalar_left_bound U V d G hd hds t) (sub_nonneg.mpr hθ1.le)
    · apply mul_le_mul_of_nonneg_left _ (EReal.coe_nonneg.mpr ha.2)
      apply extendedLog_mono
      exact Real.rpow_le_rpow (norm_nonneg _)
        (scalar_right_bound U V d G hd hd1 t) hθ0.le

end RecoveryInterpolation

set_option autoImplicit false


theorem solution {n : Type*} [Fintype n] [DecidableEq n] (G : ℂ → Matrix n n ℂ)
    (hbounded : Bornology.IsBounded (G '' {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1}))
    (hholomorphic : DifferentiableOn ℂ G {z : ℂ | 0 < z.re ∧ z.re < 1})
    (hcontinuous : ContinuousOn G {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1})
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    extendedLog (schattenNorm (ENNReal.ofReal (2/(1+θ))) (G θ)) ≤
      upperLogIntegral (fun t =>
        (alphaDensity θ t : EReal)*extendedLog ((schattenNorm 2 (G ((t : ℂ)*Complex.I)))^(1-θ)) +
        (betaDensity θ t : EReal)*extendedLog ((schattenNorm 1 (G (1+(t : ℂ)*Complex.I)))^θ)) := by
  exact RecoveryInterpolation.two_one G hbounded hholomorphic hcontinuous θ hθ0 hθ1