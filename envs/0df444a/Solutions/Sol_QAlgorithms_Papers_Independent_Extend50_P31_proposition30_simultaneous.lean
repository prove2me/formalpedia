-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P31.proposition30_simultaneous
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T06:45:27.92802+00:00
-- url     : https://prove2.me/submissions/ab416630-24f9-48a9-8c84-134375688a99

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_fine_sector_rayleigh_eigenvalue
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_proposition20_eigenmatrices
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_fine_sector_unit_vectors_phase
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_lemma29_choiBasis
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_proposition17_refinement
import Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P31_row_representative_calculus
noncomputable section
open QAlgorithms.Papers.Independent.Extend50.P31
open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)
open QAlgorithms.Papers.Independent.Information100.P34 (choi)
open QAlgorithms.Papers.Independent.Frontier18.P17 (hs res)
open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)
open scoped Matrix ComplexConjugate
set_option backward.isDefEq.respectTransparency false
variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}
private lemma rho_inverse {n : ℕ} (U : UnitaryIrrep G n) (g : G) : U.rho g⁻¹ = (U.rho g)ᴴ := by
  calc
    U.rho g⁻¹ = U.rho g⁻¹ * (U.rho g * (U.rho g)ᴴ) := by rw [(U.unitary g).2,Matrix.mul_one]
    _ = (U.rho g⁻¹ * U.rho g) * (U.rho g)ᴴ := (Matrix.mul_assoc _ _ _).symm
    _ = (U.rho g)ᴴ := by rw [← U.mul,inv_mul_cancel,U.one,Matrix.one_mul]

private lemma conjugation_mul (U : UnitaryIrrep G n) (g h : G) (X : Mat n) :
    conjugationMap U g (conjugationMap U h X) = conjugationMap U (g*h) X := by
  simp [conjugationMap, sandwich, U.mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]

private lemma row_identity : rowMatrixRepresentative (LinearMap.id : EndMat n) = 1 := by
  ext p q
  simp [rowMatrixRepresentative,matrixUnit,Matrix.single_apply,Matrix.one_apply,Prod.ext_iff,ite_and,eq_comm]
private lemma character_mul_comm (F : IrrepFamily G A) (a : A) (g h : G) :
    character (F.irrep a) (g*h) = character (F.irrep a) (h*g) := by
  simp only [character, (F.irrep a).mul]
  exact Matrix.trace_mul_comm _ _

private lemma fine_row (U : UnitaryIrrep G n) (F : IrrepFamily G A) (a : A) (i : Fin (F.dim a)) :
    rowMatrixRepresentative (fineMap U F a i) = fineMatrix U F a i := by
  obtain ⟨_,_,hs⟩ := row_representative_calculus n
  have hC (g : G) : rowMatrixRepresentative (conjugationMap U g) = tensorConjugate U g := by
    rw [conjugationMap,hs]
    rfl
  ext p q
  simp only [rowMatrixRepresentative,fineMap,fineMatrix,
    LinearMap.smul_apply,LinearMap.sum_apply,Matrix.smul_apply,Matrix.sum_apply,smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro g hg
  have h := congrArg (fun M : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ => M p q) (hC g)
  simpa only [rowMatrixRepresentative] using congrArg (fun z : ℂ => (F.irrep a).rho g⁻¹ i i * z) h

private lemma hs_coordinates (X Y : Mat n) : hs X Y = ∑ p : Fin n × Fin n, conj (rowVec X p) * rowVec Y p := by
  simp [hs,res,PiLp.inner_apply,RCLike.inner_apply,rowVec,mul_comm]
private lemma fine_orthogonal (D : Data G A n) (r s : Row D) :
    fineMatrix D.U D.F r.1.val r.2 * fineMatrix D.U D.F s.1.val s.2 =
      if r = s then fineMatrix D.U D.F r.1.val r.2 else 0 := by
  exact (proposition17_refinement D).2.1 r s
private lemma normalized_inner_self (D : Data G A n) (r : Row D) (p : Fin n × Fin n)
    (hp : 0 < pivotWeight D.U D.F r.1.val r.2 p) :
    hs (normalizedMatrix D.U D.F r.1.val r.2 p) (normalizedMatrix D.U D.F r.1.val r.2 p) = 1 := by
  exact ((proposition20_eigenmatrices D).2.1 r p hp).1
private lemma normalized_fixed (D : Data G A n) (r s : Row D) (p : Fin n × Fin n) :
    fineMap D.U D.F s.1.val s.2 (normalizedMatrix D.U D.F r.1.val r.2 p) =
      if s = r then normalizedMatrix D.U D.F r.1.val r.2 p else 0 := by
  obtain ⟨ha,_,_⟩ := row_representative_calculus n
  apply rowVec.injective
  simp only [normalizedMatrix,rawMatrix,map_smul,ha,fine_row,Matrix.mulVec_smul,
    Matrix.mulVec_mulVec,fine_orthogonal]
  split_ifs with h
  · subst s
    simp only [map_smul,ha,fine_row]
  · simp

private lemma row_conjugation (U : UnitaryIrrep G n) (g : G) :
    rowMatrixRepresentative (conjugationMap U g) = tensorConjugate U g := by
  obtain ⟨_,_,h⟩ := row_representative_calculus n
  rw [conjugationMap,h]
  rfl
private lemma tensor_mul (U : UnitaryIrrep G n) (g h : G) :
    tensorConjugate U (g*h) = tensorConjugate U g * tensorConjugate U h := by
  have he : (conjugationMap U g).comp (conjugationMap U h) = conjugationMap U (g*h) := by
    apply LinearMap.ext
    intro X
    exact conjugation_mul U g h X
  obtain ⟨_,hm,_⟩ := row_representative_calculus n
  have hh := congrArg rowMatrixRepresentative he
  rw [hm,row_conjugation,row_conjugation,row_conjugation] at hh
  exact hh.symm
private lemma tensor_one (U : UnitaryIrrep G n) : tensorConjugate U 1 = 1 := by
  have h : conjugationMap U 1 = (LinearMap.id : EndMat n) := by
    apply LinearMap.ext
    intro X
    simp [conjugationMap,sandwich,U.one]
  rw [← row_conjugation,h,row_identity]
private lemma tensor_adjoint (U : UnitaryIrrep G n) (g : G) :
    (tensorConjugate U g)ᴴ = tensorConjugate U g⁻¹ := by
  ext p q
  simp [tensorConjugate,Matrix.conjTranspose_apply,rho_inverse,map_mul,mul_comm]
private lemma tensor_unitary (U : UnitaryIrrep G n) (g : G) :
    (tensorConjugate U g)ᴴ * tensorConjugate U g = 1 := by
  rw [tensor_adjoint,← tensor_mul,inv_mul_cancel,tensor_one]
private lemma tensor_rho (U : UnitaryIrrep G n) (h g : G) :
    (tensorConjugate U h).mulVec (rowVec (U.rho g)) = rowVec (U.rho (h*g*h⁻¹)) := by
  obtain ⟨ha,_,_⟩ := row_representative_calculus n
  rw [← row_conjugation,← ha]
  change rowVec (U.rho h * (U.rho g * (U.rho h)ᴴ)) = rowVec (U.rho (h*g*h⁻¹))
  rw [U.mul,U.mul,rho_inverse,Matrix.mul_assoc]
private lemma outer_conjugation {I : Type*} [Fintype I] (M : Matrix I I ℂ) (v : I → ℂ) :
    M * Matrix.vecMulVec v (fun i => conj (v i)) * Mᴴ =
      Matrix.vecMulVec (M.mulVec v) (fun i => conj (M.mulVec v i)) := by
  rw [Matrix.mul_vecMulVec,Matrix.vecMulVec_mul]
  congr 1
  funext i
  simp [Matrix.vecMul,Matrix.mulVec,dotProduct,Matrix.conjTranspose_apply,map_sum,map_mul,mul_comm]
private lemma character_conjugate (F : IrrepFamily G A) (a : A) (h g : G) :
    character (F.irrep a) (h*g*h⁻¹) = character (F.irrep a) g := by
  rw [character_mul_comm F a (h*g) h⁻¹]
  simp
private lemma character_conjugate_inv (F : IrrepFamily G A) (a : A) (h g : G) :
    character (F.irrep a) (h*g*h⁻¹)⁻¹ = character (F.irrep a) g⁻¹ := by
  simpa [mul_inv_rev,mul_assoc] using character_conjugate F a h g⁻¹

private def kcentral (U : UnitaryIrrep G n) (F : IrrepFamily G A) (a : A) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  ((F.dim a : ℂ) / Fintype.card G) • ∑ g : G, character (F.irrep a) g⁻¹ •
    Matrix.vecMulVec (rowVec (U.rho g)) (fun p => conj (rowVec (U.rho g) p))
private lemma kcentral_choi (U : UnitaryIrrep G n) (F : IrrepFamily G A) (a : A) (p q : Fin n × Fin n) :
    kcentral U F a p q = choi (centralMap U F a) p.swap q.swap := by
  simp [kcentral,choi,centralMap,conjugationMap,sandwich,rowVec,matrixUnit,
    Matrix.vecMulVec_apply,Matrix.sum_apply,Matrix.mul_apply,Matrix.single_apply,ite_and,
    Matrix.conjTranspose_apply]
private lemma kcentral_covariant (U : UnitaryIrrep G n) (F : IrrepFamily G A) (a : A) (h : G) :
    tensorConjugate U h * kcentral U F a = kcentral U F a * tensorConjugate U h := by
  have he := Equiv.sum_comp ((Equiv.mulLeft h).trans (Equiv.mulRight h⁻¹))
    (fun g : G => character (F.irrep a) g⁻¹ • Matrix.vecMulVec (rowVec (U.rho g)) (fun p => conj (rowVec (U.rho g) p)))
  dsimp at he
  simp_rw [character_conjugate_inv] at he
  have hc : tensorConjugate U h * kcentral U F a * (tensorConjugate U h)ᴴ = kcentral U F a := by
    simp only [kcentral,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_sum,Matrix.sum_mul]
    simp_rw [outer_conjugation,tensor_rho]
    exact congrArg (fun M : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ => ((F.dim a : ℂ) / Fintype.card G) • M) he
  have hh := congrArg (fun M : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ => M * tensorConjugate U h) hc
  simpa only [Matrix.mul_assoc,tensor_unitary,Matrix.mul_one] using hh

private lemma outer_rayleigh {I : Type*} [Fintype I] (v w : I → ℂ) :
    (∑ p, conj (w p) * (Matrix.vecMulVec v (fun i => conj (v i))).mulVec w p) =
      (Complex.normSq (∑ p, conj (v p) * w p) : ℂ) := by
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [map_sum,map_mul,Complex.conj_conj,Matrix.mulVec,dotProduct,Matrix.vecMulVec_apply,
    Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  ring
private lemma qform_sum {I K : Type*} [Fintype I] [Fintype K] (c : ℂ) (d : K → ℂ)
    (M : K → Matrix I I ℂ) (w : I → ℂ) :
    (∑ p, conj (w p) * ((c • ∑ k, d k • M k).mulVec w) p) =
      c * ∑ k, d k * (∑ p, conj (w p) * (M k).mulVec w p) := by
  simp only [Matrix.smul_mulVec,Matrix.sum_mulVec,Pi.smul_apply,Finset.sum_apply,smul_eq_mul,
    Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro p hp
  ring
private lemma trace_vector (X U : Mat n) :
    (∑ p : Fin n × Fin n, conj (rowVec U p) * rowVec X p) = Matrix.trace (X * Uᴴ) := by
  simp [rowVec,Fintype.sum_prod_type,Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,
    Matrix.conjTranspose_apply,mul_comm]
private lemma kcentral_rayleigh (D : Data G A n) (a : A) (r : Row D) (p : Fin n × Fin n) :
    (∑ q, conj (rowVec (normalizedMatrix D.U D.F r.1.val r.2 p) q) *
      (kcentral D.U D.F a).mulVec (rowVec (normalizedMatrix D.U D.F r.1.val r.2 p)) q) = muAt D a r p := by
  rw [kcentral,qform_sum]
  simp_rw [outer_rayleigh,trace_vector]
  rfl
private lemma kcentral_fine_commutes (D : Data G A n) (a : A) (r : Row D) :
    kcentral D.U D.F a * fineMatrix D.U D.F r.1.val r.2 =
      fineMatrix D.U D.F r.1.val r.2 * kcentral D.U D.F a := by
  simp [fineMatrix,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_sum,Matrix.sum_mul,
    kcentral_covariant]
private lemma kcentral_eigen (D : Data G A n) (a : A) (r : Row D) (p : Fin n × Fin n)
    (hp : 0 < pivotWeight D.U D.F r.1.val r.2 p) :
    (kcentral D.U D.F a).mulVec (rowVec (normalizedMatrix D.U D.F r.1.val r.2 p)) =
      muAt D a r p • rowVec (normalizedMatrix D.U D.F r.1.val r.2 p) := by
  obtain ⟨ha,_,_⟩ := row_representative_calculus n
  have hf := congrArg rowVec (normalized_fixed D r r p)
  have hfix : (fineMatrix D.U D.F r.1.val r.2).mulVec
      (rowVec (normalizedMatrix D.U D.F r.1.val r.2 p)) =
      rowVec (normalizedMatrix D.U D.F r.1.val r.2 p) := by
    simpa only [if_pos rfl,if_true,ha,fine_row] using hf
  have hn : (∑ q, conj (rowVec (normalizedMatrix D.U D.F r.1.val r.2 p) q) *
      rowVec (normalizedMatrix D.U D.F r.1.val r.2 p) q) = 1 := by
    rw [← hs_coordinates]
    exact normalized_inner_self D r p hp
  have h := fine_sector_rayleigh_eigenvalue D r (kcentral D.U D.F a) _ hfix hn (kcentral_fine_commutes D a r)
  rw [kcentral_rayleigh] at h
  exact h
private lemma swap_action (J : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (w : (Fin n × Fin n) → ℂ) (p : Fin n × Fin n) :
    J.mulVec (fun q => w q.swap) p =
      Matrix.mulVec (fun (p q : Fin n × Fin n) => J p.swap q.swap) w p.swap := by
  have h := Equiv.sum_comp (Equiv.prodComm (Fin n) (Fin n)) (fun q => J p q * w q.swap)
  simpa [Matrix.mulVec,dotProduct] using h.symm
private lemma choi_eigen_pivot (D : Data G A n) (a : A) (r : Row D) (p : Fin n × Fin n)
    (hp : 0 < pivotWeight D.U D.F r.1.val r.2 p) :
    (choi (centralMap D.U D.F a)).mulVec (rowVec (normalizedMatrix D.U D.F r.1.val r.2 p)ᵀ) =
      muAt D a r p • rowVec (normalizedMatrix D.U D.F r.1.val r.2 p)ᵀ := by
  have h := kcentral_eigen D a r p hp
  have hK : kcentral D.U D.F a = fun p q => choi (centralMap D.U D.F a) p.swap q.swap := by
    ext p q
    exact kcentral_choi D.U D.F a p q
  ext q
  change (choi (centralMap D.U D.F a)).mulVec
    (fun k => rowVec (normalizedMatrix D.U D.F r.1.val r.2 p) k.swap) q = _
  rw [swap_action,← hK]
  exact congrArg (fun v : (Fin n × Fin n) → ℂ => v q.swap) h
private lemma mu_pivot_independent (D : Data G A n) (a : A) (r : Row D) (p q : Fin n × Fin n)
    (hp : 0 < pivotWeight D.U D.F r.1.val r.2 p) (hq : 0 < pivotWeight D.U D.F r.1.val r.2 q) :
    muAt D a r p = muAt D a r q := by
  obtain ⟨t,ht⟩ := fine_sector_unit_vectors_phase D r _ _ (normalized_inner_self D r p hp)
    (normalized_inner_self D r q hq) (by simpa using normalized_fixed D r r p)
    (by simpa using normalized_fixed D r r q)
  have hn : Complex.normSq (QAlgorithms.Papers.Independent.Information100.P75.phase t) = 1 := by
    rw [Complex.normSq_eq_norm_sq]
    simp [QAlgorithms.Papers.Independent.Information100.P75.phase,Complex.norm_exp]
  simp only [muAt,ht,Matrix.smul_mul,Matrix.trace_smul,smul_eq_mul,Complex.normSq_mul,hn,one_mul]


set_option autoImplicit false

set_option autoImplicit false
open QAlgorithms.Papers.Independent.Extend50.P31
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq



open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Bridge50.P37 (hsAdjoint)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)

open QAlgorithms.Papers.Independent.Information100.P75 (phase)

variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}

/-- PDF p.15, Proposition 30 and Remarks 31--32 Eqs.(76)--(78).
The modulus is squared, with no TP or real-character assumption. -/
theorem solution (D : Data G A n) (P : Pivots D) :
    (∀ a : OccurringIrrep D, ∀ r, (choi (centralMap D.U D.F a.val)).mulVec (choiVector D P r) =
      spectralMatrix D P r a • choiVector D P r) ∧
    (∀ a b : OccurringIrrep D, choi (centralMap D.U D.F a.val) * choi (centralMap D.U D.F b.val) =
      choi (centralMap D.U D.F b.val) * choi (centralMap D.U D.F a.val)) ∧
    (∀ a : A, ∀ r : Row D, ∀ p q,
      0 < pivotWeight D.U D.F r.1.val r.2 p → 0 < pivotWeight D.U D.F r.1.val r.2 q →
      muAt D a r p = muAt D a r q) := by
  have he (a : OccurringIrrep D) (r : Row D) :
      (choi (centralMap D.U D.F a.val)).mulVec (choiVector D P r) = spectralMatrix D P r a • choiVector D P r :=
    choi_eigen_pivot D a.val r (P.pivot r) (P.positive r)
  refine ⟨he,?_,mu_pivot_independent D⟩
  intro a b
  apply Matrix.toLin'.injective
  apply LinearMap.ext_on_range (lemma29_choiBasis D P).2
  intro r
  change (choi (centralMap D.U D.F a.val) * choi (centralMap D.U D.F b.val)).mulVec (choiVector D P r) =
    (choi (centralMap D.U D.F b.val) * choi (centralMap D.U D.F a.val)).mulVec (choiVector D P r)
  simp only [← Matrix.mulVec_mulVec,he,Matrix.mulVec_smul]
  simp [smul_smul,mul_comm]
