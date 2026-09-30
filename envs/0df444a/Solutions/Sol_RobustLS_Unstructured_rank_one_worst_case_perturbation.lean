-- Prove2me | solution 1 for RobustLS.Unstructured.rank_one_worst_case_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:13:52.128974+00:00
-- url     : https://prove2.me/submissions/ff9ef593-97e1-404c-a5fa-cea8903f8ed9

import Definitions.Def_RobustLS_Unstructured_Core
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic
open RobustLS.Unstructured Matrix
open scoped RealInnerProductSpace

private theorem euc_eq_norm {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    eucNorm v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ ι)‖ := by
  have hh : ‖(WithLp.toLp 2 v : EuclideanSpace ℝ ι)‖^2 = ∑ i,v i^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp
  rw [eucNorm,← hh,Real.sqrt_sq (norm_nonneg _)]

private theorem euc_sq {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    (eucNorm v)^2=∑ i,v i^2 := Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))
private theorem euc_nonneg {ι : Type*} [Fintype ι] (v : ι → ℝ) : 0 ≤ eucNorm v := Real.sqrt_nonneg _
private theorem euc_add {ι : Type*} [Fintype ι] (v w : ι → ℝ) :
    eucNorm (v+w) ≤ eucNorm v+eucNorm w := by
  simp only [euc_eq_norm]
  exact norm_add_le _ _
private theorem euc_smul {ι : Type*} [Fintype ι] (a : ℝ) (v : ι → ℝ) :
    eucNorm (a • v)=|a| *eucNorm v := by
  simp only [euc_eq_norm]
  change ‖a • (WithLp.toLp 2 v : EuclideanSpace ℝ ι)‖ = _
  rw [norm_smul,Real.norm_eq_abs]
private theorem frob_sq {ι κ : Type*} [Fintype ι] [Fintype κ] (X : Matrix ι κ ℝ) :
    frobNorm X^2=∑ i,∑ j,X i j^2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)))
private theorem frob_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ] (X : Matrix ι κ ℝ) :
    0 ≤ frobNorm X := Real.sqrt_nonneg _

private theorem euc_mul_le_frob {ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : Matrix ι κ ℝ) (v : κ → ℝ) : eucNorm (X *ᵥ v) ≤ frobNorm X*eucNorm v := by
  apply (sq_le_sq₀ (euc_nonneg _) (mul_nonneg (frob_nonneg _) (euc_nonneg _))).mp
  rw [mul_pow,euc_sq,frob_sq,euc_sq,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

private theorem stack_norm {m : ℕ} (x : Fin m → ℝ) :
    eucNorm (Sum.elim x (fun _ : Unit => (-1:ℝ))) = Real.sqrt (eucNorm x^2+1) := by
  rw [eucNorm,euc_sq]
  simp [Fintype.sum_sum_type]

private theorem perturb_eq {n m : ℕ} (A ΔA : Matrix (Fin n) (Fin m) ℝ)
    (b Δb : Fin n → ℝ) (x : Fin m → ℝ) :
    (A+ΔA)*ᵥx-(b+Δb)=(A*ᵥx-b)+(augment ΔA Δb)*ᵥ(Sum.elim x (fun _ : Unit => (-1:ℝ))) := by
  ext i
  simp [Matrix.mulVec, dotProduct, augment, Fintype.sum_sum_type,add_mul,Finset.sum_add_distrib]
  ring



private theorem spec_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ] (X : Matrix ι κ ℝ) :
    0 ≤ specNorm X := by
  unfold specNorm
  apply le_csInf (s := {c : ℝ | 0 ≤ c ∧ ∀ v : κ → ℝ,eucNorm (X *ᵥ v) ≤ c*eucNorm v})
    ⟨frobNorm X,frob_nonneg _,euc_mul_le_frob X⟩
  intro c hc
  exact hc.1
private theorem spec_le_frob {ι κ : Type*} [Fintype ι] [Fintype κ] (X : Matrix ι κ ℝ) :
    specNorm X ≤ frobNorm X := by
  exact csInf_le ⟨0,fun _ h => h.1⟩ ⟨frob_nonneg _,euc_mul_le_frob X⟩
private theorem euc_mul_le_spec {ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : Matrix ι κ ℝ) (v : κ → ℝ) : eucNorm (X *ᵥ v) ≤ specNorm X*eucNorm v := by
  by_cases hv : eucNorm v=0
  · have hh := euc_mul_le_frob X v
    simpa [hv] using hh
  have hvp : 0 < eucNorm v := lt_of_le_of_ne (euc_nonneg _) (Ne.symm hv)
  apply (div_le_iff₀ hvp).mp
  unfold specNorm
  apply le_csInf (s := {c : ℝ | 0 ≤ c ∧ ∀ v : κ → ℝ,eucNorm (X *ᵥ v) ≤ c*eucNorm v})
    ⟨frobNorm X,frob_nonneg _,euc_mul_le_frob X⟩
  intro c hc
  exact (div_le_iff₀ hvp).mpr (hc.2 v)

private theorem frob_rank {ι κ : Type*} [Fintype ι] [Fintype κ] (u : ι → ℝ) (v : κ → ℝ) :
    frobNorm (Matrix.vecMulVec u v)=eucNorm u*eucNorm v := by
  apply (sq_eq_sq₀ (frob_nonneg _) (mul_nonneg (euc_nonneg _) (euc_nonneg _))).mp
  simp only [frob_sq,mul_pow,euc_sq,Matrix.vecMulVec_apply,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]

private theorem spec_rank {ι κ : Type*} [Fintype ι] [Fintype κ] (u : ι → ℝ) (v : κ → ℝ) :
    specNorm (Matrix.vecMulVec u v)=eucNorm u*eucNorm v := by
  apply le_antisymm
  · simpa [frob_rank] using spec_le_frob (Matrix.vecMulVec u v)
  · have hh := euc_mul_le_spec (Matrix.vecMulVec u v) v
    have he : Matrix.vecMulVec u v *ᵥ v = (eucNorm v)^2 • u := by
      ext i
      simp only [Matrix.mulVec,Matrix.vecMulVec_apply,dotProduct,euc_sq,Pi.smul_apply,smul_eq_mul]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _; ring
    rw [he,euc_smul,abs_of_nonneg (sq_nonneg _)] at hh
    by_cases hv : eucNorm v=0
    · simpa [hv] using spec_nonneg (Matrix.vecMulVec u v)
    have hp : 0 < eucNorm v := lt_of_le_of_ne (euc_nonneg _) (Ne.symm hv)
    nlinarith

theorem solution {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (b : Fin n → ℝ) (x : Fin m → ℝ) (u : Fin n → ℝ) (hu : eucNorm u=1)
    (hu_dir : A*ᵥx≠b → u=(eucNorm (A*ᵥx-b))⁻¹ • (A*ᵥx-b)) :
    let c := (Real.sqrt (eucNorm x^2+1))⁻¹
    let ΔA := c • Matrix.vecMulVec u x
    let Δb := (-c) • u
    frobNorm (augment ΔA Δb)=1 ∧ specNorm (augment ΔA Δb)=1 ∧
      perturbedResidual A b ΔA Δb x=eucNorm (A*ᵥx-b)+Real.sqrt (eucNorm x^2+1) := by
  let r := Real.sqrt (eucNorm x^2+1)
  have hr : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hrs : r^2=eucNorm x^2+1 := Real.sq_sqrt (by positivity)
  let v : Fin m ⊕ Unit → ℝ := Sum.elim x (fun _ => -1)
  have hv : eucNorm v=r := stack_norm x
  have hm : augment (r⁻¹ • Matrix.vecMulVec u x) ((-r⁻¹) • u)=Matrix.vecMulVec (r⁻¹ • u) v := by
    ext i j
    cases j <;> simp [augment,v,Matrix.vecMulVec_apply] <;> ring
  dsimp only
  change frobNorm (augment (r⁻¹ • Matrix.vecMulVec u x) ((-r⁻¹) • u))=1 ∧
    specNorm (augment (r⁻¹ • Matrix.vecMulVec u x) ((-r⁻¹) • u))=1 ∧ _
  have hunit : eucNorm (r⁻¹ • u)*eucNorm v=1 := by
    rw [euc_smul,hu,hv,abs_of_pos (inv_pos.mpr hr)]
    field_simp
  refine ⟨by rw [hm,frob_rank,hunit],by rw [hm,spec_rank,hunit],?_⟩
  have hvv : dotProduct v v=r^2 := by
    rw [← hv,euc_sq]
    simp [dotProduct,pow_two]
  have he : augment (r⁻¹ • Matrix.vecMulVec u x) ((-r⁻¹) • u)*ᵥv=r • u := by
    rw [hm]
    ext i
    simp only [Matrix.mulVec,Matrix.vecMulVec_apply,Pi.smul_apply,smul_eq_mul,dotProduct]
    calc (∑ j,r⁻¹*u i*v j*v j) = r⁻¹*u i*dotProduct v v := by simp only [dotProduct,Finset.mul_sum]; congr 1; ext j; ring
         _ = r*u i := by rw [hvv]; field_simp <;> ring
  rw [perturbedResidual,perturb_eq]
  change eucNorm ((A*ᵥx-b)+augment (r⁻¹ • Matrix.vecMulVec u x) ((-r⁻¹) • u)*ᵥv)=eucNorm (A*ᵥx-b)+r
  rw [he]
  by_cases hz : A*ᵥx=b
  · rw [hz,sub_self,zero_add,euc_smul,hu,abs_of_pos hr]
    simp [eucNorm]
  · have hp : 0 < eucNorm (A*ᵥx-b) := by
      rw [euc_eq_norm]
      apply norm_pos_iff.mpr
      intro he
      apply hz
      exact sub_eq_zero.mp (by simpa using congrArg WithLp.ofLp he)
    rw [hu_dir hz]
    have hid : (A*ᵥx-b)+r • (eucNorm (A*ᵥx-b))⁻¹ • (A*ᵥx-b)=
        (1+r/eucNorm (A*ᵥx-b)) • (A*ᵥx-b) := by rw [smul_smul]; module
    rw [hid,euc_smul,abs_of_pos (by positivity)]
    field_simp
