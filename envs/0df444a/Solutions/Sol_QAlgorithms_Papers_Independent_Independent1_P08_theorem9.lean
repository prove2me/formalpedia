-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P08.theorem9
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T03:33:40.475053+00:00
-- url     : https://prove2.me/submissions/e6915d34-d3db-48cb-bb47-e68d16f8dcd7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P08_theorem2
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

noncomputable section
open scoped Matrix ComplexOrder Kronecker
open QAlgorithms QAlgorithms.Entanglement QAlgorithms.QubitChannels
open QAlgorithms.Papers.Independent.Independent1.P08

@[simp] private lemma transpose_apply (X : Matrix Bool Bool ℂ) : transposeMap X = Xᵀ := rfl

private lemma cp_comp (F G : QMap) (hF : IsCompletelyPositive F)
    (hG : IsCompletelyPositive G) : IsCompletelyPositive (F.comp G) := by
  intro r X hX
  exact hF r _ (hG r X hX)

-- Transposing the entire amplified matrix reverses both the reference blocks and entries.
private lemma cp_transpose (F : QMap) (hF : IsCompletelyPositive F) :
    IsCompletelyPositive (transposeMap.comp (F.comp transposeMap)) := by
  intro r X hX
  have h := (hF r Xᵀ hX.transpose).transpose
  have he : idTensorSuperop (transposeMap.comp (F.comp transposeMap)) X =
      (idTensorSuperop F Xᵀ)ᵀ := by ext p q; rfl
  rw [he]
  exact h

private def sandwich (A : Matrix Bool Bool ℂ) : QMap where
  toFun X := A * X * Aᴴ
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp

private lemma cp_sandwich (A : Matrix Bool Bool ℂ) : IsCompletelyPositive (sandwich A) := by
  intro r X hX
  have h := hX.mul_mul_conjTranspose_same
    ((1 : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ A)
  suffices he : idTensorSuperop (sandwich A) X =
      ((1 : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ A) * X *
        ((1 : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ A)ᴴ by
    rw [he]; exact h
  ext p q
  simp [idTensorSuperop,sandwich,Matrix.mul_apply,
    Matrix.conjTranspose_apply,Fintype.sum_prod_type,Matrix.one_apply,apply_ite,
    eq_comm]

private lemma canonical_entries (t lam : Bloch) (X : Matrix Bool Bool ℂ) :
    canonical t lam X = Matrix.of (fun i k : Bool =>
      if i then
        (if k then (X false false+X true true)/2*(1-(t 2 : ℂ)) -
          (lam 2 : ℂ)*(X false false-X true true)/2
        else (X false false+X true true)/2*((t 0 : ℂ)+Complex.I*(t 1 : ℂ)) +
          ((lam 0 : ℂ)*(X false true+X true false)-(lam 1 : ℂ)*(X false true-X true false))/2)
      else
        (if k then (X false false+X true true)/2*((t 0 : ℂ)-Complex.I*(t 1 : ℂ)) +
          ((lam 0 : ℂ)*(X false true+X true false)+(lam 1 : ℂ)*(X false true-X true false))/2
        else (X false false+X true true)/2*(1+(t 2 : ℂ)) +
          (lam 2 : ℂ)*(X false false-X true true)/2)) := by
  ext i k
  cases i <;> cases k <;>
    simp [canonical,blochAffineMap,sigma,pauliX,pauliY,pauliZ,Matrix.mul_apply,
      Matrix.trace,Fin.sum_univ_succ,Matrix.diagonal_apply] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

private lemma translation_neg_cp (t lam : Bloch)
    (h : IsCompletelyPositive (canonical t lam)) :
    IsCompletelyPositive (canonical (-t) lam) := by
  have hc := cp_comp (sandwich pauliY)
    ((transposeMap.comp ((canonical t lam).comp transposeMap)).comp (sandwich pauliY))
    (cp_sandwich _) (cp_comp _ _ (cp_transpose _ h) (cp_sandwich _))
  have he : canonical (-t) lam = (sandwich pauliY).comp
      ((transposeMap.comp ((canonical t lam).comp transposeMap)).comp (sandwich pauliY)) := by
    ext X i k
    cases i <;> cases k <;>
      simp [canonical_entries,sandwich,pauliY,Matrix.mul_apply,Matrix.conjTranspose_apply] <;>
      ring_nf <;> simp <;> ring
  rw [he]
  exact hc

private lemma bell_entries (i j k l : Bool) :
    pureDensity bell (i,j) (k,l) = if i = j ∧ k = l then (1/2 : ℂ) else 0 := by
  have hr : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1/2 : ℝ) := by
    rw [← mul_inv, ← pow_two, Real.sq_sqrt (by norm_num)]
    norm_num
  cases i <;> cases j <;> cases k <;> cases l <;>
    norm_num [pureDensity,bell,finiteMaxEntangled] <;> simpa only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_ofNat] using congrArg Complex.ofReal hr

private lemma choi_complement (t lam : Bloch) :
    (1/2 : ℂ) • (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ) - choiState (canonical t lam) =
      choiState (canonical (-t) (-lam)) := by
  ext ⟨i,j⟩ ⟨k,l⟩
  cases i <;> cases j <;> cases k <;> cases l <;>
    norm_num [choiState,idTensorSuperop,canonical_entries,bell_entries,Matrix.one_apply] <;> ring

private lemma choi_positive (Phi : QMap) (h : IsCompletelyPositive Phi) :
    (choiState Phi).PosSemidef := by
  have hb : (pureDensity bell).PosSemidef := by
    exact Matrix.posSemidef_vecMulVec_self_star _
  have hp := h 2
    ((pureDensity bell).submatrix (fun p : Fin 2 × Bool => (finTwoEquiv p.1,p.2))
      (fun p : Fin 2 × Bool => (finTwoEquiv p.1,p.2)))
    (hb.submatrix (fun p : Fin 2 × Bool => (finTwoEquiv p.1,p.2)))
  have hf := hp.submatrix (fun p : Bool × Bool => (finTwoEquiv.symm p.1,p.2))
  convert hf using 1
  ext p q
  simp [choiState,idTensorSuperop]

private lemma canonical_tp (t lam : Bloch) : TracePreserving (canonical t lam) := by
  intro X
  simp [Matrix.trace,canonical_entries]
  ring

private lemma amp_smul (F : QMap) {r : ℕ} (c : ℂ)
    (X : Matrix (Fin r × Bool) (Fin r × Bool) ℂ) :
    idTensorSuperop F (c • X) = c • idTensorSuperop F X := by
  ext p q
  change F (c • Matrix.of (fun i j => X (p.1,i) (q.1,j))) p.2 q.2 =
    c * F (Matrix.of (fun i j => X (p.1,i) (q.1,j))) p.2 q.2
  rw [map_smul]
  rfl

private lemma density_test_cp (F : QMap)
    (h : ∀ r : ℕ, 0 < r → ∀ X : Matrix (Fin r × Bool) (Fin r × Bool) ℂ,
      IsDensityMatrix X → (idTensorSuperop F X).PosSemidef) :
    IsCompletelyPositive F := by
  intro r X hX
  by_cases hr : r = 0
  · subst r
    have he : idTensorSuperop F X = 0 := Subsingleton.elim _ _
    rw [he]
    exact Matrix.PosSemidef.zero
  have ht := Complex.nonneg_iff.mp hX.trace_nonneg
  have htrace : X.trace = (X.trace.re : ℂ) := by
    apply Complex.ext <;> simp [ht.2.symm]
  by_cases hz : X.trace.re = 0
  · have hx0 : X = 0 := hX.trace_eq_zero_iff.mp (by rw [htrace,hz]; simp)
    subst X
    have he : idTensorSuperop F (0 : Matrix (Fin r × Bool) (Fin r × Bool) ℂ) = 0 := by
      ext p q
      change F 0 p.2 q.2 = 0
      simp
    rw [he]
    exact Matrix.PosSemidef.zero
  let Y := (X.trace.re⁻¹ : ℂ) • X
  have hY : IsDensityMatrix Y := by
    refine ⟨hX.smul (by exact_mod_cast inv_nonneg.mpr ht.1), ?_⟩
    change ((↑X.trace.re : ℂ)⁻¹ • X).trace = 1
    rw [Matrix.trace_smul]
    calc
      (↑X.trace.re : ℂ)⁻¹ * X.trace = (↑X.trace.re : ℂ)⁻¹ * ↑X.trace.re :=
        congrArg (fun z : ℂ => (↑X.trace.re : ℂ)⁻¹ * z) htrace
      _ = 1 := inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hz)
  have hp := (h r (Nat.pos_of_ne_zero hr) Y hY).smul
    (by exact_mod_cast ht.1 : (0 : ℂ) ≤ X.trace.re)
  have he : (X.trace.re : ℂ) • idTensorSuperop F Y = idTensorSuperop F X := by
    rw [show Y = (↑X.trace.re : ℂ)⁻¹ • X from rfl, amp_smul, smul_smul,
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hz), one_smul]
  rw [he] at hp
  exact hp

private lemma eb_cp_and_transpose (F : QMap) (h : IsEntanglementBreaking F) :
    IsCompletelyPositive F ∧ IsCompletelyPositive (transposeMap.comp F) := by
  constructor <;> apply density_test_cp <;> intro r hr X hX <;>
    have : Nonempty (Fin r) := ⟨⟨0,hr⟩⟩
  · obtain ⟨q,w,A,B,hw,_,hAB,he⟩ := h r hr X hX
    rw [he]
    exact Matrix.posSemidef_sum _ fun j _ =>
      ((hAB j).1.1.kronecker (hAB j).2.1).smul
        (by exact_mod_cast hw j : (0 : ℂ) ≤ w j)
  · obtain ⟨q,w,A,B,hw,_,hAB,he⟩ := h r hr X hX
    have he' : idTensorSuperop (transposeMap.comp F) X =
        ∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j)ᵀ := by
      ext p u
      have hh := congrFun (congrFun he (p.1,u.2)) (u.1,p.2)
      simpa [idTensorSuperop,Matrix.sum_apply] using hh
    rw [he']
    exact Matrix.posSemidef_sum _ fun j _ =>
      ((hAB j).1.1.kronecker (hAB j).2.1.transpose).smul
        (by exact_mod_cast hw j : (0 : ℂ) ≤ w j)

private lemma eb_neg_lambda_cp (t lam : Bloch) (h : EBT (canonical t lam)) :
    IsCompletelyPositive (canonical t (-lam)) := by
  have hc := cp_comp (sandwich pauliY) (transposeMap.comp (canonical t lam))
    (cp_sandwich _) (eb_cp_and_transpose _ h.2).2
  have he : canonical (-t) (-lam) =
      (sandwich pauliY).comp (transposeMap.comp (canonical t lam)) := by
    ext X i k
    cases i <;> cases k <;>
      simp [canonical_entries,sandwich,pauliY,Matrix.mul_apply,Matrix.conjTranspose_apply] <;>
      ring_nf <;> simp [Complex.I_sq] <;> ring
  rw [← he] at hc
  simpa using translation_neg_cp (-t) (-lam) hc

theorem solution (t : Bloch) :
    lambdaRegion t ∩ (fun lam : Bloch => -lam) ⁻¹' lambdaRegion t =
      {lam | EBT (canonical t lam)} := by
  ext lam
  change (IsCompletelyPositive (canonical t lam) ∧
    IsCompletelyPositive (canonical t (-lam))) ↔ EBT (canonical t lam)
  constructor
  · rintro ⟨hp,hn⟩
    apply (theorem2 _ ⟨canonical_tp t lam,hp⟩).mpr
    rw [choi_complement]
    exact choi_positive _ (translation_neg_cp t (-lam) hn)
  · intro h
    exact ⟨(eb_cp_and_transpose _ h.2).1,eb_neg_lambda_cp t lam h⟩

#print axioms solution
