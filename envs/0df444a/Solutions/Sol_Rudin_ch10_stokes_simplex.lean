-- Prove2me | solution 1 for Rudin.ch10_stokes_simplex
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-19T04:33:54.338642+00:00
-- url     : https://prove2.me/submissions/5dd09478-5505-48d9-be12-46d7613e179f

/-
Rudin, *Principles of Mathematical Analysis*, 3rd ed., Theorem 10.33 (Stokes' theorem),
the case of the identity surface of the standard simplex `Q^{k+1}` (pp. 273-274).

The proof follows Rudin.  Using `Rudin.ch10_integral_identity_simplex`, the left-hand side is
the integral over `Q^{k+1}` of the signed sum over `S_{k+1}` of the coefficients of `dw`;
splitting that sum according to the image of `0` turns it into the sum over the coordinate
directions `c` of `(-1)^c` times the integral of `D_c A_c`, where `A_c` is the alternation of
the coefficients of `w` along the tuple `c.succAbove`.  The fundamental theorem of calculus on
the simplex (`Rudin.ch10_simplex_ftc`) converts each of these into the difference of two
integrals over `Q^k`: one over the coordinate face `x_c = 0`, one over the slanted face
`sum x = 1` parametrized by inserting the missing coordinate at place `c`.

The boundary chain of the identity surface consists of exactly these faces, the slanted one
being parametrized with the missing coordinate at place `0`.  Two ingredients match the two
sides: the two parametrizations of the slanted face differ by an affine, measure preserving
bijection of `Q^k`; and the Jacobian of a face is constant, so the integrand of a face is
obtained by splitting the sum over index tuples according to the index that the tuple misses,
the corresponding minor being `1` for the `c`-th coordinate face and `(-1)^c` for the slanted
face -- the latter because the rows of the slanted face sum to zero, which makes its minors
alternate in sign.
-/
import Mathlib
import Definitions.Def_Rudin_ch10_forms
import Theorems.Thm_Rudin_ch10_simplex_ftc
import Theorems.Thm_Rudin_ch10_integral_identity_simplex

open Filter Topology MeasureTheory Matrix

namespace Rudin

/-! ### The standard simplex is compact -/

lemma isClosed_stdSimplex (k : ℕ) : IsClosed (stdSimplex k) := by
  have h1 : IsClosed {u : Fin k → ℝ | ∀ i, 0 ≤ u i} := by
    have h : {u : Fin k → ℝ | ∀ i, 0 ≤ u i} = ⋂ i : Fin k, {u : Fin k → ℝ | 0 ≤ u i} := by
      ext u; simp
    rw [h]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have h2 : IsClosed {u : Fin k → ℝ | ∑ i, u i ≤ 1} :=
    isClosed_le (continuous_finset_sum _ fun i _ => continuous_apply i) continuous_const
  exact h1.inter h2

lemma measurableSet_stdSimplex (k : ℕ) : MeasurableSet (stdSimplex k) :=
  (isClosed_stdSimplex k).measurableSet

lemma isCompact_stdSimplex (k : ℕ) : IsCompact (stdSimplex k) := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  refine ⟨isClosed_stdSimplex k, ?_⟩
  rw [isBounded_iff_forall_norm_le]
  refine ⟨1, fun u hu => ?_⟩
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (hu.1 i)]
  calc u i ≤ ∑ j, u j := Finset.single_le_sum (fun j _ => hu.1 j) (Finset.mem_univ i)
    _ ≤ 1 := hu.2

/-! ### Inserting a coordinate -/

/-- The point of `ℝ^{k+1}` whose `c`-th coordinate is `t` and whose remaining coordinates,
in order, are those of `y`. -/
noncomputable def ins {k : ℕ} (c : Fin (k + 1)) (t : ℝ) (y : Fin k → ℝ) : Fin (k + 1) → ℝ :=
  Fin.insertNth (α := fun _ => ℝ) c t y

@[simp] lemma ins_same {k : ℕ} (c : Fin (k + 1)) (t : ℝ) (y : Fin k → ℝ) : ins c t y c = t := by
  simp [ins]

@[simp] lemma ins_succAbove {k : ℕ} (c : Fin (k + 1)) (t : ℝ) (y : Fin k → ℝ) (s : Fin k) :
    ins c t y (c.succAbove s) = y s := by
  simp [ins]

lemma ins_sum {k : ℕ} (c : Fin (k + 1)) (t : ℝ) (y : Fin k → ℝ) :
    ∑ i, ins c t y i = t + ∑ s, y s := by
  rw [Fin.sum_univ_succAbove _ c]
  simp

lemma continuous_ins {k : ℕ} (c : Fin (k + 1)) :
    Continuous fun p : ℝ × (Fin k → ℝ) => ins c p.1 p.2 := by
  rw [continuous_pi_iff]
  intro i
  refine Fin.succAboveCases c ?_ ?_ i
  · have h : (fun p : ℝ × (Fin k → ℝ) => ins c p.1 p.2 c) = fun p => p.1 := by
      funext p; simp
    rw [h]
    exact continuous_fst
  · intro s
    have h : (fun p : ℝ × (Fin k → ℝ) => ins c p.1 p.2 (c.succAbove s)) = fun p => p.2 s := by
      funext p; simp
    rw [h]
    exact (continuous_apply s).comp continuous_snd

lemma continuous_partialDeriv {k : ℕ} {f : (Fin k → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (c : Fin k) :
    Continuous (partialDeriv f c) := by
  have h : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  exact (ContinuousLinearMap.apply ℝ ℝ (Pi.single c (1 : ℝ))).continuous.comp h

/-! ### Partial derivatives of the coordinate functions -/

/-- The partial derivatives of a coordinate function. -/
lemma partialDeriv_coord {k : ℕ} (i s : Fin k) (u : Fin k → ℝ) :
    partialDeriv (fun v : Fin k → ℝ => v i) s u = if i = s then 1 else 0 := by
  have h : (fun v : Fin k → ℝ => v i) = (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ) := rfl
  rw [partialDeriv, h, ContinuousLinearMap.fderiv]
  simp [Pi.single_apply]

/-! ### Alternating sums of coefficients -/

/-- The alternation of the coefficients of a `k`-form: the value of the associated alternating
form on the basis vectors indexed by `i`. -/
noncomputable def altCoeff {k n : ℕ} (ω : KForm k n) (i : Fin k → Fin n) (x : Fin n → ℝ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ : ℝ) * ω.coeff (fun r => i (σ r)) x

/-- The permutation of `Fin (k+1)` sending `0` to `r` and `j.succ` to `r.succAbove (σ j)`. -/
noncomputable def consPerm {k : ℕ} (r : Fin (k + 1)) (σ : Equiv.Perm (Fin k)) :
    Equiv.Perm (Fin (k + 1)) :=
  (Fin.cycleRange r).symm * Equiv.Perm.decomposeFin.symm (0, σ)

@[simp] theorem consPerm_zero {k : ℕ} (r : Fin (k + 1)) (σ : Equiv.Perm (Fin k)) :
    consPerm r σ 0 = r := by
  simp [consPerm, Fin.cycleRange_symm_zero]

@[simp] theorem consPerm_succ {k : ℕ} (r : Fin (k + 1)) (σ : Equiv.Perm (Fin k)) (j : Fin k) :
    consPerm r σ j.succ = r.succAbove (σ j) := by
  simp [consPerm, Fin.cycleRange_symm_succ]

theorem consPerm_sign {k : ℕ} (r : Fin (k + 1)) (σ : Equiv.Perm (Fin k)) :
    (Equiv.Perm.sign (consPerm r σ) : ℝ) = (-1 : ℝ) ^ (r : ℕ) * (Equiv.Perm.sign σ : ℝ) := by
  simp [consPerm, Equiv.Perm.decomposeFin.symm_sign, Fin.sign_cycleRange]

theorem consPerm_bijective {k : ℕ} :
    Function.Bijective fun q : Fin (k + 1) × Equiv.Perm (Fin k) => consPerm q.1 q.2 := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp [Fintype.card_perm, Nat.factorial_succ]⟩
  rintro ⟨r, σ⟩ ⟨r', σ'⟩ h
  simp only at h
  have hr : r = r' := by
    have := congrArg (fun e => e 0) h
    simpa using this
  subst hr
  have h2 : Equiv.Perm.decomposeFin.symm ((0 : Fin (k + 1)), σ)
      = Equiv.Perm.decomposeFin.symm (0, σ') := by
    have := congrArg (fun e => Fin.cycleRange r * e) h
    simpa [consPerm, ← mul_assoc] using this
  simpa using Equiv.Perm.decomposeFin.symm.injective h2

/-- Splitting a signed sum over `Perm (Fin (k+1))` according to the image of `0`. -/
theorem sum_perm_succ_split {k : ℕ} (f : Fin (k + 1) → (Fin k → Fin (k + 1)) → ℝ) :
    ∑ τ : Equiv.Perm (Fin (k + 1)), (Equiv.Perm.sign τ : ℝ) * f (τ 0) (fun j => τ j.succ)
      = ∑ r : Fin (k + 1), (-1 : ℝ) ^ (r : ℕ) *
          ∑ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ : ℝ) * f r (fun j => r.succAbove (σ j)) := by
  have key := Fintype.sum_bijective _ consPerm_bijective
    (fun q : Fin (k + 1) × Equiv.Perm (Fin k) =>
      (-1 : ℝ) ^ (q.1 : ℕ) * ((Equiv.Perm.sign q.2 : ℝ) * f q.1 fun j => q.1.succAbove (q.2 j)))
    (fun τ : Equiv.Perm (Fin (k + 1)) => (Equiv.Perm.sign τ : ℝ) * f (τ 0) fun j => τ j.succ)
    (by rintro ⟨r, σ⟩; simp only [consPerm_zero, consPerm_succ, consPerm_sign]; ring)
  rw [← key, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun r _ => by rw [Finset.mul_sum]

/-! ### The two imported ingredients, in the notation used below -/

/-- The fundamental theorem of calculus on the simplex (`Rudin.ch10_simplex_ftc`). -/
lemma integral_partialDeriv_stdSimplex {k : ℕ} {f : (Fin (k + 1) → ℝ) → ℝ}
    (hf : ContDiff ℝ 1 f) (c : Fin (k + 1)) :
    ∫ x in stdSimplex (k + 1), partialDeriv f c x
      = ∫ y in stdSimplex k, (f (ins c (1 - ∑ s, y s) y) - f (ins c 0 y)) :=
  ch10_simplex_ftc k f hf c

/-- The integral of a form over the identity surface of `Q^k`
(`Rudin.ch10_integral_identity_simplex`). -/
lemma integralOverSimplex_id {k : ℕ} (ω : KForm k k) :
    integralOverSimplex ω ⟨id⟩
      = ∫ u in stdSimplex k,
          ∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ω.coeff (⇑σ) u :=
  ch10_integral_identity_simplex k ω

section StokesSimplex

variable {k : ℕ}

/-! ### The faces of the standard simplex -/

/-- The `c`-th coordinate face of `Q^{k+1}`: the parametrization `y ↦ ins c 0 y` of the face
`x_c = 0`. -/
noncomputable def faceParam (c : Fin (k + 1)) : (Fin k → ℝ) → (Fin (k + 1) → ℝ) :=
  fun y => ins c 0 y

/-- The slanted face of `Q^{k+1}`, in the parametrization that puts the missing coordinate
`1 - ∑ y` in place `0`. -/
noncomputable def slantParam (k : ℕ) : (Fin k → ℝ) → (Fin (k + 1) → ℝ) :=
  fun y => ins 0 (1 - ∑ s, y s) y

/-- The rows of the (constant) Jacobian matrix of the coordinate face `faceParam c`. -/
def rowFace (c m : Fin (k + 1)) (s : Fin k) : ℝ :=
  if m = c then 0 else if m = c.succAbove s then 1 else 0

/-- The rows of the (constant) Jacobian matrix of the slanted face `slantParam k`. -/
def rowSlant (m : Fin (k + 1)) (s : Fin k) : ℝ :=
  if m = 0 then -1 else if m = s.succ then 1 else 0

/-- The reparametrization of the slanted face: `slantParam k ∘ reparam c` is the
parametrization of the slanted face that puts the missing coordinate in place `c`. -/
noncomputable def reparam (c : Fin (k + 1)) : (Fin k → ℝ) → (Fin k → ℝ) :=
  fun y r => ins c (1 - ∑ s, y s) y r.succ

/-! ### Identification of the faces of the identity surface -/

@[simp] lemma stdVertices_zero (k : ℕ) : stdVertices k 0 = 0 := rfl

@[simp] lemma stdVertices_succ (k : ℕ) (j : Fin k) : stdVertices k j.succ = Pi.single j 1 := rfl

lemma boundaryFace_id_zero (k : ℕ) :
    (boundaryFace (id : (Fin (k + 1) → ℝ) → (Fin (k + 1) → ℝ)) 0).map = slantParam k := by
  have hp : (fun r : Fin (k + 1) => stdVertices (k + 1) ((0 : Fin (k + 2)).succAbove r))
      = fun r : Fin (k + 1) => (Pi.single r 1 : Fin (k + 1) → ℝ) := by
    funext r
    rw [Fin.succAbove_zero]
    exact stdVertices_succ (k + 1) r
  funext u m
  simp only [boundaryFace, Function.comp_apply, id_eq, affineSimplexMap, slantParam, hp]
  refine Fin.cases ?_ ?_ m
  · simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      Pi.single_apply, ins_same]
    have h0 : ∀ x : Fin k, ((0 : Fin (k + 1)) = x.succ) = False := by
      intro x; simp [eq_comm, Fin.succ_ne_zero]
    simp [h0]
    ring
  · intro t
    simp [Pi.single_apply, ins, Fin.succ_ne_zero, Fin.succ_inj]

lemma boundaryFace_id_succ (k : ℕ) (c : Fin (k + 1)) :
    (boundaryFace (id : (Fin (k + 1) → ℝ) → (Fin (k + 1) → ℝ)) c.succ).map = faceParam c := by
  have hp0 : stdVertices (k + 1) ((c.succ).succAbove 0) = 0 := by
    rw [Fin.succ_succAbove_zero]; rfl
  have hps : ∀ r : Fin k, stdVertices (k + 1) ((c.succ).succAbove r.succ)
      = (Pi.single (c.succAbove r) 1 : Fin (k + 1) → ℝ) := by
    intro r
    rw [Fin.succ_succAbove_succ]
    exact stdVertices_succ (k + 1) _
  funext u m
  simp only [boundaryFace, Function.comp_apply, id_eq, affineSimplexMap, faceParam, hp0, hps,
    sub_zero, zero_add]
  refine Fin.succAboveCases c ?_ ?_ m
  · simp [ins, Finset.sum_eq_zero]
  · intro s
    simp [ins, Pi.single_apply]

/-! ### The Jacobians of the faces -/

lemma partialDeriv_slantCoord (s : Fin k) (y : Fin k → ℝ) :
    partialDeriv (fun v : Fin k → ℝ => 1 - ∑ t, v t) s y = -1 := by
  set L : (Fin k → ℝ) →L[ℝ] ℝ := ∑ t : Fin k, ContinuousLinearMap.proj t with hL
  have hfun : (fun v : Fin k → ℝ => 1 - ∑ t, v t) = fun v => 1 - L v := by
    funext v
    simp [hL, ContinuousLinearMap.sum_apply]
  rw [partialDeriv, hfun, fderiv_const_sub, ContinuousLinearMap.fderiv]
  simp [hL, ContinuousLinearMap.sum_apply, Pi.single_apply]

lemma partialDeriv_faceParam (c m : Fin (k + 1)) (s : Fin k) (y : Fin k → ℝ) :
    partialDeriv (fun v => faceParam c v m) s y = rowFace c m s := by
  refine Fin.succAboveCases c ?_ ?_ m
  · have h : (fun v : Fin k → ℝ => faceParam c v c) = fun _ => 0 := by
      funext v; simp [faceParam]
    rw [h]
    simp [partialDeriv, rowFace]
  · intro t
    have h : (fun v : Fin k → ℝ => faceParam c v (c.succAbove t)) = fun v => v t := by
      funext v; simp [faceParam]
    rw [h, partialDeriv_coord]
    simp [rowFace, Fin.succAbove_ne c t]

lemma partialDeriv_slantParam (m : Fin (k + 1)) (s : Fin k) (y : Fin k → ℝ) :
    partialDeriv (fun v => slantParam k v m) s y = rowSlant m s := by
  refine Fin.cases ?_ ?_ m
  · have h : (fun v : Fin k → ℝ => slantParam k v 0) = fun v => 1 - ∑ t, v t := by
      funext v; simp [slantParam]
    rw [h, partialDeriv_slantCoord]
    simp [rowSlant]
  · intro t
    have h : (fun v : Fin k → ℝ => slantParam k v t.succ) = fun v => v t := by
      funext v; simp [slantParam, ins]
    rw [h, partialDeriv_coord]
    simp [rowSlant, Fin.succ_ne_zero, Fin.succ_inj]

lemma jacobian_faceParam (c : Fin (k + 1)) (i : Fin k → Fin (k + 1)) (y : Fin k → ℝ) :
    jacobian (faceParam c) i y = Matrix.det (Matrix.of fun r s => rowFace c (i r) s) := by
  unfold jacobian
  congr 1
  ext r s
  exact partialDeriv_faceParam c (i r) s y

lemma jacobian_slantParam (i : Fin k → Fin (k + 1)) (y : Fin k → ℝ) :
    jacobian (slantParam k) i y = Matrix.det (Matrix.of fun r s => rowSlant (i r) s) := by
  unfold jacobian
  congr 1
  ext r s
  exact partialDeriv_slantParam (i r) s y

/-- The determinant of the Jacobian of the coordinate face `faceParam c` along the tuple
`d.succAbove`: it is `1` if `d = c` and `0` otherwise. -/
lemma det_rowFace (c d : Fin (k + 1)) :
    Matrix.det (Matrix.of fun r s => rowFace c (d.succAbove r) s) = if d = c then 1 else 0 := by
  by_cases h : d = c
  · subst h
    rw [if_pos rfl]
    have h1 : (Matrix.of fun (r s : Fin k) => rowFace d (d.succAbove r) s) = 1 := by
      ext r s
      simp [rowFace, Matrix.one_apply, eq_comm]
    rw [h1, Matrix.det_one]
  · rw [if_neg h]
    obtain ⟨r₀, hr₀⟩ := Fin.exists_succAbove_eq (show c ≠ d from fun hh => h hh.symm)
    refine Matrix.det_eq_zero_of_row_eq_zero r₀ ?_
    intro s
    simp [rowFace, hr₀]

/-- The rows of the Jacobian of a face of `Q^{k+1}`, indexed by the deleted vertex, sum to zero
when they come from the slanted face. -/
lemma sum_rowSlant (k : ℕ) : ∑ m : Fin (k + 1), (rowSlant (k := k) m) = 0 := by
  funext s
  rw [Fin.sum_univ_succ]
  simp [rowSlant, Fin.succ_ne_zero, Fin.succ_inj, eq_comm]

/-- If the rows `W m` of a `(k+1) × k` matrix sum to zero, the `k × k` minors obtained by
deleting the `c`-th row alternate in sign. -/
lemma det_succAbove_rows (W : Fin (k + 1) → Fin k → ℝ) (hW : ∑ m, W m = 0) (c : Fin (k + 1)) :
    Matrix.det (Matrix.of fun (r s : Fin k) => W (c.succAbove r) s)
      = (-1 : ℝ) ^ (c : ℕ) * Matrix.det (Matrix.of fun (r s : Fin k) => W r.succ s) := by
  refine Fin.induction ?_ ?_ c
  · simp
  · intro j ih
    set A : Matrix (Fin k) (Fin k) ℝ :=
      Matrix.of fun (r s : Fin k) => W ((Fin.castSucc j).succAbove r) s with hA
    have hsum : ∑ r : Fin k, W ((Fin.castSucc j).succAbove r) = - W (Fin.castSucc j) := by
      have h := Fin.sum_univ_succAbove W (Fin.castSucc j)
      rw [hW] at h
      exact eq_neg_of_add_eq_zero_right h.symm
    have hne : ∀ r : Fin k, r ≠ j → (j.succ).succAbove r = (Fin.castSucc j).succAbove r := by
      intro r hr
      rcases lt_or_gt_of_ne hr with h | h
      · rw [Fin.succAbove_of_castSucc_lt _ _ (lt_trans (Fin.castSucc_lt_castSucc_iff.2 h)
          (Fin.castSucc_lt_succ (i := j))), Fin.succAbove_of_castSucc_lt _ _
          (Fin.castSucc_lt_castSucc_iff.2 h)]
      · rw [Fin.succAbove_of_le_castSucc _ _ (Fin.succ_le_castSucc_iff.2 h),
          Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.2 h.le)]
    have hB : (Matrix.of fun (r s : Fin k) => W ((j.succ).succAbove r) s)
        = A.updateRow j (∑ r : Fin k, (-1 : ℝ) • A r) := by
      ext r s
      by_cases hr : r = j
      · subst hr
        rw [Matrix.updateRow_self]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hA, Matrix.of_apply, neg_one_mul]
        rw [Finset.sum_neg_distrib]
        have h2 : (∑ t : Fin k, W ((Fin.castSucc r).succAbove t) s) = - W (Fin.castSucc r) s := by
          have := congrFun hsum s
          simpa using this
        rw [h2, neg_neg, Fin.succAbove_succ_self]
      · rw [Matrix.updateRow_ne hr]
        simp [hA, hne r hr]
    rw [hB, Matrix.det_updateRow_sum]
    simp only [smul_eq_mul]
    rw [ih]
    simp [Fin.val_succ, pow_succ]

/-- The determinant of the Jacobian of the slanted face along the tuple `c.succAbove`. -/
lemma det_rowSlant (c : Fin (k + 1)) :
    Matrix.det (Matrix.of fun (r s : Fin k) => rowSlant (c.succAbove r) s)
      = (-1 : ℝ) ^ (c : ℕ) := by
  rw [det_succAbove_rows _ (sum_rowSlant k) c]
  have h1 : (Matrix.of fun (r s : Fin k) => rowSlant r.succ s) = 1 := by
    ext r s
    simp [rowSlant, Fin.succ_ne_zero, Fin.succ_inj, Matrix.one_apply]
  rw [h1, Matrix.det_one, mul_one]

/-! ### Splitting a sum of Jacobians over index tuples -/

/-- A sum over all index tuples of a coefficient times the determinant of the corresponding
rows splits, according to the index missed by the tuple, into a sum over the coordinate
directions of an alternating sum of coefficients times a fixed determinant. -/
lemma exists_succAbove_perm {i : Fin k → Fin (k + 1)} (hi : Function.Injective i) :
    ∃ (c : Fin (k + 1)) (τ : Equiv.Perm (Fin k)), i = fun r => c.succAbove (τ r) := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : Fin (k + 1), c ∉ Finset.univ.image i := by
    by_contra h
    push_neg at h
    have hsub : (Finset.univ : Finset (Fin (k + 1))) ⊆ Finset.univ.image i := fun x _ => h x
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hi] at hcard
    simp at hcard
  have hcne : ∀ r, i r ≠ c := fun r hr => hc (Finset.mem_image.2 ⟨r, Finset.mem_univ _, hr⟩)
  choose t ht using fun r => Fin.exists_succAbove_eq (hcne r)
  have htinj : Function.Injective t := by
    intro r r' h
    apply hi
    rw [← ht r, ← ht r', h]
  exact ⟨c, Equiv.ofBijective t (Finite.injective_iff_bijective.1 htinj),
    funext fun r => (ht r).symm⟩

lemma sum_det_split (W : Fin (k + 1) → Fin k → ℝ) (g : (Fin k → Fin (k + 1)) → ℝ) :
    ∑ i : Fin k → Fin (k + 1), g i * Matrix.det (Matrix.of fun r s => W (i r) s)
      = ∑ c : Fin (k + 1),
          (∑ τ : Equiv.Perm (Fin k), ((Equiv.Perm.sign τ : ℤ) : ℝ) * g fun r => c.succAbove (τ r))
            * Matrix.det (Matrix.of fun r s => W (c.succAbove r) s) := by
  classical
  have hdet : ∀ (c : Fin (k + 1)) (τ : Equiv.Perm (Fin k)),
      Matrix.det (Matrix.of fun (r s : Fin k) => W (c.succAbove (τ r)) s)
        = ((Equiv.Perm.sign τ : ℤ) : ℝ)
            * Matrix.det (Matrix.of fun r s => W (c.succAbove r) s) := by
    intro c τ
    have := Matrix.det_permute τ (Matrix.of fun (r s : Fin k) => W (c.succAbove r) s)
    simpa [Matrix.submatrix] using this
  set e : Fin (k + 1) × Equiv.Perm (Fin k) → (Fin k → Fin (k + 1)) :=
    fun p r => p.1.succAbove (p.2 r) with he
  have hinj : Set.InjOn e (Finset.univ : Finset (Fin (k + 1) × Equiv.Perm (Fin k))) := by
    rintro ⟨c, τ⟩ - ⟨c', τ'⟩ - h
    have hcc : c = c' := by
      by_contra hcc
      obtain ⟨r₀, hr₀⟩ := Fin.exists_succAbove_eq (show c ≠ c' from hcc)
      have hval := congrFun h (τ'.symm r₀)
      simp only [he, Equiv.apply_symm_apply] at hval
      rw [hr₀] at hval
      exact Fin.succAbove_ne c _ hval
    subst hcc
    have hτ : ∀ r, τ r = τ' r := by
      intro r
      have := congrFun h r
      simp only [he] at this
      exact Fin.succAbove_right_injective this
    exact Prod.ext rfl (Equiv.ext hτ)
  have hzero : ∀ i : (Fin k → Fin (k + 1)), i ∈ (Finset.univ : Finset (Fin k → Fin (k + 1))) →
      i ∉ e '' (Finset.univ : Finset (Fin (k + 1) × Equiv.Perm (Fin k))) →
      g i * Matrix.det (Matrix.of fun r s => W (i r) s) = 0 := by
    intro i _ hi
    have hni : ¬ Function.Injective i := by
      intro hinj'
      obtain ⟨c, τ, hct⟩ := exists_succAbove_perm hinj'
      exact hi ⟨(c, τ), by simp, hct.symm⟩
    rw [Function.not_injective_iff] at hni
    obtain ⟨r, r', hrr, hne⟩ := hni
    have hd : Matrix.det (Matrix.of fun (r s : Fin k) => W (i r) s) = 0 := by
      refine Matrix.det_zero_of_row_eq hne ?_
      funext s
      simp [hrr]
    rw [hd, mul_zero]
  have hmain := Finset.sum_of_injOn (f := fun p : Fin (k + 1) × Equiv.Perm (Fin k) =>
      g (e p) * Matrix.det (Matrix.of fun r s => W (e p r) s))
    (g := fun i : Fin k → Fin (k + 1) => g i * Matrix.det (Matrix.of fun r s => W (i r) s))
    e hinj (fun p _ => Finset.mem_univ _) hzero (fun p _ => rfl)
  rw [← hmain, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [he]
  rw [hdet c τ]
  ring

/-! ### The reparametrization of the slanted face -/

/-- The rows of the linear part of the reparametrization `reparam c`. -/
def rowRep (c m : Fin (k + 1)) (s : Fin k) : ℝ :=
  if m = c then -1 else if m = c.succAbove s then 1 else 0

lemma sum_rowRep (k : ℕ) (c : Fin (k + 1)) : ∑ m : Fin (k + 1), (rowRep (k := k) c m) = 0 := by
  funext s
  rw [Fin.sum_univ_succAbove _ c]
  simp [rowRep, Fin.succAbove_ne c, eq_comm]

/-- The determinant of the linear part of `reparam c` is `±1`. -/
lemma det_rowRep_succ (k : ℕ) (c : Fin (k + 1)) :
    Matrix.det (Matrix.of fun (r s : Fin k) => rowRep c r.succ s) = (-1 : ℝ) ^ (c : ℕ) := by
  have h := det_succAbove_rows (k := k) (rowRep c) (sum_rowRep k c) c
  have h1 : Matrix.det (Matrix.of fun (r s : Fin k) => rowRep c (c.succAbove r) s) = 1 := by
    have h2 : (Matrix.of fun (r s : Fin k) => rowRep c (c.succAbove r) s) = 1 := by
      ext r s
      simp [rowRep, Matrix.one_apply, eq_comm]
    rw [h2, Matrix.det_one]
  rw [h1] at h
  have hsq : ((-1 : ℝ) ^ (c : ℕ)) * ((-1 : ℝ) ^ (c : ℕ)) = 1 := by rw [← mul_pow]; norm_num
  have h3 := congrArg (fun z : ℝ => (-1 : ℝ) ^ (c : ℕ) * z) h
  simp only [mul_one] at h3
  rw [← mul_assoc, hsq, one_mul] at h3
  exact h3.symm

lemma reparam_eq_affine (k : ℕ) (c : Fin (k + 1)) :
    reparam c = fun y => Matrix.toLin' (Matrix.of fun (r s : Fin k) => rowRep c r.succ s) y
      + (fun r => if r.succ = c then (1 : ℝ) else 0) := by
  funext y r
  simp only [reparam, Pi.add_apply, Matrix.toLin'_apply, Matrix.mulVec, Matrix.of_apply,
    dotProduct]
  by_cases hr : r.succ = c
  · rw [hr]
    simp only [ins_same, rowRep]
    simp
    rw [← Finset.sum_neg_distrib]
    ring_nf
    rw [Finset.sum_neg_distrib]
    ring
  · obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq (show r.succ ≠ c from hr)
    rw [← ht, ins_succAbove, if_neg (Fin.succAbove_ne c t), add_zero]
    rw [Finset.sum_eq_single t]
    · simp [rowRep, Fin.succAbove_ne c t]
    · intro s _ hs
      have hts : ¬ (c.succAbove t = c.succAbove s) := fun h =>
        hs (Fin.succAbove_right_injective h).symm
      simp [rowRep, Fin.succAbove_ne c t, hts]
    · intro h
      exact absurd (Finset.mem_univ t) h

lemma slantParam_reparam (c : Fin (k + 1)) (y : Fin k → ℝ) :
    slantParam k (reparam c y) = ins c (1 - ∑ s, y s) y := by
  have hsum : ∑ m, ins c (1 - ∑ s, y s) y m = 1 := by rw [ins_sum]; ring
  funext m
  refine Fin.cases ?_ ?_ m
  · simp only [slantParam, reparam, ins_same]
    have h := Fin.sum_univ_succ (fun m => ins c (1 - ∑ s, y s) y m)
    rw [hsum] at h
    linarith [h]
  · intro t
    simp [slantParam, reparam, ins]

lemma measurePreserving_reparam (c : Fin (k + 1)) :
    MeasurePreserving (reparam (k := k) c) volume volume := by
  set A : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun (r s : Fin k) => rowRep c r.succ s with hA
  have hAdet : |A.det| = 1 := by
    rw [hA, det_rowRep_succ k c, abs_pow, abs_neg, abs_one, one_pow]
  have hdet : LinearMap.det (Matrix.toLin' A) = A.det := LinearMap.det_toLin' A
  have hne : LinearMap.det (Matrix.toLin' A) ≠ 0 := by
    rw [hdet]
    intro h
    rw [h] at hAdet
    simp at hAdet
  have habs : |(LinearMap.det (Matrix.toLin' A))⁻¹| = 1 := by
    rw [abs_inv, hdet, hAdet, inv_one]
  have hmapL : Measure.map (Matrix.toLin' A : (Fin k → ℝ) → (Fin k → ℝ)) volume = volume := by
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hne, habs]
    simp
  have hmp : MeasurePreserving (Matrix.toLin' A : (Fin k → ℝ) → (Fin k → ℝ)) volume volume :=
    ⟨(Matrix.toLin' A).continuous_of_finiteDimensional.measurable, hmapL⟩
  rw [reparam_eq_affine k c]
  exact (measurePreserving_add_right volume (fun r => if r.succ = c then (1 : ℝ) else 0)).comp hmp

lemma continuous_reparam (c : Fin (k + 1)) : Continuous (reparam (k := k) c) := by
  refine continuous_pi fun r => ?_
  exact (continuous_apply r.succ).comp ((continuous_ins c).comp
    (Continuous.prodMk (by fun_prop) continuous_id))

lemma injective_reparam (c : Fin (k + 1)) : Function.Injective (reparam (k := k) c) := by
  intro y y' h
  have h2 := congrArg (slantParam k) h
  rw [slantParam_reparam c y, slantParam_reparam c y'] at h2
  funext s
  have := congrFun h2 (c.succAbove s)
  simpa using this

lemma reparam_preimage_stdSimplex (c : Fin (k + 1)) :
    reparam (k := k) c ⁻¹' stdSimplex k = stdSimplex k := by
  ext y
  set G := ins c (1 - ∑ s, y s) y with hG
  have hsum : ∑ m, G m = 1 := by rw [hG, ins_sum]; ring
  have hsplit : ∑ r : Fin k, G r.succ = 1 - G 0 := by
    have h := Fin.sum_univ_succ G
    rw [hsum] at h
    linarith
  have hrep : ∀ r : Fin k, reparam c y r = G r.succ := fun r => rfl
  constructor
  · rintro ⟨hpos, hle⟩
    simp only [hrep] at hpos hle
    have h0 : 0 ≤ G 0 := by rw [hsplit] at hle; linarith
    have hall : ∀ m, 0 ≤ G m := fun m => Fin.cases h0 (fun t => hpos t) m
    refine ⟨fun s => ?_, ?_⟩
    · have := hall (c.succAbove s)
      rwa [hG, ins_succAbove] at this
    · have := hall c
      rw [hG, ins_same] at this
      linarith
  · rintro ⟨hy, hyle⟩
    have hall : ∀ m, 0 ≤ G m := by
      intro m
      refine Fin.succAboveCases c ?_ ?_ m
      · rw [hG, ins_same]; linarith
      · intro s
        rw [hG, ins_succAbove]
        exact hy s
    refine ⟨fun r => ?_, ?_⟩
    · rw [hrep]
      exact hall r.succ
    · simp only [hrep]
      rw [hsplit]
      linarith [hall 0]

/-- Changing the parametrization of the slanted face does not change the integral. -/
lemma setIntegral_slant_reparam (c : Fin (k + 1)) (f : (Fin (k + 1) → ℝ) → ℝ) :
    ∫ y in stdSimplex k, f (ins c (1 - ∑ s, y s) y) = ∫ y in stdSimplex k, f (slantParam k y) := by
  have hemb : MeasurableEmbedding (reparam (k := k) c) :=
    (continuous_reparam c).measurableEmbedding (injective_reparam c)
  have h := (measurePreserving_reparam (k := k) c).setIntegral_preimage_emb hemb
    (fun x => f (slantParam k x)) (stdSimplex k)
  rw [reparam_preimage_stdSimplex c] at h
  simp only [slantParam_reparam] at h
  exact h

/-! ### The alternation of the coefficients along a coordinate direction -/

lemma contDiff_altCoeff {n : ℕ} {ω : KForm k n} (hω : ∀ i, ContDiff ℝ 1 (ω.coeff i))
    (i : Fin k → Fin n) : ContDiff ℝ 1 (altCoeff ω i) := by
  unfold altCoeff
  exact ContDiff.sum fun σ _ => ContDiff.mul contDiff_const (hω _)

lemma partialDeriv_altCoeff {n : ℕ} {ω : KForm k n} (hω : ∀ i, ContDiff ℝ 1 (ω.coeff i))
    (i : Fin k → Fin n) (s : Fin n) (x : Fin n → ℝ) :
    partialDeriv (altCoeff ω i) s x
      = ∑ σ : Equiv.Perm (Fin k), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          partialDeriv (ω.coeff fun r => i (σ r)) s x := by
  unfold partialDeriv altCoeff
  rw [fderiv_fun_sum (fun σ _ =>
    (((hω (fun r => i (σ r))).differentiable (by norm_num)).differentiableAt).const_mul _)]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [fderiv_const_mul (((hω (fun r => i (σ r))).differentiable (by norm_num)).differentiableAt)]
  simp

/-! ### The integrands on the faces -/

/-- On the coordinate face `x_c = 0` the integrand of a `k`-form is the alternation `A_c`. -/
lemma sum_coeff_jacobian_faceParam (ω : KForm k (k + 1)) (c : Fin (k + 1)) (y : Fin k → ℝ) :
    ∑ i : Fin k → Fin (k + 1), ω.coeff i (faceParam c y) * jacobian (faceParam c) i y
      = altCoeff ω (fun r => c.succAbove r) (faceParam c y) := by
  simp only [jacobian_faceParam]
  rw [sum_det_split (rowFace c) (fun i => ω.coeff i (faceParam c y))]
  rw [Finset.sum_eq_single c]
  · rw [det_rowFace c c, if_pos rfl, mul_one, altCoeff]
  · intro d _ hd
    rw [det_rowFace c d, if_neg hd, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ c) h

/-- On the slanted face the integrand of a `k`-form is the alternating sum of the `A_c`. -/
lemma sum_coeff_jacobian_slantParam (ω : KForm k (k + 1)) (y : Fin k → ℝ) :
    ∑ i : Fin k → Fin (k + 1), ω.coeff i (slantParam k y) * jacobian (slantParam k) i y
      = ∑ c : Fin (k + 1), (-1 : ℝ) ^ (c : ℕ)
          * altCoeff ω (fun r => c.succAbove r) (slantParam k y) := by
  simp only [jacobian_slantParam]
  rw [sum_det_split rowSlant (fun i => ω.coeff i (slantParam k y))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [det_rowSlant c, altCoeff]
  ring

lemma continuous_slantParam (k : ℕ) : Continuous (slantParam k) :=
  (continuous_ins 0).comp (Continuous.prodMk (by fun_prop) continuous_id)

lemma continuous_faceParam (c : Fin (k + 1)) : Continuous (faceParam (k := k) c) :=
  (continuous_ins c).comp (Continuous.prodMk continuous_const continuous_id)

lemma integrableOn_stdSimplex {f : (Fin k → ℝ) → ℝ} (hf : Continuous f) :
    IntegrableOn f (stdSimplex k) volume :=
  hf.continuousOn.integrableOn_compact (isCompact_stdSimplex k)

lemma integralOverSimplex_map {n : ℕ} (ω : KForm k n) (Φ : SimplexSurface k n)
    (f : (Fin k → ℝ) → (Fin n → ℝ)) (h : Φ.map = f) :
    integralOverSimplex ω Φ
      = ∫ u in stdSimplex k, ∑ i : Fin k → Fin n, ω.coeff i (f u) * jacobian f i u := by
  rw [integralOverSimplex, h]

/-! ### Stokes' formula on the simplex -/

/-- The left-hand side of Stokes' formula on `Q^{k+1}`: after splitting the signed sum over
`S_{k+1}` by the image of `0` and applying the fundamental theorem of calculus in each
coordinate direction, it becomes an alternating sum of integrals over the faces. -/
lemma integral_extDeriv_identity_simplex (k : ℕ) (ω : KForm k (k + 1))
    (hω : ∀ i, ContDiff ℝ 1 (ω.coeff i)) :
    integralOverSimplex (extDeriv ω) ⟨id⟩
      = ∑ c : Fin (k + 1), (-1 : ℝ) ^ (c : ℕ) *
          ((∫ y in stdSimplex k, altCoeff ω (fun r => c.succAbove r) (slantParam k y))
            - ∫ y in stdSimplex k, altCoeff ω (fun r => c.succAbove r) (faceParam c y)) := by
  set A : Fin (k + 1) → (Fin (k + 1) → ℝ) → ℝ :=
    fun c => altCoeff ω (fun r => c.succAbove r) with hA
  have hAc : ∀ c, ContDiff ℝ 1 (A c) := fun c => contDiff_altCoeff hω _
  have hpt : ∀ u : Fin (k + 1) → ℝ,
      ∑ σ : Equiv.Perm (Fin (k + 1)), ((Equiv.Perm.sign σ : ℤ) : ℝ) * (extDeriv ω).coeff (⇑σ) u
        = ∑ c : Fin (k + 1), (-1 : ℝ) ^ (c : ℕ) * partialDeriv (A c) c u := by
    intro u
    have hcoeff : ∀ σ : Equiv.Perm (Fin (k + 1)),
        (extDeriv ω).coeff (⇑σ) u
          = partialDeriv (ω.coeff fun r => σ r.succ) (σ 0) u := fun σ => rfl
    simp only [hcoeff]
    rw [sum_perm_succ_split (fun (r : Fin (k + 1)) (i : Fin k → Fin (k + 1)) =>
      partialDeriv (ω.coeff i) r u)]
    exact Finset.sum_congr rfl fun c _ => by rw [hA, partialDeriv_altCoeff hω _ c u]
  rw [integralOverSimplex_id (extDeriv ω)]
  simp only [hpt]
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [integral_const_mul, integral_partialDeriv_stdSimplex (hAc c) c]
    congr 1
    rw [integral_sub]
    · congr 1
      exact setIntegral_slant_reparam c (A c)
    · exact integrableOn_stdSimplex (((hAc c).continuous).comp
        ((continuous_ins c).comp (Continuous.prodMk (by fun_prop) continuous_id)))
    · exact integrableOn_stdSimplex (((hAc c).continuous).comp (continuous_faceParam c))
  · intro c _
    exact integrableOn_stdSimplex (continuous_const.mul (continuous_partialDeriv (hAc c) c))

/-- The right-hand side of Stokes' formula on `Q^{k+1}`: the boundary of the identity surface
consists of the slanted face and the `k + 1` coordinate faces, and the Jacobian bookkeeping
identifies the integrands as the alternations of the coefficients. -/
lemma integral_boundary_identity_simplex (k : ℕ) (ω : KForm k (k + 1))
    (hω : ∀ i, ContDiff ℝ 1 (ω.coeff i)) :
    Chain.integral ω (surfaceBoundary (⟨id⟩ : SimplexSurface (k + 1) (k + 1)))
      = (∑ c : Fin (k + 1), (-1 : ℝ) ^ (c : ℕ) *
            ∫ y in stdSimplex k, altCoeff ω (fun r => c.succAbove r) (slantParam k y))
        + ∑ c : Fin (k + 1), (-1 : ℝ) ^ ((c : ℕ) + 1) *
            ∫ y in stdSimplex k, altCoeff ω (fun r => c.succAbove r) (faceParam c y) := by
  have hchain : Chain.integral ω (surfaceBoundary (⟨id⟩ : SimplexSurface (k + 1) (k + 1)))
      = ∑ j : Fin (k + 2), ((-1 : ℝ)) ^ (j : ℕ) *
          integralOverSimplex ω (boundaryFace (id : (Fin (k + 1) → ℝ) → (Fin (k + 1) → ℝ)) j) := by
    rw [Chain.integral, surfaceBoundary]
    simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    norm_num
  rw [hchain, Fin.sum_univ_succ]
  congr 1
  · rw [integralOverSimplex_map ω _ (slantParam k) (boundaryFace_id_zero k)]
    simp only [sum_coeff_jacobian_slantParam ω]
    rw [integral_finset_sum]
    · simp only [Fin.val_zero, pow_zero, one_mul]
      exact Finset.sum_congr rfl fun c _ => integral_const_mul _ _
    · intro c _
      exact integrableOn_stdSimplex (continuous_const.mul
        (((contDiff_altCoeff hω (fun r => c.succAbove r)).continuous).comp
          (continuous_slantParam k)))
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [integralOverSimplex_map ω _ (faceParam c) (boundaryFace_id_succ k c)]
    simp only [sum_coeff_jacobian_faceParam ω c]
    norm_num

/-- Rudin, Theorem 10.33 for the identity surface of the standard simplex `Q^{k+1}`. -/
theorem stokes_simplex (k : ℕ) (ω : KForm k (k + 1)) (hω : ∀ i, ContDiff ℝ 1 (ω.coeff i)) :
    integralOverSimplex (extDeriv ω) ⟨id⟩ = Chain.integral ω (surfaceBoundary ⟨id⟩) := by
  rw [integral_extDeriv_identity_simplex k ω hω, integral_boundary_identity_simplex k ω hω,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [pow_succ]
  ring

end StokesSimplex

end Rudin

open Rudin in
/-- Rudin, Theorem 10.33 (Stokes' theorem), the case of the identity surface of the standard
simplex `Q^{k+1}`. -/
theorem solution (k : ℕ) (ω : KForm k (k + 1)) (hω : ∀ i, ContDiff ℝ 1 (ω.coeff i)) :
    integralOverSimplex (extDeriv ω) ⟨id⟩ = Chain.integral ω (surfaceBoundary ⟨id⟩) :=
  Rudin.stokes_simplex k ω hω
