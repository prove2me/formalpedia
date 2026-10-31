-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P17.relativeEntropy_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-30T11:56:15.782304+00:00
-- url     : https://prove2.me/submissions/316ea169-bcde-47e2-aec1-7f266a268a85

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P17
import Theorems.Thm_TroppMatrixConcentration_ch8_entropy_joint_convex

open scoped Matrix.Norms.L2Operator ComplexOrder


noncomputable section

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

namespace P17Sum

open Matrix MatrixOrder

open TroppMatrixConcentration (ch8_relativeEntropy matrixLog)

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Degree-one homogeneity of Tropp's relative entropy on positive definite pairs. -/
lemma ch8_smul {A B : Matrix I I ℂ} (hA : A.PosDef) (hB : B.PosDef) {t : ℝ} (ht : 0 < t) :
    ch8_relativeEntropy (t • A) (t • B) = t * ch8_relativeEntropy A B := by
  have hlA : matrixLog (t • A) = algebraMap ℝ _ (Real.log t) + matrixLog A :=
    CFC.log_smul' A ht hA.isStrictlyPositive
  have hlB : matrixLog (t • B) = algebraMap ℝ _ (Real.log t) + matrixLog B :=
    CFC.log_smul' B ht hB.isStrictlyPositive
  rw [ch8_relativeEntropy, ch8_relativeEntropy, hlA, hlB, add_sub_add_left_eq_sub,
    smul_mul_assoc, ← smul_sub, ← smul_sub, Matrix.trace_smul, Complex.real_smul,
    Complex.re_ofReal_mul]

/-- Reindexing as a star-algebra equivalence. -/
def reindexStar {J : Type*} [Fintype J] [DecidableEq J] (e : I ≃ J) :
    Matrix I I ℂ ≃⋆ₐ[ℂ] Matrix J J ℂ :=
  { Matrix.reindexAlgEquiv ℂ ℂ e with
    map_smul' := fun r A => map_smul (Matrix.reindexAlgEquiv ℂ ℂ e) r A
    map_star' := fun A => by
      simp [Matrix.star_eq_conjTranspose] }

lemma trace_reindex' {J : Type*} [Fintype J] [DecidableEq J] (e : I ≃ J) (M : Matrix I I ℂ) :
    (Matrix.reindex e e M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.diag_apply]
  exact Equiv.sum_comp e.symm (fun i => M i i)

lemma reindexStar_apply {J : Type*} [Fintype J] [DecidableEq J] (e : I ≃ J) (A : Matrix I I ℂ) :
    reindexStar e A = Matrix.reindex e e A := rfl

lemma cfc_reindex {J : Type*} [Fintype J] [DecidableEq J] (e : I ≃ J) (f : ℝ → ℝ)
    {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    cfc f (reindexStar e A) = reindexStar e (cfc f A) := by
  have hfin := Matrix.finite_real_spectrum (A := A)
  have hc : Continuous (reindexStar e) :=
    LinearMap.continuous_of_finiteDimensional
      ((reindexStar e).toAlgEquiv.toLinearEquiv.toLinearMap)
  have hA' : IsSelfAdjoint A := hA
  exact (StarAlgHomClass.map_cfc (S := ℂ) (reindexStar e) f A (hfin.continuousOn _) hc hA'
    (hA'.map _)).symm

lemma ch8_reindex {J : Type*} [Fintype J] [DecidableEq J] (e : I ≃ J) {A B : Matrix I I ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ch8_relativeEntropy (reindexStar e A) (reindexStar e B) = ch8_relativeEntropy A B := by
  rw [ch8_relativeEntropy, ch8_relativeEntropy, matrixLog, matrixLog, cfc_reindex e _ hA,
    cfc_reindex e _ hB, ← map_sub, ← map_mul, ← map_sub, ← map_sub, reindexStar_apply,
    trace_reindex']
  rfl

lemma posDef_reindex {J : Type*} [Fintype J] [DecidableEq J] (e : I ≃ J) {A : Matrix I I ℂ}
    (hA : A.PosDef) : (reindexStar e A).PosDef := by
  rw [reindexStar_apply, Matrix.reindex_apply]; exact hA.submatrix e.symm.injective

lemma posDef_sum {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {A : ι → Matrix I I ℂ}
    (hA : ∀ i ∈ s, (A i).PosDef) : (∑ i ∈ s, A i).PosDef := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simpa using hA a (by simp)
  | cons a t hat ht ih =>
    rw [Finset.sum_cons]
    exact (hA a (by simp)).add_posSemidef
      (ih (fun i hi => hA i (by simp [hi]))).posSemidef

/-- Subadditivity of Tropp's relative entropy over positive definite families. -/
theorem ch8_sum_le {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (A B : ι → Matrix I I ℂ)
    (hA : ∀ i ∈ s, (A i).PosDef) (hB : ∀ i ∈ s, (B i).PosDef) :
    ch8_relativeEntropy (∑ i ∈ s, A i) (∑ i ∈ s, B i) ≤
      ∑ i ∈ s, ch8_relativeEntropy (A i) (B i) := by
  rcases isEmpty_or_nonempty I with hI | hI
  · simp [ch8_relativeEntropy, Matrix.trace]
  have : NeZero (Fintype.card I) := ⟨Fintype.card_ne_zero⟩
  set e := Fintype.equivFin I
  set n : ℝ := (s.card : ℝ)
  have hn : 0 < n := by simp [n, hs.card_pos]
  have key := (TroppMatrixConcentration.ch8_entropy_joint_convex
      (d := Fintype.card I)).map_sum_le
    (t := s) (w := fun _ => (1 / n : ℝ))
    (p := fun i => (reindexStar e (A i), reindexStar e (B i)))
    (fun _ _ => by positivity)
    (by simp [n, Finset.sum_const]; field_simp)
    (fun i hi => ⟨posDef_reindex e (hA i hi), posDef_reindex e (hB i hi)⟩)
  simp only [Prod.smul_mk] at key
  rw [Prod.fst_sum, Prod.snd_sum] at key
  simp only [← Finset.smul_sum, ← map_sum] at key
  rw [ch8_smul (posDef_reindex e (posDef_sum hs hA)) (posDef_reindex e (posDef_sum hs hB))
    (by positivity), ch8_reindex e (posDef_sum hs hA).1 (posDef_sum hs hB).1] at key
  simp only [smul_eq_mul] at key
  have : ∀ i ∈ s, ch8_relativeEntropy (reindexStar e (A i)) (reindexStar e (B i)) =
      ch8_relativeEntropy (A i) (B i) := fun i hi => ch8_reindex e (hA i hi).1 (hB i hi).1
  rw [Finset.sum_congr rfl this] at key
  have := mul_le_mul_of_nonneg_left key hn.le
  rwa [← mul_assoc, ← mul_assoc, mul_one_div_cancel hn.ne', one_mul, one_mul] at this


/-! ### Part 2: from positive definite to supported positive semidefinite pairs -/

open Filter Topology QAlgorithms.Papers.Independent.Dependency50.P21

/-- The finite Umegaki expression. -/
def Dfin (A B : Matrix I I ℂ) : ℝ :=
  (cfc (fun x : ℝ => x * Real.log x) A - A * cfc Real.log B).trace.re

lemma cfc_xlogx {X : Matrix I I ℂ} (hX : X.IsHermitian) :
    cfc (fun x : ℝ => x * Real.log x) X = X * cfc Real.log X := by
  have hfin := Matrix.finite_real_spectrum (A := X)
  have hsa : IsSelfAdjoint X := hX
  rw [cfc_mul (fun x : ℝ => x) Real.log X (hfin.continuousOn _) (hfin.continuousOn _),
    cfc_id' ℝ X]

lemma Dfin_eq_ch8 {A B : Matrix I I ℂ} (hA : A.IsHermitian) :
    Dfin A B = ch8_relativeEntropy A B + A.trace.re - B.trace.re := by
  rw [Dfin, ch8_relativeEntropy, cfc_xlogx hA, matrixLog, matrixLog]
  simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  ring

theorem Dfin_sum_le_posDef {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (A B : ι → Matrix I I ℂ)
    (hA : ∀ i ∈ s, (A i).PosDef) (hB : ∀ i ∈ s, (B i).PosDef) :
    Dfin (∑ i ∈ s, A i) (∑ i ∈ s, B i) ≤ ∑ i ∈ s, Dfin (A i) (B i) := by
  rw [Dfin_eq_ch8 (posDef_sum hs hA).1, Finset.sum_congr rfl fun i hi => Dfin_eq_ch8 (hA i hi).1]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Matrix.trace_sum, Complex.re_sum]
  linarith [ch8_sum_le s hs A B hA hB]

lemma traceCfc {A : Matrix I I ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, ((f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [hA.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, trace_diagonal]
  rfl

lemma trace_mul_cfc (A : Matrix I I ℂ) {B : Matrix I I ℂ} (hB : B.IsHermitian) (f : ℝ → ℝ) :
    (A * cfc f B).trace = ∑ j, ((hB.eigenvectorUnitary : Matrix I I ℂ)ᴴ * A *
      (hB.eigenvectorUnitary : Matrix I I ℂ)) j j * ((f (hB.eigenvalues j) : ℝ) : ℂ) := by
  rw [hB.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_comm,
    Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.star_eq_conjTranspose]
  simp only [← Matrix.mul_assoc]
  simp [Matrix.trace, Matrix.mul_diagonal]

lemma cfc_shift {X : Matrix I I ℂ} (hX : X.IsHermitian) (f : ℝ → ℝ) (ε : ℝ) :
    cfc f (X + algebraMap ℝ _ ε) = cfc (fun x => f (x + ε)) X := by
  have hfin := Matrix.finite_real_spectrum (A := X)
  have hsa : IsSelfAdjoint X := hX
  have e : X + algebraMap ℝ _ ε = cfc (fun x : ℝ => x + ε) X := by
    rw [cfc_add_const ε (fun x : ℝ => x) X, cfc_id' ℝ X]
  rw [e, ← cfc_comp' f (fun x : ℝ => x + ε) X
    (Set.Finite.continuousOn (hfin.image _) _) (hfin.continuousOn _)]

lemma diag_zero_of_supported {A B : Matrix I I ℂ} (hB : B.IsHermitian) (hAB : IsSupported A B)
    (j : I) (hj : hB.eigenvalues j = 0) :
    ((hB.eigenvectorUnitary : Matrix I I ℂ)ᴴ * A * (hB.eigenvectorUnitary : Matrix I I ℂ)) j j
      = 0 := by
  have hBv : B *ᵥ ⇑(hB.eigenvectorBasis j) = 0 := by
    rw [hB.mulVec_eigenvectorBasis j, hj, zero_smul]
  have hAv : A *ᵥ ⇑(hB.eigenvectorBasis j) = 0 := by
    have := hAB (show ⇑(hB.eigenvectorBasis j) ∈ LinearMap.ker B.mulVecLin from hBv)
    exact this
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  have hk : (A * (hB.eigenvectorUnitary : Matrix I I ℂ)) k j = 0 := by
    have := congrFun hAv k
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct,
      IsHermitian.eigenvectorUnitary_apply] using this
  rw [hk, mul_zero]

theorem tendsto_Dfin {A B : Matrix I I ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hAB : IsSupported A B) :
    Tendsto (fun ε : ℝ => Dfin (A + algebraMap ℝ _ ε) (B + algebraMap ℝ _ ε)) (𝓝[>] 0)
      (𝓝 (Dfin A B)) := by
  set U := (hB.1.eigenvectorUnitary : Matrix I I ℂ)
  set c : I → ℝ := fun j => ((Uᴴ * A * U) j j).re with hcdef
  set lam := hA.1.eigenvalues
  set bet := hB.1.eigenvalues
  have hc : ∀ j, bet j = 0 → c j = 0 := fun j hj => by
    simp [hcdef, U, diag_zero_of_supported hB.1 hAB j hj]
  have hform : ∀ ε : ℝ, Dfin (A + algebraMap ℝ _ ε) (B + algebraMap ℝ _ ε) =
      (∑ i, (lam i + ε) * Real.log (lam i + ε)) - (∑ j, c j * Real.log (bet j + ε))
        - ε * ∑ j, Real.log (bet j + ε) := by
    intro ε
    rw [Dfin, cfc_shift hA.1, cfc_shift hB.1, Matrix.add_mul, Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mul, Matrix.one_mul, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul,
      traceCfc hA.1, trace_mul_cfc A hB.1, traceCfc hB.1]
    simp only [Complex.sub_re, Complex.add_re, Complex.re_sum, Complex.real_smul,
      Complex.re_ofReal_mul, Complex.ofReal_re, Complex.re_mul_ofReal, Finset.mul_sum]
    simp [hcdef, U, lam, bet, mul_comm]
    ring
  have h0 : Dfin A B = (∑ i, lam i * Real.log (lam i)) - (∑ j, c j * Real.log (bet j))
      - 0 * ∑ j, Real.log (bet j + 0) := by
    have := hform 0
    simp only [map_zero, add_zero] at this
    rw [this]; ring
  rw [h0]
  simp_rw [hform]
  have hlin : ∀ a : ℝ, Tendsto (fun ε : ℝ => a + ε) (𝓝[>] 0) (𝓝 a) := fun a => by
    have := (tendsto_const_nhds (x := a)).add (tendsto_id (x := 𝓝 (0 : ℝ)))
    simpa using this.mono_left nhdsWithin_le_nhds
  have key : ∀ j, Tendsto (fun ε : ℝ => ε * Real.log (bet j + ε)) (𝓝[>] 0) (𝓝 0) := by
    intro j
    by_cases hj : bet j = 0
    · simp only [hj, zero_add]
      have h := Real.continuous_mul_log.tendsto 0
      simp only [zero_mul] at h
      exact h.mono_left nhdsWithin_le_nhds
    · have h := (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto id (𝓝[>] (0 : ℝ)) (𝓝 0)).mul
        ((Real.continuousAt_log hj).tendsto.comp (hlin (bet j)))
      simpa using h
  refine ((tendsto_finsetSum _ fun i _ => ?_).sub (tendsto_finsetSum _ fun j _ => ?_)).sub ?_
  · exact (Real.continuous_mul_log.tendsto (lam i)).comp (hlin _)
  · by_cases hj : bet j = 0
    · simp [hc j hj]
    · exact ((Real.continuousAt_log hj).tendsto.comp (hlin _)).const_mul (c j)
  · rw [zero_mul]
    simp_rw [Finset.mul_sum]
    simpa using tendsto_finsetSum Finset.univ (fun j _ => key j)

lemma psd_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix I I ℂ) (hA : ∀ i ∈ s, (A i).PosSemidef) :
    (∑ i ∈ s, A i).PosSemidef :=
  (Finset.sum_nonneg fun i hi => (hA i hi).nonneg).posSemidef

lemma supported_sum {ι : Type*} (s : Finset ι) (A B : ι → Matrix I I ℂ)
    (hB : ∀ i ∈ s, (B i).PosSemidef) (hAB : ∀ i ∈ s, IsSupported (A i) (B i)) :
    IsSupported (∑ i ∈ s, A i) (∑ i ∈ s, B i) := by
  intro v hv
  have hv' : (∑ i ∈ s, B i) *ᵥ v = 0 := hv
  show (∑ i ∈ s, A i) *ᵥ v = 0
  have hsum : ∑ i ∈ s, star v ⬝ᵥ (B i *ᵥ v) = 0 := by
    rw [← dotProduct_sum, ← Matrix.sum_mulVec, hv', dotProduct_zero]
  have hnn : ∀ i ∈ s, 0 ≤ star v ⬝ᵥ (B i *ᵥ v) := fun i hi => (hB i hi).dotProduct_mulVec_nonneg v
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hBi : B i *ᵥ v = 0 := ((hB i hi).dotProduct_mulVec_zero_iff v).1 (hz i hi)
  exact hAB i hi (show v ∈ LinearMap.ker (B i).mulVecLin from hBi)

lemma ereal_coe_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

theorem sum_main {ι : Type*} (s : Finset ι) (A B : ι → Matrix I I ℂ)
    (hA : ∀ i ∈ s, (A i).PosSemidef) (hB : ∀ i ∈ s, (B i).PosSemidef)
    (hAB : ∀ i ∈ s, IsSupported (A i) (B i)) :
    relativeEntropy (∑ i ∈ s, A i) (∑ i ∈ s, B i) ≤ ∑ i ∈ s, relativeEntropy (A i) (B i) := by
  have hsupp := supported_sum s A B hB hAB
  have hcoe : ∀ X Y : Matrix I I ℂ, IsSupported X Y → relativeEntropy X Y = (Dfin X Y : EReal) :=
    fun X Y h => by simp only [relativeEntropy, if_pos h, Dfin]
  rw [hcoe _ _ hsupp, Finset.sum_congr rfl (fun i hi => hcoe _ _ (hAB i hi)),
    ← ereal_coe_sum, EReal.coe_le_coe_iff]
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [Dfin]
  set n : ℝ := (s.card : ℝ)
  have hn : 0 < n := by simp [n, hs.card_pos]
  have hpd : ∀ ε : ℝ, 0 < ε → ∀ X : Matrix I I ℂ, X.PosSemidef →
      (X + algebraMap ℝ _ ε).PosDef := fun ε hε X hX => by
    rw [add_comm]; exact (isStrictlyPositive_algebraMap hε).posDef.add_posSemidef hX
  have hineq : ∀ ε ∈ Set.Ioi (0 : ℝ),
      Dfin ((∑ i ∈ s, A i) + algebraMap ℝ _ (n * ε)) ((∑ i ∈ s, B i) + algebraMap ℝ _ (n * ε)) ≤
        ∑ i ∈ s, Dfin (A i + algebraMap ℝ _ ε) (B i + algebraMap ℝ _ ε) := by
    intro ε hε
    have h := Dfin_sum_le_posDef s hs (fun i => A i + algebraMap ℝ _ ε)
      (fun i => B i + algebraMap ℝ _ ε) (fun i hi => hpd ε hε _ (hA i hi))
      (fun i hi => hpd ε hε _ (hB i hi))
    have e : ∀ C : ι → Matrix I I ℂ, ∑ i ∈ s, (C i + algebraMap ℝ _ ε) =
        (∑ i ∈ s, C i) + algebraMap ℝ _ (n * ε) := fun C => by
      rw [Finset.sum_add_distrib, Finset.sum_const, ← map_nsmul, nsmul_eq_mul]
    simp only [e] at h
    exact h
  have hscale : Tendsto (fun ε : ℝ => n * ε) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun ε hε =>
      mul_pos hn hε⟩
    have h0 : Tendsto (fun ε : ℝ => n * ε) (𝓝 0) (𝓝 (n * 0)) := (continuous_mul_left n).tendsto 0
    rw [mul_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hL := (tendsto_Dfin (psd_sum s A hA) (psd_sum s B hB) hsupp).comp hscale
  have hR := tendsto_finsetSum s (fun i hi => tendsto_Dfin (hA i hi) (hB i hi) (hAB i hi))
  exact le_of_tendsto_of_tendsto hL hR (eventually_nhdsWithin_of_forall hineq)

end P17Sum

open QAlgorithms.Papers.Independent.Dependency50.P21 (IsSupported relativeEntropy) in
theorem solution {I ι : Type*} [Fintype I] [DecidableEq I] (s : Finset ι)
    (A B : ι → Matrix I I ℂ) (hA : ∀ i ∈ s, (A i).PosSemidef) (hB : ∀ i ∈ s, (B i).PosSemidef)
    (hAB : ∀ i ∈ s, IsSupported (A i) (B i)) :
    relativeEntropy (∑ i ∈ s, A i) (∑ i ∈ s, B i) ≤ ∑ i ∈ s, relativeEntropy (A i) (B i) :=
  P17Sum.sum_main s A B hA hB hAB

end
