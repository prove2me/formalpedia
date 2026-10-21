-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P12.finite_group_central_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T17:22:05.940065+00:00
-- url     : https://prove2.me/submissions/9e1092cc-a8c2-440e-92d4-610f9bb479ee

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P12
noncomputable section

open scoped BigOperators Classical

open Filter

open QAlgorithms.Papers.Independent.Next46.P12

universe u v w

namespace G62K
variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]

lemma block (D : SplitPresentation k A) {z : A} (hz : z ∈ Subalgebra.center k A) (i : D.Label) :
    D.equiv z i = algebraMap k _ (centralSpectrum D z i) := by
  have hc : ∀ M, Commute M (D.equiv z i) := by
    intro M
    have := (Subalgebra.mem_center_iff.mp hz) (D.equiv.symm (Pi.single i M))
    have h2 := congrArg (fun x => D.equiv x i) this
    simp only [map_mul, AlgEquiv.apply_symm_apply, Pi.mul_apply, Pi.single_eq_same] at h2
    exact h2
  obtain ⟨r, hr⟩ := Matrix.mem_range_scalar_iff_commute_single'.mpr (fun a b => hc _)
  have : centralSpectrum D z i = r := by
    simp [centralSpectrum, ← hr]
  rw [this, ← hr]; rfl

lemma mem_center_of (D : SplitPresentation k A) (z : A) (c : D.Label → k)
    (h : ∀ i, D.equiv z i = algebraMap k _ (c i)) : z ∈ Subalgebra.center k A := by
  rw [Subalgebra.mem_center_iff]
  intro b
  apply D.equiv.injective
  funext i
  simp only [map_mul, Pi.mul_apply, h i]
  exact (Algebra.commutes _ _).symm

lemma spec_alg (D : SplitPresentation k A) (z : A) (c : D.Label → k)
    (h : ∀ i, D.equiv z i = algebraMap k _ (c i)) (i : D.Label) : centralSpectrum D z i = c i := by
  simp only [centralSpectrum, h i, Matrix.algebraMap_matrix_apply]; simp

lemma spec_aeval (D : SplitPresentation k A) {z : A} (hz : z ∈ Subalgebra.center k A)
    (p : Polynomial k) (j : D.Label) :
    D.equiv (Polynomial.aeval z p) j = algebraMap k _ (p.eval (centralSpectrum D z j)) := by
  have : D.equiv (Polynomial.aeval z p) j =
      ((Pi.evalAlgHom k _ j).comp D.equiv.toAlgHom) (Polynomial.aeval z p) := rfl
  rw [this, ← Polynomial.aeval_algHom_apply]
  change Polynomial.aeval (D.equiv z j) p = _
  rw [block D hz j, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]

lemma ci_block (D : SplitPresentation k A) (i j : D.Label) :
    D.equiv (centralIdempotent D i) j = algebraMap k _ (if j = i then 1 else 0) := by
  simp only [centralIdempotent, blockElement, AlgEquiv.apply_symm_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

lemma eval_cp (D : SplitPresentation k A) (z : A) (hinj : Function.Injective (centralSpectrum D z))
    (i j : D.Label) :
    (centralPolynomial D z i).eval (centralSpectrum D z j) = if j = i then 1 else 0 := by
  unfold centralPolynomial
  rw [Polynomial.eval_prod]
  by_cases h : j = i
  · subst h
    simp only [if_true]
    apply Finset.prod_eq_one
    intro l hl
    have hne : centralSpectrum D z j - centralSpectrum D z l ≠ 0 :=
      sub_ne_zero.mpr (fun e => (Finset.ne_of_mem_erase hl) (hinj e).symm)
    simp [interpolationFactor, hne]
  · simp only [h, if_false]
    apply Finset.prod_eq_zero (i := j) (Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩)
    simp [interpolationFactor]

theorem crit [FiniteDimensional k A] (D : SplitPresentation k A) (z : A)
    (hz : z ∈ Subalgebra.center k A) :
    GeneratesCenter (k := k) z ↔ Function.Injective (centralSpectrum D z) := by
  constructor
  · intro hg i j hij
    by_contra hne
    have hm : centralIdempotent D i ∈ Algebra.adjoin k ({z} : Set A) := by
      rw [hg]; exact mem_center_of D _ _ (ci_block D i)
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hm
    obtain ⟨p, hp⟩ := hm
    have h1 := spec_alg D _ _ (ci_block D i) i
    have h2 := spec_alg D _ _ (ci_block D i) j
    have e1 := spec_alg D _ _ (spec_aeval D hz p) i
    have e2 := spec_alg D _ _ (spec_aeval D hz p) j
    change Polynomial.aeval z p = _ at hp
    rw [hp] at e1 e2
    rw [e1, if_pos rfl] at h1
    rw [e2, if_neg (Ne.symm hne), ← hij] at h2
    rw [h1] at h2; exact one_ne_zero h2
  · intro hinj
    apply le_antisymm
    · rw [Algebra.adjoin_le_iff]; intro x hx; rw [Set.mem_singleton_iff.mp hx]; exact hz
    · intro w hw
      let P : Polynomial k := ∑ i, Polynomial.C (centralSpectrum D w i) * centralPolynomial D z i
      have : w = Polynomial.aeval z P := by
        apply D.equiv.injective
        funext j
        rw [spec_aeval D hz, block D hw]
        congr 1
        simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
          eval_cp D z hinj]
        simp
      rw [this]; exact Polynomial.aeval_mem_adjoin_singleton k z

end G62K

namespace G62K

lemma desc_cast (q m : ℕ) : (q.descFactorial m : ℝ) = ∏ i ∈ Finset.range m, ((q : ℝ) - i) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.descFactorial_succ, Finset.prod_range_succ, Nat.cast_mul, ih]
    by_cases h : m ≤ q
    · rw [Nat.cast_sub h]; ring
    · have h0 : q.descFactorial m = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      rw [h0] at ih
      rw [← ih]; simp

lemma frac_eq (m q : ℕ) (hq : q ≠ 0) :
    generatorFraction m q = (∏ i ∈ Finset.range m, ((q : ℝ) - i)) / (q : ℝ) ^ m := by
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  unfold generatorFraction
  rw [show (q:ℝ)^m = ∏ _i ∈ Finset.range m, (q:ℝ) by simp, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  field_simp

lemma frac_lim (m : ℕ) : Filter.Tendsto (generatorFraction m) Filter.atTop (nhds 1) := by
  unfold generatorFraction
  rw [show (nhds (1:ℝ)) = nhds (∏ i ∈ Finset.range m, (1 - (0:ℝ))) by simp]
  apply tendsto_finsetProd
  intro i _
  exact tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (i : ℝ))

variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]

def cenEquiv (D : SplitPresentation k A) : Subalgebra.center k A ≃ (D.Label → k) where
  toFun z := centralSpectrum D (z : A)
  invFun f := ⟨D.equiv.symm (fun i => algebraMap k _ (f i)),
    mem_center_of D _ f (fun i => by simp)⟩
  left_inv z := by
    apply Subtype.ext
    apply D.equiv.injective
    funext i
    simp [block D z.2 i]
  right_inv f := funext (spec_alg D _ f (fun i => by simp))

end G62K
namespace G62K
variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]

def bas (D : SplitPresentation k A) : Module.Basis (Σ i : D.Label, Fin (D.size i) × Fin (D.size i)) k A :=
  (Pi.basis fun i => Matrix.stdBasis k (Fin (D.size i)) (Fin (D.size i))).map D.equiv.symm.toLinearEquiv

lemma bas_repr (D : SplitPresentation k A) (x : A) (p : Σ i : D.Label, Fin (D.size i) × Fin (D.size i)) :
    (bas D).repr x p = D.equiv x p.1 p.2.1 p.2.2 := by
  simp [bas, Matrix.stdBasis]

lemma bas_apply (D : SplitPresentation k A) (p : Σ i : D.Label, Fin (D.size i) × Fin (D.size i)) :
    D.equiv (bas D p) = Pi.single p.1 (Matrix.single p.2.1 p.2.2 1) := by
  simp only [bas, Module.Basis.map_apply, LinearEquiv.coe_coe, AlgEquiv.toLinearEquiv_apply,
    AlgEquiv.apply_symm_apply, Pi.basis_apply]
  rw [Matrix.stdBasis_eq_single]

lemma reg (D : SplitPresentation k A) (a : A) :
    regularCharacter (k := k) a = ∑ lam : D.Label, simpleCharacter D lam 1 * simpleCharacter D lam a := by
  unfold regularCharacter
  rw [LinearMap.trace_eq_matrix_trace k (bas D)]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, bas_repr]
  have h : ∀ p : (Σ i : D.Label, Fin (D.size i) × Fin (D.size i)),
      D.equiv (leftRegularAction (k := k) a (bas D p)) p.1 p.2.1 p.2.2 = D.equiv a p.1 p.2.1 p.2.1 := by
    intro p
    simp only [leftRegularAction, LinearMap.coe_mk, AddHom.coe_mk, map_mul, Pi.mul_apply, bas_apply,
      Pi.single_eq_same]
    simp [Matrix.mul_apply, Matrix.single_apply]
  simp only [h]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro lam _
  rw [Fintype.sum_prod_type]
  simp [simpleCharacter, Matrix.trace, Finset.mul_sum]

lemma tau_eq (a : A) : regularCharacter (k := k) a = LinearMap.trace k A (LinearMap.mul k A a) := by
  unfold regularCharacter; congr 1

lemma tau_sum {I : Type*} [Fintype I] (c : I → k) (z : I → A) :
    regularCharacter (k := k) (∑ i, c i • z i) = ∑ i, c i * regularCharacter (k := k) (z i) := by
  simp only [tau_eq, map_sum, map_smul, smul_eq_mul]

lemma ci_mul (D : SplitPresentation k A) (lam mu : D.Label) (x : A) :
    simpleCharacter D mu (centralIdempotent D lam * x) =
      if mu = lam then simpleCharacter D lam x else 0 := by
  unfold simpleCharacter
  rw [map_mul, Pi.mul_apply]
  simp only [centralIdempotent, blockElement, AlgEquiv.apply_symm_apply]
  by_cases h : mu = lam
  · subst h; simp
  · simp [h]

lemma tau_e (D : SplitPresentation k A) (lam : D.Label) (x : A) :
    regularCharacter (k := k) (centralIdempotent D lam * x) =
      simpleCharacter D lam 1 * simpleCharacter D lam x := by
  rw [reg D]
  simp only [ci_mul]
  simp

lemma Tmul {I : Type*} [Fintype I] (b : Module.Basis I k A) (c : I → k) (i : I) :
    (Matrix.mulVec (traceMatrix b) c) i = regularCharacter (k := k) ((∑ j, c j • b j) * b i) := by
  simp only [Matrix.mulVec, dotProduct, traceMatrix, Finset.sum_mul, smul_mul_assoc, tau_sum]
  apply Finset.sum_congr rfl; intro j _; ring

lemma det_ne [CharZero k] (D : SplitPresentation k A) {I : Type*} [Fintype I] [DecidableEq I]
    (b : Module.Basis I k A) : (traceMatrix b).det ≠ 0 := by
  intro hdet
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set y := ∑ j, c j • b j with hy
  have hy0 : y ≠ 0 := by
    intro h0
    apply hc0
    funext j
    exact Fintype.linearIndependent_iff.mp b.linearIndependent c h0 j
  have hall : ∀ x : A, regularCharacter (k := k) (y * x) = 0 := by
    intro x
    rw [← b.sum_repr x, Finset.mul_sum]
    simp only [mul_smul_comm, tau_sum]
    apply Finset.sum_eq_zero; intro i _
    rw [← Tmul, hc]; simp
  have hY : D.equiv y ≠ 0 := by
    intro h; exact hy0 (D.equiv.injective (by rw [h, map_zero]))
  obtain ⟨lam, hlam⟩ := Function.ne_iff.mp hY
  obtain ⟨p, hp⟩ := Function.ne_iff.mp hlam
  obtain ⟨q, hq⟩ := Function.ne_iff.mp hp
  have := hall (D.equiv.symm (Pi.single lam (Matrix.single q p 1)))
  rw [reg D] at this
  rw [Finset.sum_eq_single lam] at this
  · simp only [simpleCharacter, map_one, Pi.one_apply, Matrix.trace_one, map_mul,
      AlgEquiv.apply_symm_apply, Pi.mul_apply, Pi.single_eq_same, Matrix.trace_mul_single] at this
    simp at this
    rcases this with h | h
    · exact absurd h (Nat.cast_ne_zero.mpr (D.positive lam).ne')
    · exact hq h
  · intro mu _ hmu
    simp [simpleCharacter, Pi.single_eq_of_ne hmu]
  · simp
end G62K
namespace G62K
variable {k : Type u} [Field k]

lemma tau_single {G : Type v} [Group G] [Fintype G] (h : G) :
    regularCharacter (k := k) (MonoidAlgebra.single h (1 : k)) =
      if h = 1 then (Fintype.card G : k) else 0 := by
  rw [tau_eq, LinearMap.trace_eq_matrix_trace k (MonoidAlgebra.basis G k)]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, MonoidAlgebra.basis_apply,
    LinearMap.mul_apply', MonoidAlgebra.single_mul_single, mul_one]
  have : ∀ i : G, (MonoidAlgebra.basis G k).repr (MonoidAlgebra.single (h * i) 1) i =
      if h = 1 then 1 else 0 := by
    intro i
    change (MonoidAlgebra.single (h * i) (1:k)).coeff i = _
    rw [MonoidAlgebra.coeff_single_apply]
    simp
  simp only [this]
  split_ifs <;> simp
end G62K

open G62K

variable {k : Type u} [Field k]

variable {A : Type v} [Ring A] [Algebra k A]

/-- Corollary A.2 (Frobenius), source PDF p. 33. Splitness is explicit; the
character is evaluated on g inverse over a general characteristic-zero field. -/
theorem solution [CharZero k]
    {G : Type w} [Group G] [Fintype G]
    (D : SplitPresentation k (MonoidAlgebra k G)) (lam : D.Label) :
    centralIdempotent D lam = (Fintype.card G : k)⁻¹ •
      ∑ g : G, (simpleCharacter D lam 1 *
        simpleCharacter D lam (MonoidAlgebra.single g⁻¹ 1)) • MonoidAlgebra.single g 1 := by
  have hG : (Fintype.card G : k) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hc : ∀ g : G, (MonoidAlgebra.basis G k).repr (centralIdempotent D lam) g =
      (Fintype.card G : k)⁻¹ * (simpleCharacter D lam 1 *
        simpleCharacter D lam (MonoidAlgebra.single g⁻¹ 1)) := by
    intro g
    have h1 := G62K.tau_e D lam (MonoidAlgebra.single g⁻¹ (1:k))
    rw [← (MonoidAlgebra.basis G k).sum_repr (centralIdempotent D lam)] at h1
    rw [Finset.sum_mul] at h1
    simp only [smul_mul_assoc, MonoidAlgebra.basis_apply, MonoidAlgebra.single_mul_single, mul_one,
      G62K.tau_sum, G62K.tau_single, mul_inv_eq_one] at h1
    simp at h1
    rw [← h1]
    field_simp
  conv_lhs => rw [← (MonoidAlgebra.basis G k).sum_repr (centralIdempotent D lam)]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [hc g, smul_smul, MonoidAlgebra.basis_apply]



end
