-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P06.supermaps_noncausal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T21:52:44.24132+00:00
-- url     : https://prove2.me/submissions/1f3380e3-4871-4c3e-9dc8-1c7482ad1ff5

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P06

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace X7S6

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P06
open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed)
open QAlgorithms.Papers.Independent.Information100.P34 (choi)

theorem X7_choi_apply {I O : Type} (M : QMap I O) (a b : I) (o o' : O) :
    choi M (a, o) (b, o') = M (Matrix.single a b 1) o o' := rfl

theorem X7_lin_expand {I O : Type} [Fintype I] (M : QMap I O)
    (X : Matrix I I ℂ) : M X = ∑ i, ∑ j, X i j • M (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

theorem X7_sum_psd {I ι : Type} [Fintype I] (s : Finset ι) (A : ι → Matrix I I ℂ)
    (h : ∀ i, (A i).PosSemidef) : (∑ i ∈ s, A i).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Matrix.PosSemidef.zero
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact (h a).add ih

theorem X7_swap22 {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    ∑ i, ∑ j, ∑ m, ∑ l, f i j m l = ∑ m, ∑ l, ∑ i, ∑ j, f i j m l := by
  calc ∑ i, ∑ j, ∑ m, ∑ l, f i j m l = ∑ i, ∑ m, ∑ j, ∑ l, f i j m l :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ m, ∑ i, ∑ j, ∑ l, f i j m l := Finset.sum_comm
    _ = ∑ m, ∑ i, ∑ l, ∑ j, f i j m l :=
        Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ m, ∑ l, ∑ i, ∑ j, f i j m l := Finset.sum_congr rfl fun m _ => Finset.sum_comm

theorem X7_cp_of_choi {I O : Type} [Fintype I] [Fintype O]
    (M : QMap I O) (hC : (choi M).PosSemidef) :
    Entanglement.IsCompletelyPositive M := by
  intro r X hX
  obtain ⟨m1, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hX
  obtain ⟨m2, g, hg⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hC
  have hMij : ∀ i j o o', M (Matrix.single i j 1) o o' =
      ∑ l, g l (i, o) * star (g l (j, o')) := by
    intro i j o o'
    rw [← X7_choi_apply, hg, Matrix.sum_apply]
    simp [Matrix.vecMulVec_apply]
  let F : Fin m1 → Fin m2 → (Fin r × O → ℂ) :=
    fun a l q => ∑ i, v a (q.1, i) * g l (i, q.2)
  have hY : idTensorSuperop M X = ∑ a, ∑ l, Matrix.vecMulVec (F a l) (star (F a l)) := by
    ext ⟨x, o⟩ ⟨y, o'⟩
    show M (Matrix.of fun i j => X (x, i) (y, j)) o o' = _
    rw [X7_lin_expand]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, hMij, hv,
      Matrix.vecMulVec_apply, Pi.star_apply, F, star_sum, star_mul']
    simp only [Finset.sum_mul_sum]
    rw [X7_swap22]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hY]
  exact X7_sum_psd _ _ fun a => X7_sum_psd _ _ fun l =>
    Matrix.posSemidef_vecMulVec_self_star _

theorem X7_trace_vmv {I : Type} [Fintype I] (P : Op I) (x : I → ℂ) :
    (P * Matrix.vecMulVec x (star x)).trace = star x ⬝ᵥ (P *ᵥ x) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply,
    dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring


/-- partial trace over the memory -/
def ptr {I E : Type} [Fintype E] (σ : Op (I × E)) : Op I := ∑ m, Matrix.of fun i j => σ (i, m) (j, m)

lemma trace_mwm {I O E : Type} [Fintype I] [Fintype O] [Fintype E] (N : QMap I O) (σ : Op (I × E)) :
    (mapWithMemory N σ).trace = (N (ptr σ)).trace := by
  rw [ptr, map_sum, Matrix.trace_sum]
  simp only [Matrix.trace, Matrix.diag, mapWithMemory, Fintype.sum_prod_type]
  rw [Finset.sum_comm]; rfl

lemma ptr_density {I E : Type} [Fintype I] [Fintype E] (σ : Op (I × E)) (h : IsDensityMatrix σ) :
    IsDensityMatrix (ptr σ) := by
  constructor
  · unfold ptr
    exact X7_sum_psd _ _ fun m => h.1.submatrix (fun i => (i, m))
  · have := h.2
    unfold ptr
    rw [Matrix.trace_sum]
    simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Matrix.of_apply] at this ⊢
    rw [Finset.sum_comm]; exact this

lemma trace_nonneg {I : Type} [Fintype I] (Q X : Op I) (hQ : Q.PosSemidef) (hX : X.PosSemidef) :
    0 ≤ ((Q * X).trace).re := by
  obtain ⟨m, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hX
  rw [hv, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_nonneg fun l _ => ?_
  rw [X7_trace_vmv]
  have := hQ.dotProduct_mulVec_nonneg (v l)
  exact (Complex.nonneg_iff.1 this).1

/-- the effect map `X ↦ Tr(P X) • M` -/
def effMap {I O : Type} [Fintype I] (P : Op I) (M : Op O) : QMap I O where
  toFun X := (P * X).trace • M
  map_add' X Y := by simp [Matrix.mul_add, Matrix.trace_add, add_smul]
  map_smul' c X := by simp [Matrix.mul_smul, Matrix.trace_smul, smul_smul]

lemma trace_mul_single {I : Type} [Fintype I] (P : Op I) (a b : I) :
    (P * Matrix.single a b 1).trace = P b a := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

lemma effMap_cp {I O : Type} [Fintype I] [Fintype O] (P : Op I) (M : Op O)
    (hP : P.PosSemidef) (hM : M.PosSemidef) : Entanglement.IsCompletelyPositive (effMap P M) := by
  apply X7_cp_of_choi
  have : choi (effMap P M) = Matrix.kronecker P.transpose M := by
    ext ⟨a, o⟩ ⟨b, o'⟩
    rw [X7_choi_apply]
    simp [effMap, trace_mul_single, Matrix.kronecker, Matrix.kroneckerMap_apply]
  rw [this]
  exact hP.transpose.kronecker hM

lemma effMap_cptni {I O : Type} [Fintype I] [Fintype O] (P : Op I) (o : O)
    (hP : P.PosSemidef) (hP1 : (1 - P).PosSemidef) :
    IsCPTNI (effMap P (Matrix.single o o 1)) := by
  refine ⟨effMap_cp P _ hP ?_, fun X hX => ?_⟩
  · have : (Matrix.single o o (1:ℂ)) = Matrix.vecMulVec (Pi.single o 1) (star (Pi.single o 1)) := by
      ext i j; by_cases h1 : i = o <;> by_cases h2 : j = o <;> simp [h1, h2, Matrix.single_apply, Matrix.vecMulVec_apply] <;> aesop
    rw [this]; exact Matrix.posSemidef_vecMulVec_self_star _
  · have h1 := trace_nonneg (1 - P) X hP1 hX.1
    have h2 : (effMap P (Matrix.single o o 1) X).trace = (P * X).trace := by
      simp [effMap, Matrix.trace_smul]
    rw [h2]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re, hX.2] at h1
    simp at h1; linarith

lemma discard_effMap {I O : Type} [Fintype I] [Fintype O] (P : Op I) (o : O) (X : Op I) :
    discardEffect X (effMap P (Matrix.single o o 1)) = ((P * X).trace).re := by
  simp [discardEffect, effMap, Matrix.trace_smul]

/-- rank-one projector -/
lemma proj_psd {I : Type} [Fintype I] (v : I → ℂ) (hv : star v ⬝ᵥ v = 1) :
    (Matrix.vecMulVec v (star v)).PosSemidef ∧ (1 - Matrix.vecMulVec v (star v)).PosSemidef := by
  refine ⟨Matrix.posSemidef_vecMulVec_self_star v, ?_⟩
  set P := Matrix.vecMulVec v (star v)
  have hPh : Pᴴ = P := by
    ext i j; simp [P, Matrix.vecMulVec_apply, Matrix.conjTranspose_apply, mul_comm]
  have hPP : P * P = P := by
    ext i j
    simp only [P, Matrix.mul_apply, Matrix.vecMulVec_apply, Pi.star_apply]
    have : ∑ x, v i * star (v x) * (v x * star (v j)) = v i * (star v ⬝ᵥ v) * star (v j) := by
      simp only [dotProduct, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => by ring
    rw [this, hv, mul_one]
  have : 1 - P = (1 - P)ᴴ * (1 - P) := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPh]
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, hPP]; abel
  rw [this]; exact Matrix.posSemidef_conjTranspose_mul_self _

lemma quad_zero {I : Type} [Fintype I] (D : Op I) (hD : D.IsHermitian)
    (h : ∀ v : I → ℂ, star v ⬝ᵥ v = 1 → (star v ⬝ᵥ (D *ᵥ v)).re = 0) : D = 0 := by
  have hall : ∀ v : I → ℂ, star v ⬝ᵥ (D *ᵥ v) = 0 := by
    intro v
    by_cases hv0 : v = 0
    · simp [hv0]
    have hpos : 0 < (star v ⬝ᵥ v).re := by
      have h0 : star v ⬝ᵥ v ≠ 0 := fun h => hv0 (dotProduct_star_self_eq_zero.mp h)
      have hn := (Matrix.PosSemidef.one (n := I) (R := ℂ)).dotProduct_mulVec_nonneg v
      simp only [Matrix.one_mulVec] at hn
      rcases (Complex.nonneg_iff.1 hn) with ⟨h1, h2⟩
      refine lt_of_le_of_ne h1 fun h3 => h0 (Complex.ext h3.symm (by simpa using h2.symm))
    set t := (star v ⬝ᵥ v).re
    have htc : star v ⬝ᵥ v = (t : ℂ) := by
      have hn := (Matrix.PosSemidef.one (n := I) (R := ℂ)).dotProduct_mulVec_nonneg v
      simp only [Matrix.one_mulVec] at hn
      exact Complex.ext rfl (by simpa using (Complex.nonneg_iff.1 hn).2.symm)
    set c : ℂ := (((Real.sqrt t)⁻¹ : ℝ) : ℂ)
    have hcc : star c * c = ((t⁻¹ : ℝ) : ℂ) := by
      simp only [c, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
      congr 1
      rw [← mul_inv, Real.mul_self_sqrt hpos.le]
    have hu : star (c • v) ⬝ᵥ (c • v) = 1 := by
      rw [star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
        hcc, htc, ← Complex.ofReal_mul, inv_mul_cancel₀ hpos.ne', Complex.ofReal_one]
    have := h _ hu
    rw [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, hcc, Complex.re_ofReal_mul] at this
    have hre : (star v ⬝ᵥ (D *ᵥ v)).re = 0 := by
      rcases mul_eq_zero.1 this with h1 | h1
      · exact absurd h1 (inv_ne_zero hpos.ne')
      · exact h1
    have him : (star v ⬝ᵥ (D *ᵥ v)).im = 0 := hD.im_star_dotProduct_mulVec_self v
    exact Complex.ext hre him
  have hT : Matrix.toEuclideanLin D = 0 := by
    rw [← inner_map_self_eq_zero]
    intro x
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    have key : ∀ a b : I → ℂ, a ⬝ᵥ star b = star (star a ⬝ᵥ b) := fun a b => by
      simp [dotProduct, mul_comm]
    rw [show WithLp.ofLp (Matrix.toEuclideanLin D x) = D *ᵥ WithLp.ofLp x from rfl, key,
      hall, star_zero]
  exact Matrix.toEuclideanLin.injective (by rw [hT, map_zero])

end X7S6

end

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P06

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed)
open QAlgorithms.Papers.Independent.Information100.P34 (choi)

end QAlgorithms.Papers.Independent.Dependency50.P06

end

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

section QuantumResults

variable {A0 A1 B0 B1 : Type}
variable [Fintype A0] [Fintype A1] [Fintype B0] [Fintype B1]
variable [hA0 : Nonempty A0] [hA1 : Nonempty A1] [hB0 : Nonempty B0] [hB1 : Nonempty B1]

open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P06 X7S6
  QAlgorithms.Papers.Independent.Information100.P22 in
theorem solution [Nonempty A1] [Nonempty B0] [Nonempty B1] [Nontrivial A0] :
    (∀ f : QMap A0 A1 → ℝ, IsDeterministicTester f ↔
      ∃ rho : Op A0, IsDensityMatrix rho ∧ f = discardEffect rho) ∧
    (∃ rho sigma : Op A0, IsDensityMatrix rho ∧ IsDensityMatrix sigma ∧
      ∃ E : QMap A0 A1, IsCPTNI E ∧ discardEffect rho E ≠ discardEffect sigma E) ∧
    (∀ tau : Op (A0 × B0), IsDensityMatrix tau → ¬ Entanglement.IsSeparableDensity tau →
      ¬ ∃ rho : Op A0, ∃ sigma : Op B0, IsDensityMatrix rho ∧ IsDensityMatrix sigma ∧
        ∀ E : QMap (A0 × B0) (A1 × B1), IsCPTNI E →
          discardEffect tau E = discardEffect (Matrix.kronecker rho sigma) E) := by
  refine ⟨fun f => ⟨?_, ?_⟩, ?_, ?_⟩
  · rintro ⟨e, -, σ, hσ, hf⟩
    refine ⟨ptr σ, ptr_density σ hσ, funext fun N => ?_⟩
    rw [hf N, trace_mwm]; rfl
  · rintro ⟨ρ, hρ, rfl⟩
    have hp : ptr (ρ.submatrix Prod.fst Prod.fst : Op (A0 × Fin 1)) = ρ := by
      ext i j; simp [ptr, Matrix.sum_apply]
    refine ⟨1, one_pos, ρ.submatrix Prod.fst Prod.fst, ⟨hρ.1.submatrix _, ?_⟩, fun N => ?_⟩
    · have := hρ.2
      simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Matrix.submatrix_apply] at this ⊢
      simpa using this
    · rw [trace_mwm, hp]; rfl
  · obtain ⟨a, b, hab⟩ := exists_pair_ne A0
    let o : A1 := Classical.arbitrary A1
    let va : A0 → ℂ := Pi.single a 1
    let vb : A0 → ℂ := Pi.single b 1
    have hva : star va ⬝ᵥ va = 1 := by simp [va, dotProduct, Pi.single_apply]
    have hvb : star vb ⬝ᵥ vb = 1 := by simp [vb, dotProduct, Pi.single_apply]
    have dens : ∀ v : A0 → ℂ, star v ⬝ᵥ v = 1 → IsDensityMatrix (Matrix.vecMulVec v (star v)) :=
      fun v hv => ⟨Matrix.posSemidef_vecMulVec_self_star v, by
        have := X7_trace_vmv 1 v; rw [Matrix.one_mul, Matrix.one_mulVec] at this; rw [this, hv]⟩
    refine ⟨_, _, dens va hva, dens vb hvb, effMap (Matrix.vecMulVec va (star va)) (Matrix.single o o 1),
      effMap_cptni _ o (proj_psd va hva).1 (proj_psd va hva).2, ?_⟩
    rw [discard_effMap, discard_effMap, X7_trace_vmv, X7_trace_vmv]
    have hab' : b ≠ a := fun h => hab h.symm
    simp [va, vb, dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, Pi.single_apply, hab, hab']
  · rintro τ hτ hent ⟨ρ, σ, hρ, hσ, heq⟩
    apply hent
    let o : A1 × B1 := Classical.arbitrary _
    have hq : ∀ v : A0 × B0 → ℂ, star v ⬝ᵥ v = 1 →
        (star v ⬝ᵥ ((τ - Matrix.kronecker ρ σ) *ᵥ v)).re = 0 := by
      intro v hv
      have := heq _ (effMap_cptni _ o (proj_psd v hv).1 (proj_psd v hv).2)
      rw [discard_effMap, discard_effMap, Matrix.trace_mul_comm, X7_trace_vmv,
        Matrix.trace_mul_comm, X7_trace_vmv] at this
      rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, this, sub_self]
    have hD := quad_zero _ (hτ.1.1.sub (hρ.1.kronecker hσ.1).1) hq
    have hτω : τ = Matrix.kronecker ρ σ := sub_eq_zero.1 hD
    exact ⟨1, fun _ => 1, fun _ => ρ, fun _ => σ, fun _ => zero_le_one, by simp,
      fun _ => ⟨hρ, hσ⟩, by simp [hτω]⟩

end QuantumResults
