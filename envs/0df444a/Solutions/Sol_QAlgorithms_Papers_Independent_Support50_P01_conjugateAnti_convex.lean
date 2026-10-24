-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P01.conjugateAnti_convex
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T02:51:08.59263+00:00
-- url     : https://prove2.me/submissions/68fe94a9-d7c8-4751-9f56-1c197f83e81b

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P01

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P01

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel)

namespace X7S1

/-- Kraus channels with an arbitrary finite index type. -/
lemma chan_of_kraus {ι κ K : Type*} [Fintype ι] [Fintype κ] [Fintype K] [DecidableEq ι]
    (E : K → Matrix κ ι ℂ) (hE : ∑ k, (E k)ᴴ * E k = 1) :
    IsChannel (krausApply E) := by
  let σ := Fintype.equivFin K
  refine ⟨Fintype.card K, fun j => E (σ.symm j), ?_, ?_⟩
  · unfold IsKrausFamily
    rw [← hE]
    exact Fintype.sum_equiv σ.symm _ _ (fun _ => rfl)
  · intro ρ
    unfold krausApply
    exact (Fintype.sum_equiv σ.symm _ _ (fun _ => rfl)).symm

lemma kraus_comp {ι κ μ K L : Type*} [Fintype ι] [Fintype κ] [Fintype μ] [Fintype K] [Fintype L]
    (E : K → Matrix κ ι ℂ) (F : L → Matrix μ κ ℂ) (ρ : Matrix ι ι ℂ) :
    krausApply F (krausApply E ρ) = krausApply (fun p : K × L => F p.2 * E p.1) ρ := by
  unfold krausApply
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]

lemma chan_comp {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ] {_i1 : DecidableEq ι} {_i2 : DecidableEq κ}
    (Φ : Superop ι κ) (Ψ : Superop κ μ) (hΦ : IsChannel Φ) (hΨ : IsChannel Ψ) :
    IsChannel (Ψ ∘ Φ) := by
  obtain ⟨m, E, hE, hΦE⟩ := hΦ
  obtain ⟨n, F, hF, hΨF⟩ := hΨ
  have h : Ψ ∘ Φ = krausApply (fun p : Fin m × Fin n => F p.2 * E p.1) := by
    funext ρ
    simp only [Function.comp, hΦE, hΨF, kraus_comp]
  rw [h]
  apply chan_of_kraus
  rw [Fintype.sum_prod_type]
  unfold IsKrausFamily at hE hF
  rw [← hE]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [Matrix.conjTranspose_mul]
  have : ∀ j : Fin n, (E k)ᴴ * (F j)ᴴ * (F j * E k) = (E k)ᴴ * ((F j)ᴴ * F j) * E k := by
    intro j; simp [Matrix.mul_assoc]
  simp only [this, ← Matrix.sum_mul, ← Matrix.mul_sum, hF, Matrix.mul_one]

lemma kraus_smul {ι κ K : Type*} [Fintype ι] [Fintype κ] [Fintype K]
    (E : K → Matrix κ ι ℂ) (z : ℂ) (ρ : Matrix ι ι ℂ) :
    krausApply E (z • ρ) = z • krausApply E ρ := by
  unfold krausApply
  rw [Finset.smul_sum]
  simp [Matrix.mul_smul, Matrix.smul_mul]

lemma kraus_add {ι κ K : Type*} [Fintype ι] [Fintype κ] [Fintype K]
    (E : K → Matrix κ ι ℂ) (ρ σ : Matrix ι ι ℂ) :
    krausApply E (ρ + σ) = krausApply E ρ + krausApply E σ := by
  unfold krausApply
  rw [← Finset.sum_add_distrib]
  simp [Matrix.mul_add, Matrix.add_mul]

/-- The entrywise-conjugated Kraus family implements the transposed channel. -/
lemma kraus_conj_transpose {ι κ K : Type*} [Fintype ι] [Fintype κ] [Fintype K]
    (E : K → Matrix κ ι ℂ) (ρ : Matrix ι ι ℂ) :
    krausApply (fun k => (E k).map (starRingEnd ℂ)) ρᵀ = (krausApply E ρ)ᵀ := by
  unfold krausApply
  rw [Matrix.transpose_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  show (E k).map (starRingEnd ℂ) * (ρᵀ * ((E k).map (starRingEnd ℂ))ᴴ) = _
  rw [show ((E k).map (starRingEnd ℂ))ᴴ = (E k)ᵀ from by
        ext i j; simp [Matrix.conjTranspose_apply],
      show (E k)ᴴᵀ = (E k).map (starRingEnd ℂ) from by
        ext i j; simp [Matrix.conjTranspose_apply]]

lemma conj_kraus_family {ι κ K : Type*} [Fintype ι] [Fintype κ] [Fintype K] [DecidableEq ι]
    (E : K → Matrix κ ι ℂ) (hE : ∑ k, (E k)ᴴ * E k = 1) :
    ∑ k, ((E k).map (starRingEnd ℂ))ᴴ * (E k).map (starRingEnd ℂ) = 1 := by
  have h := congrArg (fun M : Matrix ι ι ℂ => M.map (starRingEnd ℂ)) hE
  rw [Matrix.map_one (starRingEnd ℂ) (map_zero _) (map_one _)] at h
  rw [← h]
  ext i j
  simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply]

lemma chan_conj {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (Φ : Superop ι κ) (hΦ : IsChannel Φ) :
    ∃ G : Superop ι κ, IsChannel G ∧ ∀ ρ, G ρᵀ = (Φ ρ)ᵀ := by
  obtain ⟨m, E, hE, hΦE⟩ := hΦ
  refine ⟨krausApply (fun k => (E k).map (starRingEnd ℂ)), chan_of_kraus _ ?_, ?_⟩
  · exact conj_kraus_family E hE
  · intro ρ; rw [hΦE]; exact kraus_conj_transpose E ρ

end X7S1

end QAlgorithms.Papers.Independent.Support50.P01

end


noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P01

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace X7S1

variable {a b : ℕ}

/-- Conjugate antidegradability of a dilation with an arbitrary environment type. -/
def GenCAD {E : Type*} [Fintype E] (U : Matrix (Fin b × E) (Fin a) ℂ) : Prop :=
  Uᴴ * U = 1 ∧ ∃ D : Superop E (Fin b), IsChannel D ∧
    ∀ X, D (complementaryChannel U X) = (receiverChannel U X)ᵀ

lemma reindex_cad {E : Type*} [Fintype E] [Nonempty E] (U : Matrix (Fin b × E) (Fin a) ℂ)
    (hU : GenCAD U) : ConjugateAntiChannel (receiverChannel U) := by
  obtain ⟨hiso, D, hD, hDU⟩ := hU
  let σ := Fintype.equivFin E
  let U' : Matrix (Fin b × Fin (Fintype.card E)) (Fin a) ℂ :=
    fun p α => U (p.1, σ.symm p.2) α
  have hrec : receiverChannel U' = receiverChannel U := by
    funext X
    ext β β'
    simp only [receiverChannel, traceRight, Matrix.of_apply]
    exact Fintype.sum_equiv σ.symm _ _ (fun _ => rfl)
  have hcomp : ∀ X, complementaryChannel U' X =
      (complementaryChannel U X).submatrix σ.symm σ.symm := by
    intro X; ext i j; rfl
  obtain ⟨m, F, hF, hDF⟩ := hD
  refine ⟨Fintype.card E, Fintype.card_pos, U', ⟨?_, ?_⟩, hrec⟩
  · rw [← hiso]
    ext α α'
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun β _ => ?_)
    exact Fintype.sum_equiv σ.symm _ _ (fun _ => rfl)
  · refine ⟨krausApply (fun k => (F k).submatrix id σ.symm), ?_, ?_⟩
    · apply chan_of_kraus
      unfold IsKrausFamily at hF
      ext i j
      have := congrFun (congrFun hF (σ.symm i)) (σ.symm j)
      have h1 : (1 : Matrix (Fin (Fintype.card E)) (Fin (Fintype.card E)) ℂ) i j =
          (1 : Matrix E E ℂ) (σ.symm i) (σ.symm j) := by
        simp only [Matrix.one_apply, σ.symm.injective.eq_iff]
      rw [h1, ← this]
      simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.submatrix_apply, id]
    · intro X
      rw [hrec, ← hDU, hDF, hcomp]
      unfold krausApply
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ext β β'
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id]
      refine Fintype.sum_equiv σ.symm _ _ (fun x => ?_)
      congr 1
      refine Fintype.sum_equiv σ.symm _ _ (fun y => ?_)
      simp

end X7S1

end QAlgorithms.Papers.Independent.Support50.P01

end


noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P01

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace X7S1

lemma blk {P Q A : Type*} [Fintype A] (c : ℂ) (U : Matrix P A ℂ) (V : Matrix Q A ℂ)
    (f : P → Q) (hV : ∀ p α, V (f p) α = c * U p α) (X : Matrix A A ℂ) (p q : P) :
    (V * X * Vᴴ) (f p) (f q) = (c * star c) * (U * X * Uᴴ) p q := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hV, Finset.mul_sum, Finset.sum_mul,
    star_mul']
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
  ring

/-- Block-diagonal Kraus family on a direct-sum environment. -/
def sumKraus {B E1 E2 K1 K2 : Type*} (F1 : K1 → Matrix B E1 ℂ) (F2 : K2 → Matrix B E2 ℂ) :
    K1 ⊕ K2 → Matrix B (E1 ⊕ E2) ℂ
  | Sum.inl i => Matrix.of fun β x => Sum.elim (F1 i β) 0 x
  | Sum.inr j => Matrix.of fun β x => Sum.elim 0 (F2 j β) x

lemma sumKraus_apply {B E1 E2 K1 K2 : Type*} [Fintype B] [Fintype E1] [Fintype E2]
    [Fintype K1] [Fintype K2]
    (F1 : K1 → Matrix B E1 ℂ) (F2 : K2 → Matrix B E2 ℂ) (Y : Matrix (E1 ⊕ E2) (E1 ⊕ E2) ℂ) :
    krausApply (sumKraus F1 F2) Y =
      krausApply F1 (Y.submatrix Sum.inl Sum.inl) + krausApply F2 (Y.submatrix Sum.inr Sum.inr) := by
  unfold krausApply
  rw [Fintype.sum_sum_type]
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    ext β β'
    simp [sumKraus, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_sum_type]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    ext β β'
    simp [sumKraus, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_sum_type]

lemma sumKraus_family {B E1 E2 K1 K2 : Type*} [Fintype B] [Fintype E1] [Fintype E2]
    [Fintype K1] [Fintype K2] [DecidableEq E1] [DecidableEq E2]
    (F1 : K1 → Matrix B E1 ℂ) (F2 : K2 → Matrix B E2 ℂ)
    (h1 : ∑ k, (F1 k)ᴴ * F1 k = 1) (h2 : ∑ k, (F2 k)ᴴ * F2 k = 1) :
    ∑ k, (sumKraus F1 F2 k)ᴴ * sumKraus F1 F2 k = 1 := by
  rw [Fintype.sum_sum_type]
  ext x y
  rcases x with x | x <;> rcases y with y | y
  · have := congrFun (congrFun h1 x) y
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.star_def] at this
    simp [sumKraus, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    simpa [Matrix.one_apply] using this
  · simp [sumKraus, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  · simp [sumKraus, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  · have := congrFun (congrFun h2 x) y
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.star_def] at this
    simp [sumKraus, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    simpa [Matrix.one_apply] using this

variable {a b : ℕ}

lemma convex_main (ha : 0 < a) (hb : 0 < b) (Phi Psi : Superop (Fin a) (Fin b))
    (hPhi : ConjugateAntiChannel Phi) (hPsi : ConjugateAntiChannel Psi)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ConjugateAntiChannel (fun X => (t : ℂ) • Phi X + ((1-t : ℝ) : ℂ) • Psi X) := by
  obtain ⟨e1, he1, U1, ⟨hU1, D1, ⟨m1, F1, hF1, hD1⟩, hDU1⟩, rfl⟩ := hPhi
  obtain ⟨e2, he2, U2, ⟨hU2, D2, ⟨m2, F2, hF2, hD2⟩, hDU2⟩, rfl⟩ := hPsi
  have : Nonempty (Fin e1) := ⟨⟨0, he1⟩⟩
  set s1 : ℂ := (Real.sqrt t : ℂ) with hs1
  set s2 : ℂ := (Real.sqrt (1 - t) : ℂ) with hs2
  have hs1' : s1 * star s1 = (t : ℂ) := by
    rw [hs1, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt ht0]
  have hs2' : s2 * star s2 = ((1 - t : ℝ) : ℂ) := by
    rw [hs2, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by linarith)]
  let V : Matrix (Fin b × (Fin e1 ⊕ Fin e2)) (Fin a) ℂ := fun p α =>
    match p.2 with
    | Sum.inl ε => s1 * U1 (p.1, ε) α
    | Sum.inr ε => s2 * U2 (p.1, ε) α
  have hV1 : ∀ (X : Matrix (Fin a) (Fin a) ℂ) (p q : Fin b × Fin e1), (V * X * Vᴴ) (p.1, Sum.inl p.2) (q.1, Sum.inl q.2) =
      (s1 * star s1) * (U1 * X * U1ᴴ) p q := fun X p q =>
    blk s1 U1 V (fun p => (p.1, Sum.inl p.2)) (fun _ _ => rfl) X p q
  have hV2 : ∀ (X : Matrix (Fin a) (Fin a) ℂ) (p q : Fin b × Fin e2), (V * X * Vᴴ) (p.1, Sum.inr p.2) (q.1, Sum.inr q.2) =
      (s2 * star s2) * (U2 * X * U2ᴴ) p q := fun X p q =>
    blk s2 U2 V (fun p => (p.1, Sum.inr p.2)) (fun _ _ => rfl) X p q
  have hrec : receiverChannel V =
      (fun X => (t : ℂ) • receiverChannel U1 X + ((1-t : ℝ) : ℂ) • receiverChannel U2 X) := by
    funext X
    ext β β'
    simp only [receiverChannel, traceRight, Matrix.of_apply, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, Fintype.sum_sum_type, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl (fun ε _ => ?_)
      rw [← hs1']; exact hV1 X (β, ε) (β', ε)
    · refine Finset.sum_congr rfl (fun ε _ => ?_)
      rw [← hs2']; exact hV2 X (β, ε) (β', ε)
  have hcomp1 : ∀ X, (complementaryChannel V X).submatrix Sum.inl Sum.inl =
      (t : ℂ) • complementaryChannel U1 X := by
    intro X; ext ε ε'
    simp only [complementaryChannel, traceLeft, Matrix.submatrix_apply, Matrix.of_apply,
      Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun β _ => ?_)
    rw [← hs1']; exact hV1 X (β, ε) (β, ε')
  have hcomp2 : ∀ X, (complementaryChannel V X).submatrix Sum.inr Sum.inr =
      ((1 - t : ℝ) : ℂ) • complementaryChannel U2 X := by
    intro X; ext ε ε'
    simp only [complementaryChannel, traceLeft, Matrix.submatrix_apply, Matrix.of_apply,
      Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun β _ => ?_)
    rw [← hs2']; exact hV2 X (β, ε) (β, ε')
  rw [← hrec]
  apply reindex_cad
  refine ⟨?_, krausApply (sumKraus F1 F2), (by convert chan_of_kraus (sumKraus F1 F2) (sumKraus_family F1 F2 hF1 hF2)), ?_⟩
  · ext α α'
    have e1' := congrFun (congrFun hU1 α) α'
    have e2' := congrFun (congrFun hU2 α) α'
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply] at e1' e2' ⊢
    rw [Fintype.sum_prod_type] at e1' e2' ⊢
    have : ∀ β, ∑ x : Fin e1 ⊕ Fin e2, star (V (β, x) α) * V (β, x) α' =
        (t : ℂ) * ∑ ε, star (U1 (β, ε) α) * U1 (β, ε) α' +
        ((1 - t : ℝ) : ℂ) * ∑ ε, star (U2 (β, ε) α) * U2 (β, ε) α' := by
      intro β
      rw [Fintype.sum_sum_type, Finset.mul_sum, Finset.mul_sum, ← hs1', ← hs2']
      congr 1
      · refine Finset.sum_congr rfl (fun ε _ => ?_)
        show star (s1 * _) * (s1 * _) = _
        rw [star_mul']; ring
      · refine Finset.sum_congr rfl (fun ε _ => ?_)
        show star (s2 * _) * (s2 * _) = _
        rw [star_mul']; ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, e1', e2']
    push_cast
    ring
  · intro X
    rw [sumKraus_apply, hrec, ← hD1, ← hD2, hcomp1, hcomp2, hD1, hD2, kraus_smul, kraus_smul,
      ← hD1, ← hD2, hDU1, hDU2]
    simp [Matrix.transpose_add, Matrix.transpose_smul]

end X7S1

end QAlgorithms.Papers.Independent.Support50.P01

end

section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P01 in
theorem solution {a b : ℕ} (ha : 0<a) (hb : 0<b)
    (Phi Psi : Superop (Fin a) (Fin b))
    (hPhi : ConjugateAntiChannel Phi) (hPsi : ConjugateAntiChannel Psi)
    (t : ℝ) (ht0 : 0≤t) (ht1 : t≤1) :
    ConjugateAntiChannel (fun X => (t : ℂ) • Phi X + ((1-t : ℝ) : ℂ) • Psi X) :=
  QAlgorithms.Papers.Independent.Support50.P01.X7S1.convex_main ha hb Phi Psi hPhi hPsi t ht0 ht1

end
