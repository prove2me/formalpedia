-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P01.conjugateAnti_postprocess
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T02:51:07.588302+00:00
-- url     : https://prove2.me/submissions/eaec9486-d604-4cea-91d7-05514862a00e

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

variable {a b c e m : ℕ}

lemma star_ite' (p : Prop) [Decidable p] (x y : ℂ) :
    star (if p then x else y) = if p then star x else star y := by
  split_ifs <;> rfl

/-- Stinespring-type isometry of the Kraus family `E`, acting on the receiver output. -/
def postW (E : Fin m → Matrix (Fin c) (Fin b) ℂ) :
    Matrix (Fin c × (Fin e × Fin m)) (Fin b × Fin e) ℂ :=
  Matrix.of fun p q => E p.2.2 p.1 q.1 * (if q.2 = p.2.1 then 1 else 0)

lemma postW_conj (E : Fin m → Matrix (Fin c) (Fin b) ℂ)
    (M : Matrix (Fin b × Fin e) (Fin b × Fin e) ℂ) (γ γ' : Fin c) (ε ε' : Fin e) (k k' : Fin m) :
    (postW (e := e) E * M * (postW (e := e) E)ᴴ) (γ, (ε, k)) (γ', (ε', k')) =
      ∑ β, ∑ β', E k γ β * M (β, ε) (β', ε') * star (E k' γ' β') := by
  simp only [postW, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Fintype.sum_prod_type, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, star_ite', star_zero,
    star_one, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  rw [Finset.sum_mul]

lemma postW_apply (E : Fin m → Matrix (Fin c) (Fin b) ℂ) (γ : Fin c) (ε'' : Fin e) (k : Fin m)
    (β : Fin b) (ε : Fin e) :
    postW (e := e) E (γ, (ε'', k)) (β, ε) = if ε = ε'' then E k γ β else 0 := by
  simp [postW]

lemma postW_iso (E : Fin m → Matrix (Fin c) (Fin b) ℂ) (hE : ∑ k, (E k)ᴴ * E k = 1) :
    (postW (e := e) E)ᴴ * postW (e := e) E = 1 := by
  ext q q'
  obtain ⟨β, ε⟩ := q
  obtain ⟨β', ε'⟩ := q'
  have h := congrFun (congrFun hE β) β'
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply] at h
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type, postW_apply]
  rw [Finset.sum_comm, Finset.sum_eq_single ε]
  · rw [Matrix.one_apply]
    by_cases hεε : ε' = ε
    · subst hεε
      simp only [if_true, Prod.mk.injEq, and_true]
      rw [Finset.sum_comm, h, Matrix.one_apply]
    · simp [hεε, Ne.symm hεε]
  · intro ε'' _ hne
    simp [Ne.symm hne]
  · simp

/-- The Kraus family tracing out the `Fin m` factor. -/
def traceK : Fin m → Matrix (Fin e) (Fin e × Fin m) ℂ :=
  fun k => Matrix.of fun ε q => if q = (ε, k) then 1 else 0

lemma traceK_apply (Y : Matrix (Fin e × Fin m) (Fin e × Fin m) ℂ) (ε ε' : Fin e) :
    krausApply traceK Y ε ε' = ∑ k, Y (ε, k) (ε', k) := by
  simp only [krausApply, traceK, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.of_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero, star_ite', star_one,
    star_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma traceK_family : IsKrausFamily (traceK (e := e) (m := m)) := by
  unfold IsKrausFamily
  ext q q'
  obtain ⟨ε, k⟩ := q
  obtain ⟨ε', k'⟩ := q'
  rw [Matrix.sum_apply]
  simp only [traceK, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, star_ite',
    star_one, star_zero, ite_mul, one_mul, zero_mul, Matrix.one_apply, Prod.mk.injEq]
  simp only [ite_and, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  by_cases h1 : ε = ε' <;> by_cases h2 : k = k' <;> simp [h1, h2, eq_comm]

lemma sum3 {K G B : Type*} [Fintype K] [Fintype G] [Fintype B]
    (f : K → G → B → ℂ) :
    ∑ k, ∑ γ, ∑ β, f k γ β = ∑ β, ∑ γ, ∑ k, f k γ β := by
  calc ∑ k, ∑ γ, ∑ β, f k γ β
      = ∑ x : K × G × B, f x.1 x.2.1 x.2.2 := by
        simp only [Fintype.sum_prod_type]
    _ = ∑ y : B × G × K, f y.2.2 y.2.1 y.1 :=
        Fintype.sum_equiv
          ⟨fun x => (x.2.2, x.2.1, x.1), fun y => (y.2.2, y.2.1, y.1),
            fun _ => rfl, fun _ => rfl⟩ _ _ (fun _ => rfl)
    _ = _ := by simp only [Fintype.sum_prod_type]

lemma sum4 {K G B B' : Type*} [Fintype K] [Fintype G] [Fintype B] [Fintype B']
    (f : K → G → B → B' → ℂ) :
    ∑ k, ∑ γ, ∑ β, ∑ β', f k γ β β' = ∑ β, ∑ β', ∑ k, ∑ γ, f k γ β β' := by
  calc ∑ k, ∑ γ, ∑ β, ∑ β', f k γ β β'
      = ∑ x : K × G × B × B', f x.1 x.2.1 x.2.2.1 x.2.2.2 := by
        simp only [Fintype.sum_prod_type]
    _ = ∑ y : B × B' × K × G, f y.2.2.1 y.2.2.2 y.1 y.2.1 :=
        Fintype.sum_equiv
          ⟨fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1), fun y => (y.2.2.1, y.2.2.2, y.1, y.2.1),
            fun _ => rfl, fun _ => rfl⟩ _ _ (fun _ => rfl)
    _ = _ := by simp only [Fintype.sum_prod_type]

lemma post_main (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (Phi : Superop (Fin a) (Fin b)) (Delta : Superop (Fin b) (Fin c))
    (hPhi : ConjugateAntiChannel Phi) (hDelta : IsChannel Delta) :
    ConjugateAntiChannel (Delta ∘ Phi) := by
  obtain ⟨e, he, U, ⟨hU, D, hD, hDU⟩, rfl⟩ := hPhi
  obtain ⟨m, E, hE, hΔ⟩ := hDelta
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0
      have := congrFun (congrFun hE ⟨0, hb⟩) ⟨0, hb⟩
      simp at this
    · exact h0
  have : Nonempty (Fin e × Fin m) := ⟨(⟨0, he⟩, ⟨0, hm⟩)⟩
  let W := postW (e := e) E
  let V := W * U
  have hVX : ∀ X : Matrix (Fin a) (Fin a) ℂ, V * X * Vᴴ = W * (U * X * Uᴴ) * Wᴴ := by
    intro X; simp only [V, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hrec : receiverChannel V = Delta ∘ receiverChannel U := by
    funext X
    ext γ γ'
    simp only [Function.comp, hΔ, receiverChannel, traceRight, Matrix.of_apply, hVX]
    generalize U * X * Uᴴ = M
    rw [Fintype.sum_prod_type]
    simp only [W, postW_conj]
    simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.of_apply, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [sum3 (fun ε β β' => E k γ β * M (β, ε) (β', ε) * star (E k γ' β'))]
  have htk : ∀ X, krausApply traceK (complementaryChannel V X) = complementaryChannel U X := by
    intro X
    ext ε ε'
    rw [traceK_apply]
    simp only [complementaryChannel, traceLeft, Matrix.of_apply, hVX]
    generalize U * X * Uᴴ = M
    simp only [W, postW_conj]
    rw [sum4 (fun k γ β β' => E k γ β * M (β, ε) (β', ε') * star (E k γ β'))]
    refine Finset.sum_congr rfl (fun β _ => ?_)
    have hk : ∀ β', ∑ k, ∑ γ, E k γ β * M (β, ε) (β', ε') * star (E k γ β') =
        if β' = β then M (β, ε) (β', ε') else 0 := by
      intro β'
      have := congrFun (congrFun hE β') β
      simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.one_apply] at this
      have e2 : ∑ k, ∑ γ, E k γ β * M (β, ε) (β', ε') * star (E k γ β') =
          M (β, ε) (β', ε') * ∑ k, ∑ γ, star (E k γ β') * E k γ β := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun γ _ => ?_)
        ring
      rw [e2, this]
      split_ifs <;> simp
    simp only [hk, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← hrec]
  apply reindex_cad
  obtain ⟨G, hG, hGt⟩ := chan_conj Delta ⟨m, E, hE, hΔ⟩
  refine ⟨?_, G ∘ D ∘ krausApply traceK, ?_, ?_⟩
  · simp only [V, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Wᴴ W U, postW_iso E hE, Matrix.one_mul, hU]
  · have hT : @IsChannel _ _ _ _ (Classical.decEq _) (krausApply (traceK (e := e) (m := m))) := by
      convert chan_of_kraus _ (traceK_family (e := e) (m := m))
    exact chan_comp _ _ (chan_comp _ _ hT hD) hG
  · intro X
    simp only [Function.comp]
    rw [htk, hDU, hGt, hrec]
    rfl

end X7S1

end QAlgorithms.Papers.Independent.Support50.P01

end

section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P01 in
theorem solution {a b c : ℕ} (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (Phi : Superop (Fin a) (Fin b)) (Delta : Superop (Fin b) (Fin c))
    (hPhi : ConjugateAntiChannel Phi) (hDelta : IsChannel Delta) :
    ConjugateAntiChannel (Delta ∘ Phi) :=
  QAlgorithms.Papers.Independent.Support50.P01.X7S1.post_main ha hb hc Phi Delta hPhi hDelta

end
