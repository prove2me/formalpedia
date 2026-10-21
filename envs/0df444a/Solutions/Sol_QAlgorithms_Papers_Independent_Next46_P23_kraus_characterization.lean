-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P23.kraus_characterization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T22:47:24.174151+00:00
-- url     : https://prove2.me/submissions/8867a31c-c4f3-4f60-85f7-a4cf6a1d0a71

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P23
noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

open QAlgorithms.Papers.Independent.Next46.P23

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P15 (propagator legendre rightSlope leftSlope FiniteExperiment exponentialMoment)

open QAlgorithms.Papers.Independent.Dependency50.P05 (uniformDensity)

open QAlgorithms.Papers.Independent.Dependency50.P28 (Schwarz)

open QAlgorithms.Papers.Independent.Frontier30.P28 (inverseExponent)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms (traceRight)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem g64d_lin_expand (M : Mat I →ₗ[ℂ] Mat J)
    (X : Mat I) : M X = ∑ i, ∑ j, X i j • M (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

theorem g64d_sum_psd {K ι : Type*} [Fintype K] (s : Finset ι) (A : ι → Matrix K K ℂ)
    (h : ∀ i, (A i).PosSemidef) : (∑ i ∈ s, A i).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Matrix.PosSemidef.zero
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact (h a).add ih

theorem g64d_swap22 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    ∑ i, ∑ j, ∑ m, ∑ l, f i j m l = ∑ m, ∑ l, ∑ i, ∑ j, f i j m l := by
  calc ∑ i, ∑ j, ∑ m, ∑ l, f i j m l = ∑ i, ∑ m, ∑ j, ∑ l, f i j m l :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ m, ∑ i, ∑ j, ∑ l, f i j m l := Finset.sum_comm
    _ = ∑ m, ∑ i, ∑ l, ∑ j, f i j m l :=
        Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ m, ∑ l, ∑ i, ∑ j, f i j m l := Finset.sum_congr rfl fun m _ => Finset.sum_comm

theorem g64d_cp_of_rep (M : Mat I →ₗ[ℂ] Mat J) (m2 : ℕ) (g : Fin m2 → (J × I → ℂ))
    (hMij : ∀ i j o o', M (Matrix.single i j 1) o o' = ∑ l, g l (o, i) * star (g l (o', j))) :
    QAlgorithms.Entanglement.IsCompletelyPositive M := by
  intro r X hX
  obtain ⟨m1, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hX
  let F : Fin m1 → Fin m2 → (Fin r × J → ℂ) := fun a l q => ∑ i, v a (q.1, i) * g l (q.2, i)
  have hY : QAlgorithms.idTensorSuperop M X = ∑ a, ∑ l, Matrix.vecMulVec (F a l) (star (F a l)) := by
    ext ⟨x, o⟩ ⟨y, o'⟩
    show M (Matrix.of fun i j => X (x, i) (y, j)) o o' = _
    rw [g64d_lin_expand]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, hMij, hv,
      Matrix.vecMulVec_apply, Pi.star_apply, F, star_sum, star_mul']
    simp only [Finset.sum_mul_sum]
    rw [g64d_swap22]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hY]
  exact g64d_sum_psd _ _ fun a => g64d_sum_psd _ _ fun l =>
    Matrix.posSemidef_vecMulVec_self_star _

theorem g64d_choi_of_cp (M : Mat I →ₗ[ℂ] Mat J)
    (h : QAlgorithms.Entanglement.IsCompletelyPositive M) :
    (Matrix.of fun (p q : J × I) => M (Matrix.single p.2 q.2 1) p.1 q.1).PosSemidef := by
  let e := Fintype.equivFin I
  let Ω : Fin (Fintype.card I) × I → ℂ := fun q => if q.1 = e q.2 then 1 else 0
  have hY := h _ _ (Matrix.posSemidef_vecMulVec_self_star Ω)
  have hE : (Matrix.of fun (p q : J × I) => M (Matrix.single p.2 q.2 1) p.1 q.1) =
      (QAlgorithms.idTensorSuperop M (Matrix.vecMulVec Ω (star Ω))).submatrix
      (fun q : J × I => (e q.2, q.1)) (fun q => (e q.2, q.1)) := by
    ext ⟨o, i⟩ ⟨o', i'⟩
    rw [Matrix.submatrix_apply, Matrix.of_apply]
    show M (Matrix.single i i' 1) o o' =
      M (Matrix.of fun j j' => Matrix.vecMulVec Ω (star Ω) (e i, j) (e i', j')) o o'
    have hX : (Matrix.of fun j j' => Matrix.vecMulVec Ω (star Ω) (e i, j) (e i', j')) =
        Matrix.single i i' 1 := by
      ext j j'
      by_cases h1 : i = j <;> by_cases h2 : i' = j' <;>
        simp [Matrix.single_apply, Matrix.vecMulVec_apply, Ω, h1, h2, Ne.symm, eq_comm]
    rw [hX]
  rw [hE]
  exact hY.submatrix _

theorem g64d_kraus_single (r : ℕ) (V : Fin r → Matrix J I ℂ) (i j : I) (o o' : J) :
    (∑ k, V k * Matrix.single i j (1 : ℂ) * (V k)ᴴ) o o' = ∑ k, V k o i * star (V k o' j) := by
  rw [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, ite_and,
    Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem g64d_trace_ext (X Y : Mat I) (h : ∀ B : Mat I, (X * B).trace = (Y * B).trace) : X = Y := by
  ext i j
  have := h (Matrix.single j i 1)
  simpa [Matrix.trace_mul_single] using this

theorem solution [Nonempty I] [Nonempty J] (Phi : Mat I →ₗ[ℂ] Mat J) :
    (QAlgorithms.Entanglement.IsCompletelyPositive Phi ↔
      ∃ r : ℕ, ∃ V : Fin r → Matrix J I ℂ,
        ∀ A, Phi A = ∑ k, V k * A * (V k)ᴴ) ∧
    (∀ r : ℕ, ∀ V : Fin r → Matrix J I ℂ,
      (∀ A, Phi A = ∑ k, V k * A * (V k)ᴴ) →
      (Phi 1 = 1 ↔ ∑ k, V k * (V k)ᴴ = 1) ∧
      ((∀ A, (Phi A).trace = A.trace) ↔ ∑ k, (V k)ᴴ * V k = 1)) := by
  refine ⟨⟨fun hcp => ?_, fun ⟨r, V, hV⟩ => ?_⟩, fun r V hV => ⟨?_, ?_⟩⟩
  · obtain ⟨m, g, hg⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp (g64d_choi_of_cp Phi hcp)
    refine ⟨m, fun l => Matrix.of fun o i => g l (o, i), fun A => ?_⟩
    have h1 : ∀ i j o o', Phi (Matrix.single i j 1) o o' = ∑ l, g l (o, i) * star (g l (o', j)) := by
      intro i j o o'
      have := congrFun (congrFun hg (o, i)) (o', j)
      simp only [Matrix.of_apply] at this
      rw [this, Matrix.sum_apply]
      simp [Matrix.vecMulVec_apply]
    ext o o'
    rw [g64d_lin_expand Phi A]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, h1, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    simp only [RCLike.star_def]; ring
  · refine g64d_cp_of_rep Phi r (fun k p => V k p.1 p.2) fun i j o o' => ?_
    rw [hV, g64d_kraus_single]
  · rw [hV 1]; simp
  · have key : ∀ A, (Phi A).trace = ((∑ k, (V k)ᴴ * V k) * A).trace := by
      intro A
      rw [hV A, Matrix.trace_sum, Finset.sum_mul, Matrix.trace_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.mul_assoc]
    constructor
    · intro h
      apply g64d_trace_ext
      intro B
      rw [← key, h, Matrix.one_mul]
    · intro h A
      rw [key, h, Matrix.one_mul]
