-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P36.tensorBellCanonicalDecomposition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T16:48:25.235305+00:00
-- url     : https://prove2.me/submissions/73d6dce8-866c-42ac-ad96-102e8ebf6d02

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P36
noncomputable section

open MeasureTheory Filter

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

attribute [local instance] Classical.decEq Classical.propDecidable

open QAlgorithms.Papers.Independent.Next46.P36

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P36.matrixMeasurable

variable {G : Type*} [Group G] [TopologicalSpace G]

theorem g62i_card_mi {d N : ℕ} {S : Type*} [Fintype S] [DecidableEq S]
    (D : S → BasedIrrep (Matrix.specialUnitaryGroup (Fin d) ℂ))
    (B : BasedDecomposition (actualTensorRepresentation d N) D) :
    (∑ s, ((D s).dim : ℝ) * B.multiplicity s) = (d : ℝ) ^ N := by
  have h1 := congrArg Matrix.trace B.isometry
  have h2 := congrArg Matrix.trace B.exhaustive
  rw [Matrix.trace_mul_comm] at h1
  rw [h1] at h2
  simp only [Matrix.trace_one, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fun] at h2
  have : (∑ s, (D s).dim * B.multiplicity s : ℕ) = d ^ N := by exact_mod_cast h2
  exact_mod_cast this

theorem g62i_basis_entry {d N : ℕ} {S : Type*} [Fintype S] [DecidableEq S]
    (D : S → BasedIrrep (Matrix.specialUnitaryGroup (Fin d) ℂ))
    (B : BasedDecomposition (actualTensorRepresentation d N) D) (x y) :
    (∑ p, conj (B.basis p x) * B.basis p y) = if x = y then 1 else 0 := by
  have := congrFun (congrFun B.isometry x) y
  rw [Matrix.mul_apply] at this
  simpa [Matrix.conjTranspose_apply, Matrix.one_apply] using this

theorem g62i_basis_entry' {d N : ℕ} {S : Type*} [Fintype S] [DecidableEq S]
    (D : S → BasedIrrep (Matrix.specialUnitaryGroup (Fin d) ℂ))
    (B : BasedDecomposition (actualTensorRepresentation d N) D) (a b) :
    (∑ x, B.basis a x * conj (B.basis b x)) = if a = b then 1 else 0 := by
  have := congrFun (congrFun B.exhaustive a) b
  rw [Matrix.mul_apply] at this
  simpa [Matrix.conjTranspose_apply, Matrix.one_apply] using this

theorem g62i_core {X Y : Type*} [Fintype X] (b : X → Y → ℂ) (α α' β β' : Y) :
    (∑ p : X × X, star (b p.1 α * conj (b p.2 β)) * (b p.1 α' * conj (b p.2 β'))) =
      (∑ x, conj (b x α) * b x α') * conj (∑ x, conj (b x β) * b x β') := by
  rw [Fintype.sum_prod_type, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  simp only [star_mul', Complex.star_def, map_mul, Complex.conj_conj]
  ring

theorem g62i_iso {d N : ℕ} {S : Type*} [Fintype S] [DecidableEq S]
    (D : S → BasedIrrep (Matrix.specialUnitaryGroup (Fin d) ℂ))
    (B : BasedDecomposition (actualTensorRepresentation d N) D) :
    (bellEmbedding D B)ᴴ * bellEmbedding D B = 1 := by
  ext ⟨s, i, j⟩ ⟨s', i', j'⟩
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, bellEmbedding, star_mul', star_sum]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_comm (γ := TensorRegister d N × TensorRegister d N)]
  have e1 : ∀ (k' : Fin (B.multiplicity s')) (k : Fin (B.multiplicity s)),
      (∑ p : TensorRegister d N × TensorRegister d N,
        star ((Real.sqrt (B.multiplicity s) : ℂ)⁻¹) *
          (star (B.basis p.1 ⟨s, (i, k)⟩) * star (conj (B.basis p.2 ⟨s, (j, k)⟩))) *
        ((Real.sqrt (B.multiplicity s') : ℂ)⁻¹ *
          (B.basis p.1 ⟨s', (i', k')⟩ * conj (B.basis p.2 ⟨s', (j', k')⟩)))) =
      star ((Real.sqrt (B.multiplicity s) : ℂ)⁻¹) * (Real.sqrt (B.multiplicity s') : ℂ)⁻¹ *
        ((if (⟨s, (i, k)⟩ : MultiplicityIndex D B.multiplicity) = ⟨s', (i', k')⟩ then 1 else 0) *
          conj (if (⟨s, (j, k)⟩ : MultiplicityIndex D B.multiplicity) = ⟨s', (j', k')⟩ then 1 else 0)) := by
    intro k' k
    have h := g62i_core (fun x y => B.basis x y) ⟨s, (i, k)⟩ ⟨s', (i', k')⟩ ⟨s, (j, k)⟩ ⟨s', (j', k')⟩
    have h1 := g62i_basis_entry D B ⟨s, (i, k)⟩ ⟨s', (i', k')⟩
    have h2 := g62i_basis_entry D B ⟨s, (j, k)⟩ ⟨s', (j', k')⟩
    beta_reduce at h
    rw [h1, h2] at h
    rw [← h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [star_mul']
    ring
  simp only [e1]
  by_cases hs : s = s'
  · subst hs
    simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and, Prod.mk.injEq, Matrix.one_apply]
    by_cases hi : i = i' <;> by_cases hj : j = j' <;> simp [hi, hj]
    have hm : (0:ℝ) < B.multiplicity s := by exact_mod_cast B.positive s
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt hm.le]
    have : (B.multiplicity s : ℂ) ≠ 0 := by exact_mod_cast (B.positive s).ne'
    push_cast
    field_simp
  · have : (⟨s, (i, j)⟩ : CanonicalIndex D) ≠ ⟨s', (i', j')⟩ := fun h => hs (congrArg Sigma.fst h)
    rw [Matrix.one_apply_ne this]
    refine Finset.sum_eq_zero fun k' _ => Finset.sum_eq_zero fun k _ => ?_
    have h1 : (⟨s, (i, k)⟩ : MultiplicityIndex D B.multiplicity) ≠ ⟨s', (i', k')⟩ :=
      fun h => hs (congrArg Sigma.fst h)
    simp [h1]

theorem g62i_blk {S R : Type*} [Fintype S] [DecidableEq S] (n m : S → ℕ)
    (A : ∀ s, Matrix (Fin (n s)) (Fin (n s)) ℂ)
    (X : Matrix R ((s : S) × (Fin (n s) × Fin (m s))) ℂ) (r : R) (s : S) (i : Fin (n s))
    (k : Fin (m s)) :
    (X * Matrix.blockDiagonal' (fun s => A s ⊗ₖ (1 : Matrix (Fin (m s)) (Fin (m s)) ℂ))) r ⟨s, (i, k)⟩ =
      ∑ i', X r ⟨s, (i', k)⟩ * A s i' i := by
  rw [Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single s]
  · rw [Fintype.sum_prod_type]
    simp only [Matrix.blockDiagonal'_apply_eq, Matrix.kroneckerMap_apply, Matrix.one_apply]
    refine Finset.sum_congr rfl fun i' _ => ?_
    simp
  · intro t _ ht
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ ht, mul_zero]
  · simp

theorem g62i_intertwine {d N : ℕ} {S : Type*} [Fintype S] [DecidableEq S]
    (D : S → BasedIrrep (Matrix.specialUnitaryGroup (Fin d) ℂ))
    (B : BasedDecomposition (actualTensorRepresentation d N) D) (g) :
    bellAction d N g * bellEmbedding D B = bellEmbedding D B * canonicalAction D g := by
  ext p ⟨s, i, j⟩
  have hR := g62i_blk (fun s => (D s).dim) (fun s => (D s).dim) (fun s => (D s).matrix g)
    (bellEmbedding D B) p s i j
  rw [canonicalAction, hR]
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [bellAction, Matrix.kroneckerMap_apply, Matrix.one_apply, bellEmbedding]
  have hL : ∀ k : Fin (B.multiplicity s),
      (actualTensorRepresentation d N g * B.basis) p.1 ⟨s, (i, k)⟩ =
        ∑ i', B.basis p.1 ⟨s, (i', k)⟩ * (D s).matrix g i' i := by
    intro k
    rw [B.intertwines g, multiplicityAction, g62i_blk]
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_zero, mul_one, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have e : ∀ k : Fin (B.multiplicity s), (∑ a, actualTensorRepresentation d N g p.1 a *
      ((Real.sqrt (B.multiplicity s) : ℂ)⁻¹ * (B.basis a ⟨s, (i, k)⟩ * conj (B.basis p.2 ⟨s, (j, k)⟩)))) =
      (Real.sqrt (B.multiplicity s) : ℂ)⁻¹ * conj (B.basis p.2 ⟨s, (j, k)⟩) *
        (actualTensorRepresentation d N g * B.basis) p.1 ⟨s, (i, k)⟩ := by
    intro k
    rw [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  simp only [e, hL, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem g62i_coef {d N : ℕ} (hd : 0 < d) {S : Type*} [Fintype S] [DecidableEq S]
    (D : S → BasedIrrep (Matrix.specialUnitaryGroup (Fin d) ℂ))
    (B : BasedDecomposition (actualTensorRepresentation d N) D) (s : S) :
    (Real.sqrt (B.multiplicity s))⁻¹ * (bellCoefficient D B s / Real.sqrt (D s).dim) =
      (Real.sqrt ((d : ℝ) ^ N))⁻¹ := by
  have hm : (0:ℝ) < B.multiplicity s := by exact_mod_cast B.positive s
  have hD : (0:ℝ) < (D s).dim := by exact_mod_cast (D s).positive
  have hn : (0:ℝ) < (d : ℝ) ^ N := by positivity
  rw [bellCoefficient, Real.sqrt_div' _ hn.le, Real.sqrt_mul hD.le]
  have h1 := Real.sqrt_pos.2 hm
  have h2 := Real.sqrt_pos.2 hD
  have h3 := Real.sqrt_pos.2 hn
  field_simp

theorem g62i_vec {d N : ℕ} (hd : 0 < d) {S : Type*} [Fintype S] [DecidableEq S]
    (D : S → BasedIrrep (Matrix.specialUnitaryGroup (Fin d) ℂ))
    (B : BasedDecomposition (actualTensorRepresentation d N) D) :
    tensorBell d N = WithLp.toLp 2 ((bellEmbedding D B).mulVec
      (WithLp.ofLp (canonicalInput D (fun s => (bellCoefficient D B s : ℂ)) (fun _ => 1)))) := by
  rw [tensorBell]
  congr 1
  funext p
  simp only [Matrix.mulVec, dotProduct, canonicalInput, Fintype.sum_sigma, Fintype.sum_prod_type,
    bellEmbedding]
  simp only [OneMemClass.coe_one, Matrix.one_apply, mul_ite, mul_zero, mul_one,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hk : ∀ s, (Real.sqrt (B.multiplicity s) : ℂ)⁻¹ *
      ((bellCoefficient D B s : ℂ) / (Real.sqrt (D s).dim : ℂ)) = (Real.sqrt ((d : ℝ) ^ N) : ℂ)⁻¹ := by
    intro s
    have := g62i_coef hd D B s
    have := congrArg (fun x : ℝ => (x : ℂ)) this
    push_cast at this
    exact this
  have e : ∀ s (i : Fin (D s).dim),
      (Real.sqrt (B.multiplicity s) : ℂ)⁻¹ *
        (∑ k : Fin (B.multiplicity s), B.basis p.1 ⟨s, (i, k)⟩ * conj (B.basis p.2 ⟨s, (i, k)⟩)) *
        ((bellCoefficient D B s : ℂ) / (Real.sqrt (D s).dim : ℂ)) =
      (Real.sqrt ((d : ℝ) ^ N) : ℂ)⁻¹ *
        ∑ k : Fin (B.multiplicity s), B.basis p.1 ⟨s, (i, k)⟩ * conj (B.basis p.2 ⟨s, (i, k)⟩) := by
    intro s i
    rw [← hk s]
    ring
  simp only [e, ← Finset.mul_sum]
  have hB := g62i_basis_entry' D B p.1 p.2
  rw [Fintype.sum_sigma] at hB
  simp only [Fintype.sum_prod_type] at hB
  rw [hB]
  split_ifs <;> simp

theorem g62i_state {d N : ℕ} (hd : 0 < d) : QAlgorithms.IsState (tensorBell d N) := by
  have hn : (0:ℝ) < (d : ℝ) ^ N := by positivity
  rw [QAlgorithms.IsState, EuclideanSpace.norm_eq, Real.sqrt_eq_one, Fintype.sum_prod_type]
  simp only [tensorBell]
  simp only [apply_ite (fun x : ℂ => ‖x‖ ^ 2), norm_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    nsmul_eq_mul]
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
    Real.sq_sqrt hn.le]
  push_cast
  field_simp

theorem g62i_coefsum {d N : ℕ} (hd : 0 < d) {S : Type*} [Fintype S] [DecidableEq S]
    (D : S → BasedIrrep (Matrix.specialUnitaryGroup (Fin d) ℂ))
    (B : BasedDecomposition (actualTensorRepresentation d N) D) :
    (∑ s, (bellCoefficient D B s) ^ 2) = 1 := by
  have hn : (0:ℝ) < (d : ℝ) ^ N := by positivity
  simp only [bellCoefficient]
  rw [Finset.sum_congr rfl fun s _ => Real.sq_sqrt (by positivity), ← Finset.sum_div,
    g62i_card_mi D B, div_self hn.ne']

/-- PDF pp.9-11 Lemma 4 and Eqs.(59),(60),(75),(76): the embedding is the
specific one computed from the actual Clebsch-Gordan basis; it is fixed before g. -/
theorem solution
    (d N : ℕ) (hd : 0 < d) (hN : 1 ≤ N)
    {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (D : S → BasedIrrep (Matrix.specialUnitaryGroup (Fin d) ℂ)) (hD : OccurringIrrepsInequivalent D)
    (B : BasedDecomposition (actualTensorRepresentation d N) D) :
    QAlgorithms.IsState (tensorBell d N) ∧
    (∑ s, (bellCoefficient D B s) ^ 2) = 1 ∧
    (bellEmbedding D B)ᴴ * bellEmbedding D B = 1 ∧
    (∀ g, bellAction d N g * bellEmbedding D B =
      bellEmbedding D B * canonicalAction D g) ∧
    tensorBell d N = WithLp.toLp 2 ((bellEmbedding D B).mulVec
      (WithLp.ofLp (canonicalInput D (fun s => (bellCoefficient D B s : ℂ)) (fun _ => 1)))) :=
  ⟨g62i_state hd, g62i_coefsum hd D B, g62i_iso D B, g62i_intertwine D B, g62i_vec hd D B⟩


end
