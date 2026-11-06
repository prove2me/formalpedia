-- Prove2me | solution 1 for StrongConv.exists_stableRep_noTrivialSummand_schreierAdjPerp_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T23:13:27.376859+00:00
-- url     : https://prove2.me/submissions/e995d828-f23a-411e-b3f5-153db26939b8

import Definitions.Def_StrongConv
import Definitions.Def_StrongConvG2
import Mathlib

section
section
noncomputable section

namespace StrongConv
namespace W2Sec3

open scoped InnerProductSpace

lemma tuplePermOp_ones (k N : ℕ) (τ : Equiv.Perm (Fin N)) :
    tuplePermOp k τ (tupleOnes k N) = tupleOnes k N := by
  ext j
  simp [tuplePermOp, tupleOnes, LinearIsometryEquiv.piLpCongrLeft_apply]

lemma tuplePermOp_mem (k N : ℕ) (τ : Equiv.Perm (Fin N)) (x : TupleOnesPerp k N) :
    tuplePermOp k τ x ∈ TupleOnesPerp k N := by
  have hx := x.2
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hx ⊢
  rw [← tuplePermOp_ones k N τ]
  simp only [tuplePermOp, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.inner_map_map]
  simpa [tuplePermOp] using hx

/-- The restriction of `P_σ` to `{1}⊥`. -/
def Rop (k : ℕ) {N : ℕ} (σ : Equiv.Perm (Fin N)) : TupleOnesPerp k N →L[ℂ] TupleOnesPerp k N :=
  ((tuplePermOp k σ).comp (TupleOnesPerp k N).subtypeL).codRestrict (TupleOnesPerp k N)
    (fun x => tuplePermOp_mem k N σ x)

end W2Sec3
end StrongConv

end
end
end

section
section
noncomputable section

namespace StrongConv
namespace W2Sec3

open scoped InnerProductSpace

lemma tuplePermOp_apply (k N : ℕ) (σ : Equiv.Perm (Fin N)) (x : EuclideanSpace ℂ (Fin k ↪ Fin N))
    (t : Fin k ↪ Fin N) : tuplePermOp k σ x t = x ((tuplePerm k σ).symm t) := by
  simp [tuplePermOp, LinearIsometryEquiv.piLpCongrLeft_apply]

lemma tuplePerm_symm (k N : ℕ) (σ : Equiv.Perm (Fin N)) :
    (tuplePerm k σ).symm = tuplePerm k σ⁻¹ := by
  exact Equiv.ext fun t => Function.Embedding.ext fun i => rfl

lemma tuplePermOp_mul (k N : ℕ) (σ τ : Equiv.Perm (Fin N)) :
    tuplePermOp k (σ * τ) = tuplePermOp k σ * tuplePermOp k τ := by
  refine ContinuousLinearMap.ext fun x => ?_
  ext t
  rw [ContinuousLinearMap.mul_apply]
  simp only [tuplePermOp_apply, tuplePerm_symm]
  exact congrArg (fun a => x a) (Function.Embedding.ext fun i => rfl)

lemma tuplePermOp_one (k N : ℕ) : tuplePermOp k (1 : Equiv.Perm (Fin N)) = 1 := by
  refine ContinuousLinearMap.ext fun x => ?_
  ext t
  simp only [tuplePermOp_apply, tuplePerm_symm, inv_one]
  rfl

lemma inner_tuplePermOp (k N : ℕ) (σ : Equiv.Perm (Fin N)) (x y : EuclideanSpace ℂ (Fin k ↪ Fin N)) :
    ⟪tuplePermOp k σ x, y⟫_ℂ = ⟪x, tuplePermOp k σ⁻¹ y⟫_ℂ := by
  have h : ∀ (a b : EuclideanSpace ℂ (Fin k ↪ Fin N)),
      ⟪tuplePermOp k σ a, tuplePermOp k σ b⟫_ℂ = ⟪a, b⟫_ℂ := fun a b => by
    simp only [tuplePermOp, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.inner_map_map]
  have h2 : tuplePermOp k σ (tuplePermOp k σ⁻¹ y) = y := by
    rw [← ContinuousLinearMap.mul_apply, ← tuplePermOp_mul, mul_inv_cancel, tuplePermOp_one]
    rfl
  conv_lhs => rw [← h2]
  exact h x _

lemma star_tuplePermOp (k N : ℕ) (σ : Equiv.Perm (Fin N)) :
    star (tuplePermOp k σ) = tuplePermOp k σ⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [inner_tuplePermOp, inv_inv]

lemma Rop_mul (k N : ℕ) (σ τ : Equiv.Perm (Fin N)) : Rop k (σ * τ) = Rop k σ * Rop k τ := by
  refine ContinuousLinearMap.ext fun x => Subtype.ext ?_
  show tuplePermOp k (σ * τ) (x : EuclideanSpace ℂ (Fin k ↪ Fin N)) =
    tuplePermOp k σ (tuplePermOp k τ (x : EuclideanSpace ℂ (Fin k ↪ Fin N)))
  rw [tuplePermOp_mul]; rfl

lemma Rop_one (k N : ℕ) : Rop k (1 : Equiv.Perm (Fin N)) = 1 := by
  refine ContinuousLinearMap.ext fun x => Subtype.ext ?_
  show tuplePermOp k 1 (x : EuclideanSpace ℂ (Fin k ↪ Fin N)) = x
  rw [tuplePermOp_one]; rfl

lemma star_Rop (k N : ℕ) (σ : Equiv.Perm (Fin N)) : star (Rop k σ) = Rop k σ⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [Submodule.coe_inner, Submodule.coe_inner]
  have e := inner_tuplePermOp k N σ⁻¹ ↑x ↑y
  rw [inv_inv] at e
  exact e

lemma schreierAdjPerp_eq (k : ℕ) {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) :
    schreierAdjPerp k σ = ∑ i, (Rop k (σ i) + star (Rop k (σ i))) := by
  refine ContinuousLinearMap.ext fun x => Subtype.ext ?_
  rw [ContinuousLinearMap.sum_apply, Submodule.coe_sum]
  show schreierAdj k σ x = _
  rw [schreierAdj, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply, Submodule.coe_add, star_Rop, star_tuplePermOp]
  rfl

end W2Sec3
end StrongConv

end
end
end

section
section
noncomputable section

namespace StrongConv
namespace W2Sec3

open scoped InnerProductSpace

lemma exists_perm_tuple (k N : ℕ) (t t' : Fin k ↪ Fin N) :
    ∃ σ : Equiv.Perm (Fin N), tuplePerm k σ t = t' := by
  classical
  let e : {a // a ∈ Set.range t} ≃ {a // a ∈ Set.range t'} :=
    (Equiv.ofInjective t t.injective).symm.trans (Equiv.ofInjective t' t'.injective)
  refine ⟨Equiv.extendSubtype (p := fun a => a ∈ Set.range t) (q := fun a => a ∈ Set.range t') e,
    Function.Embedding.ext fun i => ?_⟩
  show Equiv.extendSubtype (p := fun a => a ∈ Set.range t) (q := fun a => a ∈ Set.range t') e (t i) = t' i
  rw [Equiv.extendSubtype_apply_of_mem _ _ ⟨i, rfl⟩]
  simp [e]

lemma eq_zero_of_fixed (k N : ℕ) (hk : k ≤ N) (x : TupleOnesPerp k N)
    (h : ∀ σ : Equiv.Perm (Fin N), Rop k σ x = x) : x = 0 := by
  classical
  have hc : ∀ t t' : Fin k ↪ Fin N, (x : EuclideanSpace ℂ (Fin k ↪ Fin N)) t' = (x : EuclideanSpace ℂ (Fin k ↪ Fin N)) t := by
    intro t t'
    obtain ⟨σ, hσ⟩ := exists_perm_tuple k N t t'
    have h1 : tuplePermOp k σ (x : EuclideanSpace ℂ (Fin k ↪ Fin N)) = x := congrArg Subtype.val (h σ)
    have h2 := congrFun (congrArg WithLp.ofLp h1) t'
    rw [show tuplePermOp k σ (x : EuclideanSpace ℂ (Fin k ↪ Fin N)) t' =
      (x : EuclideanSpace ℂ (Fin k ↪ Fin N)) ((tuplePerm k σ).symm t') from tuplePermOp_apply k N σ _ t'] at h2
    have : (tuplePerm k σ).symm t' = t := by rw [← hσ]; simp
    rw [this] at h2
    exact h2.symm
  have hmem := x.2
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hmem
  have : Nonempty (Fin k ↪ Fin N) := ⟨Fin.castLEEmb hk⟩
  obtain ⟨t0⟩ := this
  set c := (x : EuclideanSpace ℂ (Fin k ↪ Fin N)) t0 with hcdef
  have hall : ∀ t, (x : EuclideanSpace ℂ (Fin k ↪ Fin N)) t = c := fun t => hc t0 t
  have hs : ⟪tupleOnes k N, (x : EuclideanSpace ℂ (Fin k ↪ Fin N))⟫_ℂ =
      (Fintype.card (Fin k ↪ Fin N) : ℂ) * c := by
    rw [PiLp.inner_apply]
    simp [tupleOnes, hall]
  rw [hs] at hmem
  have hcard : (Fintype.card (Fin k ↪ Fin N) : ℂ) ≠ 0 := by
    have : 0 < Fintype.card (Fin k ↪ Fin N) := Fintype.card_pos_iff.mpr ⟨t0⟩
    exact_mod_cast this.ne'
  have hc0 : c = 0 := by
    rcases mul_eq_zero.mp hmem with h | h
    · exact absurd h hcard
    · exact h
  apply Subtype.ext
  ext t
  simp [hall, hc0]

end W2Sec3
end StrongConv

end
end
end

section
section
noncomputable section

namespace StrongConv
namespace W2Sec3

open scoped InnerProductSpace

lemma tuplePerm_apply (k N : ℕ) (σ : Equiv.Perm (Fin N)) (t : Fin k ↪ Fin N) (i : Fin k) :
    tuplePerm k σ t i = σ (t i) := rfl

lemma card_fixed_tuples (k N : ℕ) (σ : Equiv.Perm (Fin N)) :
    (Finset.univ.filter fun t : Fin k ↪ Fin N => tuplePerm k σ t = t).card =
      (xi 1 σ).descFactorial k := by
  classical
  have e : {t : Fin k ↪ Fin N // tuplePerm k σ t = t} ≃ (Fin k ↪ {x : Fin N // σ x = x}) :=
    { toFun := fun t => ⟨fun i => ⟨t.1 i, by
          have := congrArg (fun f : Fin k ↪ Fin N => f i) t.2
          simpa [tuplePerm_apply] using this⟩,
        fun i j h => t.1.injective (by simpa using congrArg Subtype.val h)⟩
      invFun := fun t => ⟨t.trans (Function.Embedding.subtype _), by
          exact DFunLike.ext _ _ (fun i => (t i).2)⟩
      left_inv := fun t => by ext i; rfl
      right_inv := fun t => by ext i; rfl }
  have h1 : (Finset.univ.filter fun t : Fin k ↪ Fin N => tuplePerm k σ t = t).card =
      Fintype.card {t : Fin k ↪ Fin N // tuplePerm k σ t = t} := by
    rw [Fintype.card_subtype]
  rw [h1, Fintype.card_congr e, Fintype.card_embedding_eq, Fintype.card_fin]
  congr 1
  rw [Fintype.card_subtype]
  rfl

lemma trace_tuplePermOp (k N : ℕ) (σ : Equiv.Perm (Fin N)) :
    LinearMap.trace ℂ (EuclideanSpace ℂ (Fin k ↪ Fin N)) (tuplePermOp k σ : _ →ₗ[ℂ] _) =
      ((xi 1 σ).descFactorial k : ℂ) := by
  classical
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin k ↪ Fin N) ℂ)]
  have h : ∀ t : Fin k ↪ Fin N,
      ⟪EuclideanSpace.basisFun (Fin k ↪ Fin N) ℂ t,
        (tuplePermOp k σ : _ →ₗ[ℂ] _) (EuclideanSpace.basisFun (Fin k ↪ Fin N) ℂ t)⟫_ℂ =
        if tuplePerm k σ t = t then 1 else 0 := by
    intro t
    simp only [EuclideanSpace.basisFun_apply, tuplePermOp, ContinuousLinearMap.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv]
    rw [LinearIsometryEquiv.piLpCongrLeft_single, EuclideanSpace.inner_single_left,
      EuclideanSpace.single_apply]
    simp [eq_comm]
  simp only [h]
  rw [Finset.sum_boole, card_fixed_tuples]


lemma tupleOnes_ne_zero (k N : ℕ) (hk : k ≤ N) : tupleOnes k N ≠ 0 := by
  intro h
  have : Nonempty (Fin k ↪ Fin N) := ⟨Fin.castLEEmb hk⟩
  obtain ⟨t⟩ := this
  have := congrFun (congrArg WithLp.ofLp h) t
  simp [tupleOnes] at this

lemma trace_Rop (k N : ℕ) (hk : k ≤ N) (σ : Equiv.Perm (Fin N)) :
    LinearMap.trace ℂ (TupleOnesPerp k N) (Rop k σ : _ →ₗ[ℂ] _) =
      ((xi 1 σ).descFactorial k : ℂ) - 1 := by
  classical
  set K : Submodule ℂ (EuclideanSpace ℂ (Fin k ↪ Fin N)) := ℂ ∙ tupleOnes k N with hK
  let P : EuclideanSpace ℂ (Fin k ↪ Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin k ↪ Fin N) :=
    (tuplePermOp k σ : _ →ₗ[ℂ] _)
  let Nn : Fin 2 → Submodule ℂ (EuclideanSpace ℂ (Fin k ↪ Fin N)) := ![K, Kᗮ]
  have hint : DirectSum.IsInternal Nn := by
    rw [DirectSum.isInternal_submodule_iff_isCompl Nn (i := 0) (j := 1) (by decide) (by
      ext i; fin_cases i <;> simp)]
    exact Submodule.isCompl_orthogonal_of_hasOrthogonalProjection
  have hKP : ∀ x ∈ K, P x = x := by
    intro x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp [P, tuplePermOp_ones]
  have hmaps : ∀ i, Set.MapsTo P (Nn i) (Nn i) := by
    intro i; fin_cases i
    · intro x hx
      have hx' : x ∈ K := hx
      show P x ∈ K
      rw [hKP x hx']; exact hx'
    · intro x hx
      exact tuplePermOp_mem k N σ ⟨x, hx⟩
  have h := LinearMap.trace_eq_sum_trace_restrict hint hmaps
  rw [Fin.sum_univ_two] at h
  have hP : LinearMap.trace ℂ _ P = ((xi 1 σ).descFactorial k : ℂ) := trace_tuplePermOp k N σ
  have hfin : Module.finrank ℂ K = 1 := finrank_span_singleton (tupleOnes_ne_zero k N hk)
  have h0 : LinearMap.trace ℂ (Nn 0) (P.restrict (hmaps 0)) = 1 := by
    have : P.restrict (hmaps 0) = LinearMap.id := by
      exact LinearMap.ext fun ⟨x, hx⟩ => Subtype.ext (hKP x hx)
    rw [this, LinearMap.trace_id]
    have : Module.finrank ℂ (Nn 0) = 1 := hfin
    rw [this]; simp
  have h1 : LinearMap.trace ℂ (Nn 1) (P.restrict (hmaps 1)) =
      LinearMap.trace ℂ (TupleOnesPerp k N)
        ((Rop k σ : TupleOnesPerp k N →L[ℂ] TupleOnesPerp k N) :
          TupleOnesPerp k N →ₗ[ℂ] TupleOnesPerp k N) := by
    have : (P.restrict (hmaps 1) : TupleOnesPerp k N →ₗ[ℂ] TupleOnesPerp k N) =
        ((Rop k σ : TupleOnesPerp k N →L[ℂ] TupleOnesPerp k N) :
          TupleOnesPerp k N →ₗ[ℂ] TupleOnesPerp k N) := by
      ext ⟨x, hx⟩; rfl
    exact congrArg (LinearMap.trace ℂ (TupleOnesPerp k N)) this
  rw [hP, h0, h1] at h
  linear_combination -h

end W2Sec3
end StrongConv

end
end
end

section
section
noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace StrongConv
namespace W2Sec3

open scoped InnerProductSpace

section build
variable (k N : ℕ)

/-- dimension of `{1}⊥` -/
def dimV : ℕ := Module.finrank ℂ (TupleOnesPerp k N)

def basisV : OrthonormalBasis (Fin (dimV k N)) ℂ (TupleOnesPerp k N) :=
  stdOrthonormalBasis ℂ (TupleOnesPerp k N)

def EV : TupleOnesPerp k N ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (dimV k N)) := (basisV k N).repr

def ΦV : (TupleOnesPerp k N →L[ℂ] TupleOnesPerp k N) ≃⋆ₐ[ℂ]
    Matrix (Fin (dimV k N)) (Fin (dimV k N)) ℂ :=
  (EV k N).conjStarAlgEquiv.trans (Matrix.toEuclideanCLM (n := Fin (dimV k N)) (𝕜 := ℂ)).symm

lemma Rop_unitary (σ : Equiv.Perm (Fin N)) :
    Rop k σ ∈ unitary (TupleOnesPerp k N →L[ℂ] TupleOnesPerp k N) := by
  rw [Unitary.mem_iff, star_Rop, ← Rop_mul, ← Rop_mul, inv_mul_cancel, mul_inv_cancel, Rop_one]
  exact ⟨rfl, rfl⟩

lemma ΦV_Rop_unitary (σ : Equiv.Perm (Fin N)) :
    ΦV k N (Rop k σ) ∈ unitary (Matrix (Fin (dimV k N)) (Fin (dimV k N)) ℂ) := by
  have h := Rop_unitary k N σ
  rw [Unitary.mem_iff] at h ⊢
  constructor
  · rw [← map_star, ← map_mul, h.1, map_one]
  · rw [← map_star, ← map_mul, h.2, map_one]

def piV : Equiv.Perm (Fin N) →* Matrix.unitaryGroup (Fin (dimV k N)) ℂ where
  toFun σ := ⟨ΦV k N (Rop k σ), ΦV_Rop_unitary k N σ⟩
  map_one' := Subtype.ext (by simp [Rop_one])
  map_mul' σ τ := Subtype.ext (by simp [Rop_mul])


lemma trace_matrix_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace M = LinearMap.trace ℂ (EuclideanSpace ℂ (Fin n))
      (Matrix.toEuclideanCLM (𝕜 := ℂ) M : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun (Fin n) ℂ).toBasis]
  congr 1
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, Matrix.toEuclideanLin_eq_toLin_orthonormal]
  simp

lemma trace_ΦV (R : TupleOnesPerp k N →L[ℂ] TupleOnesPerp k N) :
    Matrix.trace (ΦV k N R) = LinearMap.trace ℂ (TupleOnesPerp k N)
      (R : TupleOnesPerp k N →ₗ[ℂ] TupleOnesPerp k N) := by
  rw [trace_matrix_eq]
  have h : Matrix.toEuclideanCLM (𝕜 := ℂ) (ΦV k N R) = (EV k N).conjStarAlgEquiv R := by
    simp [ΦV]
  rw [h]
  have := LinearMap.trace_conj' (R : TupleOnesPerp k N →ₗ[ℂ] TupleOnesPerp k N)
    (EV k N).toLinearEquiv
  rw [← this]
  congr 1

end build


lemma prod_cast_eq_descFactorial (n k : ℕ) :
    ∏ j ∈ Finset.range k, ((n : ℂ) - j) = (n.descFactorial k : ℂ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, ih, Nat.descFactorial_succ, Nat.cast_mul, mul_comm]
    by_cases h : k ≤ n
    · rw [Nat.cast_sub h]
    · have : n.descFactorial k = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      rw [this]; simp

def phiV (k : ℕ) : MvPolynomial (Fin 1) ℂ :=
  (∏ j ∈ Finset.range k, (MvPolynomial.X 0 - MvPolynomial.C (j : ℂ))) - 1

abbrev stableRepV (k : ℕ) : StableRep where
  N₀ := k
  r := 1
  φ := phiV k
  dim := dimV k
  π := fun N => piV k N
  trace_eq := fun N hN σ => by
    show Matrix.trace (ΦV k N (Rop k σ)) = _
    rw [trace_ΦV, trace_Rop k N hN σ]
    simp [phiV, MvPolynomial.eval_sub, map_prod, prod_cast_eq_descFactorial]

lemma toEuclideanCLM_piV (k N : ℕ) (σ : Equiv.Perm (Fin N)) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) ((piV k N σ : Matrix.unitaryGroup _ ℂ) :
      Matrix (Fin (dimV k N)) (Fin (dimV k N)) ℂ) = (EV k N).conjStarAlgEquiv (Rop k σ) := by
  show Matrix.toEuclideanCLM (𝕜 := ℂ) (ΦV k N (Rop k σ)) = _
  simp [ΦV]

lemma conj_apply_EV (k N : ℕ) (R : TupleOnesPerp k N →L[ℂ] TupleOnesPerp k N)
    (y : TupleOnesPerp k N) :
    (EV k N).conjStarAlgEquiv R (EV k N y) = EV k N (R y) := by
  simp [LinearIsometryEquiv.conjStarAlgEquiv_apply]

lemma noTrivialSummand_stableRepV (k : ℕ) : (stableRepV k).NoTrivialSummand := by
  intro N hN v hv
  let y : TupleOnesPerp k N := (EV k N).symm (WithLp.toLp 2 v)
  have hfix : ∀ σ : Equiv.Perm (Fin N), Rop k σ y = y := by
    intro σ
    have h1 := hv σ
    have h2 : Matrix.toEuclideanCLM (𝕜 := ℂ) ((piV k N σ : Matrix.unitaryGroup _ ℂ) :
        Matrix (Fin (dimV k N)) (Fin (dimV k N)) ℂ) (WithLp.toLp 2 v) = WithLp.toLp 2 v := by
      rw [Matrix.toEuclideanCLM_toLp]
      exact congrArg (WithLp.toLp 2) h1
    rw [toEuclideanCLM_piV] at h2
    have h3 : (EV k N).conjStarAlgEquiv (Rop k σ) (EV k N y) = EV k N y := by
      have : EV k N y = WithLp.toLp 2 v := (EV k N).apply_symm_apply _
      rw [this]; exact h2
    rw [conj_apply_EV] at h3
    exact (EV k N).injective h3
  have : y = 0 := eq_zero_of_fixed k N hN y hfix
  have h4 : (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin (dimV k N))) = 0 := by
    have : (EV k N) y = 0 := by rw [this]; simp
    simpa [y] using this
  ext i
  have := congrArg (fun z => z.ofLp i) h4
  simpa [WithLp.ofLp_zero, Pi.zero_apply] using this

theorem main_dev (k : ℕ) :
    ∃ π : StableRep, π.NoTrivialSummand ∧ ∀ N : ℕ, π.N₀ ≤ N →
      ∃ U : TupleOnesPerp k N ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (π.dim N)),
        ∀ (d : ℕ) (σ : Fin d → Equiv.Perm (Fin N)) (x : TupleOnesPerp k N),
          U (schreierAdjPerp k σ x) = (∑ i, (π.model σ i + star (π.model σ i))) (U x) := by
  refine ⟨stableRepV k, noTrivialSummand_stableRepV k, fun N hN => ⟨EV k N, fun d σ x => ?_⟩⟩
  rw [schreierAdjPerp_eq, ContinuousLinearMap.sum_apply, map_sum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hm : (stableRepV k).model σ i = (EV k N).conjStarAlgEquiv (Rop k (σ i)) :=
    toEuclideanCLM_piV k N (σ i)
  rw [hm, ← map_star, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply, map_add,
    conj_apply_EV, conj_apply_EV]

end W2Sec3

theorem exists_stableRep_noTrivialSummand_schreierAdjPerp_eq_dev (k : ℕ) :
    ∃ π : StableRep, π.NoTrivialSummand ∧ ∀ N : ℕ, π.N₀ ≤ N →
      ∃ U : TupleOnesPerp k N ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (π.dim N)),
        ∀ (d : ℕ) (σ : Fin d → Equiv.Perm (Fin N)) (x : TupleOnesPerp k N),
          U (schreierAdjPerp k σ x) = (∑ i, (π.model σ i + star (π.model σ i))) (U x) :=
  W2Sec3.main_dev k

end StrongConv

end
end
end

section
open StrongConv

theorem solution (k : ℕ) :
    ∃ π : StableRep, π.NoTrivialSummand ∧ ∀ N : ℕ, π.N₀ ≤ N →
      ∃ U : TupleOnesPerp k N ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (π.dim N)),
        ∀ (d : ℕ) (σ : Fin d → Equiv.Perm (Fin N)) (x : TupleOnesPerp k N),
          U (schreierAdjPerp k σ x) = (∑ i, (π.model σ i + star (π.model σ i))) (U x) := by
  exact StrongConv.exists_stableRep_noTrivialSummand_schreierAdjPerp_eq_dev k

end
