-- Prove2me | solution 1 for StrongConv.exists_tendsto_uniformExp_trace_wordEval_model
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T22:58:15.431141+00:00
-- url     : https://prove2.me/submissions/f14bab07-9bfd-469c-bc1f-d11cada38427
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvG4
import Theorems.Thm_HananyPuder_exists_uniformExp_prod_xi_eq_sum_partitions
import Theorems.Thm_HananyPuder_tendsto_uniformExp_prod_xi_pow_sub_uniformExp

section
open Polynomial Filter Topology

noncomputable section

namespace StrongConv.W2

/-- The permutation a letter stands for. -/
def letterPerm {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) : Letter d → Equiv.Perm (Fin N)
  | none => 1
  | some (Sum.inl i) => σ i
  | some (Sum.inr i) => (σ i)⁻¹

/-- The permutation a word stands for (product in the order the letters appear). -/
def wordPerm {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w : List (Letter d)) :
    Equiv.Perm (Fin N) :=
  (w.map (letterPerm σ)).prod

theorem wordPerm_eq_lift {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w : List (Letter d)) :
    wordPerm σ w = FreeGroup.lift σ (wordFree w) := by
  induction w with
  | nil => simp [wordPerm, wordFree]
  | cons a w ih =>
    simp only [wordPerm, wordFree, List.map_cons, List.prod_cons, map_mul] at ih ⊢
    rw [ih]
    congr 1
    rcases a with _ | (i | i) <;> simp [letterPerm]

section Model

variable (π : StableRep)

/-- the matrix of `π_N` at a permutation, as an operator -/
abbrev opOf {N : ℕ} (τ : Equiv.Perm (Fin N)) :
    EuclideanSpace ℂ (Fin (π.dim N)) →L[ℂ] EuclideanSpace ℂ (Fin (π.dim N)) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (π.π N τ : Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ)

lemma opOf_mul {N : ℕ} (τ ρ : Equiv.Perm (Fin N)) : opOf π (τ * ρ) = opOf π τ * opOf π ρ := by
  simp [opOf, map_mul]

lemma opOf_one {N : ℕ} : opOf π (1 : Equiv.Perm (Fin N)) = 1 := by
  simp [opOf]

lemma star_opOf {N : ℕ} (τ : Equiv.Perm (Fin N)) : star (opOf π τ) = opOf π τ⁻¹ := by
  have h1 : star (π.π N τ : Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ) =
      (π.π N τ⁻¹ : Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ) := by
    rw [map_inv]
    simp
  unfold opOf
  rw [← map_star, h1]

lemma wordEval_model {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w : List (Letter d)) :
    wordEval (π.model σ) w = opOf π (wordPerm σ w) := by
  induction w with
  | nil => simp [wordEval, wordPerm, opOf_one]
  | cons a w ih =>
    simp only [wordEval, wordPerm, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, opOf_mul]
    congr 1
    rcases a with _ | (i | i)
    · simp [letterPerm, opOf_one]
    · simp [letterPerm, letterOp, StableRep.model, opOf]
    · simp [letterPerm, letterOp, StableRep.model, star_opOf]

lemma trace_opOf {N : ℕ} (τ : Equiv.Perm (Fin N)) :
    LinearMap.trace ℂ (EuclideanSpace ℂ (Fin (π.dim N)))
      (opOf π τ : EuclideanSpace ℂ (Fin (π.dim N)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (π.dim N))) =
      (π.π N τ : Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ).trace := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun (Fin (π.dim N)) ℂ).toBasis]
  congr 1
  ext i j
  simp [LinearMap.toMatrix_apply, opOf, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct,
    Pi.single_apply]

/-- The trace of `w(Π^N)` as the character polynomial at the cycle counts of the word map. -/
theorem trace_wordEval_model {d N : ℕ} (hN : π.N₀ ≤ N) (σ : Fin d → Equiv.Perm (Fin N))
    (w : List (Letter d)) :
    LinearMap.trace ℂ (EuclideanSpace ℂ (Fin (π.dim N)))
        (wordEval (π.model σ) w :
          EuclideanSpace ℂ (Fin (π.dim N)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (π.dim N))) =
      MvPolynomial.eval (fun i : Fin π.r =>
        ((xi ((i : ℕ) + 1) (FreeGroup.lift σ (wordFree w)) : ℕ) : ℂ)) π.φ := by
  rw [wordEval_model, trace_opOf, π.trace_eq N hN, wordPerm_eq_lift]

end Model

end StrongConv.W2

end
end

section
open Polynomial Filter Topology

noncomputable section

namespace StrongConv.W2

section Expand

variable (π : StableRep)

/-- expectation of the monomial `∏ ξ_{i+1}^{α i}` of the word `u`. -/
def Mexp {d : ℕ} (α : Fin π.r → ℕ) (u : FreeGroup (Fin d)) (N : ℕ) : ℝ :=
  uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
    ∏ i : Fin π.r, ((xi ((i : ℕ) + 1) (FreeGroup.lift σ u) : ℕ) : ℝ) ^ α i)

lemma re_eval_phi {r : ℕ} (φ : MvPolynomial (Fin r) ℂ) (x : Fin r → ℕ) :
    (MvPolynomial.eval (fun i => ((x i : ℕ) : ℂ)) φ).re =
      ∑ α ∈ φ.support, (φ.coeff α).re * ∏ i, ((x i : ℕ) : ℝ) ^ (α i) := by
  rw [MvPolynomial.eval_eq', Complex.re_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  have : (∏ i, ((x i : ℕ) : ℂ) ^ (α i)) = ((∏ i, ((x i : ℕ) : ℝ) ^ (α i) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [this, Complex.re_mul_ofReal]

lemma uniformExp_finset_sum {X ι : Type*} [Fintype X] (s : Finset ι) (f : ι → X → ℝ) :
    uniformExp (fun x => ∑ a ∈ s, f a x) = ∑ a ∈ s, uniformExp (f a) := by
  unfold uniformExp
  rw [Finset.sum_comm, Finset.sum_div]

lemma uniformExp_const_mul {X : Type*} [Fintype X] (c : ℝ) (f : X → ℝ) :
    uniformExp (fun x => c * f x) = c * uniformExp f := by
  unfold uniformExp
  rw [← Finset.mul_sum, mul_div_assoc]

/-- The expectation of `Re Tr w(Π^N)` is the character-polynomial combination of the monomial
expectations of the word map. -/
theorem uniformExp_trace_eq_sum {d N : ℕ} (hN : π.N₀ ≤ N) (w : List (Letter d)) :
    uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
      (LinearMap.trace ℂ (EuclideanSpace ℂ (Fin (π.dim N)))
        (wordEval (π.model σ) w :
          EuclideanSpace ℂ (Fin (π.dim N)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (π.dim N)))).re) =
      ∑ α ∈ π.φ.support, (π.φ.coeff α).re * Mexp π (fun i => α i) (wordFree w) N := by
  have h : ∀ σ : Fin d → Equiv.Perm (Fin N),
      (LinearMap.trace ℂ (EuclideanSpace ℂ (Fin (π.dim N)))
        (wordEval (π.model σ) w :
          EuclideanSpace ℂ (Fin (π.dim N)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (π.dim N)))).re =
      ∑ α ∈ π.φ.support, (π.φ.coeff α).re * ∏ i : Fin π.r,
        ((xi ((i : ℕ) + 1) (FreeGroup.lift σ (wordFree w)) : ℕ) : ℝ) ^ (α i) := by
    intro σ
    rw [trace_wordEval_model π hN, re_eval_phi]
  simp_rw [h]
  rw [uniformExp_finset_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [uniformExp_const_mul]
  rfl

/-- the weighted degree of every monomial of `φ` is at most `β`. -/
theorem weight_le_beta (α : Fin π.r →₀ ℕ) (hα : α ∈ π.φ.support) :
    ∑ i : Fin π.r, ((i : ℕ) + 1) * α i ≤ π.beta := by
  classical
  set Q := MvPolynomial.aeval (fun i : Fin π.r =>
    (MvPolynomial.X i : MvPolynomial (Fin π.r) ℂ) ^ ((i : ℕ) + 1)) π.φ with hQ
  have hexp : Q = ∑ β ∈ π.φ.support, MvPolynomial.monomial
      (Finsupp.equivFunOnFinite.symm (fun i : Fin π.r => ((i : ℕ) + 1) * β i)) (π.φ.coeff β) := by
    rw [hQ, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (by intro i; simp),
      MvPolynomial.algebraMap_eq]
    congr 1
    rw [Finset.prod_subset (Finset.subset_univ β.support) (fun i _ hi => by
      rw [Finsupp.notMem_support_iff] at hi; simp [hi])]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [← pow_mul]
  have hcoeff : Q.coeff (Finsupp.equivFunOnFinite.symm
      (fun i : Fin π.r => ((i : ℕ) + 1) * α i)) = π.φ.coeff α := by
    rw [hexp, MvPolynomial.coeff_sum, Finset.sum_eq_single α]
    · simp
    · intro β _ hβ
      rw [MvPolynomial.coeff_monomial, if_neg]
      intro h
      apply hβ
      ext i
      have := congr_fun (Finsupp.equivFunOnFinite.symm.injective h) i
      simp at this
      exact this
    · intro h; exact absurd hα h
  have hne : Q.coeff (Finsupp.equivFunOnFinite.symm
      (fun i : Fin π.r => ((i : ℕ) + 1) * α i)) ≠ 0 := by
    rw [hcoeff]; exact MvPolynomial.mem_support_iff.mp hα
  have := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hne)
  rw [Finsupp.sum_fintype _ _ (by intro i; rfl)] at this
  simpa [StableRep.beta, hQ] using this

end Expand

end StrongConv.W2

end
end

section
open Polynomial Filter Topology

noncomputable section

namespace StrongConv.W2

/-- the multiplicity vector `a_t = α_i` at `t + 1 = (i + 1) k`, and `0` elsewhere -/
def aOf (r k : ℕ) (α : Fin r → ℕ) : Fin (r * k) → ℕ :=
  fun t => ∑ i : Fin r, if (t : ℕ) + 1 = ((i : ℕ) + 1) * k then α i else 0

/-- the value of Hanany–Puder's partition sum at the multiset `{(i+1)k : α_i times}` -/
def Vval (r k : ℕ) (α : Fin r → ℕ) : ℝ :=
  ∑ P : Finpartition (Finset.univ : Finset (Σ t : Fin (r * k), Fin (aOf r k α t))),
    ∏ A ∈ P.parts, ∑ e ∈ (A.gcd fun x => (x.1 : ℕ) + 1).divisors, (e : ℝ) ^ (A.card - 1)

lemma tIdx_lt {r k : ℕ} (hk : 1 ≤ k) (i : Fin r) : ((i : ℕ) + 1) * k - 1 < r * k := by
  have : ((i : ℕ) + 1) * k ≤ r * k := Nat.mul_le_mul_right _ i.2
  have : 1 ≤ ((i : ℕ) + 1) * k := Nat.mul_pos (by omega) (by omega)
  omega

lemma aOf_tIdx {r k : ℕ} (hk : 1 ≤ k) (α : Fin r → ℕ) (i : Fin r) :
    aOf r k α ⟨((i : ℕ) + 1) * k - 1, tIdx_lt hk i⟩ = α i := by
  unfold aOf
  rw [Finset.sum_eq_single i]
  · have : 1 ≤ ((i : ℕ) + 1) * k := Nat.mul_pos (by omega) (by omega)
    simp only
    rw [if_pos (by omega)]
  · intro j _ hj
    have : 1 ≤ ((i : ℕ) + 1) * k := Nat.mul_pos (by omega) (by omega)
    rw [if_neg]
    intro h
    have h2 : ((j : ℕ) + 1) * k = ((i : ℕ) + 1) * k := by simp only at h; omega
    have := Nat.eq_of_mul_eq_mul_right (by omega : 0 < k) h2
    exact hj (Fin.ext (by omega))
  · simp

/-- the reindexing of the product over `t` -/
lemma prod_reindex {r k : ℕ} (hk : 1 ≤ k) (α : Fin r → ℕ) (f : ℕ → ℝ) :
    ∏ t : Fin (r * k), f ((t : ℕ) + 1) ^ aOf r k α t =
      ∏ i : Fin r, f (((i : ℕ) + 1) * k) ^ α i := by
  classical
  let g : Fin r → Fin (r * k) := fun i => ⟨((i : ℕ) + 1) * k - 1, tIdx_lt hk i⟩
  have hg : Function.Injective g := by
    intro i j h
    have h1 : ((i : ℕ) + 1) * k - 1 = ((j : ℕ) + 1) * k - 1 := congrArg Fin.val h
    have : 1 ≤ ((i : ℕ) + 1) * k := Nat.mul_pos (by omega) (by omega)
    have : 1 ≤ ((j : ℕ) + 1) * k := Nat.mul_pos (by omega) (by omega)
    have h2 : ((i : ℕ) + 1) * k = ((j : ℕ) + 1) * k := by omega
    have := Nat.eq_of_mul_eq_mul_right (by omega : 0 < k) h2
    exact Fin.ext (by omega)
  have hsub : Finset.univ.image g ⊆ (Finset.univ : Finset (Fin (r * k))) := Finset.subset_univ _
  rw [← Finset.prod_subset hsub, Finset.prod_image (fun i _ j _ h => hg h)]
  · refine Finset.prod_congr rfl fun i _ => ?_
    have h1 : 1 ≤ ((i : ℕ) + 1) * k := Nat.mul_pos (by omega) (by omega)
    have : ((g i : ℕ) + 1) = ((i : ℕ) + 1) * k := by simp only [g]; omega
    rw [this]
    have := aOf_tIdx hk α i
    rw [show aOf r k α (g i) = α i from this]
  · intro t _ ht
    have h0 : aOf r k α t = 0 := by
      unfold aOf
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [if_neg]
      intro h
      apply ht
      refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      have h1 : 1 ≤ ((i : ℕ) + 1) * k := Nat.mul_pos (by omega) (by omega)
      simp only [g]; omega
    rw [h0, pow_zero]

/-- Remark 7.3 for the multiset `{(i+1)k : α_i times}`. -/
lemma exists_uniformExp_prod_xi_mul_eq {r k : ℕ} (hk : 1 ≤ k) (α : Fin r → ℕ) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      uniformExp (fun σ : Equiv.Perm (Fin N) =>
        ∏ i : Fin r, ((xi (((i : ℕ) + 1) * k) σ : ℕ) : ℝ) ^ α i) = Vval r k α := by
  obtain ⟨N₁, hN₁⟩ := HananyPuder.exists_uniformExp_prod_xi_eq_sum_partitions (aOf r k α)
  refine ⟨N₁, fun N hN => ?_⟩
  have := hN₁ N hN
  have hfun : (fun σ : Equiv.Perm (Fin N) => ∏ t : Fin (r * k), ((xi ((t : ℕ) + 1) σ : ℕ) : ℝ) ^
      aOf r k α t) = fun σ => ∏ i : Fin r, ((xi (((i : ℕ) + 1) * k) σ : ℕ) : ℝ) ^ α i := by
    funext σ
    exact prod_reindex hk α (fun n => ((xi n σ : ℕ) : ℝ))
  rw [hfun] at this
  exact this

lemma sum_aOf {r k : ℕ} (hk : 1 ≤ k) (α : Fin r → ℕ) : ∑ t, aOf r k α t = ∑ i, α i := by
  have h := prod_reindex hk α (fun _ => (2 : ℝ))
  rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum] at h
  exact Nat.pow_right_injective (le_refl 2) (by exact_mod_cast h)

lemma card_finpartition_le (X : Type*) [Fintype X] [DecidableEq X] :
    Fintype.card (Finpartition (Finset.univ : Finset X)) ≤ 2 ^ (2 ^ Fintype.card X) := by
  classical
  have : Fintype.card (Finpartition (Finset.univ : Finset X)) ≤ Fintype.card (Finset (Finset X)) :=
    Fintype.card_le_of_injective (fun P => P.parts) (fun P Q h => Finpartition.ext h)
  simpa [Fintype.card_finset] using this

lemma block_bound {r k : ℕ} {X : Type*} (A : Finset X) (hA : A.Nonempty)
    (f : X → ℕ) (hf : ∀ x, f x ≤ r * k) (hpos : ∀ x, 0 < f x) :
    ∑ e ∈ (A.gcd f).divisors, ((e : ℕ) : ℝ) ^ (A.card - 1) ≤ ((r * k : ℕ) : ℝ) ^ A.card := by
  obtain ⟨x, hx⟩ := hA
  have hg : A.gcd f ≤ r * k :=
    le_trans (Nat.le_of_dvd (hpos x) (Finset.gcd_dvd hx)) (hf x)
  have hcard : 1 ≤ A.card := Finset.card_pos.mpr ⟨x, hx⟩
  calc ∑ e ∈ (A.gcd f).divisors, ((e : ℕ) : ℝ) ^ (A.card - 1)
      ≤ ∑ e ∈ (A.gcd f).divisors, ((r * k : ℕ) : ℝ) ^ (A.card - 1) := by
        refine Finset.sum_le_sum fun e he => ?_
        have : e ≤ r * k := le_trans (Nat.divisor_le he) hg
        exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast this) _
    _ = ((A.gcd f).divisors.card : ℝ) * ((r * k : ℕ) : ℝ) ^ (A.card - 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((r * k : ℕ) : ℝ) * ((r * k : ℕ) : ℝ) ^ (A.card - 1) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast le_trans (Nat.card_divisors_le_self _) hg
    _ = ((r * k : ℕ) : ℝ) ^ A.card := by
        rw [← pow_succ']; congr 1; omega

lemma Vval_nonneg (r k : ℕ) (α : Fin r → ℕ) : 0 ≤ Vval r k α := by
  unfold Vval
  refine Finset.sum_nonneg fun P _ => Finset.prod_nonneg fun A _ => Finset.sum_nonneg fun e _ => ?_
  positivity

lemma Vval_le {r k : ℕ} (hk : 1 ≤ k) (α : Fin r → ℕ) :
    Vval r k α ≤ (2 : ℝ) ^ (2 ^ (∑ i, α i)) * ((r * k : ℕ) : ℝ) ^ (∑ i, α i) := by
  classical
  set X := Σ t : Fin (r * k), Fin (aOf r k α t) with hX
  have hcardX : Fintype.card X = ∑ i, α i := by
    have : Fintype.card (Σ t : Fin (r * k), Fin (aOf r k α t)) = ∑ i, α i := by
      rw [Fintype.card_sigma]
      simp only [Fintype.card_fin]
      exact sum_aOf hk α
    exact this
  have hP : ∀ P : Finpartition (Finset.univ : Finset X),
      ∏ A ∈ P.parts, ∑ e ∈ (A.gcd fun x : X => (x.1 : ℕ) + 1).divisors, ((e : ℕ) : ℝ) ^ (A.card - 1) ≤
        ((r * k : ℕ) : ℝ) ^ (∑ i, α i) := by
    intro P
    calc _ ≤ ∏ A ∈ P.parts, ((r * k : ℕ) : ℝ) ^ A.card := by
          refine Finset.prod_le_prod (fun A _ => Finset.sum_nonneg fun e _ => by positivity)
            fun A hA => ?_
          exact block_bound A (P.nonempty_of_mem_parts hA) _ (fun x => x.1.2) (fun x => by omega)
      _ = ((r * k : ℕ) : ℝ) ^ (∑ A ∈ P.parts, A.card) := Finset.prod_pow_eq_pow_sum _ _ _
      _ = _ := by rw [P.sum_card_parts, Finset.card_univ, hcardX]
  calc Vval r k α ≤ ∑ P : Finpartition (Finset.univ : Finset X), ((r * k : ℕ) : ℝ) ^ (∑ i, α i) :=
        Finset.sum_le_sum fun P _ => hP P
    _ = (Fintype.card (Finpartition (Finset.univ : Finset X)) : ℝ) * _ := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ ≤ (2 : ℝ) ^ (2 ^ (∑ i, α i)) * _ := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have := card_finpartition_le X
        rw [hcardX] at this
        exact_mod_cast this

variable (π : StableRep)

/-- the real coefficient -/
def cre (α : Fin π.r →₀ ℕ) : ℝ := (π.φ.coeff α).re

/-- the limit function `ϖ` -/
def varpi (k : ℕ) : ℝ := ∑ α ∈ π.φ.support, cre π α * Vval π.r k (fun i => α i)

lemma tendsto_Mexp {d : ℕ} (α : Fin π.r → ℕ) (v : FreeGroup (Fin d)) (hv : IsNonPower v) (k : ℕ)
    (hk : 1 ≤ k) :
    Tendsto (fun N => Mexp π α (v ^ k) N) atTop (𝓝 (Vval π.r k α)) := by
  have h13 := HananyPuder.tendsto_uniformExp_prod_xi_pow_sub_uniformExp v hv k hk α
  obtain ⟨N₁, hN₁⟩ := exists_uniformExp_prod_xi_mul_eq hk α
  have h2 : Tendsto (fun N => Mexp π α (v ^ k) N - Vval π.r k α) atTop (𝓝 0) := by
    refine h13.congr' ?_
    filter_upwards [eventually_ge_atTop N₁] with N hN
    rw [hN₁ N hN]
    rfl
  have := h2.add_const (Vval π.r k α)
  simpa using this

lemma tendsto_sum {d : ℕ} (v : FreeGroup (Fin d)) (hv : IsNonPower v) (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (fun N => ∑ α ∈ π.φ.support, cre π α * Mexp π (fun i => α i) (v ^ k) N) atTop
      (𝓝 (varpi π k)) := by
  unfold varpi
  refine tendsto_finsetSum _ fun α _ => ?_
  exact (tendsto_Mexp π _ v hv k hk).const_mul _

lemma trace_sum_zero (hπ : π.NoTrivialSummand) {N : ℕ} (hN : π.N₀ ≤ N) :
    ∑ σ : Equiv.Perm (Fin N),
      ((π.π N σ : Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ).trace) = 0 := by
  classical
  set M : Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ :=
    ∑ σ : Equiv.Perm (Fin N), (π.π N σ : Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ) with hM
  have hfix : ∀ τ : Equiv.Perm (Fin N), (π.π N τ : Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ) * M = M := by
    intro τ
    rw [hM, Finset.mul_sum]
    simp_rw [← Submonoid.coe_mul, ← map_mul]
    exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun _ => rfl)
  have hM0 : M = 0 := by
    ext i j
    have hv := hπ N hN (M.mulVec (Pi.single j 1)) (fun τ => by
      rw [Matrix.mulVec_mulVec, hfix τ])
    have := congr_fun hv i
    simpa [Matrix.mulVec_single_one] using this
  have : (∑ σ : Equiv.Perm (Fin N),
      ((π.π N σ : Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ).trace)) = M.trace := by
    rw [hM, Matrix.trace_sum]
  rw [this, hM0]; simp

lemma varpi_one (hπ : π.NoTrivialSummand) : varpi π 1 = 0 := by
  classical
  have hev : ∀ᶠ N in atTop, ∀ α ∈ π.φ.support,
      uniformExp (fun σ : Equiv.Perm (Fin N) =>
        ∏ i : Fin π.r, ((xi (((i : ℕ) + 1) * 1) σ : ℕ) : ℝ) ^ (α i)) = Vval π.r 1 (fun i => α i) := by
    rw [Filter.eventually_all_finset]
    intro α _
    obtain ⟨N₁, hN₁⟩ := exists_uniformExp_prod_xi_mul_eq (r := π.r) (k := 1) le_rfl (fun i => α i)
    exact eventually_atTop.mpr ⟨N₁, hN₁⟩
  obtain ⟨N, hN, hN0⟩ := (hev.and (eventually_ge_atTop π.N₀)).exists
  unfold varpi
  have h1 : ∑ α ∈ π.φ.support, cre π α * Vval π.r 1 (fun i => α i) =
      uniformExp (fun σ : Equiv.Perm (Fin N) => ∑ α ∈ π.φ.support, cre π α *
        ∏ i : Fin π.r, ((xi (((i : ℕ) + 1) * 1) σ : ℕ) : ℝ) ^ (α i)) := by
    rw [uniformExp_finset_sum]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [uniformExp_const_mul, hN α hα]
  rw [h1]
  have h2 : (fun σ : Equiv.Perm (Fin N) => ∑ α ∈ π.φ.support, cre π α *
        ∏ i : Fin π.r, ((xi (((i : ℕ) + 1) * 1) σ : ℕ) : ℝ) ^ (α i)) =
      fun σ => ((π.π N σ : Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ).trace).re := by
    funext σ
    rw [π.trace_eq N hN0, re_eval_phi]
    simp [cre]
  rw [h2]
  unfold uniformExp
  rw [← Complex.re_sum, trace_sum_zero π hπ hN0]
  simp

lemma abs_varpi_le (k : ℕ) (hk : 1 ≤ k) :
    |varpi π k| ≤ (∑ α ∈ π.φ.support, |cre π α|) * 2 ^ (2 ^ π.beta) *
      ((max π.r 1 : ℕ) : ℝ) ^ π.beta * (k : ℝ) ^ π.beta := by
  unfold varpi
  calc |∑ α ∈ π.φ.support, cre π α * Vval π.r k (fun i => α i)|
      ≤ ∑ α ∈ π.φ.support, |cre π α * Vval π.r k (fun i => α i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ α ∈ π.φ.support, |cre π α| * (2 ^ (2 ^ π.beta) *
          ((max π.r 1 : ℕ) : ℝ) ^ π.beta * (k : ℝ) ^ π.beta) := by
        refine Finset.sum_le_sum fun α hα => ?_
        rw [abs_mul, abs_of_nonneg (Vval_nonneg _ _ _)]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have hm : ∑ i, α i ≤ π.beta :=
          le_trans (Finset.sum_le_sum fun i _ => Nat.le_mul_of_pos_left (α i) (Nat.succ_pos _))
            (weight_le_beta π α hα)
        refine le_trans (Vval_le hk _) ?_
        have hR : (1 : ℝ) ≤ ((max π.r 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
        have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
        have h2 : (2 : ℝ) ^ (2 ^ (∑ i, α i)) ≤ 2 ^ (2 ^ π.beta) :=
          pow_le_pow_right₀ (by norm_num) (Nat.pow_le_pow_right (by norm_num) hm)
        have h3 : ((π.r * k : ℕ) : ℝ) ^ (∑ i, α i) ≤
            ((max π.r 1 : ℕ) : ℝ) ^ π.beta * (k : ℝ) ^ π.beta := by
          rw [Nat.cast_mul, mul_pow]
          refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
          · calc ((π.r : ℕ) : ℝ) ^ (∑ i, α i) ≤ ((max π.r 1 : ℕ) : ℝ) ^ (∑ i, α i) :=
                  pow_le_pow_left₀ (by positivity) (by exact_mod_cast le_max_left _ _) _
              _ ≤ _ := pow_le_pow_right₀ hR hm
          · exact pow_le_pow_right₀ hk1 hm
        calc (2 : ℝ) ^ (2 ^ (∑ i, α i)) * ((π.r * k : ℕ) : ℝ) ^ (∑ i, α i)
            ≤ 2 ^ (2 ^ π.beta) * (((max π.r 1 : ℕ) : ℝ) ^ π.beta * (k : ℝ) ^ π.beta) :=
              mul_le_mul h2 h3 (by positivity) (by positivity)
          _ = _ := by ring
    _ = _ := by rw [← Finset.sum_mul]; ring

end StrongConv.W2
end
end

section
open Filter Topology

namespace StrongConv.W2

theorem lemma102 (π : StableRep) (hπ : π.NoTrivialSummand) :
    ∃ (ϖ : ℕ → ℝ) (c : ℝ),
      (∀ (d : ℕ) (w : List (Letter d)), wordFree w ≠ 1 → ∀ (v : FreeGroup (Fin d)) (k : ℕ),
        IsNonPower v → 1 ≤ k → wordFree w = v ^ k →
        Tendsto (fun N : ℕ => uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
            (LinearMap.trace ℂ (EuclideanSpace ℂ (Fin (π.dim N)))
              (wordEval (π.model σ) w :
                EuclideanSpace ℂ (Fin (π.dim N)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (π.dim N)))).re))
          atTop (𝓝 (ϖ k))) ∧
      ϖ 1 = 0 ∧ ∀ k : ℕ, 2 ≤ k → |ϖ k| ≤ c * (k : ℝ) ^ π.beta := by
  refine ⟨varpi π, (∑ α ∈ π.φ.support, |cre π α|) * 2 ^ (2 ^ π.beta) *
    ((max π.r 1 : ℕ) : ℝ) ^ π.beta, ?_, varpi_one π hπ, ?_⟩
  · intro d w _ v k hv hk hwv
    refine (tendsto_sum π v hv k hk).congr' ?_
    filter_upwards [eventually_ge_atTop π.N₀] with N hN
    rw [uniformExp_trace_eq_sum π hN w, hwv]
    rfl
  · intro k hk
    exact abs_varpi_le π k (by omega)

end StrongConv.W2
end

open StrongConv Filter Topology in
theorem solution (π : StableRep) (hπ : π.NoTrivialSummand) :
    ∃ (ϖ : ℕ → ℝ) (c : ℝ),
      (∀ (d : ℕ) (w : List (Letter d)), wordFree w ≠ 1 → ∀ (v : FreeGroup (Fin d)) (k : ℕ),
        IsNonPower v → 1 ≤ k → wordFree w = v ^ k →
        Tendsto (fun N : ℕ => uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
            (LinearMap.trace ℂ (EuclideanSpace ℂ (Fin (π.dim N)))
              (wordEval (π.model σ) w :
                EuclideanSpace ℂ (Fin (π.dim N)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (π.dim N)))).re))
          atTop (𝓝 (ϖ k))) ∧
      ϖ 1 = 0 ∧ ∀ k : ℕ, 2 ≤ k → |ϖ k| ≤ c * (k : ℝ) ^ π.beta :=
  StrongConv.W2.lemma102 π hπ
