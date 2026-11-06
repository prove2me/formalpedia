-- Prove2me | solution 1 for StrongConv.exists_uniformExp_trace_wordEval_model_eq_div
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T23:07:54.284215+00:00
-- url     : https://prove2.me/submissions/3167e790-ff09-4f43-b613-3666f334fe0d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_StrongConv
import Definitions.Def_StrongConvG4
import Theorems.Thm_HananyPuder_exists_uniformExp_prod_xi_eq_sum_partitions
import Theorems.Thm_HananyPuder_tendsto_uniformExp_prod_xi_pow_sub_uniformExp
import Theorems.Thm_HananyPuder_uniformExp_prod_xi_eq_sum_quotients

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

variable (π : StableRep)

/-- the real coefficient -/
def cre (α : Fin π.r →₀ ℕ) : ℝ := (π.φ.coeff α).re

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

end StrongConv.W2
end
end

section
open Polynomial Filter Topology

noncomputable section

namespace StrongConv.W2

open HananyPuder

lemma norm_wordFree_le {d : ℕ} (w : List (Letter d)) : FreeGroup.norm (wordFree w) ≤ w.length := by
  induction w with
  | nil => simp [wordFree]
  | cons a w ih =>
    have h : wordFree (a :: w) = (match a with
        | none => 1
        | some (Sum.inl i) => FreeGroup.of i
        | some (Sum.inr i) => (FreeGroup.of i)⁻¹) * wordFree w := by
      simp only [wordFree, List.map_cons, List.prod_cons]; rfl
    rw [h]
    refine (FreeGroup.norm_mul_le _ _).trans ?_
    have : FreeGroup.norm (match a with
        | none => (1 : FreeGroup (Fin d))
        | some (Sum.inl i) => FreeGroup.of i
        | some (Sum.inr i) => (FreeGroup.of i)⁻¹) ≤ 1 := by
      rcases a with _ | (i | i) <;> simp [FreeGroup.norm_of, FreeGroup.norm_inv_eq, FreeGroup.norm_one]
    simp only [List.length_cons]
    omega

lemma length_reduceCyclically_le {d : ℕ} (x : FreeGroup (Fin d)) :
    (FreeGroup.reduceCyclically x.toWord).length ≤ FreeGroup.norm x := by
  have := congrArg List.length (FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically x.toWord)
  simp only [List.length_append] at this
  unfold FreeGroup.norm
  omega

lemma card_cycleVert {d r : ℕ} (L : List (Fin d × Bool)) (α : Fin r → ℕ) :
    Fintype.card (CycleVert L α) = ∑ i : Fin r, α i * (((i : ℕ) + 1) * L.length) := by
  unfold CycleVert
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin, cycleWord, List.length_flatten, List.map_replicate,
    List.sum_replicate, smul_eq_mul]
  rw [Fintype.sum_sigma]
  simp [mul_comm]

lemma sum_quotEdge_le {d r : ℕ} {L : List (Fin d × Bool)} {α : Fin r → ℕ}
    (P : Finpartition (Finset.univ : Finset (CycleVert L α))) :
    ∑ j, quotEdge P j ≤ Fintype.card (CycleVert L α) := by
  classical
  calc ∑ j, quotEdge P j ≤ ∑ j : Fin d, (Finset.univ.filter fun e : CycleVert L α =>
        (edgeLetter e).1 = j).card :=
        Finset.sum_le_sum fun j _ => Finset.card_image_le
    _ = Fintype.card (CycleVert L α) := by
        rw [← Finset.card_univ]
        exact (Finset.card_eq_sum_card_fiberwise (fun e _ => Finset.mem_univ _)).symm

end StrongConv.W2

end
end

section
open Polynomial Filter Topology

noncomputable section

namespace StrongConv.W2.Alg
open Polynomial Finset

/-- The linear factor `1 - j X`. -/
abbrev L (j : ℕ) : ℝ[X] := 1 - (j : ℝ[X]) * X

lemma L_eq (j : ℕ) : L j = C (-(j : ℝ)) * X + C 1 := by
  simp [L, sub_eq_add_neg, add_comm, map_natCast]

lemma natDegree_L (j : ℕ) (hj : 1 ≤ j) : (L j).natDegree = 1 := by
  rw [L_eq]
  apply natDegree_linear
  have : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  simpa using this

lemma natDegree_L_le (j : ℕ) : (L j).natDegree ≤ 1 := by
  rw [L_eq]; exact natDegree_linear_le

lemma eval_L (j : ℕ) (x : ℝ) : (L j).eval x = 1 - j * x := by
  simp [L]

lemma natDegree_gPoly (d q : ℕ) :
    (gPoly d q).natDegree = ∑ j ∈ Ico 1 q, min d (q / (j + 1)) := by
  unfold gPoly
  rw [natDegree_prod]
  · apply sum_congr rfl
    intro j hj
    rw [mem_Ico] at hj
    rw [natDegree_pow, natDegree_L j hj.1, mul_one]
  · intro j hj
    rw [mem_Ico] at hj
    apply pow_ne_zero
    intro h
    have := natDegree_L j hj.1
    change L j = 0 at h
    rw [h] at this; simp at this

lemma factor_pos (j q N : ℕ) (hj : j < q) (hN : q ≤ N) (hN1 : 1 ≤ N) :
    0 < 1 - (j : ℝ) * (1 / (N : ℝ)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have : (j : ℝ) < N := by exact_mod_cast (by omega : j < N)
  rw [mul_one_div, sub_pos, div_lt_one hNpos]
  exact this

lemma eval_prod_pos (q N : ℕ) (hN : q ≤ N) (hN1 : 1 ≤ N) (s : Finset ℕ) (hs : ∀ j ∈ s, j < q)
    (k : ℕ → ℕ) : 0 < (∏ j ∈ s, L j ^ k j).eval (1 / (N : ℝ)) := by
  rw [eval_prod]
  apply prod_pos
  intro j hj
  rw [eval_pow, eval_L]
  exact pow_pos (factor_pos j q N (hs j hj) hN hN1) _

theorem gPoly_eval_ne_zero (d q N : ℕ) (hN : q ≤ N) (hN1 : 1 ≤ N) :
    (gPoly d q).eval (1 / (N : ℝ)) ≠ 0 := by
  have := eval_prod_pos q N hN hN1 (Ico 1 q) (fun j hj => (mem_Ico.1 hj).2)
    (fun j => min d (q / (j + 1)))
  exact ne_of_gt this

lemma filter_lt_Ico (e q : ℕ) (he : e ≤ q) : (Ico 1 q).filter (· < e) = Ico 1 e := by
  ext j; simp only [mem_filter, mem_Ico]; omega

lemma prod_prod_Ico {d : ℕ} (e : Fin d → ℕ) (q : ℕ) (he : ∀ i, e i ≤ q) (f : ℕ → ℝ) :
    ∏ i, ∏ j ∈ Ico 1 (e i), f j =
      ∏ j ∈ Ico 1 q, f j ^ (univ.filter (fun i => j < e i)).card := by
  have : ∀ i, ∏ j ∈ Ico 1 (e i), f j = ∏ j ∈ Ico 1 q, (if j < e i then f j else 1) := by
    intro i
    rw [← prod_filter, filter_lt_Ico _ _ (he i)]
  simp_rw [this]
  rw [Finset.prod_comm]
  apply prod_congr rfl
  intro j _
  rw [← prod_filter, prod_const]

/-- `#{j < d : (j+1) b ≤ q} = min d (q / b)`. -/
lemma card_filter_mul_le (d b q : ℕ) (hb : 0 < b) :
    ((range d).filter (fun j => (j + 1) * b ≤ q)).card = min d (q / b) := by
  have : (range d).filter (fun j => (j + 1) * b ≤ q) = range (min d (q / b)) := by
    ext j
    simp only [mem_filter, mem_range, lt_min_iff]
    rw [← Nat.le_div_iff_mul_le hb]
    omega
  rw [this, card_range]

theorem natDegree_gPoly_add_min_le (d q : ℕ) (hq : 1 ≤ q) :
    (((gPoly d q).natDegree + min d q : ℕ) : ℝ) ≤ q * (1 + Real.log d) := by
  have key : (gPoly d q).natDegree + min d q = ∑ j ∈ range d, q / (j + 1) := by
    rw [natDegree_gPoly]
    have h1 : ∑ m ∈ range q, min d (q / (m + 1)) =
        min d q + ∑ j ∈ Ico 1 q, min d (q / (j + 1)) := by
      rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega)]
      simp
    rw [add_comm, ← h1]
    have h2 : ∀ m, min d (q / (m + 1)) =
        ∑ j ∈ range d, if (j + 1) * (m + 1) ≤ q then 1 else 0 := by
      intro m
      rw [← card_filter_mul_le d (m + 1) q (by omega), card_filter]
    have h3 : ∀ j, q / (j + 1) =
        ∑ m ∈ range q, if (j + 1) * (m + 1) ≤ q then 1 else 0 := by
      intro j
      have := card_filter_mul_le q (j + 1) q (by omega)
      rw [min_eq_right (Nat.div_le_self _ _), card_filter] at this
      rw [← this]
      apply sum_congr rfl; intro m _; rw [mul_comm]
    simp_rw [h2, h3]
    rw [sum_comm]
  rw [key]
  have hq0 : (0 : ℝ) ≤ q := by positivity
  calc ((∑ j ∈ range d, q / (j + 1) : ℕ) : ℝ) ≤ ∑ j ∈ range d, (q : ℝ) / ((j : ℝ) + 1) := by
        push_cast
        apply sum_le_sum; intro j _
        have := Nat.cast_div_le (α := ℝ) (m := q) (n := j + 1)
        push_cast at this
        exact this
    _ = q * (harmonic d : ℝ) := by
        simp only [harmonic]
        push_cast
        rw [mul_sum]
        apply sum_congr rfl; intro j _
        field_simp
    _ ≤ q * (1 + Real.log d) := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log d) hq0

end StrongConv.W2.Alg

end
end

section
open Polynomial Filter Topology

noncomputable section

namespace StrongConv.W2.Alg
open Polynomial Finset

theorem exists_poly_term2 (d q : ℕ) (hq : 1 ≤ q) (v : ℕ) (e : Fin d → ℕ)
    (h2 : v ≤ ∑ i, e i) (h3 : ∑ i, e i ≤ q) :
    ∃ φ : ℝ[X], φ.natDegree ≤ (gPoly d q).natDegree + min d q ∧
      ∀ N : ℕ, q ≤ N → 1 ≤ N →
        (1 / (N : ℝ)) ^ (∑ i, e i - v) * (∏ j ∈ Ico 1 v, (1 - (j : ℝ) * (1 / (N : ℝ)))) /
            ∏ i, ∏ j ∈ Ico 1 (e i), (1 - (j : ℝ) * (1 / (N : ℝ))) =
          φ.eval (1 / (N : ℝ)) / (gPoly d q).eval (1 / (N : ℝ)) := by
  set E := ∑ i, e i with hE
  have he : ∀ i, e i ≤ q := fun i =>
    le_trans (single_le_sum (fun i _ => Nat.zero_le (e i)) (mem_univ i)) h3
  set c : ℕ → ℕ := fun j => (univ.filter (fun i => j < e i)).card with hc
  set dd : ℕ → ℕ := fun j => min d (q / (j + 1)) with hdd
  have hcd : ∀ j, c j ≤ dd j := by
    intro j
    apply le_min
    · exact (card_filter_le _ _).trans (by simp)
    · rw [Nat.le_div_iff_mul_le (by omega)]
      calc c j * (j + 1) = ∑ i ∈ univ.filter (fun i => j < e i), (j + 1) := by
            simp [hc]
        _ ≤ ∑ i ∈ univ.filter (fun i => j < e i), e i := by
            apply sum_le_sum; intro i hi; simp at hi; omega
        _ ≤ E := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; omega)
        _ ≤ q := h3
  -- Σ_{j<q} c j = E
  have hsumc : ∑ j ∈ range q, c j = E := by
    simp only [hc, card_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    rw [← card_filter]
    have : (range q).filter (fun j => j < e i) = range (e i) := by
      ext j; simp only [mem_filter, mem_range]; have := he i; omega
    rw [this, card_range]
  have hc0 : c 0 ≤ min d q := by
    apply le_min
    · exact (card_filter_le _ _).trans (by simp)
    · calc c 0 = ∑ i ∈ univ.filter (fun i => 0 < e i), 1 := by simp [hc]
        _ ≤ ∑ i ∈ univ.filter (fun i => 0 < e i), e i := by
            apply sum_le_sum; intro i hi; simp at hi; omega
        _ ≤ E := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; omega)
        _ ≤ q := h3
  have hsplit : ∑ j ∈ range q, c j = c 0 + ∑ j ∈ Ico 1 q, c j := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega)]
  refine ⟨X ^ (E - v) * (∏ j ∈ Ico 1 v, L j) * ∏ j ∈ Ico 1 q, L j ^ (dd j - c j), ?_, ?_⟩
  · rw [natDegree_gPoly]
    have hA : (∏ j ∈ Ico 1 v, L j).natDegree ≤ v - 1 := by
      refine (natDegree_prod_le _ _).trans ?_
      calc ∑ j ∈ Ico 1 v, (L j).natDegree ≤ ∑ j ∈ Ico 1 v, 1 :=
            sum_le_sum (fun j _ => natDegree_L_le j)
        _ = v - 1 := by simp
    have hR : (∏ j ∈ Ico 1 q, L j ^ (dd j - c j)).natDegree ≤ ∑ j ∈ Ico 1 q, (dd j - c j) := by
      refine (natDegree_prod_le _ _).trans ?_
      apply sum_le_sum
      intro j _
      refine natDegree_pow_le.trans ?_
      calc (dd j - c j) * (L j).natDegree ≤ (dd j - c j) * 1 :=
            Nat.mul_le_mul_left _ (natDegree_L_le j)
        _ = _ := mul_one _
    have hX : (X ^ (E - v) : ℝ[X]).natDegree ≤ E - v := natDegree_X_pow_le _
    have hsub : ∑ j ∈ Ico 1 q, (dd j - c j) + ∑ j ∈ Ico 1 q, c j = ∑ j ∈ Ico 1 q, dd j := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro j _; have := hcd j; omega
    refine (natDegree_mul_le).trans ?_
    have := (natDegree_mul_le (p := (X ^ (E - v) : ℝ[X])) (q := ∏ j ∈ Ico 1 v, L j))
    have hdd : ∑ j ∈ Ico 1 q, dd j = ∑ j ∈ Ico 1 q, min d (q / (j + 1)) := rfl
    omega
  · intro N hN hN1
    set x : ℝ := 1 / (N : ℝ) with hx
    have hD : ∏ i, ∏ j ∈ Ico 1 (e i), (1 - (j : ℝ) * x) =
        ∏ j ∈ Ico 1 q, (1 - (j : ℝ) * x) ^ c j :=
      prod_prod_Ico e q he (fun j => 1 - (j : ℝ) * x)
    have hCpos : 0 < ∏ j ∈ Ico 1 q, (1 - (j : ℝ) * x) ^ c j := by
      apply prod_pos; intro j hj
      exact pow_pos (factor_pos j q N (mem_Ico.1 hj).2 hN hN1) _
    have hRpos : 0 < ∏ j ∈ Ico 1 q, (1 - (j : ℝ) * x) ^ (dd j - c j) := by
      apply prod_pos; intro j hj
      exact pow_pos (factor_pos j q N (mem_Ico.1 hj).2 hN hN1) _
    have hg : (gPoly d q).eval x = (∏ j ∈ Ico 1 q, (1 - (j : ℝ) * x) ^ c j) *
        ∏ j ∈ Ico 1 q, (1 - (j : ℝ) * x) ^ (dd j - c j) := by
      unfold gPoly
      rw [eval_prod, ← prod_mul_distrib]
      apply prod_congr rfl
      intro j _
      rw [← pow_add, eval_pow]
      change (L j).eval x ^ _ = _
      rw [eval_L]
      congr 1
      have := hcd j
      simp only [hdd] at this ⊢
      omega
    have hφ : (X ^ (E - v) * (∏ j ∈ Ico 1 v, L j) *
        ∏ j ∈ Ico 1 q, L j ^ (dd j - c j)).eval x =
        x ^ (E - v) * (∏ j ∈ Ico 1 v, (1 - (j : ℝ) * x)) *
          ∏ j ∈ Ico 1 q, (1 - (j : ℝ) * x) ^ (dd j - c j) := by
      simp [eval_prod]
    rw [hφ, hg, hD]
    exact (mul_div_mul_right _ _ hRpos.ne').symm


end StrongConv.W2.Alg

end
end

section
open Polynomial Filter Topology

noncomputable section

namespace StrongConv.W2

/-- the summand of Hanany–Puder's (10.2) -/
def termV {d : ℕ} (V : ℕ) (e : Fin d → ℕ) (N : ℕ) : ℝ :=
  ((1 : ℝ) / N) ^ (((∑ j, e j : ℕ) : ℤ) - V) * (∏ i ∈ Finset.Ico 1 V, (1 - (i : ℝ) / N)) /
    ∏ j : Fin d, ∏ i ∈ Finset.Ico 1 (e j), (1 - (i : ℝ) / N)

lemma factor_pos' {i N : ℕ} (hi : i < N) : 0 < 1 - (i : ℝ) / N := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [sub_pos, div_lt_one hN]; exact_mod_cast hi

lemma factor_le_one (i N : ℕ) : 1 - (i : ℝ) / N ≤ 1 := by
  have : (0 : ℝ) ≤ (i : ℝ) / N := by positivity
  linarith

lemma den_pos {d : ℕ} (e : Fin d → ℕ) (N : ℕ) (he : ∀ j, e j ≤ N) :
    0 < ∏ j : Fin d, ∏ i ∈ Finset.Ico 1 (e j), (1 - (i : ℝ) / N) := by
  refine Finset.prod_pos fun j _ => Finset.prod_pos fun i hi => factor_pos' ?_
  have := (Finset.mem_Ico.1 hi).2
  have := he j
  omega

lemma den_le_one {d : ℕ} (e : Fin d → ℕ) (N : ℕ) (he : ∀ j, e j ≤ N) :
    ∏ j : Fin d, ∏ i ∈ Finset.Ico 1 (e j), (1 - (i : ℝ) / N) ≤ 1 := by
  refine Finset.prod_le_one (fun j _ => Finset.prod_nonneg fun i hi => (factor_pos' ?_).le)
    fun j _ => Finset.prod_le_one (fun i hi => (factor_pos' ?_).le) fun i _ => factor_le_one i N
  · have := (Finset.mem_Ico.1 hi).2
    have := he j
    omega
  · have := (Finset.mem_Ico.1 ‹_›).2
    have := he j
    omega

lemma termV_nonneg {d : ℕ} (V : ℕ) (e : Fin d → ℕ) (N : ℕ) (hV : V ≤ N) (he : ∀ j, e j ≤ N) :
    0 ≤ termV V e N := by
  unfold termV
  refine div_nonneg (mul_nonneg (zpow_nonneg (by positivity) _)
    (Finset.prod_nonneg fun i hi => (factor_pos' ?_).le)) (den_pos e N he).le
  have := (Finset.mem_Ico.1 hi).2
  omega

lemma termV_ge {d : ℕ} (V : ℕ) (e : Fin d → ℕ) (N : ℕ) (hE : ∑ j, e j < V) (hV : 2 * V ≤ N)
    (he : ∀ j, e j ≤ N) : (N : ℝ) / 2 ^ V ≤ termV V e N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  unfold termV
  set E := ∑ j, e j
  have hz : ((1 : ℝ) / N) ^ ((E : ℤ) - V) = (N : ℝ) ^ (V - E) := by
    rw [show ((E : ℤ) - V) = -((V - E : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast, one_div, inv_pow,
      inv_inv]
  rw [hz]
  have hA : ((1 : ℝ) / 2) ^ V ≤ ∏ i ∈ Finset.Ico 1 V, (1 - (i : ℝ) / N) := by
    calc ((1 : ℝ) / 2) ^ V ≤ ((1 : ℝ) / 2) ^ (Finset.Ico 1 V).card :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by simp)
      _ = ∏ i ∈ Finset.Ico 1 V, ((1 : ℝ) / 2) := by rw [Finset.prod_const]
      _ ≤ _ := Finset.prod_le_prod (fun i _ => by norm_num) fun i hi => by
          have hi' := (Finset.mem_Ico.1 hi).2
          have : (i : ℝ) / N ≤ 1 / 2 := by
            rw [div_le_iff₀ hNpos]
            have : (2 * V : ℝ) ≤ N := by exact_mod_cast hV
            have : (i : ℝ) ≤ V := by exact_mod_cast hi'.le
            linarith
          linarith
  have hD := den_pos e N he
  have hD1 := den_le_one e N he
  have hpow : (N : ℝ) ≤ (N : ℝ) ^ (V - E) := by
    calc (N : ℝ) = (N : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hN1 (by omega)
  have hA0 : 0 ≤ ∏ i ∈ Finset.Ico 1 V, (1 - (i : ℝ) / N) := le_trans (by positivity) hA
  calc (N : ℝ) / 2 ^ V = N * ((1 : ℝ) / 2) ^ V := by rw [one_div, inv_pow]; ring
    _ ≤ (N : ℝ) ^ (V - E) * ∏ i ∈ Finset.Ico 1 V, (1 - (i : ℝ) / N) :=
        mul_le_mul hpow hA (by positivity) (by positivity)
    _ ≤ _ := by
        rw [le_div_iff₀ hD]
        exact mul_le_of_le_one_right (mul_nonneg (by positivity) hA0) hD1

end StrongConv.W2

end
end

section
open Polynomial Filter Topology

noncomputable section

namespace StrongConv.W2.Root

open FreeGroup FreeGroup.reduceCyclically

lemma length_toWord_pow_ge {d : ℕ} (v : FreeGroup (Fin d)) (hv : v ≠ 1) (k : ℕ) :
    k ≤ (v ^ k).toWord.length := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hr : reduceCyclically v.toWord ≠ [] := by
    intro h
    apply hv
    have := congr_arg FreeGroup.mk (conj_conjugator_reduceCyclically v.toWord)
    rw [mk_toWord, h, List.append_nil, ← mul_mk, ← inv_mk, mul_inv_cancel] at this
    exact this.symm
  have hw : (v ^ k).toWord = conjugator v.toWord ++
      (List.replicate k (reduceCyclically v.toWord)).flatten ++ invRev (conjugator v.toWord) := by
    rw [toWord_pow, reduce_flatten_replicate isReduced_toWord, if_neg hk.ne']
  rw [hw]
  simp only [List.length_append, List.length_flatten, List.map_replicate, List.sum_replicate,
    smul_eq_mul]
  have : 1 ≤ (reduceCyclically v.toWord).length := List.length_pos_iff.mpr hr
  nlinarith

theorem exists_nonpower_pow {d : ℕ} (g : FreeGroup (Fin d)) (hg : g ≠ 1) :
    ∃ (v : FreeGroup (Fin d)) (k : ℕ), IsNonPower v ∧ 1 ≤ k ∧ g = v ^ k := by
  classical
  let B := g.toWord.length
  let P : ℕ → Prop := fun k => ∃ v : FreeGroup (Fin d), g = v ^ k
  have hbound : ∀ k, P k → k ≤ B := by
    rintro k ⟨v, hv⟩
    have hv1 : v ≠ 1 := by rintro rfl; exact hg (by simpa using hv)
    have := length_toWord_pow_ge v hv1 k
    rw [← hv] at this
    exact this
  have hP1 : P 1 := ⟨g, by simp⟩
  have h1B : 1 ≤ B := hbound 1 hP1
  set k := Nat.findGreatest P B with hk
  have hPk : P k := Nat.findGreatest_spec h1B hP1
  have hk1 : 1 ≤ k := Nat.le_findGreatest h1B hP1
  obtain ⟨v, hv⟩ := hPk
  refine ⟨v, k, ⟨?_, ?_⟩, hk1, hv⟩
  · rintro rfl; exact hg (by simpa using hv)
  · intro u m hm hvu
    have hPkm : P (k * m) := ⟨u, by rw [hv, hvu, ← pow_mul, mul_comm]⟩
    have hle : k * m ≤ k := Nat.le_findGreatest (hbound _ hPkm) hPkm
    nlinarith

end StrongConv.W2.Root

end
end

section
open Polynomial Filter Topology

noncomputable section

namespace StrongConv.W2

open HananyPuder

lemma termV_eq_npow {d : ℕ} (V : ℕ) (e : Fin d → ℕ) (N : ℕ) (h : V ≤ ∑ j, e j) :
    termV V e N = ((1 / (N : ℝ)) ^ (∑ j, e j - V) *
        (∏ j ∈ Finset.Ico 1 V, (1 - (j : ℝ) * (1 / (N : ℝ))))) /
      ∏ i, ∏ j ∈ Finset.Ico 1 (e i), (1 - (j : ℝ) * (1 / (N : ℝ))) := by
  unfold termV
  rw [show (((∑ j, e j : ℕ) : ℤ) - V) = ((∑ j, e j - V : ℕ) : ℤ) by omega, zpow_natCast]
  simp only [mul_one_div]

variable (π : StableRep)

lemma Mexp_zero {d : ℕ} (u : FreeGroup (Fin d)) (N : ℕ) : Mexp π (fun _ => 0) u N = 1 := by
  unfold Mexp uniformExp
  simp only [pow_zero, Finset.prod_const_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one]
  have : (Fintype.card (Fin d → Equiv.Perm (Fin N)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact div_self this

theorem exists_poly_of_pos {d q : ℕ} (u : FreeGroup (Fin d)) (hu : u ≠ 1)
    (hlen : FreeGroup.norm u ≤ q) (α : Fin π.r → ℕ) (hα : 0 < ∑ i, α i)
    (hwt : ∑ i : Fin π.r, ((i : ℕ) + 1) * α i ≤ π.beta) :
    ∃ p : ℝ[X], p.natDegree ≤ (gPoly d (π.beta * q)).natDegree + min d (π.beta * q) ∧
      ∀ N : ℕ, π.beta * q ≤ N → Mexp π α u N =
        p.eval (1 / (N : ℝ)) / (gPoly d (π.beta * q)).eval (1 / (N : ℝ)) := by
  classical
  set B := π.beta * q with hBdef
  set L := FreeGroup.reduceCyclically u.toWord with hL
  have hnorm1 : 1 ≤ FreeGroup.norm u := Nat.one_le_iff_ne_zero.mpr (by
    intro h; exact hu (FreeGroup.norm_eq_zero.mp h))
  have hq : 1 ≤ q := hnorm1.trans hlen
  have hβ : 1 ≤ π.beta := by
    have : ∑ i : Fin π.r, α i ≤ ∑ i : Fin π.r, ((i : ℕ) + 1) * α i :=
      Finset.sum_le_sum fun i _ => Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    omega
  have hB : 1 ≤ B := Nat.mul_pos hβ hq
  have hℓ : L.length ≤ q := (length_reduceCyclically_le u).trans hlen
  have hcard : Fintype.card (CycleVert L α) ≤ B := by
    rw [card_cycleVert]
    calc ∑ i : Fin π.r, α i * (((i : ℕ) + 1) * L.length) =
          L.length * ∑ i : Fin π.r, ((i : ℕ) + 1) * α i := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ q * π.beta := Nat.mul_le_mul hℓ hwt
      _ = B := mul_comm _ _
  obtain ⟨v₀, k, hv₀, hk, huv⟩ := Root.exists_nonpower_pow u hu
  have hlim := tendsto_Mexp π α v₀ hv₀ k hk
  rw [← huv] at hlim
  have hEle : ∀ P : Finpartition (Finset.univ : Finset (CycleVert L α)), ∑ j, quotEdge P j ≤ B :=
    fun P => (sum_quotEdge_le P).trans hcard
  have hej : ∀ (P : Finpartition (Finset.univ : Finset (CycleVert L α))) (j : Fin d),
      quotEdge P j ≤ B := fun P j =>
    (Finset.single_le_sum (fun j _ => Nat.zero_le (quotEdge P j)) (Finset.mem_univ j)).trans (hEle P)
  have hVle : ∀ P : Finpartition (Finset.univ : Finset (CycleVert L α)), quotVert P ≤ B := by
    intro P
    unfold quotVert
    refine le_trans ?_ hcard
    simpa using P.card_parts_le_card
  have hHP : ∀ N, B ≤ N → Mexp π α u N =
      ∑ P ∈ (Finset.univ : Finset (Finpartition (Finset.univ : Finset (CycleVert L α)))).filter
        IsFoldFree, termV (quotVert P) (quotEdge P) N := by
    intro N hN
    exact HananyPuder.uniformExp_prod_xi_eq_sum_quotients u hu α hα N
      (fun P _ j => (hej P j).trans hN)
  have hnn : ∀ N, B ≤ N → ∀ P : Finpartition (Finset.univ : Finset (CycleVert L α)),
      0 ≤ termV (quotVert P) (quotEdge P) N := fun N hN P =>
    termV_nonneg _ _ N ((hVle P).trans hN) (fun j => (hej P j).trans hN)
  have hkey : ∀ P : Finpartition (Finset.univ : Finset (CycleVert L α)), IsFoldFree P →
      quotVert P ≤ ∑ j, quotEdge P j := by
    intro P hP
    by_contra hlt
    push_neg at hlt
    have h1 : ∀ᶠ N in atTop, Mexp π α u N < Vval π.r k α + 1 :=
      hlim.eventually (gt_mem_nhds (lt_add_one _))
    have h2 : ∀ᶠ N : ℕ in atTop, B ≤ N ∧ 2 * quotVert P ≤ N ∧
        (2 : ℝ) ^ quotVert P * (Vval π.r k α + 1) < N := by
      refine ((eventually_ge_atTop B).and ((eventually_ge_atTop (2 * quotVert P)).and ?_))
      exact tendsto_natCast_atTop_atTop.eventually_gt_atTop _
    obtain ⟨N, hM, hN1, hN2, hN3⟩ := (h1.and h2).exists
    have hge := termV_ge (quotVert P) (quotEdge P) N hlt hN2 (fun j => (hej P j).trans hN1)
    have hle : termV (quotVert P) (quotEdge P) N ≤ Mexp π α u N := by
      rw [hHP N hN1]
      exact Finset.single_le_sum (fun P' _ => hnn N hN1 P') (Finset.mem_filter.2 ⟨Finset.mem_univ _, hP⟩)
    have h2pos : (0 : ℝ) < 2 ^ quotVert P := by positivity
    have : Vval π.r k α + 1 < (N : ℝ) / 2 ^ quotVert P := by
      rw [lt_div_iff₀ h2pos]; linarith
    linarith
  have hpoly : ∀ P : Finpartition (Finset.univ : Finset (CycleVert L α)), IsFoldFree P →
      ∃ φ : ℝ[X], φ.natDegree ≤ (gPoly d B).natDegree + min d B ∧
        ∀ N : ℕ, B ≤ N → 1 ≤ N →
          ((1 / (N : ℝ)) ^ (∑ j, quotEdge P j - quotVert P) *
            (∏ j ∈ Finset.Ico 1 (quotVert P), (1 - (j : ℝ) * (1 / (N : ℝ))))) /
            ∏ i, ∏ j ∈ Finset.Ico 1 (quotEdge P i), (1 - (j : ℝ) * (1 / (N : ℝ))) =
          φ.eval (1 / (N : ℝ)) / (gPoly d B).eval (1 / (N : ℝ)) := by
    intro P hP
    exact Alg.exists_poly_term2 d B hB (quotVert P) (quotEdge P) (hkey P hP) (hEle P)
  choose! φ hφdeg hφeq using hpoly
  set S := (Finset.univ : Finset (Finpartition (Finset.univ : Finset (CycleVert L α)))).filter
    IsFoldFree with hS
  refine ⟨∑ P ∈ S, φ P, ?_, ?_⟩
  · exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun P hP =>
      hφdeg P (Finset.mem_filter.1 hP).2
  · intro N hN
    have hN1 : 1 ≤ N := hB.trans hN
    rw [hHP N hN, Polynomial.eval_finset_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun P hP => ?_
    have hP' := (Finset.mem_filter.1 hP).2
    rw [termV_eq_npow _ _ N (hkey P hP'), hφeq P hP' N hN hN1]

end StrongConv.W2
end
end

section
open Polynomial Filter Topology

noncomputable section

namespace StrongConv.W2

theorem lemma101 (π : StableRep) (hπ : π.NoTrivialSummand) (d q : ℕ) (w : List (Letter d))
    (hw : w.length ≤ q) (hw1 : wordFree w ≠ 1) :
    ((gPoly d (π.beta * q)).natDegree : ℝ) ≤ π.beta * q * (1 + Real.log d) ∧
      ∃ f : ℝ[X], (f.natDegree : ℝ) ≤ π.beta * q * (1 + Real.log d) ∧
        ∀ N : ℕ, π.beta * q ≤ N → π.N₀ ≤ N →
          uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
              (LinearMap.trace ℂ (EuclideanSpace ℂ (Fin (π.dim N)))
                (wordEval (π.model σ) w :
                  EuclideanSpace ℂ (Fin (π.dim N)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (π.dim N)))).re) =
            f.eval (1 / (N : ℝ)) / (gPoly d (π.beta * q)).eval (1 / (N : ℝ)) := by
  classical
  set B := π.beta * q with hBdef
  set g := gPoly d B with hg
  have hlen : FreeGroup.norm (wordFree w) ≤ q := (norm_wordFree_le w).trans hw
  -- degree bounds
  have hG : (((g.natDegree + min d B : ℕ)) : ℝ) ≤ B * (1 + Real.log d) := by
    rcases Nat.eq_zero_or_pos B with h0 | h0
    · have : g = 1 := by rw [hg, h0]; simp [gPoly]
      rw [this, h0]; simp
    · exact Alg.natDegree_gPoly_add_min_le d B h0
  have hgdeg : (g.natDegree : ℝ) ≤ B * (1 + Real.log d) :=
    le_trans (by exact_mod_cast Nat.le_add_right _ _) hG
  have hBc : (B : ℝ) = π.beta * q := by simp [hBdef]
  rw [hBc] at hG hgdeg
  refine ⟨hgdeg, ?_⟩
  have hgne : ∀ N : ℕ, B ≤ N → g.eval (1 / (N : ℝ)) ≠ 0 := by
    intro N hN
    rcases Nat.eq_zero_or_pos B with h0 | h0
    · simp [hg, h0, gPoly]
    · exact Alg.gPoly_eval_ne_zero d B N hN (h0.trans_le hN)
  have hper : ∀ α ∈ π.φ.support, ∃ p : ℝ[X], p.natDegree ≤ g.natDegree + min d B ∧
      ∀ N : ℕ, B ≤ N → Mexp π (fun i => α i) (wordFree w) N =
        p.eval (1 / (N : ℝ)) / g.eval (1 / (N : ℝ)) := by
    intro α hα
    by_cases h0 : ∑ i, α i = 0
    · refine ⟨g, Nat.le_add_right _ _, fun N hN => ?_⟩
      have : (fun i => α i) = fun _ => 0 := by
        funext i
        exact (Finset.sum_eq_zero_iff.mp h0) i (Finset.mem_univ i)
      rw [this, Mexp_zero, div_self (hgne N hN)]
    · exact exists_poly_of_pos π (wordFree w) hw1 hlen (fun i => α i) (Nat.pos_of_ne_zero h0)
        (weight_le_beta π α hα)
  choose! p hpdeg hpeq using hper
  refine ⟨∑ α ∈ π.φ.support, C (cre π α) * p α, ?_, ?_⟩
  · refine le_trans ?_ hG
    exact_mod_cast Polynomial.natDegree_sum_le_of_forall_le _ _ fun α hα =>
      (Polynomial.natDegree_C_mul_le _ _).trans (hpdeg α hα)
  · intro N hN hN0
    rw [uniformExp_trace_eq_sum π hN0 w, Polynomial.eval_finsetSum, Finset.sum_div]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [hpeq α hα N hN]
    simp [cre, mul_div_assoc]

end StrongConv.W2

end
end

open StrongConv Polynomial in
theorem solution (π : StableRep) (hπ : π.NoTrivialSummand)
    (d q : ℕ) (w : List (Letter d)) (hw : w.length ≤ q) (hw1 : wordFree w ≠ 1) :
    ((gPoly d (π.beta * q)).natDegree : ℝ) ≤ π.beta * q * (1 + Real.log d) ∧
      ∃ f : ℝ[X], (f.natDegree : ℝ) ≤ π.beta * q * (1 + Real.log d) ∧
        ∀ N : ℕ, π.beta * q ≤ N → π.N₀ ≤ N →
          uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
              (LinearMap.trace ℂ (EuclideanSpace ℂ (Fin (π.dim N)))
                (wordEval (π.model σ) w :
                  EuclideanSpace ℂ (Fin (π.dim N)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (π.dim N)))).re) =
            f.eval (1 / (N : ℝ)) / (gPoly d (π.beta * q)).eval (1 / (N : ℝ)) :=
  StrongConv.W2.lemma101 π hπ d q w hw hw1
