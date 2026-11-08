-- Prove2me | solution 1 for ShadowTomography.UpperBound.adaptive_rounds
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-07T08:41:53.750046+00:00
-- url     : https://prove2.me/submissions/ab22aaad-ce9e-4566-bf1d-c852a98f470f

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ShadowTomography_UpperBound_IsEffect
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_ShadowTomography_UpperBound_POVM
import Definitions.Def_ShadowTomography_UpperBound_ampMeasurements
import Definitions.Def_ShadowTomography_UpperBound_avgMarginal
import Definitions.Def_ShadowTomography_UpperBound_seqAccept
set_option autoImplicit false

open scoped ComplexOrder MatrixOrder

namespace ShadowTomography.UpperBound.Leaves

open Matrix

/-- PSD matrices are `star s * s` with `s = √A` self-adjoint. -/
lemma psd_sqrt {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.PosSemidef) :
    (CFC.sqrt A)ᴴ = CFC.sqrt A ∧ CFC.sqrt A * CFC.sqrt A = A := by
  have h0 : (0 : Matrix n n ℂ) ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  refine ⟨?_, CFC.sqrt_mul_sqrt_self A h0⟩
  have := (CFC.sqrt_nonneg A).isSelfAdjoint
  simpa [IsSelfAdjoint, Matrix.star_eq_conjTranspose] using this

lemma trace_mul_psd {n : Type} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace.re := by
  obtain ⟨hs, hss⟩ := psd_sqrt B hB
  set s := CFC.sqrt B
  have h1 : (A * B).trace = (sᴴ * A * s).trace := by
    rw [← hss, hs, ← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  have h2 : (sᴴ * A * s).PosSemidef := hA.conjTranspose_mul_mul_same s
  rw [h1]
  exact (Complex.nonneg_iff.mp h2.trace_nonneg).1

/-- Product operator on `q` registers. -/
def prodOp {n : Type} {q : ℕ} (f : Fin q → Matrix n n ℂ) : Matrix (Fin q → n) (Fin q → n) ℂ :=
  fun x y => ∏ r, f r (x r) (y r)

lemma prodOp_mul {n : Type} [Fintype n] {q : ℕ} (f g : Fin q → Matrix n n ℂ) :
    prodOp f * prodOp g = prodOp (fun r => f r * g r) := by
  ext x y
  simp only [prodOp, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.prod_mul_distrib]

lemma prodOp_conjTranspose {n : Type} [Fintype n] {q : ℕ} (f : Fin q → Matrix n n ℂ) :
    (prodOp f)ᴴ = prodOp (fun r => (f r)ᴴ) := by
  ext x y
  simp [prodOp, Matrix.conjTranspose_apply]

lemma prodOp_psd {n : Type} [Fintype n] [DecidableEq n] {q : ℕ} (f : Fin q → Matrix n n ℂ)
    (hf : ∀ r, (f r).PosSemidef) : (prodOp f).PosSemidef := by
  have : prodOp f = (prodOp (fun r => CFC.sqrt (f r)))ᴴ * prodOp (fun r => CFC.sqrt (f r)) := by
    rw [prodOp_conjTranspose, prodOp_mul]
    congr 1; funext r
    rw [(psd_sqrt _ (hf r)).1, (psd_sqrt _ (hf r)).2]
  rw [this]; exact Matrix.posSemidef_conjTranspose_mul_self _

lemma prodOp_trace {n : Type} [Fintype n] {q : ℕ} (f : Fin q → Matrix n n ℂ) :
    (prodOp f).trace = ∏ r, (f r).trace := by
  simp only [Matrix.trace, Matrix.diag, prodOp]
  rw [Fintype.prod_sum]

/-- A PSD matrix of trace one lies below the identity. -/
lemma one_sub_psd_of_trace_one {m : Type} [Fintype m] [DecidableEq m] (P : Matrix m m ℂ)
    (hP : P.PosSemidef) (ht : P.trace = 1) : (1 - P).PosSemidef := by
  have hH := hP.1
  set U := hH.eigenvectorUnitary
  have hspec : P = (U : Matrix m m ℂ) * Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) *
      star (U : Matrix m m ℂ) := by
    conv_lhs => rw [hH.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply]
    rfl
  have hUU : (U : Matrix m m ℂ) * star (U : Matrix m m ℂ) = 1 := Unitary.mul_star_self_of_mem U.2
  have hsum : ∑ i, hH.eigenvalues i = 1 := by
    have := hH.trace_eq_sum_eigenvalues; rw [ht] at this
    have h2 := congrArg Complex.re this
    simpa using h2.symm
  have hle : ∀ i, hH.eigenvalues i ≤ 1 := fun i => by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => hP.eigenvalues_nonneg j) (Finset.mem_univ i)
  have hrw : 1 - P = (U : Matrix m m ℂ) *
      Matrix.diagonal (RCLike.ofReal ∘ (fun i => 1 - hH.eigenvalues i)) *
      (U : Matrix m m ℂ)ᴴ := by
    rw [← Matrix.star_eq_conjTranspose]
    conv_lhs => rw [hspec, ← hUU]
    have : Matrix.diagonal (RCLike.ofReal ∘ (fun i => 1 - hH.eigenvalues i)) =
        (1 : Matrix m m ℂ) - Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
      ext i j; by_cases h : i = j <;> simp [h]
    rw [this, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  rw [hrw]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro i
  simp only [Pi.zero_apply, Function.comp_apply]
  exact Complex.zero_le_real.mpr (sub_nonneg.mpr (hle i))

lemma sum_acceptPattern {n : Type} [Fintype n] [DecidableEq n] (E : Matrix n n ℂ) (q : ℕ) :
    ∑ S : Finset (Fin q), acceptPattern E q S = 1 := by
  classical
  ext x y
  rw [Matrix.sum_apply]
  have key : ∀ S : Finset (Fin q), acceptPattern E q S x y =
      (∏ r ∈ S, E (x r) (y r)) * ∏ r ∈ Finset.univ \ S, (1 - E) (x r) (y r) := by
    intro S
    have : acceptPattern E q S x y = ∏ r, (if r ∈ S then E (x r) (y r) else (1 - E) (x r) (y r)) := by
      simp only [acceptPattern]
      exact Finset.prod_congr rfl fun r _ => by split_ifs <;> rfl
    rw [this, Finset.prod_ite]
    congr 2
    · ext r; simp
    · ext r; simp
  simp_rw [key]
  rw [← Finset.powerset_univ, ← Finset.prod_add]
  simp only [Matrix.sub_apply, add_sub_cancel]
  by_cases hxy : x = y
  · subst hxy; simp [Matrix.one_apply]
  · obtain ⟨r, hr⟩ : ∃ r, x r ≠ y r := by
      by_contra h; push Not at h; exact hxy (funext h)
    rw [Matrix.one_apply_ne hxy]
    exact Finset.prod_eq_zero (Finset.mem_univ r) (Matrix.one_apply_ne hr)

lemma filter_sum_isEffect {n : Type} [Fintype n] [DecidableEq n] (E : Matrix n n ℂ)
    (hE : IsEffect E) (q : ℕ) (p : Finset (Fin q) → Prop) [DecidablePred p] :
    IsEffect (∑ S ∈ Finset.univ.filter p, acceptPattern E q S) := by
  have hAP : ∀ S, (acceptPattern E q S).PosSemidef := fun S => by
    have : acceptPattern E q S = prodOp (fun r => if r ∈ S then E else 1 - E) := by
      ext x y; simp [acceptPattern, prodOp]
    rw [this]; apply prodOp_psd; intro r; split_ifs
    · exact hE.1
    · exact hE.2
  refine ⟨Matrix.posSemidef_sum _ (fun S _ => hAP S), ?_⟩
  have : 1 - ∑ S ∈ Finset.univ.filter p, acceptPattern E q S =
      ∑ S ∈ Finset.univ.filter (fun S => ¬ p S), acceptPattern E q S := by
    rw [← sum_acceptPattern E q, ← Finset.sum_filter_add_sum_filter_not Finset.univ p]
    abel
  rw [this]; exact Matrix.posSemidef_sum _ (fun S _ => hAP S)

end ShadowTomography.UpperBound.Leaves

namespace ShadowTomography.UpperBound.PovmKit
open Matrix ShadowTomography.UpperBound ShadowTomography.UpperBound.Leaves
open scoped Kronecker

/-- Tensor power indexed by an arbitrary finite type. -/
def tp {n : Type} (ρ : Matrix n n ℂ) (ι : Type) [Fintype ι] : Matrix (ι → n) (ι → n) ℂ :=
  fun x y => ∏ i, ρ (x i) (y i)

section tp
variable {n : Type} [Fintype n] [DecidableEq n]

lemma tp_mul (ι : Type) [Fintype ι] [DecidableEq ι] (A B : Matrix n n ℂ) :
    tp A ι * tp B ι = tp (A * B) ι := by
  ext x y
  simp only [tp, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl fun z _ => by rw [Finset.prod_mul_distrib]

lemma tp_conjTranspose (ι : Type) [Fintype ι] (A : Matrix n n ℂ) : (tp A ι)ᴴ = tp Aᴴ ι := by
  ext x y; simp [tp, Matrix.conjTranspose_apply]

lemma tp_density (ι : Type) [Fintype ι] [DecidableEq ι] (ρ : Matrix n n ℂ)
    (hρ : WildeQIT.IsDensityOperator ρ) : WildeQIT.IsDensityOperator (tp ρ ι) := by
  obtain ⟨hs, hss⟩ := psd_sqrt ρ hρ.1
  refine ⟨?_, ?_⟩
  · have : tp ρ ι = (tp (CFC.sqrt ρ) ι)ᴴ * tp (CFC.sqrt ρ) ι := by
      rw [tp_conjTranspose, tp_mul, hs, hss]
    rw [this]; exact Matrix.posSemidef_conjTranspose_mul_self _
  · simp only [Matrix.trace, Matrix.diag, tp]
    rw [show (∑ x : ι → n, ∏ i, ρ (x i) (x i)) = ∏ _i : ι, ∑ a, ρ a a from
      (Fintype.prod_sum (fun (_ : ι) (a : n) => ρ a a)).symm]
    have h := hρ.2
    simp only [Matrix.trace, Matrix.diag] at h
    simp [h]

lemma tp_reindex {ι κ : Type} [Fintype ι] [Fintype κ] (ρ : Matrix n n ℂ) (e : ι ≃ κ) :
    (tp ρ κ).submatrix (e.arrowCongr (Equiv.refl n)) (e.arrowCongr (Equiv.refl n)) = tp ρ ι := by
  ext x y
  simp only [tp, Matrix.submatrix_apply, Equiv.arrowCongr_apply, Equiv.coe_refl,
    Function.comp_apply, id]
  exact Equiv.prod_comp e.symm (fun i => ρ (x i) (y i))

lemma tp_sum (ι κ : Type) [Fintype ι] [Fintype κ] (ρ : Matrix n n ℂ) :
    (tp ρ ι ⊗ₖ tp ρ κ).submatrix (Equiv.sumArrowEquivProdArrow ι κ n)
      (Equiv.sumArrowEquivProdArrow ι κ n) = tp ρ (ι ⊕ κ) := by
  ext x y
  simp [tp, Matrix.kroneckerMap_apply, Fintype.prod_sum_type]

lemma tp_curry (ι κ : Type) [Fintype ι] [Fintype κ] (ρ : Matrix n n ℂ) :
    (tp (tp ρ κ) ι).submatrix (Equiv.curry ι κ n) (Equiv.curry ι κ n) = tp ρ (ι × κ) := by
  ext x y
  simp [tp, Fintype.prod_prod_type]

end tp

section povm
variable {n : Type} [Fintype n] [DecidableEq n]

lemma trace_submatrix_equiv {X Z : Type} [Fintype X] [Fintype Z] (M : Matrix X X ℂ) (e : Z ≃ X) :
    (M.submatrix e e).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact Equiv.sum_comp e (fun i => M i i)

lemma trace_mul_psd_c {X : Type} [Fintype X] [DecidableEq X]
    (A B : Matrix X X ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  obtain ⟨hs, hss⟩ := psd_sqrt B hB
  set s := CFC.sqrt B
  have h1 : (A * B).trace = (sᴴ * A * s).trace := by
    rw [← hss, hs, ← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  rw [h1]; exact (hA.conjTranspose_mul_mul_same _).trace_nonneg

/-- Reindex the system of a POVM along an equivalence. -/
def comap {Ω X Z : Type} [Fintype Ω] [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    (P : POVM Ω X) (e : Z ≃ X) : POVM Ω Z where
  op ω := (P.op ω).submatrix e e
  psd ω := (Matrix.posSemidef_submatrix_equiv e).mpr (P.psd ω)
  complete := by
    ext i j
    rw [Matrix.sum_apply]
    have := congrArg (fun M : Matrix X X ℂ => M (e i) (e j)) P.complete
    simp only [Matrix.sum_apply] at this
    simp only [Matrix.submatrix_apply, this, Matrix.one_apply, e.injective.eq_iff]

lemma prob_comap {Ω X Z : Type} [Fintype Ω] [Fintype X] [DecidableEq X] [Fintype Z]
    [DecidableEq Z] (P : POVM Ω X) (e : Z ≃ X) (σ : Matrix X X ℂ) (A : Ω → Prop) :
    (comap P e).prob (σ.submatrix e e) A = P.prob σ A := by
  unfold POVM.prob
  refine Finset.sum_congr rfl fun ω _ => ?_
  simp only [comap]
  rw [Matrix.submatrix_mul_equiv, trace_submatrix_equiv]

/-- Relabel the outcomes of a POVM. -/
def mapOut {Ω Ω' X : Type} [Fintype Ω] [Fintype Ω'] [Fintype X] [DecidableEq X]
    (P : POVM Ω X) (e : Ω ≃ Ω') : POVM Ω' X where
  op ω := P.op (e.symm ω)
  psd ω := P.psd _
  complete := (Equiv.sum_comp e.symm P.op).trans P.complete

lemma prob_mapOut {Ω Ω' X : Type} [Fintype Ω] [Fintype Ω'] [Fintype X] [DecidableEq X]
    (P : POVM Ω X) (e : Ω ≃ Ω') (σ : Matrix X X ℂ) (A : Ω' → Prop) :
    (mapOut P e).prob σ A = P.prob σ (fun ω => A (e ω)) := by
  classical
  unfold POVM.prob
  rw [Finset.sum_filter, Finset.sum_filter, ← Equiv.sum_comp e]
  simp [mapOut]

/-- The trivial one-outcome POVM. -/
def triv (X : Type) [Fintype X] [DecidableEq X] : POVM Unit X :=
  ⟨fun _ => 1, fun _ => Matrix.PosSemidef.one, by simp⟩

/-- Two-stage product POVM `P_{ω₁} ⊗ Q_{ω₁, ω₂}`. -/
def kron {Ω₁ Ω₂ X Y : Type} [Fintype Ω₁] [Fintype Ω₂] [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] (P : POVM Ω₁ X) (Q : Ω₁ → POVM Ω₂ Y) : POVM (Ω₁ × Ω₂) (X × Y) where
  op ω := P.op ω.1 ⊗ₖ (Q ω.1).op ω.2
  psd ω := (P.psd _).kronecker ((Q _).psd _)
  complete := by
    ext ⟨x, y⟩ ⟨x', y'⟩
    rw [Matrix.sum_apply, Fintype.sum_prod_type]
    simp only [Matrix.kroneckerMap_apply]
    have hQ : ∀ a, ∑ b, (Q a).op b y y' = (1 : Matrix Y Y ℂ) y y' := fun a => by
      rw [← Matrix.sum_apply, (Q a).complete]
    simp_rw [← Finset.mul_sum, hQ, ← Finset.sum_mul]
    rw [← Matrix.sum_apply, P.complete]
    simp only [Matrix.one_apply, Prod.mk.injEq]
    split_ifs <;> simp_all

lemma term_nonneg {Ω X : Type} [Fintype Ω] [Fintype X] [DecidableEq X] (P : POVM Ω X)
    (σ : Matrix X X ℂ) (hσ : σ.PosSemidef) (ω : Ω) : 0 ≤ (P.op ω * σ).trace.re :=
  trace_mul_psd _ _ (P.psd ω) hσ

lemma prob_univ {Ω X : Type} [Fintype Ω] [Fintype X] [DecidableEq X] (P : POVM Ω X)
    (σ : Matrix X X ℂ) : P.prob σ (fun _ => True) = σ.trace.re := by
  unfold POVM.prob
  rw [Finset.sum_filter]
  simp_rw [if_pos trivial]
  rw [← Complex.re_sum, ← Matrix.trace_sum,
    ← Finset.sum_mul, P.complete, Matrix.one_mul]

lemma prob_mono {Ω X : Type} [Fintype Ω] [Fintype X] [DecidableEq X] (P : POVM Ω X)
    (σ : Matrix X X ℂ) (hσ : σ.PosSemidef) (A B : Ω → Prop) (h : ∀ ω, A ω → B ω) :
    P.prob σ A ≤ P.prob σ B := by
  classical
  unfold POVM.prob
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_le_sum fun ω _ => ?_
  by_cases hA : A ω
  · simp [hA, h ω hA]
  · by_cases hB : B ω
    · simp [hA, hB, term_nonneg P σ hσ ω]
    · simp [hA, hB]

lemma prob_le_one {Ω X : Type} [Fintype Ω] [Fintype X] [DecidableEq X] (P : POVM Ω X)
    (σ : Matrix X X ℂ) (hσ : WildeQIT.IsDensityOperator σ) (A : Ω → Prop) :
    P.prob σ A ≤ 1 := by
  have := prob_mono P σ hσ.1 A (fun _ => True) (fun _ _ => trivial)
  rw [prob_univ, hσ.2, Complex.one_re] at this
  exact this

lemma kron_prob {Ω₁ Ω₂ X Y : Type} [Fintype Ω₁] [Fintype Ω₂] [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (P : POVM Ω₁ X) (Q : Ω₁ → POVM Ω₂ Y)
    (σ : Matrix X X ℂ) (τ : Matrix Y Y ℂ) (hσ : σ.PosSemidef) (hτ : τ.PosSemidef)
    (B : Ω₁ × Ω₂ → Prop) [DecidablePred B] :
    (kron P Q).prob (σ ⊗ₖ τ) B = ∑ a, ∑ b, if B (a, b) then
      (P.op a * σ).trace.re * ((Q a).op b * τ).trace.re else 0 := by
  classical
  unfold POVM.prob
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs
  · simp only [kron]
    rw [← Matrix.mul_kronecker_mul, Matrix.trace_kronecker, Complex.mul_re]
    have h1 := (Complex.nonneg_iff.mp (trace_mul_psd_c _ _ (P.psd a) hσ)).2
    rw [← h1, zero_mul, sub_zero]
  · rfl

lemma kron_bound {Ω₁ Ω₂ X Y : Type} [Fintype Ω₁] [Fintype Ω₂] [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (P : POVM Ω₁ X) (Q : Ω₁ → POVM Ω₂ Y)
    (σ : Matrix X X ℂ) (τ : Matrix Y Y ℂ) (hσ : WildeQIT.IsDensityOperator σ)
    (hτ : WildeQIT.IsDensityOperator τ) (S : Ω₁ → Prop) (good : Ω₁ → Ω₂ → Prop)
    (δ₁ δ₂ : ℝ) (h0 : 0 ≤ δ₂) (h1 : 1 - δ₁ ≤ P.prob σ S)
    (h2 : ∀ a, S a → 1 - δ₂ ≤ (Q a).prob τ (good a)) :
    1 - δ₁ - δ₂ ≤ (kron P Q).prob (σ ⊗ₖ τ) (fun ω => S ω.1 ∧ good ω.1 ω.2) := by
  classical
  rw [kron_prob P Q σ τ hσ.1 hτ.1]
  have step : ∀ a, (if S a then (P.op a * σ).trace.re * (1 - δ₂) else 0) ≤
      ∑ b, if S a ∧ good a b then (P.op a * σ).trace.re * ((Q a).op b * τ).trace.re else 0 := by
    intro a
    by_cases hS : S a
    · simp only [hS, true_and, if_true]
      have hq : (Q a).prob τ (good a) =
          ∑ b, if good a b then ((Q a).op b * τ).trace.re else 0 := by
        unfold POVM.prob; rw [Finset.sum_filter]
      calc (P.op a * σ).trace.re * (1 - δ₂)
          ≤ (P.op a * σ).trace.re * (Q a).prob τ (good a) :=
            mul_le_mul_of_nonneg_left (h2 a hS) (term_nonneg P σ hσ.1 a)
        _ = _ := by
            rw [hq, Finset.mul_sum]
            exact Finset.sum_congr rfl fun b _ => by split_ifs <;> simp
    · simp [hS]
  have hsum : ∑ a, (if S a then (P.op a * σ).trace.re * (1 - δ₂) else 0) =
      (1 - δ₂) * P.prob σ S := by
    unfold POVM.prob
    rw [Finset.sum_filter, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by split_ifs <;> ring
  have hle := prob_le_one P σ hσ S
  have hm : δ₂ * P.prob σ S ≤ δ₂ := mul_le_of_le_one_right h0 hle
  calc 1 - δ₁ - δ₂ ≤ (1 - δ₂) * P.prob σ S := by linarith
    _ = _ := hsum.symm
    _ ≤ _ := Finset.sum_le_sum fun a _ => step a

end povm
end ShadowTomography.UpperBound.PovmKit

open Matrix ShadowTomography.UpperBound ShadowTomography.UpperBound.Leaves
  ShadowTomography.UpperBound.PovmKit
open scoped Kronecker

theorem solution {n : Type} [Fintype n] [DecidableEq n] {Ω : Type} [Fintype Ω]
    (R k : ℕ) (P : ∀ r : Fin R, (Fin r → Ω) → POVM Ω (Fin k → n)) :
    ∃ Q : POVM (Fin R → Ω) (Fin (R * k) → n),
      ∀ (ρ : Matrix n n ℂ), WildeQIT.IsDensityOperator ρ →
        ∀ (good : ∀ r : Fin R, (Fin r → Ω) → Ω → Prop) (δ : Fin R → ℝ),
          (∀ r h, 1 - δ r ≤ (P r h).prob (tensorPow ρ k) (good r h)) →
          1 - ∑ r, δ r ≤ Q.prob (tensorPow ρ (R * k))
            (fun ω => ∀ r : Fin R,
              good r (fun i => ω (Fin.castLT i (lt_trans i.isLt r.isLt))) (ω r)) := by
  classical
  induction R with
  | zero =>
    refine ⟨⟨fun _ => 1, fun _ => Matrix.PosSemidef.one, by simp⟩, ?_⟩
    intro ρ hρ good δ _
    have hE : (fun ω : Fin 0 → Ω => ∀ r : Fin 0,
        good r (fun i => ω (Fin.castLT i (lt_trans i.isLt r.isLt))) (ω r)) = fun _ => True :=
      funext fun ω => propext ⟨fun _ => trivial, fun _ r => r.elim0⟩
    rw [hE, prob_univ, show tensorPow ρ (0 * k) = tp ρ (Fin (0 * k)) from rfl,
      (tp_density _ ρ hρ).2]
    simp
  | succ R ih =>
    obtain ⟨Q', hQ'⟩ := ih (fun r h => P r.castSucc h)
    let eo : (Fin R → Ω) × Ω ≃ (Fin (R + 1) → Ω) :=
      (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ => Ω))
    let ec : Fin ((R + 1) * k) ≃ Fin (R * k) ⊕ Fin k :=
      (finCongr (by ring : (R + 1) * k = R * k + k)).trans finSumFinEquiv.symm
    refine ⟨comap (comap (mapOut (kron Q' (fun h => P (Fin.last R) h)) eo)
      (Equiv.sumArrowEquivProdArrow (Fin (R * k)) (Fin k) n))
      (ec.arrowCongr (Equiv.refl n)), ?_⟩
    intro ρ hρ good δ hP
    have hA := tp_density (Fin (R * k)) ρ hρ
    have hB := tp_density (Fin k) ρ hρ
    rw [show tensorPow ρ ((R + 1) * k) = tp ρ (Fin ((R + 1) * k)) from rfl,
      ← tp_reindex ρ ec, prob_comap, ← tp_sum, prob_comap, prob_mapOut]
    -- the last-round slack is nonnegative
    have hne : Nonempty Ω := by
      by_contra hΩ
      rw [not_nonempty_iff] at hΩ
      have h1 := prob_univ (P ⟨0, by omega⟩ (fun i => Fin.elim0 i)) (tp ρ (Fin k))
      rw [hB.2] at h1
      simp [POVM.prob, Finset.univ_eq_empty] at h1
    obtain ⟨ω0⟩ := hne
    have hδ : 0 ≤ δ (Fin.last R) := by
      have h1 := hP (Fin.last R) (fun _ => ω0)
      have h2 := prob_le_one (P (Fin.last R) (fun _ => ω0)) (tensorPow ρ k) hB
        (good (Fin.last R) (fun _ => ω0))
      linarith
    have hq : 1 - ∑ r : Fin R, δ r.castSucc ≤ Q'.prob (tp ρ (Fin (R * k)))
        (fun ω' => ∀ r : Fin R,
          good r.castSucc (fun i => ω' (Fin.castLT i (lt_trans i.isLt r.isLt))) (ω' r)) :=
      hQ' ρ hρ (fun r h => good r.castSucc h) (fun r => δ r.castSucc)
        (fun r h => hP r.castSucc h)
    have hl : ∀ ω' : Fin R → Ω, True → 1 - δ (Fin.last R) ≤
        (P (Fin.last R) ω').prob (tp ρ (Fin k)) (good (Fin.last R) ω') :=
      fun ω' _ => hP (Fin.last R) ω'
    have hb := kron_bound Q' (fun h => P (Fin.last R) h) (tp ρ (Fin (R * k))) (tp ρ (Fin k)) hA hB
      (fun ω' => ∀ r : Fin R,
        good r.castSucc (fun i => ω' (Fin.castLT i (lt_trans i.isLt r.isLt))) (ω' r))
      (fun ω' x => good (Fin.last R) ω' x) (∑ r : Fin R, δ r.castSucc) (δ (Fin.last R)) hδ
      hq (fun ω' _ => hl ω' trivial)
    rw [Fin.sum_univ_castSucc]
    refine le_trans (by linarith [hb]) (le_trans hb ?_)
    refine prob_mono _ _ (hA.1.kronecker hB.1) _ _ ?_
    rintro ⟨ω', x⟩ ⟨hS, hg⟩
    have key : ∀ (m : ℕ) (hm : m < R) (h : m < R + 1),
        (Fin.snoc (α := fun _ => Ω) ω' x ⟨m, h⟩ : Ω) = ω' ⟨m, hm⟩ := fun m hm h =>
      Fin.snoc_castSucc (α := fun _ => Ω) (p := ω') (x := x) ⟨m, hm⟩
    have heo : eo (ω', x) = Fin.snoc (α := fun _ => Ω) ω' x := rfl
    simp only [heo]
    intro r
    refine Fin.lastCases ?_ (fun r' => ?_) r
    · rw [Fin.snoc_last]
      convert hg using 2
      all_goals first
        | rfl
        | (funext i; exact key i.1 i.2 _)
        | exact key _ _ _
    · rw [Fin.snoc_castSucc]
      convert hS r' using 2
      all_goals first
        | rfl
        | (funext i; exact key i.1 _ _)
        | exact key _ _ _
