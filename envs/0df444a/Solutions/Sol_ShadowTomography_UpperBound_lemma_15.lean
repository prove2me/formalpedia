-- Prove2me | solution 1 for ShadowTomography.UpperBound.lemma_15
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-07T14:09:46.500055+00:00
-- url     : https://prove2.me/submissions/a4617133-03f1-4708-bf35-0da481762733

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ShadowTomography_UpperBound_IsEffect
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_ShadowTomography_UpperBound_POVM
import Theorems.Thm_ShadowTomography_UpperBound_lemma_14
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

namespace ShadowTomography.UpperBound.L15
open Matrix ShadowTomography.UpperBound ShadowTomography.UpperBound.Leaves
  ShadowTomography.UpperBound.PovmKit
open scoped Kronecker

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Split the system `ι → n` along `ι ≃ α ⊕ β`. -/
def sp {ι α β : Type} (e : ι ≃ α ⊕ β) : (ι → n) ≃ (α → n) × (β → n) :=
  (e.arrowCongr (Equiv.refl n)).trans (Equiv.sumArrowEquivProdArrow α β n)

lemma tp_sp {ι α β : Type} [Fintype ι] [Fintype α] [Fintype β] (ρ : Matrix n n ℂ)
    (e : ι ≃ α ⊕ β) : (tp ρ α ⊗ₖ tp ρ β).submatrix (sp e) (sp e) = tp ρ ι := by
  rw [← tp_reindex ρ e, ← tp_sum α β ρ, Matrix.submatrix_submatrix]
  rfl

/-- The two-outcome POVM `{A, 1 - A}` of an effect. -/
def two {X : Type} [Fintype X] [DecidableEq X] (A : Matrix X X ℂ) (hA : IsEffect A) :
    POVM (Fin 2) X where
  op := ![A, 1 - A]
  psd i := by fin_cases i <;> simp [hA.1, hA.2]
  complete := by simp [Fin.sum_univ_two]

open Classical in
lemma two_prob {X : Type} [Fintype X] [DecidableEq X] (A : Matrix X X ℂ) (hA : IsEffect A)
    (σ : Matrix X X ℂ) (S : Fin 2 → Prop) :
    (two A hA).prob σ S = (if S 0 then (A * σ).trace.re else 0) +
      (if S 1 then ((1 - A) * σ).trace.re else 0) := by
  unfold POVM.prob
  rw [Finset.sum_filter, Fin.sum_univ_two]
  simp [two]

/-- Push the outcomes of a POVM forward along a function (coarse-graining). -/
def push {Ω Ω2 X : Type} [Fintype Ω] [Fintype Ω2] [DecidableEq Ω2] [Fintype X] [DecidableEq X]
    (P : POVM Ω X) (f : Ω → Ω2) : POVM Ω2 X where
  op j := ∑ ω ∈ Finset.univ.filter (fun ω => f ω = j), P.op ω
  psd j := Matrix.posSemidef_sum _ fun ω _ => P.psd ω
  complete := by rw [Finset.sum_fiberwise]; exact P.complete

lemma prob_push {Ω Ω2 X : Type} [Fintype Ω] [Fintype Ω2] [DecidableEq Ω2] [Fintype X]
    [DecidableEq X] (P : POVM Ω X) (f : Ω → Ω2) (σ : Matrix X X ℂ) (A : Ω2 → Prop) :
    (push P f).prob σ A = P.prob σ (fun ω => A (f ω)) := by
  classical
  unfold POVM.prob
  simp only [push, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
  rw [Finset.sum_filter, Finset.sum_filter]
  rw [← Finset.sum_fiberwise Finset.univ f
    (fun ω => if A (f ω) then ((P.op ω) * σ).trace.re else 0)]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hj
  · refine Finset.sum_congr rfl fun ω hω => ?_
    rw [(Finset.mem_filter.mp hω).2, if_pos hj]
  · symm
    refine Finset.sum_eq_zero fun ω hω => ?_
    rw [(Finset.mem_filter.mp hω).2, if_neg hj]

/-- Pad a test on `k` copies to `K ≥ k` copies (identity on the extra copies). -/
lemma pad {k K : ℕ} (hk : k ≤ K) (A : Matrix (Fin k → n) (Fin k → n) ℂ) (hA : IsEffect A) :
    ∃ A2 : Matrix (Fin K → n) (Fin K → n) ℂ, IsEffect A2 ∧
      ∀ ρ : Matrix n n ℂ, WildeQIT.IsDensityOperator ρ →
        (A2 * tp ρ (Fin K)).trace = (A * tp ρ (Fin k)).trace := by
  let e : Fin K ≃ Fin k ⊕ Fin (K - k) := (finCongr (by omega)).trans finSumFinEquiv.symm
  refine ⟨(A ⊗ₖ (1 : Matrix (Fin (K - k) → n) (Fin (K - k) → n) ℂ)).submatrix (sp e) (sp e),
    ⟨?_, ?_⟩, ?_⟩
  · exact (Matrix.posSemidef_submatrix_equiv (sp e)).mpr (hA.1.kronecker Matrix.PosSemidef.one)
  · have : (1 : Matrix (Fin K → n) (Fin K → n) ℂ) -
        (A ⊗ₖ (1 : Matrix (Fin (K - k) → n) (Fin (K - k) → n) ℂ)).submatrix (sp e) (sp e) =
        ((1 - A) ⊗ₖ (1 : Matrix (Fin (K - k) → n) (Fin (K - k) → n) ℂ)).submatrix
          (sp e) (sp e) := by
      have hk : (1 - A) ⊗ₖ (1 : Matrix (Fin (K - k) → n) (Fin (K - k) → n) ℂ) =
          (1 : Matrix (Fin k → n) (Fin k → n) ℂ) ⊗ₖ (1 : Matrix (Fin (K - k) → n) _ ℂ) -
            A ⊗ₖ (1 : Matrix (Fin (K - k) → n) (Fin (K - k) → n) ℂ) := by
        rw [eq_sub_iff_add_eq, ← Matrix.add_kronecker, sub_add_cancel]
      rw [hk, Matrix.one_kronecker_one]
      ext x y
      simp [Matrix.sub_apply, Matrix.submatrix_apply, Matrix.one_apply]
    rw [this]
    exact (Matrix.posSemidef_submatrix_equiv (sp e)).mpr (hA.2.kronecker Matrix.PosSemidef.one)
  · intro ρ hρ
    rw [← tp_sp ρ e, Matrix.submatrix_mul_equiv, trace_submatrix_equiv,
      ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker, Matrix.one_mul,
      (tp_density _ ρ hρ).2, mul_one]

/-- Binary search: from a uniform OR test (gap `g`, failure `dd`, `K` copies) for families of
size `≤ N`, an index search over `2^l ≤ 2N` effects on `l K` copies losing `l g` and `l dd`. -/
lemma search (N K : ℕ) (g dd : ℝ) (hg : 0 ≤ g) (hdd : 0 ≤ dd)
    (H : ∀ (m : ℕ) (G : Fin m → Matrix n n ℂ) (c : ℝ), 0 < m → m ≤ N →
      (∀ i, IsEffect (G i)) →
      ∃ A : Matrix (Fin K → n) (Fin K → n) ℂ, IsEffect A ∧ ∀ ρ : Matrix n n ℂ,
        WildeQIT.IsDensityOperator ρ →
        ((∃ i, c ≤ ((G i) * ρ).trace.re) → 1 - dd ≤ (A * tp ρ (Fin K)).trace.re) ∧
        ((∀ i, ((G i) * ρ).trace.re ≤ c - g) → (A * tp ρ (Fin K)).trace.re ≤ dd)) :
    ∀ l : ℕ, 2 ^ l ≤ 2 * N → ∀ (F : Fin (2 ^ l) → Matrix n n ℂ) (c : ℝ),
      (∀ i, IsEffect (F i)) →
      ∃ P : POVM (Fin (2 ^ l)) (Fin (l * K) → n), ∀ ρ : Matrix n n ℂ,
        WildeQIT.IsDensityOperator ρ → (∃ i, c ≤ ((F i) * ρ).trace.re) →
        1 - l * dd ≤ P.prob (tp ρ (Fin (l * K))) (fun j => c - l * g ≤ ((F j) * ρ).trace.re) := by
  intro l
  induction l with
  | zero =>
    intro _ F c _
    refine ⟨⟨fun _ => 1, fun _ => Matrix.PosSemidef.one, by simp⟩, fun ρ hρ ⟨i, hi⟩ => ?_⟩
    have hall : ∀ j : Fin (2 ^ 0), c - ((0 : ℕ) : ℝ) * g ≤ ((F j) * ρ).trace.re := fun j => by
      have : j = i := Fin.ext (by have := j.isLt; have := i.isLt; simp only [pow_zero] at *; omega)
      rw [this]; simpa using hi
    have hd := tp_density (Fin (0 * K)) ρ hρ
    calc 1 - ((0 : ℕ) : ℝ) * dd ≤ 1 := by simp
      _ = POVM.prob ⟨fun _ => 1, fun _ => Matrix.PosSemidef.one, by simp⟩
            (tp ρ (Fin (0 * K))) (fun (_ : Fin (2 ^ 0)) => True) := by
          rw [prob_univ, hd.2, Complex.one_re]
      _ ≤ _ := prob_mono _ _ hd.1 _ _ (fun j _ => hall j)
  | succ l ih =>
    intro h2 F c hF
    have hl : 2 ^ l ≤ N := by rw [pow_succ] at h2; omega
    have hl2 : 2 ^ l ≤ 2 * N := by omega
    let eo : Fin 2 × Fin (2 ^ l) ≃ Fin (2 ^ (l + 1)) :=
      finProdFinEquiv.trans (finCongr (by ring))
    let G : Fin 2 → Fin (2 ^ l) → Matrix n n ℂ := fun a b => F (eo (a, b))
    obtain ⟨A, hA, hAρ⟩ := H (2 ^ l) (G 0) c (by positivity) hl (fun b => hF _)
    have hQ : ∀ a : Fin 2, ∃ Q : POVM (Fin (2 ^ l)) (Fin (l * K) → n), ∀ ρ : Matrix n n ℂ,
        WildeQIT.IsDensityOperator ρ → (∃ i, c - g ≤ ((G a i) * ρ).trace.re) →
        1 - l * dd ≤ Q.prob (tp ρ (Fin (l * K)))
          (fun j => c - g - l * g ≤ ((G a j) * ρ).trace.re) :=
      fun a => ih hl2 (G a) (c - g) (fun b => hF _)
    choose Q hQ using hQ
    let es : Fin ((l + 1) * K) ≃ Fin K ⊕ Fin (l * K) :=
      (finCongr (by ring)).trans finSumFinEquiv.symm
    refine ⟨mapOut (comap (kron (two A hA) Q) (sp es)) eo, fun ρ hρ hex => ?_⟩
    rw [prob_mapOut, ← tp_sp ρ es, prob_comap]
    have hσ := tp_density (Fin K) ρ hρ
    have hτ := tp_density (Fin (l * K)) ρ hρ
    obtain ⟨i, hi⟩ := hex
    obtain ⟨⟨a, b⟩, rfl⟩ := eo.surjective i
    have hab : c ≤ ((G a b) * ρ).trace.re := hi
    let S : Fin 2 → Prop := fun a => ∃ b, c - g ≤ ((G a b) * ρ).trace.re
    have ha01 : a = 0 ∨ a = 1 := by fin_cases a <;> simp
    have h1 : 1 - dd ≤ (two A hA).prob (tp ρ (Fin K)) S := by
      rw [two_prob]
      have ht0 : 0 ≤ (A * tp ρ (Fin K)).trace.re := trace_mul_psd _ _ hA.1 hσ.1
      have ht1 : ((1 - A) * tp ρ (Fin K)).trace.re = 1 - (A * tp ρ (Fin K)).trace.re := by
        rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re, hσ.2,
          Complex.one_re]
      by_cases hS0 : S 0
      · by_cases hS1 : S 1
        · rw [if_pos hS0, if_pos hS1, ht1]; linarith
        · rw [if_pos hS0, if_neg hS1]
          rcases ha01 with ha | ha
          · subst ha
            linarith [(hAρ ρ hρ).1 ⟨b, hab⟩]
          · subst ha
            exact absurd ⟨b, by linarith⟩ hS1
      · have hlow : (A * tp ρ (Fin K)).trace.re ≤ dd := (hAρ ρ hρ).2 (fun b2 => by
          by_contra h; push Not at h; exact hS0 ⟨b2, h.le⟩)
        have hS1 : S 1 := by
          rcases ha01 with ha | ha
          · subst ha; exact absurd ⟨b, by linarith⟩ hS0
          · subst ha; exact ⟨b, by linarith⟩
        rw [if_neg hS0, if_pos hS1, ht1]; linarith
    have hk := kron_bound (two A hA) Q (tp ρ (Fin K)) (tp ρ (Fin (l * K))) hσ hτ S
      (fun a b => c - g - l * g ≤ ((G a b) * ρ).trace.re) dd (l * dd)
      (mul_nonneg (Nat.cast_nonneg _) hdd) h1 (fun a ha => hQ a ρ hρ ha)
    calc 1 - ((l + 1 : ℕ) : ℝ) * dd = 1 - dd - l * dd := by push_cast; ring
      _ ≤ _ := hk
      _ ≤ _ := by
        refine prob_mono _ _ (hσ.1.kronecker hτ.1) _ _ ?_
        rintro ⟨a2, b2⟩ ⟨_, h⟩
        simp only at h ⊢
        push_cast
        have : ((G a2 b2) * ρ).trace.re = ((F (eo (a2, b2))) * ρ).trace.re := rfl
        linarith

end ShadowTomography.UpperBound.L15

open ShadowTomography.UpperBound ShadowTomography.UpperBound.PovmKit
  ShadowTomography.UpperBound.L15 ShadowTomography.UpperBound.Leaves

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n : Type} [Fintype n] [DecidableEq n] (M : ℕ) (E : Fin M → Matrix n n ℂ) (c ε δ : ℝ),
        1 ≤ M → (∀ i, IsEffect (E i)) → 0 < ε → 0 < δ → δ ≤ 1 / 2 →
        ∃ k : ℕ, (k : ℝ) ≤ C * (Real.log M ^ 4 / ε ^ 2) *
            (Real.log (Real.log M) + Real.log (1 / δ)) ∧
          ∃ P : POVM (Fin M) (Fin k → n),
            ∀ ρ : Matrix n n ℂ, WildeQIT.IsDensityOperator ρ →
              (∃ i, c ≤ ((E i) * ρ).trace.re) →
                1 - δ ≤ P.prob (tensorPow ρ k) (fun j => c - ε ≤ ((E j) * ρ).trace.re) := by
  obtain ⟨C₁, hC₁, h14⟩ := ShadowTomography.UpperBound.lemma_14
  refine ⟨1000 * C₁, by positivity, ?_⟩
  intro n _ _ M E c ε δ hM hE hε hδ hδ2
  rcases Nat.lt_or_ge M 2 with hM2 | hM2
  · -- M = 1: no copies, output the only index.
    have hM1 : M = 1 := by omega
    subst hM1
    refine ⟨0, by simp, ⟨fun _ => 1, fun _ => Matrix.PosSemidef.one, by simp⟩,
      fun ρ hρ ⟨i, hi⟩ => ?_⟩
    have hall : ∀ j : Fin 1, c - ε ≤ (E j * ρ).trace.re := fun j => by
      rw [Subsingleton.elim j i]; linarith
    have hd := tp_density (Fin 0) ρ hρ
    calc 1 - δ ≤ 1 := by linarith
      _ = POVM.prob ⟨fun _ => 1, fun _ => Matrix.PosSemidef.one, by simp⟩
            (tp ρ (Fin 0)) (fun (_ : Fin 1) => True) := by
          rw [prob_univ, hd.2, Complex.one_re]
      _ ≤ _ := prob_mono _ _ hd.1 _ _ (fun j _ => hall j)
  -- M ≥ 2: pad to 2^L with L = ⌈log₂ M⌉ and binary-search.
  obtain ⟨L, hLdef⟩ : ∃ L, L = Nat.clog 2 M := ⟨_, rfl⟩
  have hML : M ≤ 2 ^ L := hLdef ▸ Nat.le_pow_clog (by norm_num) M
  have hL1 : 1 ≤ L := by
    by_contra h
    have h0 : L = 0 := by omega
    rw [h0] at hML; simp at hML; omega
  have hLlt : 2 ^ (L - 1) < M := by
    have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := M) (by omega)
    rw [← hLdef, Nat.pred_eq_sub_one] at this; exact this
  have hLpos : (0 : ℝ) < L := Nat.cast_pos.mpr (by omega)
  obtain ⟨g, hgdef⟩ : ∃ g : ℝ, g = ε / L := ⟨_, rfl⟩
  obtain ⟨dd, hdddef⟩ : ∃ dd : ℝ, dd = δ / L := ⟨_, rfl⟩
  have hg : 0 < g := by rw [hgdef]; positivity
  have hdd0 : 0 < dd := by rw [hdddef]; positivity
  have hdd1 : dd < 1 := by
    rw [hdddef, div_lt_one hLpos]
    have : (1 : ℝ) ≤ L := by exact_mod_cast hL1
    linarith
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ,
      K = ⌊C₁ * (Real.log (1 / dd) / g ^ 2) * Real.log ((2 ^ L : ℕ) : ℝ)⌋₊ := ⟨_, rfl⟩
  have h2L : 2 ≤ 2 ^ L := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL1
  have H : ∀ (m : ℕ) (G : Fin m → Matrix n n ℂ) (c : ℝ), 0 < m → m ≤ 2 ^ L →
      (∀ i, IsEffect (G i)) →
      ∃ A : Matrix (Fin K → n) (Fin K → n) ℂ, IsEffect A ∧ ∀ ρ : Matrix n n ℂ,
        WildeQIT.IsDensityOperator ρ →
        ((∃ i, c ≤ ((G i) * ρ).trace.re) → 1 - dd ≤ (A * tp ρ (Fin K)).trace.re) ∧
        ((∀ i, ((G i) * ρ).trace.re ≤ c - g) → (A * tp ρ (Fin K)).trace.re ≤ dd) := by
    intro m G c2 hm hmN hG
    let G2 : Fin (2 ^ L) → Matrix n n ℂ := fun i => G ⟨min i.val (m - 1), by omega⟩
    obtain ⟨k, hk, A, hA, hAρ⟩ := h14 (2 ^ L) G2 c2 g dd h2L (fun i => hG _) hg hdd0 hdd1
    have hkK : k ≤ K := by rw [hKdef]; exact Nat.le_floor hk
    obtain ⟨A2, hA2, htr⟩ := pad hkK A hA
    refine ⟨A2, hA2, fun ρ hρ => ⟨fun ⟨i, hi⟩ => ?_, fun hall => ?_⟩⟩
    · rw [htr ρ hρ]
      have hi2 := i.isLt
      refine (hAρ ρ hρ).1 ⟨⟨i.val, by omega⟩, ?_⟩
      have : (⟨min i.val (m - 1), by omega⟩ : Fin m) = i := Fin.ext (by simp only; omega)
      show c2 ≤ ((G ⟨min i.val (m - 1), _⟩) * ρ).trace.re
      rw [this]; exact hi
    · rw [htr ρ hρ]
      exact (hAρ ρ hρ).2 (fun i => hall _)
  have hS := search (2 ^ L) K g dd hg.le hdd0.le H L (by omega)
  let f : Fin (2 ^ L) → Fin M := fun j => ⟨min j.val (M - 1), by omega⟩
  obtain ⟨P, hP⟩ := hS (fun j => E (f j)) c (fun j => hE _)
  have e1 : (L : ℝ) * dd = δ := by rw [hdddef]; field_simp
  have e2 : (L : ℝ) * g = ε := by rw [hgdef]; field_simp
  refine ⟨L * K, ?_, push P f, fun ρ hρ ⟨i, hi⟩ => ?_⟩
  swap
  · rw [prob_push]
    have hi2 := i.isLt
    have hfi : f ⟨i.val, by omega⟩ = i := Fin.ext (by simp only [f]; omega)
    have := hP ρ hρ ⟨⟨i.val, by omega⟩, by rw [hfi]; exact hi⟩
    rw [e1, e2] at this
    exact this
  -- the sample bound
  have hl2 := Real.log_two_gt_d9
  have hl2u := Real.log_two_lt_d9
  have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM2
  have hlM : Real.log 2 ≤ Real.log M := Real.log_le_log (by norm_num) hMr
  have hlMpos : 0 < Real.log M := by linarith
  have hL3 : (L : ℝ) ≤ 3 * Real.log M := by
    have h1 : ((2 : ℝ) ^ (L - 1)) < M := by exact_mod_cast hLlt
    have h2 : ((L - 1 : ℕ) : ℝ) * Real.log 2 < Real.log M := by
      rw [← Real.log_pow]; exact Real.log_lt_log (by positivity) h1
    have h3 : ((L - 1 : ℕ) : ℝ) = L - 1 := by rw [Nat.cast_sub hL1]; simp
    rw [h3] at h2
    nlinarith
  have hδ1 : (1 : ℝ) ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
  have hlogδ : Real.log 2 ≤ Real.log (1 / δ) :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hδ]; linarith)
  have hll : Real.log (Real.log 2) ≤ Real.log (Real.log M) :=
    Real.log_le_log (by linarith) hlM
  have hll2 : 1 - (Real.log 2)⁻¹ ≤ Real.log (Real.log 2) :=
    Real.one_sub_inv_le_log_of_pos (by linarith)
  have hinv : (Real.log 2)⁻¹ ≤ 1.443 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; norm_num at hl2 ⊢; linarith
  have hs : 1 / 5 ≤ Real.log (Real.log M) + Real.log (1 / δ) := by linarith
  have hlogL : Real.log L ≤ 2 + Real.log (Real.log M) := by
    have := Real.log_le_log hLpos hL3
    rw [Real.log_mul (by norm_num) hlMpos.ne'] at this
    have h3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
    linarith
  have hX0 : 0 ≤ Real.log L + Real.log (1 / δ) :=
    add_nonneg (Real.log_nonneg (by exact_mod_cast hL1)) (Real.log_nonneg hδ1)
  have hX : Real.log L + Real.log (1 / δ) ≤ 11 * (Real.log (Real.log M) + Real.log (1 / δ)) := by
    linarith
  have hlogdd : Real.log (1 / dd) = Real.log L + Real.log (1 / δ) := by
    rw [← Real.log_mul hLpos.ne' (by positivity)]
    congr 1
    rw [hdddef]; field_simp
  have hlog2L : Real.log ((2 ^ L : ℕ) : ℝ) = L * Real.log 2 := by
    push_cast; rw [Real.log_pow]
  have hKnn : 0 ≤ C₁ * (Real.log (1 / dd) / g ^ 2) * Real.log ((2 ^ L : ℕ) : ℝ) := by
    rw [hlogdd, hlog2L]
    exact mul_nonneg (mul_nonneg hC₁.le (div_nonneg hX0 (by positivity)))
      (mul_nonneg hLpos.le (by linarith))
  have hKle : (K : ℝ) ≤ C₁ * (Real.log (1 / dd) / g ^ 2) * Real.log ((2 ^ L : ℕ) : ℝ) := by
    rw [hKdef]; exact Nat.floor_le hKnn
  rw [hlogdd, hlog2L, hgdef] at hKle
  have hs0 : 0 ≤ Real.log (Real.log M) + Real.log (1 / δ) := by linarith
  push_cast
  calc (L : ℝ) * K ≤ L * (C₁ * ((Real.log L + Real.log (1 / δ)) / (ε / L) ^ 2) *
          (L * Real.log 2)) := mul_le_mul_of_nonneg_left hKle hLpos.le
    _ = C₁ * Real.log 2 * L ^ 4 * (Real.log L + Real.log (1 / δ)) / ε ^ 2 := by
        field_simp
    _ ≤ C₁ * 1 * (3 * Real.log M) ^ 4 *
          (11 * (Real.log (Real.log M) + Real.log (1 / δ))) / ε ^ 2 := by
        gcongr <;> first | linarith | positivity
    _ = 891 * C₁ * (Real.log M ^ 4 / ε ^ 2) * (Real.log (Real.log M) + Real.log (1 / δ)) := by
        ring
    _ ≤ 1000 * C₁ * (Real.log M ^ 4 / ε ^ 2) * (Real.log (Real.log M) + Real.log (1 / δ)) := by
        have h0 : 0 ≤ C₁ * (Real.log M ^ 4 / ε ^ 2) *
            (Real.log (Real.log M) + Real.log (1 / δ)) :=
          mul_nonneg (by positivity) hs0
        nlinarith
