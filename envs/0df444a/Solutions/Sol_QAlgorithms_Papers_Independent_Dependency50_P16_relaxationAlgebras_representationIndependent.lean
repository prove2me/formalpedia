-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P16.relaxationAlgebras_representationIndependent
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:31:03.178996+00:00
-- url     : https://prove2.me/submissions/68eeff05-f697-440a-a8e8-ac9046c0386d

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16

-- ===== RI =====

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace X4RI

open Matrix QAlgorithms.Papers.Independent.Dependency50.P16

variable {n : ℕ}

abbrev M (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

lemma f_expand (f : Module.Dual ℂ (M n)) (X : M n) :
    f X = ∑ i, ∑ j, f (single i j 1) * X i j := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show single i j (X i j) = X i j • single i j (1 : ℂ) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul, mul_comm]

/-- Choi-type sesquilinear form of a superoperator. -/
def B (Φ : Module.End ℂ (M n)) (f g : Module.Dual ℂ (M n)) : ℂ :=
  ∑ i, ∑ j, ∑ m, ∑ l, f (single i j 1) * conj (g (single m l 1)) * Φ (single j l 1) i m

lemma B_sub (Φ Ψ : Module.End ℂ (M n)) f g : B (Φ - Ψ) f g = B Φ f g - B Ψ f g := by
  simp only [B, LinearMap.sub_apply, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma B_sum {r : ℕ} (Φ : Fin r → Module.End ℂ (M n)) f g :
    B (∑ k, Φ k) f g = ∑ k, B (Φ k) f g := by
  simp only [B, LinearMap.sum_apply, Matrix.sum_apply, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_comm]

lemma entry (A C : M n) (i j l m : Fin n) : ((A * single j l (1 : ℂ) * C : M n)) i m = A i j * C l m := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and]

lemma B_sandwich (A C : M n) f g : B (sandwich A C) f g = f A * conj (g Cᴴ) := by
  have e : f A * conj (g Cᴴ) = ∑ i, ∑ j, ∑ m, ∑ l,
      f (single i j 1) * conj (g (single m l 1)) * (A i j * C l m) := by
    rw [f_expand f A, f_expand g Cᴴ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [map_mul, conjTranspose_apply, RCLike.star_def, Complex.conj_conj]
    ring
  rw [e]
  simp only [B, sandwich, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply,
    LinearMap.mulLeft_apply, ← mul_assoc, entry]

lemma B_gen {r : ℕ} (K : M n) (V : Fin r → M n) f g :
    B (cpGenerator K V) f g =
      ∑ k, f (V k) * conj (g (V k)) - f K * conj (g 1) - f 1 * conj (g K) := by
  have h1 : (LinearMap.mulLeft ℂ K : Module.End ℂ (M n)) = sandwich K 1 := by
    ext X : 1; simp [sandwich]
  have h2 : (LinearMap.mulRight ℂ Kᴴ : Module.End ℂ (M n)) = sandwich 1 Kᴴ := by
    ext X : 1; simp [sandwich]
  rw [cpGenerator, h1, h2, B_sub, B_sub, B_sum]
  simp only [B_sandwich, conjTranspose_conjTranspose, conjTranspose_one]

/-- The span of `1` and the jumps. -/
def S {r : ℕ} (V : Fin r → M n) : Submodule ℂ (M n) :=
  Submodule.span ℂ (insert 1 (Set.range V))

lemma mem_S {r : ℕ} (V : Fin r → M n) (Y : M n) :
    Y ∈ S V ↔ ∀ f : Module.Dual ℂ (M n), f 1 = 0 → (∀ k, f (V k) = 0) → f Y = 0 := by
  constructor
  · intro hY f h1 hV
    have : S V ≤ LinearMap.ker f := by
      rw [S, Submodule.span_le]
      rintro x (rfl | ⟨k, rfl⟩)
      · exact h1
      · exact hV k
    exact this hY
  · intro H
    by_contra hY
    obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hY inferInstance
    refine hf (H f ?_ ?_)
    · have : f 1 ∈ (S V).map f := Submodule.mem_map_of_mem (Submodule.subset_span (Set.mem_insert _ _))
      rw [hmap] at this; exact this
    · intro k
      have : f (V k) ∈ (S V).map f :=
        Submodule.mem_map_of_mem (Submodule.subset_span (Set.mem_insert_of_mem _ ⟨k, rfl⟩))
      rw [hmap] at this; exact this

lemma vanish_iff {r : ℕ} (K : M n) (V : Fin r → M n) (f : Module.Dual ℂ (M n)) (h1 : f 1 = 0) :
    (∀ k, f (V k) = 0) ↔ B (cpGenerator K V) f f = 0 := by
  rw [B_gen, h1]
  simp only [zero_mul, sub_zero, map_zero, mul_zero, Complex.mul_conj]
  rw [← Complex.ofReal_sum, Complex.ofReal_eq_zero,
    Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Complex.normSq_nonneg _)]
  simp

lemma S_eq {r s : ℕ} (K K' : M n) (V : Fin r → M n) (W : Fin s → M n)
    (h : cpGenerator K V = cpGenerator K' W) : S V = S W := by
  ext Y
  rw [mem_S, mem_S]
  refine forall_congr' fun f => forall_congr' fun h1 => ?_
  rw [vanish_iff K V f h1, vanish_iff K' W f h1, h]

lemma K_mem {r s : ℕ} (hn : n ≠ 0) (K K' : M n) (V : Fin r → M n) (W : Fin s → M n)
    (h : cpGenerator K V = cpGenerator K' W) : K' - K ∈ S V := by
  rw [mem_S]
  intro f h1 hV
  have hW : ∀ l, f (W l) = 0 := by
    intro l
    have hl : W l ∈ S V := by
      rw [S_eq K K' V W h]; exact Submodule.subset_span (Set.mem_insert_of_mem _ ⟨l, rfl⟩)
    exact (mem_S V _).1 hl f h1 hV
  let t : Module.Dual ℂ (M n) := Matrix.traceLinearMap (Fin n) ℂ ℂ
  have e := congrArg (fun Φ => B Φ f t) h
  simp only [B_gen, hV, hW, h1, zero_mul, Finset.sum_const_zero, zero_sub, sub_zero] at e
  have ht : t 1 = n := by simp [t]
  rw [ht, Complex.conj_natCast, neg_inj] at e
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [map_sub, mul_right_cancel₀ hn' e, sub_self]

lemma S_le {r : ℕ} (K : M n) (V : Fin r → M n) :
    S V ≤ Subalgebra.toSubmodule (Algebra.adjoin ℂ (insert K (Set.range V))) := by
  rw [S, Submodule.span_le]
  rintro x (rfl | ⟨k, rfl⟩)
  · exact Subalgebra.one_mem _
  · exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨k, rfl⟩)

lemma S_le' {r : ℕ} (V : Fin r → M n) :
    S V ≤ Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range V)) := by
  rw [S, Submodule.span_le]
  rintro x (rfl | ⟨k, rfl⟩)
  · exact Subalgebra.one_mem _
  · exact Algebra.subset_adjoin ⟨k, rfl⟩

lemma rel_le {r s : ℕ} (K K' : M n) (V : Fin r → M n) (W : Fin s → M n)
    (h : cpGenerator K V = cpGenerator K' W) :
    relaxationAlgebra W ≤ relaxationAlgebra V := by
  rw [relaxationAlgebra, relaxationAlgebra, Algebra.adjoin_le_iff]
  rintro x ⟨l, rfl⟩
  have hl : W l ∈ S V := by
    rw [S_eq K K' V W h]; exact Submodule.subset_span (Set.mem_insert_of_mem _ ⟨l, rfl⟩)
  exact S_le' V hl

lemma ext_le {r s : ℕ} (hn : n ≠ 0) (K K' : M n) (V : Fin r → M n) (W : Fin s → M n)
    (h : cpGenerator K V = cpGenerator K' W) :
    extendedAlgebra K' W ≤ extendedAlgebra K V := by
  rw [extendedAlgebra, extendedAlgebra, Algebra.adjoin_le_iff]
  rintro x (rfl | ⟨l, rfl⟩)
  · have hk := S_le K V (K_mem hn K x V W h)
    have hK : K ∈ Algebra.adjoin ℂ (insert K (Set.range V)) :=
      Algebra.subset_adjoin (Set.mem_insert _ _)
    have := Subalgebra.add_mem _ hk hK
    simpa using this
  · have hl : W l ∈ S V := by
      rw [S_eq K K' V W h]; exact Submodule.subset_span (Set.mem_insert_of_mem _ ⟨l, rfl⟩)
    exact S_le K V hl

theorem main {r s : ℕ} (hn : 2 ≤ n)
    (K Knew : M n) (V : Fin r → M n) (W : Fin s → M n)
    (h : cpGenerator K V = cpGenerator Knew W) :
    relaxationAlgebra V = relaxationAlgebra W ∧ extendedAlgebra K V = extendedAlgebra Knew W := by
  have hn0 : n ≠ 0 := by omega
  exact ⟨le_antisymm (rel_le Knew K W V h.symm) (rel_le K Knew V W h),
    le_antisymm (ext_le hn0 Knew K W V h.symm) (ext_le hn0 K Knew V W h)⟩

end X4RI

-- ===== RISol =====

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator

open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing

namespace QAlgorithms.Papers.Independent.Dependency50.P16

local notation "Mat" => fun n : ℕ => Matrix (Fin n) (Fin n) ℂ

theorem _root_.solution {n r s : ℕ} (hn : 2 ≤ n)
    (K Knew : Mat n) (V : Fin r → Mat n) (W : Fin s → Mat n)
    (h : cpGenerator K V = cpGenerator Knew W) :
    relaxationAlgebra V = relaxationAlgebra W ∧ extendedAlgebra K V = extendedAlgebra Knew W :=
  X4RI.main hn K Knew V W h

end QAlgorithms.Papers.Independent.Dependency50.P16

end
