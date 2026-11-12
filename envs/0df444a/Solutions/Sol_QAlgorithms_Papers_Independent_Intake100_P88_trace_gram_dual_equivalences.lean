-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P88.trace_gram_dual_equivalences
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T20:51:27.101173+00:00
-- url     : https://prove2.me/submissions/9ec23b65-181e-4c32-82cd-565826727c3d

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P88

attribute [local instance] Classical.propDecidable

open scoped BigOperators Matrix

open QAlgorithms.Papers.Independent.Intake100.P88 in
theorem solution (F A I : Type*) [Field F] [Ring A] [Algebra F A]
    [FiniteDimensional F A] [Fintype I] [DecidableEq I]
    (t : A →ₗ[F] F) (_htrace : ∀ a b : A, t (a * b) = t (b * a)) (b : Module.Basis I F A) :
    (TraceNondegenerate (fun a => t a) ↔ (traceGram t b).det ≠ 0) ∧
    ((traceGram t b).det ≠ 0 ↔ ∃ c : Module.Basis I F A, IsTraceDualBasis t b c) := by
  let B : A →ₗ[F] A →ₗ[F] F := (LinearMap.mul F A).compr₂ t
  have hB : ∀ x y : A, B x y = t (x * y) := by
    intro x y
    simp [B]
  have hG : traceGram t b = LinearMap.toMatrix₂ b b B := by
    ext i j
    show t (b i * b j) = _
    rw [LinearMap.toMatrix₂_apply, hB]
  have hpart1 : TraceNondegenerate (fun a => t a) ↔ (traceGram t b).det ≠ 0 := by
    rw [hG, ← LinearMap.separatingLeft_iff_det_ne_zero b]
    constructor
    · intro hnd x hx
      by_contra hne
      obtain ⟨a, ha⟩ := hnd x hne
      apply ha
      have h := hx a
      rw [hB] at h
      exact h
    · intro hsep x hx
      by_contra hall
      push_neg at hall
      exact hx (hsep x (fun y => by rw [hB]; exact hall y))
  refine ⟨hpart1, ?_⟩
  constructor
  · intro hdet
    have hdet' : (LinearMap.toMatrix₂ b b B).det ≠ 0 := by
      rw [← hG]
      exact hdet
    have hnd : B.Nondegenerate := (LinearMap.nondegenerate_iff_det_ne_zero b).mpr hdet'
    have hsym : LinearMap.BilinForm.IsSymm B := ⟨fun x y => by rw [hB, hB, _htrace]⟩
    refine ⟨LinearMap.BilinForm.dualBasis B hnd b, fun i j => ?_⟩
    rw [← hB]
    exact LinearMap.BilinForm.apply_dualBasis_right hnd hsym b i j
  · rintro ⟨c, hc⟩
    rw [← hpart1]
    intro x hx
    by_contra hall
    push_neg at hall
    apply hx
    have hrep : ∀ j, b.repr x j = 0 := by
      intro j
      have h := hall (c j)
      have hc' : ∀ i, t (b i * c j) = if i = j then 1 else 0 := fun i => hc i j
      rw [← b.sum_repr x] at h
      simp only [Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, smul_eq_mul, hc', mul_ite,
        mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
      exact h
    have hz : b.repr x = 0 := Finsupp.ext hrep
    exact b.repr.map_eq_zero_iff.mp hz
