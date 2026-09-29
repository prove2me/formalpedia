-- Prove2me | solution 1 for Representation.exists_map_eq_conj_and_span_range_eq_top_of_charpoly_coeff_mem_range_of_finite_fin_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/2ee9bb86-cc29-5c01-83ab-63936e4e31ab

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.LittleWedderburn
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Representation_exists_map_eq_conj_and_span_range_eq_top_of_charpoly_coeff_mem_range_of_finite_fin_two

set_option autoImplicit false

namespace FiniteDescent

open Matrix

variable {F : Type} [Field F]

private theorem trace_mul_E11 (x : Matrix (Fin 2) (Fin 2) F) : (x * !![1, 0; 0, 0]).trace = x 0 0 := by
  simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

private theorem trace_mul_E12 (x : Matrix (Fin 2) (Fin 2) F) (c : F) : (x * !![0, c; 0, 0]).trace = x 1 0 * c := by
  simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

private theorem trace_mul_E21 (x : Matrix (Fin 2) (Fin 2) F) (c : F) : (x * !![0, 0; c, 0]).trace = x 0 1 * c := by
  simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

private theorem E22_mul_mul_E11 (x : Matrix (Fin 2) (Fin 2) F) :
    (1 - !![1, 0; 0, 0]) * x * !![1, 0; 0, 0] = !![0, 0; x 1 0, 0] := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp

private theorem E11_mul_mul_E22 (x : Matrix (Fin 2) (Fin 2) F) :
    !![1, 0; 0, 0] * x * (1 - !![1, 0; 0, 0]) = !![0, x 0 1; 0, 0] := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp

private theorem trace_E12_mul_E21 (b c : F) : (!![0, b; 0, 0] * !![0, 0; c, 0] : Matrix (Fin 2) (Fin 2) F).trace = b * c := by
  simp [Matrix.trace_fin_two]

private theorem mul_trace_smul_one_sub (x : Matrix (Fin 2) (Fin 2) F) :
    x * (x.trace • (1 : Matrix (Fin 2) (Fin 2) F) - x) = x.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

private theorem trace_smul_one_sub_mul (x : Matrix (Fin 2) (Fin 2) F) :
    (x.trace • (1 : Matrix (Fin 2) (Fin 2) F) - x) * x = x.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

private theorem mul_self_eq_of_det_eq_zero {x : Matrix (Fin 2) (Fin 2) F} (hx : x.det = 0) : x * x = x.trace • x := by
  have h := mul_trace_smul_one_sub x
  rw [hx, zero_smul, Matrix.mul_sub, sub_eq_zero, Matrix.mul_smul, Matrix.mul_one] at h
  exact h.symm

private theorem eq_zero_of_forall_trace_mul (x : Matrix (Fin 2) (Fin 2) F)
    (h : ∀ y : Matrix (Fin 2) (Fin 2) F, (x * y).trace = 0) : x = 0 := by
  ext i j
  have := h (Matrix.single j i 1)
  fin_cases i <;> fin_cases j <;>
    simpa [Matrix.trace, Matrix.mul_apply, Matrix.single, Fin.sum_univ_two, Matrix.of_apply] using this

private theorem diag_inv_mul_mul_diag (y : Matrix (Fin 2) (Fin 2) F) {c : F} (hc : c ≠ 0) :
    !![(1 : F), 0; 0, c⁻¹] * y * !![1, 0; 0, c] = !![y 0 0, y 0 1 * c; c⁻¹ * y 1 0, y 1 1] := by
  have h11 : c⁻¹ * y 1 1 * c = y 1 1 := by field_simp
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [h11]

private theorem forall_of_span_eq_top {ι : Type*} (v : ι → Matrix (Fin 2) (Fin 2) F)
    (hspan : Submodule.span F (Set.range v) = ⊤) (f : Matrix (Fin 2) (Fin 2) F →ₗ[F] F)
    (hf : ∀ i, f (v i) = 0) (y : Matrix (Fin 2) (Fin 2) F) : f y = 0 := by
  have hy : y ∈ Submodule.span F (Set.range v) := by rw [hspan]; exact Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hf i
  | zero => exact map_zero f
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

private def trMul (x : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2) (Fin 2) F →ₗ[F] F where
  toFun y := (x * y).trace
  map_add' y z := by rw [Matrix.mul_add, Matrix.trace_add]
  map_smul' c y := by rw [Matrix.mul_smul, Matrix.trace_smul, RingHom.id_apply]

@[scoped simp] private theorem trMul_apply (x y : Matrix (Fin 2) (Fin 2) F) : trMul x y = (x * y).trace := rfl

private def entryLM (i j : Fin 2) : Matrix (Fin 2) (Fin 2) F →ₗ[F] F where
  toFun y := y i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[scoped simp] private theorem entryLM_apply (i j : Fin 2) (y : Matrix (Fin 2) (Fin 2) F) : entryLM i j y = y i j := rfl

variable (𝕜 : Subfield F) {G : Type*} [Group G] (ρ : G →* Matrix (Fin 2) (Fin 2) F)

private abbrev alg : Subalgebra 𝕜 (Matrix (Fin 2) (Fin 2) F) := Algebra.adjoin 𝕜 (Set.range ρ)

private theorem closure_range_eq : (Submonoid.closure (Set.range ρ) : Set (Matrix (Fin 2) (Fin 2) F)) = Set.range ρ := by
  have : Submonoid.closure (Set.range ρ) = MonoidHom.mrange ρ := by
    apply le_antisymm
    · rw [Submonoid.closure_le]; rintro _ ⟨g, rfl⟩; exact ⟨g, rfl⟩
    · rintro _ ⟨g, rfl⟩; exact Submonoid.subset_closure ⟨g, rfl⟩
  rw [this]; rfl

private theorem alg_toSubmodule : (alg 𝕜 ρ).toSubmodule = Submodule.span 𝕜 (Set.range ρ) := by
  rw [alg, Algebra.adjoin_eq_span, closure_range_eq]

private theorem mem_alg_iff (x : Matrix (Fin 2) (Fin 2) F) : x ∈ alg 𝕜 ρ ↔ x ∈ Submodule.span 𝕜 (Set.range ρ) := by
  rw [← Subalgebra.mem_toSubmodule, alg_toSubmodule]

variable {𝕜 ρ}

private theorem trace_mem (htr : ∀ g, (ρ g).trace ∈ 𝕜) {x : Matrix (Fin 2) (Fin 2) F} (hx : x ∈ alg 𝕜 ρ) : x.trace ∈ 𝕜 := by
  rw [mem_alg_iff] at hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨g, rfl⟩ := hx; exact htr g
  | zero => rw [Matrix.trace_zero]; exact zero_mem 𝕜
  | add x y _ _ hx hy => rw [Matrix.trace_add]; exact add_mem hx hy
  | smul c x _ hx => rw [Matrix.trace_smul]; exact mul_mem c.2 hx

private theorem det_add_fin_two (x y : Matrix (Fin 2) (Fin 2) F) :
    (x + y).det = x.det + y.det + x.trace * y.trace - (x * y).trace := by
  simp only [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem det_mem (hdt : ∀ g, (ρ g).det ∈ 𝕜) (htr : ∀ g, (ρ g).trace ∈ 𝕜) {x : Matrix (Fin 2) (Fin 2) F}
    (hx : x ∈ alg 𝕜 ρ) : x.det ∈ 𝕜 := by
  rw [mem_alg_iff] at hx
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨g, rfl⟩ := hy; exact hdt g
  | zero => simp only [Matrix.det_fin_two, Matrix.zero_apply, mul_zero, sub_zero]; exact zero_mem 𝕜
  | add y z hy hz hdy hdz =>
    have hya : y ∈ alg 𝕜 ρ := (mem_alg_iff 𝕜 ρ y).2 hy
    have hza : z ∈ alg 𝕜 ρ := (mem_alg_iff 𝕜 ρ z).2 hz
    rw [det_add_fin_two]
    exact sub_mem (add_mem (add_mem hdy hdz) (mul_mem (trace_mem htr hya) (trace_mem htr hza)))
      (trace_mem htr (mul_mem hya hza))
  | smul c y _ hdy =>
    rw [show c • y = (c : F) • y from rfl, Matrix.det_smul, Fintype.card_fin]
    exact mul_mem (pow_mem c.2 2) hdy

private theorem smul_mem_alg {c : F} (hc : c ∈ 𝕜) {x : Matrix (Fin 2) (Fin 2) F} (hx : x ∈ alg 𝕜 ρ) : c • x ∈ alg 𝕜 ρ := by
  have : c • x = (⟨c, hc⟩ : 𝕜) • x := rfl
  rw [this]; exact Subalgebra.smul_mem _ hx _

private theorem isUnit_of_det_ne_zero (hdt : ∀ g, (ρ g).det ∈ 𝕜) (htr : ∀ g, (ρ g).trace ∈ 𝕜) (a : alg 𝕜 ρ)
    (ha : (a : Matrix (Fin 2) (Fin 2) F).det ≠ 0) : IsUnit a := by
  set x : Matrix (Fin 2) (Fin 2) F := (a : Matrix (Fin 2) (Fin 2) F) with hxdef
  have hmem : x.det⁻¹ • (x.trace • (1 : Matrix (Fin 2) (Fin 2) F) - x) ∈ alg 𝕜 ρ := by
    refine smul_mem_alg (inv_mem (det_mem hdt htr a.2)) (sub_mem (smul_mem_alg (trace_mem htr a.2) (one_mem _)) a.2)
  refine ⟨⟨a, ⟨_, hmem⟩, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext
    change x * (x.det⁻¹ • (x.trace • (1 : Matrix (Fin 2) (Fin 2) F) - x)) = 1
    rw [Matrix.mul_smul, mul_trace_smul_one_sub, smul_smul, inv_mul_cancel₀ ha, one_smul]
  · apply Subtype.ext
    change (x.det⁻¹ • (x.trace • (1 : Matrix (Fin 2) (Fin 2) F) - x)) * x = 1
    rw [Matrix.smul_mul, trace_smul_one_sub_mul, smul_smul, inv_mul_cancel₀ ha, one_smul]

private theorem finite_alg [Finite 𝕜] (hfin : (Set.range ρ).Finite) : Finite (alg 𝕜 ρ) := by
  haveI : Module.Finite 𝕜 (Submodule.span 𝕜 (Set.range ρ)) := Module.Finite.span_of_finite 𝕜 hfin
  haveI : Finite (Submodule.span 𝕜 (Set.range ρ)) := Module.finite_of_finite 𝕜
  refine Finite.of_injective (fun a : alg 𝕜 ρ => (⟨a.1, (mem_alg_iff 𝕜 ρ a.1).1 a.2⟩ : Submodule.span 𝕜 (Set.range ρ))) ?_
  intro a b h
  have h' := congrArg (fun z : Submodule.span 𝕜 (Set.range ρ) => (z : Matrix (Fin 2) (Fin 2) F)) h
  exact Subtype.ext h'

private theorem exists_not_commute (hspan : Submodule.span F (Set.range ρ) = ⊤) :
    ∃ g h : G, ρ g * ρ h ≠ ρ h * ρ g := by
  by_contra hall
  push Not at hall
  have hc : ∀ x y : Matrix (Fin 2) (Fin 2) F, Commute x y := by
    intro x y
    have hx : x ∈ Submodule.span F (Set.range ρ) := by rw [hspan]; exact Submodule.mem_top
    have hy : y ∈ Submodule.span F (Set.range ρ) := by rw [hspan]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy => obtain ⟨h, rfl⟩ := hy; exact hall g h
      | zero => exact Commute.zero_right _
      | add y z _ _ hy hz => exact hy.add_right hz
      | smul c y _ hy => exact hy.smul_right c
    | zero => exact Commute.zero_left _
    | add x z _ _ hx hz => exact hx.add_left hz
    | smul c x _ hx => exact hx.smul_left c
  have := hc !![0, 1; 0, 0] !![0, 0; 1, 0]
  have h00 := congrFun (congrFun this.eq 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00

private theorem exists_singular [Finite 𝕜] (hdt : ∀ g, (ρ g).det ∈ 𝕜) (hfin : (Set.range ρ).Finite)
    (hspan : Submodule.span F (Set.range ρ) = ⊤) (htr : ∀ g, (ρ g).trace ∈ 𝕜) :
    ∃ a ∈ alg 𝕜 ρ, a ≠ 0 ∧ a.det = 0 := by
  by_contra hnone
  push Not at hnone
  haveI := finite_alg (𝕜 := 𝕜) (ρ := ρ) hfin
  have hu : ∀ a : alg 𝕜 ρ, IsUnit a ∨ a = 0 := by
    intro a
    by_cases ha : (a : Matrix (Fin 2) (Fin 2) F) = 0
    · exact Or.inr (Subtype.ext ha)
    · exact Or.inl (isUnit_of_det_ne_zero hdt htr a (hnone a a.2 ha))
  letI : DivisionRing (alg 𝕜 ρ) := DivisionRing.ofIsUnitOrEqZero hu
  letI : Field (alg 𝕜 ρ) := littleWedderburn (alg 𝕜 ρ)
  obtain ⟨g, h, hgh⟩ := exists_not_commute (ρ := ρ) hspan
  apply hgh
  have hg : ρ g ∈ alg 𝕜 ρ := Algebra.subset_adjoin ⟨g, rfl⟩
  have hh : ρ h ∈ alg 𝕜 ρ := Algebra.subset_adjoin ⟨h, rfl⟩
  have := mul_comm (⟨ρ g, hg⟩ : alg 𝕜 ρ) ⟨ρ h, hh⟩
  exact congrArg Subtype.val this

private theorem exists_idempotent [Finite 𝕜] (hdt : ∀ g, (ρ g).det ∈ 𝕜) (hfin : (Set.range ρ).Finite)
    (hspan : Submodule.span F (Set.range ρ) = ⊤) (htr : ∀ g, (ρ g).trace ∈ 𝕜) :
    ∃ e ∈ alg 𝕜 ρ, e * e = e ∧ e.trace = 1 := by

  obtain ⟨a, ha, ha0, hadet⟩ := exists_singular (𝕜 := 𝕜) hdt hfin hspan htr
  have : ∃ b ∈ alg 𝕜 ρ, b.det = 0 ∧ b.trace ≠ 0 := by
    by_cases hat : a.trace = 0
    · have : ∃ g, (a * ρ g).trace ≠ 0 := by
        by_contra hall
        push Not at hall
        apply ha0
        apply eq_zero_of_forall_trace_mul
        intro y
        exact forall_of_span_eq_top ρ hspan (trMul a) hall y
      obtain ⟨g, hg⟩ := this
      refine ⟨a * ρ g, mul_mem ha (Algebra.subset_adjoin ⟨g, rfl⟩), ?_, hg⟩
      rw [Matrix.det_mul, hadet, zero_mul]
    · exact ⟨a, ha, hadet, hat⟩
  obtain ⟨b, hb, hbdet, hbt⟩ := this
  refine ⟨b.trace⁻¹ • b, smul_mem_alg (inv_mem (trace_mem htr hb)) hb, ?_, ?_⟩
  · rw [Matrix.smul_mul, Matrix.mul_smul, mul_self_eq_of_det_eq_zero hbdet, smul_smul, smul_smul, mul_assoc,
      inv_mul_cancel₀ hbt, mul_one]
  · rw [Matrix.trace_smul, smul_eq_mul, inv_mul_cancel₀ hbt]

private theorem det_eq_zero_of_idempotent {e : Matrix (Fin 2) (Fin 2) F} (he : e * e = e) (htr : e.trace = 1) : e.det = 0 := by
  have h := mul_trace_smul_one_sub e
  rw [htr, one_smul] at h
  have h1 : e * (1 - e) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, he, sub_self]
  rw [h1] at h
  have := congrFun (congrFun h 0) 0
  simp at this
  exact this.symm

private theorem exists_conj_E11 {e : Matrix (Fin 2) (Fin 2) F} (he : e * e = e) (htr : e.trace = 1) :
    ∃ Q : Matrix (Fin 2) (Fin 2) F, Q.det ≠ 0 ∧ e * Q = Q * !![1, 0; 0, 0] := by
  classical
  have hdet := det_eq_zero_of_idempotent he htr

  obtain ⟨w₀, hw₀, hew₀⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet

  have he0 : e ≠ 0 := by rintro rfl; simp at htr
  have : ∃ v : Fin 2 → F, e *ᵥ v ≠ 0 := by
    by_contra hall
    push Not at hall
    apply he0
    ext i j
    have := congrFun (hall (Pi.single j 1)) i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply] using this
  obtain ⟨v, hv⟩ := this
  set w₁ := e *ᵥ v with hw₁
  have hew₁ : e *ᵥ w₁ = w₁ := by rw [hw₁, Matrix.mulVec_mulVec, he]
  refine ⟨!![w₁ 0, w₀ 0; w₁ 1, w₀ 1], ?_, ?_⟩
  · intro hQ
    obtain ⟨c, hc, hQc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hQ
    have key : !![w₁ 0, w₀ 0; w₁ 1, w₀ 1] *ᵥ c = c 0 • w₁ + c 1 • w₀ := by
      ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
    have hsum : c 0 • w₁ + c 1 • w₀ = 0 := by rw [← key, hQc]
    have h0 : c 0 = 0 := by
      have h1 := congrArg (fun u => e *ᵥ u) hsum
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hew₁, hew₀, smul_zero, add_zero, Matrix.mulVec_zero] at h1
      by_contra h0
      apply hv
      have h2 := congrArg (fun u => (c 0)⁻¹ • u) h1
      simpa [smul_smul, inv_mul_cancel₀ h0] using h2
    rw [h0, zero_smul, zero_add] at hsum
    have h1 : c 1 = 0 := by
      by_contra h1
      apply hw₀
      have h2 := congrArg (fun u => (c 1)⁻¹ • u) hsum
      simpa [smul_smul, inv_mul_cancel₀ h1] using h2
    apply hc
    ext i; fin_cases i
    · exact h0
    · exact h1
  · have h10 := congrFun hew₁ 0
    have h11 := congrFun hew₁ 1
    have h00 := congrFun hew₀ 0
    have h01 := congrFun hew₀ 1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.zero_apply] at h10 h11 h00 h01
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h10, h11, h00, h01]

private theorem exists_conj_mem [Finite 𝕜] (hdt : ∀ g, (ρ g).det ∈ 𝕜) (hfin : (Set.range ρ).Finite)
    (hspan : Submodule.span F (Set.range ρ) = ⊤) (htr : ∀ g, (ρ g).trace ∈ 𝕜) :
    ∃ P : Matrix (Fin 2) (Fin 2) F, P.det ≠ 0 ∧ (∀ g (i j : Fin 2), (P⁻¹ * ρ g * P) i j ∈ 𝕜) ∧
      ∀ i j : Fin 2, ∃ x ∈ alg 𝕜 ρ, P⁻¹ * x * P = Matrix.single i j 1 := by
  classical
  obtain ⟨e, he, hee, hetr⟩ := exists_idempotent (𝕜 := 𝕜) hdt hfin hspan htr
  obtain ⟨Q, hQ, heQ⟩ := exists_conj_E11 hee hetr
  have hQu : IsUnit Q.det := isUnit_iff_ne_zero.2 hQ

  set cj : Matrix (Fin 2) (Fin 2) F → Matrix (Fin 2) (Fin 2) F := fun x => Q⁻¹ * x * Q with hcj
  have cj_mul : ∀ x y, cj (x * y) = cj x * cj y := by
    intro x y
    simp only [hcj]
    rw [Matrix.mul_assoc (Q⁻¹ * x) Q, ← Matrix.mul_assoc Q, ← Matrix.mul_assoc Q, Matrix.mul_nonsing_inv _ hQu, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
  have cj_trace : ∀ x, (cj x).trace = x.trace := by
    intro x
    simp only [hcj]
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQu, Matrix.mul_one]
  have cj_one : cj 1 = 1 := by simp only [hcj]; rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ hQu]
  have cj_sub : ∀ x y, cj (x - y) = cj x - cj y := by intro x y; simp only [hcj]; rw [Matrix.mul_sub, Matrix.sub_mul]
  have cj_e : cj e = !![1, 0; 0, 0] := by
    simp only [hcj]; rw [Matrix.mul_assoc, heQ, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hQu, Matrix.one_mul]

  have trc : ∀ {x}, x ∈ alg 𝕜 ρ → (cj x).trace ∈ 𝕜 := fun hx => by rw [cj_trace]; exact trace_mem htr hx

  have van : ∀ f : Matrix (Fin 2) (Fin 2) F →ₗ[F] F, (∀ g, f (cj (ρ g)) = 0) → ∀ y, f y = 0 := by
    intro f hf y

    let f' : Matrix (Fin 2) (Fin 2) F →ₗ[F] F :=
      { toFun := fun x => f (cj x)
        map_add' := fun x z => by simp only [hcj]; rw [Matrix.mul_add, Matrix.add_mul, map_add]
        map_smul' := fun c x => by simp only [hcj]; rw [Matrix.mul_smul, Matrix.smul_mul, map_smul, RingHom.id_apply] }
    have hy : f' (Q * y * Q⁻¹) = 0 := forall_of_span_eq_top ρ hspan f' hf _
    have : cj (Q * y * Q⁻¹) = y := by
      simp only [hcj]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hQu, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hQu, Matrix.mul_one]
    change f (cj (Q * y * Q⁻¹)) = 0 at hy
    rwa [this] at hy

  have hex10 : ∃ g, (cj (ρ g)) 1 0 ≠ 0 := by
    by_contra hall; push Not at hall
    have := van (entryLM 1 0) hall !![0, 0; 1, 0]
    simp at this
  have hex01 : ∃ g, (cj (ρ g)) 0 1 ≠ 0 := by
    by_contra hall; push Not at hall
    have := van (entryLM 0 1) hall !![0, 1; 0, 0]
    simp at this
  obtain ⟨gu, hgu⟩ := hex10
  obtain ⟨gv, hgv⟩ := hex01
  set u₁₀ := (cj (ρ gu)) 1 0 with hu₁₀
  set v₀₁ := (cj (ρ gv)) 0 1 with hv₀₁

  set U := (1 - e) * ρ gu * e with hU
  set V := e * ρ gv * (1 - e) with hV
  have hUmem : U ∈ alg 𝕜 ρ := mul_mem (mul_mem (sub_mem (one_mem _) he) (Algebra.subset_adjoin ⟨gu, rfl⟩)) he
  have hVmem : V ∈ alg 𝕜 ρ := mul_mem (mul_mem he (Algebra.subset_adjoin ⟨gv, rfl⟩)) (sub_mem (one_mem _) he)
  have cjU : cj U = !![0, 0; u₁₀, 0] := by
    rw [hU, cj_mul, cj_mul, cj_sub, cj_one, cj_e, E22_mul_mul_E11]
  have cjV : cj V = !![0, v₀₁; 0, 0] := by
    rw [hV, cj_mul, cj_mul, cj_sub, cj_one, cj_e, E11_mul_mul_E22]

  have hμ : v₀₁ * u₁₀ ∈ 𝕜 := by
    have := trc (mul_mem hVmem hUmem)
    rwa [cj_mul, cjV, cjU, trace_E12_mul_E21] at this
  have hμ0 : v₀₁ * u₁₀ ≠ 0 := mul_ne_zero hgv hgu

  have e00 : ∀ g, (cj (ρ g)) 0 0 ∈ 𝕜 := by
    intro g
    have := trc (mul_mem (Algebra.subset_adjoin ⟨g, rfl⟩) he)
    rwa [cj_mul, cj_e, trace_mul_E11] at this
  have e11 : ∀ g, (cj (ρ g)) 1 1 ∈ 𝕜 := by
    intro g
    have h1 := trc (Algebra.subset_adjoin ⟨g, rfl⟩ : ρ g ∈ alg 𝕜 ρ)
    rw [Matrix.trace_fin_two] at h1
    have := sub_mem h1 (e00 g)
    rwa [add_sub_cancel_left] at this
  have e10 : ∀ g, (cj (ρ g)) 1 0 * v₀₁ ∈ 𝕜 := by
    intro g
    have := trc (mul_mem (Algebra.subset_adjoin ⟨g, rfl⟩) hVmem)
    rwa [cj_mul, cjV, trace_mul_E12] at this
  have e01 : ∀ g, (cj (ρ g)) 0 1 * u₁₀ ∈ 𝕜 := by
    intro g
    have := trc (mul_mem (Algebra.subset_adjoin ⟨g, rfl⟩) hUmem)
    rwa [cj_mul, cjU, trace_mul_E21] at this

  have hD : (!![(1 : F), 0; 0, u₁₀] : Matrix (Fin 2) (Fin 2) F)⁻¹ = !![1, 0; 0, u₁₀⁻¹] := by
    apply Matrix.inv_eq_left_inv
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [hgu]
  have hconj : ∀ x, (Q * !![1, 0; 0, u₁₀])⁻¹ * x * (Q * !![1, 0; 0, u₁₀]) = !![(1 : F), 0; 0, u₁₀⁻¹] * cj x * !![1, 0; 0, u₁₀] := by
    intro x
    rw [Matrix.mul_inv_rev, hD]
    simp only [hcj, Matrix.mul_assoc]
  refine ⟨Q * !![1, 0; 0, u₁₀], ?_, ?_, ?_⟩
  · rw [Matrix.det_mul]; exact mul_ne_zero hQ (by simp [Matrix.det_fin_two, hgu])
  · intro g i j
    rw [hconj, diag_inv_mul_mul_diag _ hgu]
    fin_cases i <;> fin_cases j
    · exact e00 g
    · exact e01 g
    · change u₁₀⁻¹ * (cj (ρ g)) 1 0 ∈ 𝕜
      have : u₁₀⁻¹ * (cj (ρ g)) 1 0 = ((cj (ρ g)) 1 0 * v₀₁) * (v₀₁ * u₁₀)⁻¹ := by
        field_simp
      rw [this]
      exact mul_mem (e10 g) (inv_mem hμ)
    · exact e11 g
  · intro i j
    fin_cases i <;> fin_cases j
    all_goals (try simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue])
    · refine ⟨e, he, ?_⟩
      rw [hconj, cj_e, diag_inv_mul_mul_diag _ hgu]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.single]
    · refine ⟨(v₀₁ * u₁₀)⁻¹ • V, smul_mem_alg (inv_mem hμ) hVmem, ?_⟩
      rw [hconj]
      have : cj ((v₀₁ * u₁₀)⁻¹ • V) = (v₀₁ * u₁₀)⁻¹ • cj V := by simp only [hcj]; rw [Matrix.mul_smul, Matrix.smul_mul]
      have hs : !![(1 : F), 0; 0, u₁₀⁻¹] * !![0, v₀₁; 0, 0] * !![1, 0; 0, u₁₀] = (v₀₁ * u₁₀) • Matrix.single 0 1 1 := by
        rw [diag_inv_mul_mul_diag _ hgu]
        ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.single]
      rw [this, cjV, Matrix.mul_smul, Matrix.smul_mul, hs, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
    · refine ⟨U, hUmem, ?_⟩
      rw [hconj, cjU, diag_inv_mul_mul_diag _ hgu]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.single, hgu]
    · refine ⟨1 - e, sub_mem (one_mem _) he, ?_⟩
      rw [hconj, cj_sub, cj_one, cj_e, diag_inv_mul_mul_diag _ hgu]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.single]

private theorem _root_.FiniteDescent.finite_range [Finite 𝕜] (hspan : Submodule.span F (Set.range ρ) = ⊤) (htr : ∀ g, (ρ g).trace ∈ 𝕜) :
    (Set.range ρ).Finite := by
  classical
  obtain ⟨b, hb, hbspan, hbli⟩ := exists_linearIndependent F (Set.range ⇑ρ)
  rw [hspan] at hbspan
  have hbfin : b.Finite := hbli.set_finite_of_isNoetherian
  haveI : Finite b := hbfin.to_subtype
  let Φ : Matrix (Fin 2) (Fin 2) F → (b → F) := fun x y => (x * y).trace
  have hinj : Function.Injective Φ := by
    intro x x' h
    rw [← sub_eq_zero]
    apply eq_zero_of_forall_trace_mul
    intro y
    have hv : Submodule.span F (Set.range ((↑) : b → Matrix (Fin 2) (Fin 2) F)) = ⊤ := by
      rwa [Subtype.range_coe]
    refine forall_of_span_eq_top _ hv (trMul (x - x')) (fun i => ?_) y
    have hi := congrFun h i
    rw [trMul_apply, Matrix.sub_mul, Matrix.trace_sub]
    exact sub_eq_zero.mpr hi
  have hmem : ∀ x ∈ Set.range ⇑ρ, ∀ y : b, Φ x y ∈ 𝕜 := by
    rintro _ ⟨g, rfl⟩ y
    obtain ⟨g', hg'⟩ := hb y.2
    show (ρ g * (y : Matrix (Fin 2) (Fin 2) F)).trace ∈ 𝕜
    rw [← hg', ← map_mul]
    exact htr (g * g')
  have : Finite (Set.range ⇑ρ) := by
    refine Finite.of_injective (fun x : Set.range ⇑ρ => fun y : b => (⟨Φ x.1 y, hmem x.1 x.2 y⟩ : 𝕜)) ?_
    intro a a' h
    apply Subtype.ext
    apply hinj
    funext y
    exact congrArg Subtype.val (congrFun h y)
  exact Set.finite_coe_iff.mp this

p2m_export "FiniteDescent" "finite_range"

section transfer

variable (𝕜) (ρ) {R : Type*} [CommRing R] (ψ : 𝕜 →+* R)

private noncomputable def lift (x : F) : R := by
  classical
  exact if h : x ∈ 𝕜 then ψ ⟨x, h⟩ else 0

private theorem lift_of_mem {x : F} (h : x ∈ 𝕜) : lift 𝕜 ψ x = ψ ⟨x, h⟩ := by
  classical
  simp [lift, h]

private theorem lift_add {x y : F} (hx : x ∈ 𝕜) (hy : y ∈ 𝕜) : lift 𝕜 ψ (x + y) = lift 𝕜 ψ x + lift 𝕜 ψ y := by
  rw [lift_of_mem 𝕜 ψ (add_mem hx hy), lift_of_mem 𝕜 ψ hx, lift_of_mem 𝕜 ψ hy, ← map_add]; rfl

private theorem lift_mul {x y : F} (hx : x ∈ 𝕜) (hy : y ∈ 𝕜) : lift 𝕜 ψ (x * y) = lift 𝕜 ψ x * lift 𝕜 ψ y := by
  rw [lift_of_mem 𝕜 ψ (mul_mem hx hy), lift_of_mem 𝕜 ψ hx, lift_of_mem 𝕜 ψ hy, ← map_mul]; rfl

private theorem lift_sub {x y : F} (hx : x ∈ 𝕜) (hy : y ∈ 𝕜) : lift 𝕜 ψ (x - y) = lift 𝕜 ψ x - lift 𝕜 ψ y := by
  rw [lift_of_mem 𝕜 ψ (sub_mem hx hy), lift_of_mem 𝕜 ψ hx, lift_of_mem 𝕜 ψ hy, ← map_sub]; rfl

private theorem lift_zero : lift 𝕜 ψ 0 = 0 := by rw [lift_of_mem 𝕜 ψ (zero_mem 𝕜)]; exact map_zero ψ

private theorem lift_one : lift 𝕜 ψ 1 = 1 := by rw [lift_of_mem 𝕜 ψ (one_mem 𝕜)]; exact map_one ψ

private theorem lift_natCast (n : ℕ) : lift 𝕜 ψ (n : F) = n := by
  rw [lift_of_mem 𝕜 ψ (natCast_mem 𝕜 n)]
  have : (⟨(n : F), natCast_mem 𝕜 n⟩ : 𝕜) = (n : 𝕜) := Subtype.ext (by push_cast; rfl)
  rw [this, map_natCast]

private theorem lift_intCast (n : ℤ) : lift 𝕜 ψ (n : F) = n := by
  rw [lift_of_mem 𝕜 ψ (intCast_mem 𝕜 n)]
  have : (⟨(n : F), intCast_mem 𝕜 n⟩ : 𝕜) = (n : 𝕜) := Subtype.ext (by push_cast; rfl)
  rw [this, map_intCast]

private def IsRat (x : Matrix (Fin 2) (Fin 2) F) : Prop := ∀ i j, x i j ∈ 𝕜

private theorem isRat_add {x y : Matrix (Fin 2) (Fin 2) F} (hx : IsRat 𝕜 x) (hy : IsRat 𝕜 y) : IsRat 𝕜 (x + y) :=
  fun i j => add_mem (hx i j) (hy i j)

private theorem isRat_sub {x y : Matrix (Fin 2) (Fin 2) F} (hx : IsRat 𝕜 x) (hy : IsRat 𝕜 y) : IsRat 𝕜 (x - y) :=
  fun i j => sub_mem (hx i j) (hy i j)

private theorem isRat_mul {x y : Matrix (Fin 2) (Fin 2) F} (hx : IsRat 𝕜 x) (hy : IsRat 𝕜 y) : IsRat 𝕜 (x * y) := by
  intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact add_mem (mul_mem (hx i 0) (hy 0 j)) (mul_mem (hx i 1) (hy 1 j))

private theorem isRat_smul {x : Matrix (Fin 2) (Fin 2) F} {c : F} (hc : c ∈ 𝕜) (hx : IsRat 𝕜 x) : IsRat 𝕜 (c • x) :=
  fun i j => mul_mem hc (hx i j)

private theorem isRat_one : IsRat 𝕜 (1 : Matrix (Fin 2) (Fin 2) F) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem 𝕜
  · exact zero_mem 𝕜

private theorem isRat_zero : IsRat 𝕜 (0 : Matrix (Fin 2) (Fin 2) F) := fun _ _ => zero_mem 𝕜

private noncomputable def rmap (x : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2) (Fin 2) R := fun i j => lift 𝕜 ψ (x i j)

private theorem rmap_apply (x : Matrix (Fin 2) (Fin 2) F) (i j : Fin 2) : rmap 𝕜 ψ x i j = lift 𝕜 ψ (x i j) := rfl

private theorem rmap_add {x y : Matrix (Fin 2) (Fin 2) F} (hx : IsRat 𝕜 x) (hy : IsRat 𝕜 y) :
    rmap 𝕜 ψ (x + y) = rmap 𝕜 ψ x + rmap 𝕜 ψ y := by
  ext i j; simp only [rmap_apply, Matrix.add_apply]; exact lift_add 𝕜 ψ (hx i j) (hy i j)

private theorem rmap_sub {x y : Matrix (Fin 2) (Fin 2) F} (hx : IsRat 𝕜 x) (hy : IsRat 𝕜 y) :
    rmap 𝕜 ψ (x - y) = rmap 𝕜 ψ x - rmap 𝕜 ψ y := by
  ext i j; simp only [rmap_apply, Matrix.sub_apply]; exact lift_sub 𝕜 ψ (hx i j) (hy i j)

private theorem rmap_mul {x y : Matrix (Fin 2) (Fin 2) F} (hx : IsRat 𝕜 x) (hy : IsRat 𝕜 y) :
    rmap 𝕜 ψ (x * y) = rmap 𝕜 ψ x * rmap 𝕜 ψ y := by
  ext i j
  simp only [rmap_apply, Matrix.mul_apply, Fin.sum_univ_two]
  rw [lift_add 𝕜 ψ (mul_mem (hx i 0) (hy 0 j)) (mul_mem (hx i 1) (hy 1 j)), lift_mul 𝕜 ψ (hx i 0) (hy 0 j),
    lift_mul 𝕜 ψ (hx i 1) (hy 1 j)]

private theorem rmap_smul {x : Matrix (Fin 2) (Fin 2) F} {c : F} (hc : c ∈ 𝕜) (hx : IsRat 𝕜 x) :
    rmap 𝕜 ψ (c • x) = lift 𝕜 ψ c • rmap 𝕜 ψ x := by
  ext i j; simp only [rmap_apply, Matrix.smul_apply, smul_eq_mul]; exact lift_mul 𝕜 ψ hc (hx i j)

private theorem rmap_one : rmap 𝕜 ψ (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext i j
  simp only [rmap_apply, Matrix.one_apply]
  split_ifs
  · exact lift_one 𝕜 ψ
  · exact lift_zero 𝕜 ψ

private theorem rmap_zero : rmap 𝕜 ψ (0 : Matrix (Fin 2) (Fin 2) F) = 0 := by
  ext i j; simp only [rmap_apply, Matrix.zero_apply]; exact lift_zero 𝕜 ψ

private theorem rmap_trace {x : Matrix (Fin 2) (Fin 2) F} (hx : IsRat 𝕜 x) : (rmap 𝕜 ψ x).trace = lift 𝕜 ψ x.trace := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two, rmap_apply, rmap_apply, lift_add 𝕜 ψ (hx 0 0) (hx 1 1)]

private theorem rmap_det {x : Matrix (Fin 2) (Fin 2) F} (hx : IsRat 𝕜 x) : (rmap 𝕜 ψ x).det = lift 𝕜 ψ x.det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two, rmap_apply, rmap_apply, rmap_apply, rmap_apply,
    lift_sub 𝕜 ψ (mul_mem (hx 0 0) (hx 1 1)) (mul_mem (hx 0 1) (hx 1 0)), lift_mul 𝕜 ψ (hx 0 0) (hx 1 1),
    lift_mul 𝕜 ψ (hx 0 1) (hx 1 0)]

private noncomputable def transRep {P : Matrix (Fin 2) (Fin 2) F} (hP : P.det ≠ 0)
    (hrat : ∀ g, IsRat 𝕜 (P⁻¹ * ρ g * P)) : G →* Matrix (Fin 2) (Fin 2) R where
  toFun g := rmap 𝕜 ψ (P⁻¹ * ρ g * P)
  map_one' := by rw [map_one, Matrix.mul_one, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hP), rmap_one]
  map_mul' g h := by
    rw [← rmap_mul 𝕜 ψ (hrat g) (hrat h), map_mul]
    congr 1
    rw [Matrix.mul_assoc (P⁻¹ * ρ g) P, ← Matrix.mul_assoc P, ← Matrix.mul_assoc P,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hP), Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.mul_assoc]

private theorem transRep_apply {P : Matrix (Fin 2) (Fin 2) F} (hP : P.det ≠ 0) (hrat : ∀ g, IsRat 𝕜 (P⁻¹ * ρ g * P)) (g : G) :
    transRep 𝕜 ρ ψ hP hrat g = rmap 𝕜 ψ (P⁻¹ * ρ g * P) := rfl

private theorem transRep_eq_one {P : Matrix (Fin 2) (Fin 2) F} (hP : P.det ≠ 0) (hrat : ∀ g, IsRat 𝕜 (P⁻¹ * ρ g * P))
    {g : G} (hg : ρ g = 1) : transRep 𝕜 ρ ψ hP hrat g = 1 := by
  rw [transRep_apply, hg, Matrix.mul_one, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hP), rmap_one]

private theorem trace_transRep {P : Matrix (Fin 2) (Fin 2) F} (hP : P.det ≠ 0) (hrat : ∀ g, IsRat 𝕜 (P⁻¹ * ρ g * P)) (g : G) :
    (transRep 𝕜 ρ ψ hP hrat g).trace = lift 𝕜 ψ (ρ g).trace := by
  rw [transRep_apply, rmap_trace 𝕜 ψ (hrat g), Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hP), Matrix.mul_one]

private theorem det_transRep {P : Matrix (Fin 2) (Fin 2) F} (hP : P.det ≠ 0) (hrat : ∀ g, IsRat 𝕜 (P⁻¹ * ρ g * P)) (g : G) :
    (transRep 𝕜 ρ ψ hP hrat g).det = lift 𝕜 ψ (ρ g).det := by
  rw [transRep_apply, rmap_det 𝕜 ψ (hrat g), Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv,
    mul_comm (Ring.inverse P.det), mul_assoc, Ring.inverse_mul_cancel _ (isUnit_iff_ne_zero.2 hP), mul_one]

private theorem span_transRep_eq_top (ψ : 𝕜 →+* R)
    {P : Matrix (Fin 2) (Fin 2) F} (hP : P.det ≠ 0) (hrat : ∀ g, IsRat 𝕜 (P⁻¹ * ρ g * P))
    (hunits : ∀ i j : Fin 2, ∃ x ∈ alg 𝕜 ρ, P⁻¹ * x * P = Matrix.single i j 1) :
    Submodule.span R (Set.range (transRep 𝕜 ρ ψ hP hrat)) = ⊤ := by
  classical
  have hu := isUnit_iff_ne_zero.2 hP
  set cj : Matrix (Fin 2) (Fin 2) F → Matrix (Fin 2) (Fin 2) F := fun x => P⁻¹ * x * P with hcj

  have key : ∀ x, x ∈ Submodule.span 𝕜 (Set.range ρ) →
      IsRat 𝕜 (cj x) ∧ rmap 𝕜 ψ (cj x) ∈ Submodule.span R (Set.range (transRep 𝕜 ρ ψ hP hrat)) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact ⟨hrat g, Submodule.subset_span ⟨g, rfl⟩⟩
    | zero =>
      have : cj 0 = 0 := by simp only [hcj]; rw [Matrix.mul_zero, Matrix.zero_mul]
      rw [this, rmap_zero]
      exact ⟨isRat_zero 𝕜, zero_mem _⟩
    | add x y _ _ hx hy =>
      have : cj (x + y) = cj x + cj y := by simp only [hcj]; rw [Matrix.mul_add, Matrix.add_mul]
      rw [this, rmap_add 𝕜 ψ hx.1 hy.1]
      exact ⟨isRat_add 𝕜 hx.1 hy.1, add_mem hx.2 hy.2⟩
    | smul c x _ hx =>
      have : cj (c • x) = (c : F) • cj x := by
        simp only [hcj]; rw [show c • x = (c : F) • x from rfl, Matrix.mul_smul, Matrix.smul_mul]
      rw [this, rmap_smul 𝕜 ψ c.2 hx.1]
      exact ⟨isRat_smul 𝕜 c.2 hx.1, Submodule.smul_mem _ _ hx.2⟩

  have units : ∀ i j : Fin 2, Matrix.single i j (1 : R) ∈ Submodule.span R (Set.range (transRep 𝕜 ρ ψ hP hrat)) := by
    intro i j
    obtain ⟨x, hx, hxP⟩ := hunits i j
    have hx' : x ∈ Submodule.span 𝕜 (Set.range ρ) := (mem_alg_iff 𝕜 ρ x).1 hx
    obtain ⟨hr, hmem⟩ := key x hx'
    have hcjx : cj x = Matrix.single i j 1 := hxP
    rw [hcjx] at hmem
    have : rmap 𝕜 ψ (Matrix.single i j (1 : F)) = Matrix.single i j (1 : R) := by
      ext a b
      simp only [rmap_apply, Matrix.single_apply]
      split_ifs
      · exact lift_one 𝕜 ψ
      · exact lift_zero 𝕜 ψ
    rwa [this] at hmem
  rw [eq_top_iff]
  intro y _
  rw [Matrix.matrix_eq_sum_single y]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have : Matrix.single i j (y i j) = y i j • Matrix.single i j (1 : R) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this]
  exact Submodule.smul_mem _ _ (units i j)

private theorem map_rmap (e₀ : R →+* F) (hψ : ∀ y : 𝕜, e₀ (ψ y) = y) {x : Matrix (Fin 2) (Fin 2) F} (hx : IsRat 𝕜 x) :
    (rmap 𝕜 ψ x).map e₀ = x := by
  ext i j
  rw [Matrix.map_apply, rmap_apply, lift_of_mem 𝕜 ψ (hx i j), hψ]

end transfer

end FiniteDescent
p2m_reactivate "P2MW.S_Representation_exists_map_eq_conj_and_span_range_eq_top_of_charpoly_coeff_mem_range_of_finite_fin_two.FiniteDescent"

namespace FiniteDescent

open Matrix

section burnside

variable {K : Type} [Field K]

private theorem apply_eq_sum_single (f : Matrix (Fin 2) (Fin 2) K →ₗ[K] K) (s : Matrix (Fin 2) (Fin 2) K) :
    f s = ∑ i, ∑ j, s i j * f (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single s]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

private theorem exists_trace_mul_eq_zero_of_ne_top {S : Submodule K (Matrix (Fin 2) (Fin 2) K)}
    (hS : S ≠ ⊤) : ∃ Y : Matrix (Fin 2) (Fin 2) K, Y ≠ 0 ∧ ∀ s ∈ S, (Y * s).trace = 0 := by
  obtain ⟨f, hf0, hfS⟩ := Submodule.exists_le_ker_of_lt_top S hS.lt_top
  have key : ∀ s, (Matrix.of (fun i j => f (Matrix.single j i 1)) * s).trace = f s := by
    intro s
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply]
    rw [apply_eq_sum_single f s, Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => mul_comm _ _
  refine ⟨Matrix.of fun i j => f (Matrix.single j i 1), fun hY => hf0 ?_, fun s hs => ?_⟩
  · ext s
    rw [← key s, hY, Matrix.zero_mul, Matrix.trace_zero, LinearMap.zero_apply]
  · rw [key s]
    exact LinearMap.mem_ker.mp (hfS hs)

private theorem col_ne_zero {Q : Matrix (Fin 2) (Fin 2) K} (hQ : Q.det ≠ 0) (j : Fin 2) :
    (fun i => Q i j) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Pi.zero_apply] at h0 h1
  apply hQ
  rw [Matrix.det_fin_two]
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue] at h0 h1
    rw [h0, h1, zero_mul, mul_zero, sub_zero]
  · simp only [Fin.mk_one, Fin.isValue] at h0 h1
    rw [h0, h1, zero_mul, mul_zero, sub_zero]

private theorem conj_apply_one_zero_ne_zero {Q X : Matrix (Fin 2) (Fin 2) K} (hQ : Q.det ≠ 0)
    (hu : X *ᵥ (fun i => Q i 0) ∉ K ∙ (fun i => Q i 0)) : (Q⁻¹ * X * Q) 1 0 ≠ 0 := by
  intro h0
  apply hu
  set M := Q⁻¹ * X * Q with hM
  have hQX : X * Q = Q * M := by
    rw [hM, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hQ),
      Matrix.one_mul]
  refine Submodule.mem_span_singleton.mpr ⟨M 0 0, ?_⟩
  ext i
  have e1 : (X *ᵥ fun i => Q i 0) i = (X * Q) i 0 := by
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  rw [e1, hQX, Matrix.mul_apply, Fin.sum_univ_two, h0, mul_zero, add_zero, Pi.smul_apply, smul_eq_mul,
    mul_comm]

private theorem conj_apply_zero_one_ne_zero {Q X : Matrix (Fin 2) (Fin 2) K} (hQ : Q.det ≠ 0)
    (hu : X *ᵥ (fun i => Q i 1) ∉ K ∙ (fun i => Q i 1)) : (Q⁻¹ * X * Q) 0 1 ≠ 0 := by
  intro h0
  apply hu
  set M := Q⁻¹ * X * Q with hM
  have hQX : X * Q = Q * M := by
    rw [hM, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hQ),
      Matrix.one_mul]
  refine Submodule.mem_span_singleton.mpr ⟨M 1 1, ?_⟩
  ext i
  have e1 : (X *ᵥ fun i => Q i 1) i = (X * Q) i 1 := by
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  rw [e1, hQX, Matrix.mul_apply, Fin.sum_univ_two, h0, mul_zero, zero_add, Pi.smul_apply, smul_eq_mul,
    mul_comm]

private theorem conj_mul_conj {Q : Matrix (Fin 2) (Fin 2) K} (hQu : IsUnit Q.det)
    (a b : Matrix (Fin 2) (Fin 2) K) : Q⁻¹ * (a * b) * Q = Q⁻¹ * a * Q * (Q⁻¹ * b * Q) := by
  rw [Matrix.mul_assoc (Q⁻¹ * a) Q, ← Matrix.mul_assoc Q, ← Matrix.mul_assoc Q, Matrix.mul_nonsing_inv _ hQu,
    Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]

private theorem conj_sub_conj (Q a b : Matrix (Fin 2) (Fin 2) K) :
    Q⁻¹ * (a - b) * Q = Q⁻¹ * a * Q - Q⁻¹ * b * Q := by
  rw [Matrix.mul_sub, Matrix.sub_mul]

private theorem conj_smul_conj (Q : Matrix (Fin 2) (Fin 2) K) (c : K) (a : Matrix (Fin 2) (Fin 2) K) :
    Q⁻¹ * (c • a) * Q = c • (Q⁻¹ * a * Q) := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

private theorem conj_one_conj {Q : Matrix (Fin 2) (Fin 2) K} (hQu : IsUnit Q.det) :
    Q⁻¹ * 1 * Q = 1 := by
  rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ hQu]

private theorem exists_conj_E12 {N : Matrix (Fin 2) (Fin 2) K} (hN : N * N = 0) (hN0 : N ≠ 0) :
    ∃ Q : Matrix (Fin 2) (Fin 2) K, Q.det ≠ 0 ∧ N * Q = Q * !![0, 1; 0, 0] := by
  classical
  have : ∃ v : Fin 2 → K, N *ᵥ v ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hN0
    ext i j
    have := congrFun (hall (Pi.single j 1)) i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply] using this
  obtain ⟨v, hv⟩ := this
  set w := N *ᵥ v with hw
  have hNw : N *ᵥ w = 0 := by rw [hw, Matrix.mulVec_mulVec, hN, Matrix.zero_mulVec]
  refine ⟨!![w 0, v 0; w 1, v 1], ?_, ?_⟩
  · intro hQ
    obtain ⟨c, hc, hQc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hQ
    have key : !![w 0, v 0; w 1, v 1] *ᵥ c = c 0 • w + c 1 • v := by
      ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
    have hsum : c 0 • w + c 1 • v = 0 := by rw [← key, hQc]
    have h1 : c 1 = 0 := by
      have happ := congrArg (fun u => N *ᵥ u) hsum
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hNw, smul_zero, zero_add, Matrix.mulVec_zero] at happ
      by_contra h1
      apply hv
      have h2 := congrArg (fun u => (c 1)⁻¹ • u) happ
      simp only [smul_smul, inv_mul_cancel₀ h1, one_smul, smul_zero] at h2
      exact h2
    rw [h1, zero_smul, add_zero] at hsum
    have h0 : c 0 = 0 := by
      by_contra h0
      apply hv
      have h2 := congrArg (fun u => (c 0)⁻¹ • u) hsum
      simp only [smul_smul, inv_mul_cancel₀ h0, one_smul, smul_zero] at h2
      exact h2
    apply hc
    ext i; fin_cases i
    · exact h0
    · exact h1
  · have h10 := congrFun hNw 0
    have h11 := congrFun hNw 1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.zero_apply] at h10 h11
    ext i j; fin_cases i <;> fin_cases j
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using h10
    · simp [Matrix.mul_apply, Fin.sum_univ_two, hw, Matrix.mulVec, dotProduct]
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using h11
    · simp [Matrix.mul_apply, Fin.sum_univ_two, hw, Matrix.mulVec, dotProduct]

private theorem eq_top_of_conj_single (A : Submodule K (Matrix (Fin 2) (Fin 2) K))
    {Q : Matrix (Fin 2) (Fin 2) K} (hQ : Q.det ≠ 0)
    (h : ∀ i j : Fin 2, ∃ a ∈ A, Q⁻¹ * a * Q = Matrix.single i j 1) : A = ⊤ := by
  classical
  have hQu : IsUnit Q.det := isUnit_iff_ne_zero.2 hQ
  rw [eq_top_iff]
  intro y _
  set M := Q⁻¹ * y * Q with hMdef
  have hy : y = Q * M * Q⁻¹ := by
    rw [hMdef, Matrix.mul_assoc Q, Matrix.mul_assoc (Q⁻¹ * y), Matrix.mul_nonsing_inv _ hQu,
      Matrix.mul_one, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQu, Matrix.one_mul]
  rw [hy, Matrix.matrix_eq_sum_single M, Matrix.mul_sum, Matrix.sum_mul]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Submodule.sum_mem _ fun j _ => ?_
  obtain ⟨a, ha, hcj⟩ := h i j
  have ha' : Q * Matrix.single i j 1 * Q⁻¹ = a := by
    rw [← hcj, Matrix.mul_assoc Q, Matrix.mul_assoc (Q⁻¹ * a), Matrix.mul_nonsing_inv _ hQu,
      Matrix.mul_one, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQu, Matrix.one_mul]
  rw [show Matrix.single i j (M i j) = M i j • Matrix.single i j (1 : K) by
      rw [Matrix.smul_single, smul_eq_mul, mul_one],
    Matrix.mul_smul, Matrix.smul_mul, ha']
  exact A.smul_mem _ ha

private theorem span_eq_top_of_forall_mulVec_not_mem [IsAlgClosed K] {G : Type} [Group G]
    (X : G →* Matrix (Fin 2) (Fin 2) K)
    (hns : ∀ u : Fin 2 → K, u ≠ 0 → ∃ x : G, X x *ᵥ u ∉ K ∙ u) :
    Submodule.span K (Set.range ⇑X) = ⊤ := by
  classical
  set A := Submodule.span K (Set.range ⇑X) with hA

  have hmul : ∀ {a b : Matrix (Fin 2) (Fin 2) K}, a ∈ A → b ∈ A → a * b ∈ A := by
    intro a b ha hb
    have e : (Algebra.adjoin K (Set.range ⇑X)).toSubmodule = A := by
      rw [hA, Algebra.adjoin_eq_span, closure_range_eq]
    rw [← e] at ha hb ⊢
    exact (Algebra.adjoin K (Set.range ⇑X)).mul_mem ha hb
  have hX : ∀ x, X x ∈ A := fun x => Submodule.subset_span ⟨x, rfl⟩
  have h1 : (1 : Matrix (Fin 2) (Fin 2) K) ∈ A := (map_one X) ▸ hX 1

  obtain ⟨x₀, hx₀⟩ : ∃ x₀, ∀ c : K, X x₀ ≠ c • (1 : Matrix (Fin 2) (Fin 2) K) := by
    by_contra hall
    push Not at hall
    obtain ⟨x, hx⟩ := hns (Pi.single 0 1) (by simp)
    obtain ⟨c, hc⟩ := hall x
    exact hx (Submodule.mem_span_singleton.mpr ⟨c, by rw [hc, Matrix.smul_mulVec, Matrix.one_mulVec]⟩)

  obtain ⟨lam, hlam⟩ := IsAlgClosed.exists_root
    (Polynomial.C (1 : K) * Polynomial.X ^ 2 + Polynomial.C (-(X x₀).trace) * Polynomial.X +
      Polynomial.C (X x₀).det) (by rw [Polynomial.degree_quadratic one_ne_zero]; decide)
  set N : Matrix (Fin 2) (Fin 2) K := X x₀ - lam • (1 : Matrix (Fin 2) (Fin 2) K) with hNdef
  have hNA : N ∈ A := A.sub_mem (hX x₀) (A.smul_mem lam h1)
  have hN0 : N ≠ 0 := fun h => hx₀ lam (sub_eq_zero.mp h)
  have hNdet : N.det = 0 := by
    have h := hlam.eq_zero
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, one_mul] at h
    rw [Matrix.trace_fin_two, Matrix.det_fin_two] at h
    rw [hNdef, Matrix.det_fin_two]
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
      Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0),
      smul_eq_mul, mul_one, mul_zero, sub_zero]
    linear_combination h
  have hNN : N * N = N.trace • N := mul_self_eq_of_det_eq_zero hNdet
  by_cases ht : N.trace = 0
  ·
    rw [ht, zero_smul] at hNN
    obtain ⟨Q, hQ, hNQ⟩ := exists_conj_E12 hNN hN0
    have hQu : IsUnit Q.det := isUnit_iff_ne_zero.2 hQ
    have cjN : Q⁻¹ * N * Q = !![0, 1; 0, 0] := by
      rw [Matrix.mul_assoc, hNQ, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hQu, Matrix.one_mul]
    obtain ⟨x₁, hx₁⟩ := hns (fun i => Q i 0) (col_ne_zero hQ 0)
    set M := Q⁻¹ * X x₁ * Q with hMdef
    have hc : M 1 0 ≠ 0 := conj_apply_one_zero_ne_zero hQ hx₁

    set a₀₀ := (M 1 0)⁻¹ • (N * X x₁ - M 1 1 • N) with ha₀₀
    have ha₀₀A : a₀₀ ∈ A := A.smul_mem _ (A.sub_mem (hmul hNA (hX x₁)) (A.smul_mem _ hNA))
    have cj₀₀ : Q⁻¹ * a₀₀ * Q = Matrix.single 0 0 1 := by
      rw [ha₀₀, conj_smul_conj, conj_sub_conj, conj_smul_conj, conj_mul_conj hQu, cjN, ← hMdef]
      ext i j
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single,
        Matrix.of_apply, smul_eq_mul]
      fin_cases i <;> fin_cases j <;> simp [hc]
    have cj₁₁ : Q⁻¹ * (1 - a₀₀) * Q = Matrix.single 1 1 1 := by
      rw [conj_sub_conj, conj_one_conj hQu, cj₀₀]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.single]
    set a₁₀ := (M 1 0)⁻¹ • ((1 - a₀₀) * X x₁ * a₀₀) with ha₁₀
    have ha₁₀A : a₁₀ ∈ A := A.smul_mem _ (hmul (hmul (A.sub_mem h1 ha₀₀A) (hX x₁)) ha₀₀A)
    have cj₁₀ : Q⁻¹ * a₁₀ * Q = Matrix.single 1 0 1 := by
      rw [ha₁₀, conj_smul_conj, conj_mul_conj hQu, conj_mul_conj hQu, cj₁₁, cj₀₀, ← hMdef]
      ext i j
      simp only [Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single, Matrix.of_apply,
        smul_eq_mul]
      fin_cases i <;> fin_cases j <;> simp [hc]
    have cj₀₁ : Q⁻¹ * N * Q = Matrix.single 0 1 1 := by
      rw [cjN]; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.single]
    refine eq_top_of_conj_single A hQ fun i j => ?_
    fin_cases i <;> fin_cases j
    all_goals (try simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue])
    · exact ⟨a₀₀, ha₀₀A, cj₀₀⟩
    · exact ⟨N, hNA, cj₀₁⟩
    · exact ⟨a₁₀, ha₁₀A, cj₁₀⟩
    · exact ⟨1 - a₀₀, A.sub_mem h1 ha₀₀A, cj₁₁⟩
  ·
    set e := (N.trace)⁻¹ • N with hedef
    have heA : e ∈ A := A.smul_mem _ hNA
    have hee : e * e = e := by
      rw [hedef, Matrix.smul_mul, Matrix.mul_smul, hNN, smul_smul, smul_smul, mul_assoc, inv_mul_cancel₀ ht,
        mul_one]
    have hetr : e.trace = 1 := by rw [hedef, Matrix.trace_smul, smul_eq_mul, inv_mul_cancel₀ ht]
    obtain ⟨Q, hQ, heQ⟩ := exists_conj_E11 hee hetr
    have hQu : IsUnit Q.det := isUnit_iff_ne_zero.2 hQ
    have cje : Q⁻¹ * e * Q = !![1, 0; 0, 0] := by
      rw [Matrix.mul_assoc, heQ, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hQu, Matrix.one_mul]
    obtain ⟨x₁, hx₁⟩ := hns (fun i => Q i 0) (col_ne_zero hQ 0)
    obtain ⟨x₂, hx₂⟩ := hns (fun i => Q i 1) (col_ne_zero hQ 1)
    have hu : (Q⁻¹ * X x₁ * Q) 1 0 ≠ 0 := conj_apply_one_zero_ne_zero hQ hx₁
    have hv : (Q⁻¹ * X x₂ * Q) 0 1 ≠ 0 := conj_apply_zero_one_ne_zero hQ hx₂
    set U := (1 - e) * X x₁ * e with hU
    set V := e * X x₂ * (1 - e) with hV
    have hUA : U ∈ A := hmul (hmul (A.sub_mem h1 heA) (hX x₁)) heA
    have hVA : V ∈ A := hmul (hmul heA (hX x₂)) (A.sub_mem h1 heA)
    have cjU : Q⁻¹ * U * Q = !![0, 0; (Q⁻¹ * X x₁ * Q) 1 0, 0] := by
      rw [hU, conj_mul_conj hQu, conj_mul_conj hQu, conj_sub_conj, conj_one_conj hQu, cje, E22_mul_mul_E11]
    have cjV : Q⁻¹ * V * Q = !![0, (Q⁻¹ * X x₂ * Q) 0 1; 0, 0] := by
      rw [hV, conj_mul_conj hQu, conj_mul_conj hQu, conj_sub_conj, conj_one_conj hQu, cje, E11_mul_mul_E22]
    have cj₀₀ : Q⁻¹ * e * Q = Matrix.single 0 0 1 := by
      rw [cje]; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.single]
    have cj₁₁ : Q⁻¹ * (1 - e) * Q = Matrix.single 1 1 1 := by
      rw [conj_sub_conj, conj_one_conj hQu, cje]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.single]
    have cj₁₀ : Q⁻¹ * (((Q⁻¹ * X x₁ * Q) 1 0)⁻¹ • U) * Q = Matrix.single 1 0 1 := by
      rw [conj_smul_conj, cjU]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.single, hu]
    have cj₀₁ : Q⁻¹ * (((Q⁻¹ * X x₂ * Q) 0 1)⁻¹ • V) * Q = Matrix.single 0 1 1 := by
      rw [conj_smul_conj, cjV]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.single, hv]
    refine eq_top_of_conj_single A hQ fun i j => ?_
    fin_cases i <;> fin_cases j
    all_goals (try simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue])
    · exact ⟨e, heA, cj₀₀⟩
    · exact ⟨_, A.smul_mem _ hVA, cj₀₁⟩
    · exact ⟨_, A.smul_mem _ hUA, cj₁₀⟩
    · exact ⟨1 - e, A.sub_mem h1 heA, cj₁₁⟩

end burnside
p2m_reactivate "P2MW.S_Representation_exists_map_eq_conj_and_span_range_eq_top_of_charpoly_coeff_mem_range_of_finite_fin_two.FiniteDescent"

private theorem span_range_eq_top_of_forall_exists_mulVec_not_mem
    {G : Type} [Group G] {F : Type} [Field F] (ρ : G →* GL (Fin 2) F)
    (habs : ∀ {F' : Type} [Field F'] (e : F →+* F') (u : Fin 2 → F'), u ≠ 0 →
      ∃ x : G, Matrix.mulVec ((ρ x).val.map e) u ∉ F' ∙ u) :
    Submodule.span F (Set.range (fun x : G => (ρ x).val)) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨Y, hY0, hY⟩ := exists_trace_mul_eq_zero_of_ne_top hne

  let Fb : Type := AlgebraicClosure F
  let e : F →+* Fb := algebraMap F Fb
  let Xb : G →* Matrix (Fin 2) (Fin 2) Fb :=
    (RingHom.mapMatrix e).toMonoidHom.comp ((Units.coeHom (Matrix (Fin 2) (Fin 2) F)).comp ρ)
  have hXb : ∀ x, Xb x = (ρ x).val.map e := fun x => rfl
  have hspan : Submodule.span Fb (Set.range ⇑Xb) = ⊤ :=
    span_eq_top_of_forall_mulVec_not_mem Xb fun u hu => by
      obtain ⟨x, hx⟩ := habs e u hu
      exact ⟨x, hx⟩

  have hYb : ∀ s ∈ Submodule.span Fb (Set.range ⇑Xb), (Y.map e * s).trace = 0 := by
    intro s hs
    induction hs using Submodule.span_induction with
    | mem s hs =>
      obtain ⟨x, rfl⟩ := hs
      have hmap : Y.map e * Xb x = (Y * (ρ x).val).map e := by rw [hXb, Matrix.map_mul]
      have htr : ((Y * (ρ x).val).map ⇑e).trace = e (Y * (ρ x).val).trace := by
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.map_apply, map_sum]
      rw [hmap, htr, hY _ (Submodule.subset_span ⟨x, rfl⟩), map_zero]
    | zero => rw [Matrix.mul_zero, Matrix.trace_zero]
    | add s t _ _ hs ht => rw [Matrix.mul_add, Matrix.trace_add, hs, ht, add_zero]
    | smul c s _ hs => rw [Matrix.mul_smul, Matrix.trace_smul, hs, smul_zero]
  have hYb0 : Y.map ⇑e = 0 := by
    apply eq_zero_of_forall_trace_mul
    intro s
    exact hYb s (hspan ▸ Submodule.mem_top)
  apply hY0
  ext i j
  have hij := congrFun (congrFun hYb0 i) j
  simp only [Matrix.map_apply, Matrix.zero_apply] at hij
  exact (map_eq_zero_iff e e.injective).mp hij

end FiniteDescent
p2m_reactivate "P2MW.S_Representation_exists_map_eq_conj_and_span_range_eq_top_of_charpoly_coeff_mem_range_of_finite_fin_two.FiniteDescent"

theorem solution
    {G : Type} [Group G] {k₀ : Type} [Field k₀] [Finite k₀] {F : Type} [Field F] (e₀ : k₀ →+* F)
    (ρ : G →* GL (Fin 2) F)
    (hcoeff : ∀ (x : G) (i : ℕ), ((ρ x).val.charpoly).coeff i ∈ e₀.range)
    (habs : ∀ {F' : Type} [Field F'] (e : F →+* F') (u : Fin 2 → F'), u ≠ 0 →
      ∃ x : G, Matrix.mulVec ((ρ x).val.map e) u ∉ F' ∙ u) :
    ∃ (ρ₀ : G →* GL (Fin 2) k₀) (g : GL (Fin 2) F),
      (∀ x : G, (ρ₀ x).val.map e₀ = g.val * (ρ x).val * (g⁻¹).val) ∧
      Submodule.span k₀ (Set.range (fun x : G => (ρ₀ x).val)) = ⊤ := by
  classical

  set 𝕜 : Subfield F := e₀.fieldRange with h𝕜
  haveI : Finite 𝕜 := by
    have hfinset : ((𝕜 : Subfield F) : Set F).Finite := by
      rw [h𝕜, RingHom.coe_fieldRange]; exact Set.finite_range e₀
    exact hfinset.to_subtype

  set ρM : G →* Matrix (Fin 2) (Fin 2) F := (Units.coeHom (Matrix (Fin 2) (Fin 2) F)).comp ρ with hρMdef
  have hρM : ∀ x, ρM x = (ρ x).val := fun x => rfl
  have htr : ∀ x, (ρM x).trace ∈ 𝕜 := by
    intro x
    obtain ⟨c, hc⟩ := RingHom.mem_range.mp (hcoeff x 1)
    have e1 : (ρM x).trace = -(((ρ x).val.charpoly).coeff 1) := by
      rw [hρM, Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin]
    rw [e1]
    exact neg_mem (RingHom.mem_fieldRange.mpr ⟨c, hc⟩)
  have hdt : ∀ x, (ρM x).det ∈ 𝕜 := by
    intro x
    obtain ⟨c, hc⟩ := RingHom.mem_range.mp (hcoeff x 0)
    have e1 : (ρM x).det = (-1) ^ 2 * ((ρ x).val.charpoly).coeff 0 := by
      rw [hρM, Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin]
    rw [e1]
    exact mul_mem (pow_mem (neg_mem (one_mem _)) 2) (RingHom.mem_fieldRange.mpr ⟨c, hc⟩)

  have hspan : Submodule.span F (Set.range ⇑ρM) = ⊤ := by
    have h := FiniteDescent.span_range_eq_top_of_forall_exists_mulVec_not_mem ρ habs
    rwa [show (fun x : G => (ρ x).val) = ⇑ρM from rfl] at h
  have hfin : (Set.range ⇑ρM).Finite := FiniteDescent.finite_range hspan htr

  obtain ⟨P, hP, hrat, hunits⟩ := FiniteDescent.exists_conj_mem (𝕜 := 𝕜) (ρ := ρM) hdt hfin hspan htr
  have hrat' : ∀ x, FiniteDescent.IsRat 𝕜 (P⁻¹ * ρM x * P) := fun x i j => hrat x i j

  let ψ : 𝕜 →+* k₀ := e₀.rangeRestrictFieldEquiv.symm.toRingHom
  have hψ : ∀ y : 𝕜, e₀ (ψ y) = y := fun y => by
    have h1 : e₀.rangeRestrictFieldEquiv (ψ y) = y := e₀.rangeRestrictFieldEquiv.apply_symm_apply y
    have h2 := congrArg (fun z : 𝕜 => (z : F)) h1
    exact (RingHom.coe_rangeRestrictField e₀ (ψ y)).symm.trans h2
  let ρ₀ : G →* Matrix (Fin 2) (Fin 2) k₀ := FiniteDescent.transRep 𝕜 ρM ψ hP hrat'
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.2 hP
  refine ⟨ρ₀.toHomUnits, (Matrix.nonsingInvUnit P hPu)⁻¹, fun x => ?_, ?_⟩
  · change (FiniteDescent.rmap 𝕜 ψ (P⁻¹ * ρM x * P)).map e₀ = P⁻¹ * (ρ x).val * P
    exact FiniteDescent.map_rmap 𝕜 ψ e₀ hψ (hrat' x)
  · exact FiniteDescent.span_transRep_eq_top 𝕜 ρM ψ hP hrat' hunits

end S_Representation_exists_map_eq_conj_and_span_range_eq_top_of_charpoly_coeff_mem_range_of_finite_fin_two
end P2MW
export P2MW.S_Representation_exists_map_eq_conj_and_span_range_eq_top_of_charpoly_coeff_mem_range_of_finite_fin_two (solution)
