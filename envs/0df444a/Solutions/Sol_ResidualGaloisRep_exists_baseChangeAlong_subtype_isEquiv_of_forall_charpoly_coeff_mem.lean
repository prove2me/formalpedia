-- Prove2me | solution 1 for ResidualGaloisRep.exists_baseChangeAlong_subtype_isEquiv_of_forall_charpoly_coeff_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/4ab50c63-2903-566d-843c-591c427468d5

import Mathlib.RingTheory.LittleWedderburn
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.FieldTheory.Minpoly.Field
import Definitions.Def_GaloisRep_ResidualEquiv
import Theorems.Thm_ResidualGaloisRep_isAbsolutelyIrreducible_iff_span_eq_top
import Theorems.Thm_ResidualGaloisRep_isEquiv_of_isAbsolutelyIrreducible_of_charpoly_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_exists_baseChangeAlong_subtype_isEquiv_of_forall_charpoly_coeff_mem

set_option autoImplicit false

namespace W3ResdescSol

open Matrix

section Core

variable {k : Type} [Field k] (k₀ : Subfield k)

local notation "M₂" => Matrix (Fin 2) (Fin 2) k

theorem trace_mul_mem_of_mem_span (S : Submonoid M₂) (htr : ∀ s ∈ S, trace s ∈ k₀)
    {x y : M₂} (hx : x ∈ Submodule.span k₀ (S : Set M₂))
    (hy : y ∈ Submodule.span k₀ (S : Set M₂)) : trace (x * y) ∈ k₀ := by
  induction hx using Submodule.span_induction generalizing y with
  | mem s hs =>
    induction hy using Submodule.span_induction with
    | mem t ht => exact htr _ (S.mul_mem hs ht)
    | zero => simp
    | add u v _ _ hu hv => rw [mul_add, trace_add]; exact add_mem hu hv
    | smul c u _ hu =>
      rw [mul_smul_comm, trace_smul, Algebra.smul_def]
      exact k₀.mul_mem (SetLike.coe_mem c) hu
  | zero => simp
  | add u v _ _ hu hv => rw [add_mul, trace_add]; exact add_mem (hu hy) (hv hy)
  | smul c u _ hu =>
    rw [smul_mul_assoc, trace_smul, Algebra.smul_def]
    exact k₀.mul_mem (SetLike.coe_mem c) (hu hy)

theorem trace_mem_of_mem_span (S : Submonoid M₂) (htr : ∀ s ∈ S, trace s ∈ k₀)
    {x : M₂} (hx : x ∈ Submodule.span k₀ (S : Set M₂)) : trace x ∈ k₀ := by
  simpa using trace_mul_mem_of_mem_span k₀ S htr hx (Submodule.subset_span S.one_mem)

theorem eq_zero_or_eq_zero_of_forall_mul_mul_eq_zero {a b : M₂} (h : ∀ x : M₂, a * x * b = 0) :
    a = 0 ∨ b = 0 := by
  by_contra hab
  push Not at hab
  obtain ⟨ha, hb⟩ := hab
  obtain ⟨i, j, hij⟩ : ∃ i j, a i j ≠ 0 := by
    by_contra h'; push Not at h'; exact ha (Matrix.ext h')
  obtain ⟨i', j', hij'⟩ : ∃ i j, b i j ≠ 0 := by
    by_contra h'; push Not at h'; exact hb (Matrix.ext h')
  have h0 : single (0 : Fin 2) i (1 : k) * (a * single j i' 1 * b) * single j' (0 : Fin 2) 1 = 0 := by
    rw [h, mul_zero, zero_mul]
  rw [show single (0 : Fin 2) i (1 : k) * (a * single j i' 1 * b) * single j' (0 : Fin 2) 1
      = (single 0 i 1 * a * single j i' 1) * b * single j' 0 1 by simp only [mul_assoc],
    single_mul_mul_single, single_mul_mul_single] at h0
  have := congrFun (congrFun h0 0) 0
  simp [hij, hij'] at this

theorem commute_of_mem_span (S : Set M₂) (hS : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s)
    {x y : M₂} (hx : x ∈ Submodule.span k S) (hy : y ∈ Submodule.span k S) : x * y = y * x := by
  induction hx using Submodule.span_induction generalizing y with
  | mem s hs =>
    induction hy using Submodule.span_induction with
    | mem t ht => exact hS s hs t ht
    | zero => simp
    | add u v _ _ hu hv => rw [mul_add, add_mul, hu, hv]
    | smul c u _ hu => rw [mul_smul_comm, smul_mul_assoc, hu]
  | zero => simp
  | add u v _ _ hu hv => rw [add_mul, mul_add, hu hy, hv hy]
  | smul c u _ hu => rw [smul_mul_assoc, mul_smul_comm, hu hy]

theorem mul_mul_eq_zero_of_mem_span (S : Set M₂) (e f : M₂) (hS : ∀ s ∈ S, e * s * f = 0)
    {x : M₂} (hx : x ∈ Submodule.span k S) : e * x * f = 0 := by
  induction hx using Submodule.span_induction with
  | mem s hs => exact hS s hs
  | zero => simp
  | add u v _ _ hu hv => rw [mul_add, add_mul, hu, hv, add_zero]
  | smul c u _ hu => rw [mul_smul_comm, smul_mul_assoc, hu, smul_zero]

theorem exists_sq_eq_zero_mem_adjoin [Finite k₀] (S : Submonoid M₂) (hfin : (S : Set M₂).Finite)
    (htr : ∀ s ∈ S, trace s ∈ k₀) (hspan : Submodule.span k (S : Set M₂) = ⊤) :
    ∃ n ∈ Algebra.adjoin k₀ (S : Set M₂), n ≠ 0 ∧ n * n = 0 := by
  classical
  set A₀ := Algebra.adjoin k₀ (S : Set M₂) with hA₀
  have hA₀span : Subalgebra.toSubmodule A₀ = Submodule.span k₀ (S : Set M₂) := by
    rw [hA₀, Algebra.adjoin_eq_span, Submonoid.closure_eq]
  have hmemA₀ : ∀ {x : M₂}, x ∈ A₀ ↔ x ∈ Submodule.span k₀ (S : Set M₂) := fun {x} => by
    rw [← Subalgebra.mem_toSubmodule, hA₀span]
  haveI : Module.Finite k₀ (Subalgebra.toSubmodule A₀) := by
    rw [Module.Finite.iff_fg, hA₀span]
    exact Submodule.fg_span hfin
  haveI : Finite A₀ := Module.finite_of_finite k₀ (M := Subalgebra.toSubmodule A₀)
  by_contra hno
  push Not at hno

  have hunit : ∀ a : A₀, a ≠ 0 → IsUnit a := by
    intro a ha
    have ha' : (a : M₂) ≠ 0 := fun h => ha (Subtype.ext h)
    by_cases hdet : (a : M₂).det = 0
    · exfalso
      have hCH : (a : M₂) * a = trace (a : M₂) • (a : M₂) := by
        have := Matrix.aeval_self_charpoly (a : M₂)
        rw [Matrix.charpoly_fin_two, hdet] at this
        simp only [map_zero, add_zero, map_sub, map_mul, Polynomial.aeval_X,
          Polynomial.aeval_C, sub_eq_zero, pow_two, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
          one_mul] at this
        exact this
      have htra : trace (a : M₂) ∈ k₀ := trace_mem_of_mem_span k₀ S htr (hmemA₀.mp a.2)
      by_cases ht : trace (a : M₂) = 0
      · exact hno a a.2 ha' (by rw [hCH, ht, zero_smul])
      · set c : k := (trace (a : M₂))⁻¹ with hc
        set e : M₂ := c • (a : M₂) with he
        have heA : e ∈ A₀ := by
          have : e = (⟨trace (a : M₂), htra⟩⁻¹ : k₀) • (a : M₂) := by
            rw [Subfield.smul_def]; rfl
          rw [this]; exact A₀.smul_mem a.2 _
        have hee : e * e = e := by
          simp only [he, smul_mul_assoc, mul_smul_comm, hCH, smul_smul]
          congr 1
          rw [hc, inv_mul_cancel₀ ht, mul_one]
        have he0 : e ≠ 0 := smul_ne_zero (inv_ne_zero ht) ha'
        have he1 : 1 - e ≠ 0 := by
          intro h
          have h1 : e = 1 := (sub_eq_zero.mp h).symm
          have := congrArg det h1
          rw [he, det_smul, hdet, mul_zero, det_one] at this
          exact zero_ne_one this
        have h10 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, hee, sub_self]
        obtain ⟨s, hs, hn⟩ : ∃ s ∈ S, e * s * (1 - e) ≠ 0 := by
          by_contra hall
          push Not at hall
          have : ∀ x : M₂, e * x * (1 - e) = 0 := fun x =>
            mul_mul_eq_zero_of_mem_span _ e (1 - e) hall (hspan ▸ Submodule.mem_top)
          rcases eq_zero_or_eq_zero_of_forall_mul_mul_eq_zero this with h | h
          · exact he0 h
          · exact he1 h
        refine hno (e * s * (1 - e)) ?_ hn ?_
        · exact A₀.mul_mem (A₀.mul_mem heA (Algebra.subset_adjoin hs))
            (A₀.sub_mem A₀.one_mem heA)
        · calc e * s * (1 - e) * (e * s * (1 - e))
              = e * s * ((1 - e) * e) * s * (1 - e) := by simp only [mul_assoc]
            _ = 0 := by rw [h10, mul_zero, zero_mul, zero_mul]
    ·
      obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).mpr (Ne.isUnit hdet)
      have hinj : Function.Injective fun x : A₀ => a * x := by
        intro x y hxy
        apply Subtype.ext
        have : (a : M₂) * x = (a : M₂) * y := congrArg Subtype.val hxy
        rw [← hu] at this
        simpa using congrArg (fun z => (↑u⁻¹ : M₂) * z) this
      obtain ⟨b, hb⟩ := (Finite.surjective_of_injective hinj) 1
      have hab : (a : M₂) * b = 1 := congrArg Subtype.val hb
      have hba : (b : M₂) * a = 1 := mul_eq_one_comm.mp hab
      exact ⟨⟨a, b, Subtype.ext hab, Subtype.ext hba⟩, rfl⟩

  haveI : NoZeroDivisors A₀ := ⟨fun {a b} h => by
    by_cases ha : a = 0
    · exact Or.inl ha
    · exact Or.inr ((hunit a ha).mul_right_eq_zero.mp h)⟩
  haveI : IsDomain A₀ := NoZeroDivisors.to_isDomain A₀
  have hF := Finite.isDomain_to_isField A₀
  have hcommS : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s := fun s hs t ht => by
    have := hF.mul_comm ⟨s, Algebra.subset_adjoin hs⟩ ⟨t, Algebra.subset_adjoin ht⟩
    exact congrArg Subtype.val this
  have hall : ∀ x y : M₂, x * y = y * x := fun x y =>
    commute_of_mem_span (S : Set M₂) hcommS (hspan ▸ Submodule.mem_top) (hspan ▸ Submodule.mem_top)
  have := congrFun (congrFun (hall (single 0 1 1) (single 1 0 1)) 0) 0
  rw [single_mul_single_same, single_mul_single_same] at this
  simp at this

theorem exists_basis_entries_mem (S : Submonoid M₂) (htr : ∀ s ∈ S, trace s ∈ k₀)
    (hspan : Submodule.span k (S : Set M₂) = ⊤) {n : M₂}
    (hnA : n ∈ Submodule.span k₀ (S : Set M₂)) (hn0 : n ≠ 0) (hnn : n * n = 0) :
    ∃ B : Module.Basis (Fin 2) k (Fin 2 → k),
      ∀ s ∈ S, ∀ i j, LinearMap.toMatrix B B (Matrix.toLin' s) i j ∈ k₀ := by
  classical

  obtain ⟨u, hu⟩ : ∃ u : Fin 2 → k, n *ᵥ u ≠ 0 := by
    by_contra h
    push Not at h
    exact hn0 (Matrix.toLin'.injective (LinearMap.ext fun v => by simpa using h v))
  set v₁ := n *ᵥ u with hv₁
  have hnv₁ : n *ᵥ v₁ = 0 := by rw [hv₁, mulVec_mulVec, hnn, zero_mulVec]

  obtain ⟨h₁, hh₁S, hh₁⟩ : ∃ h₁ ∈ S, ∀ a : k, a • v₁ ≠ h₁ *ᵥ v₁ := by
    by_contra hall
    push Not at hall
    have hline : ∀ x ∈ Submodule.span k (S : Set M₂), ∃ a : k, a • v₁ = x *ᵥ v₁ := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem s hs => exact hall s hs
      | zero => exact ⟨0, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
        exact ⟨a + b, by rw [add_smul, ha, hb, add_mulVec]⟩
      | smul c x _ hx =>
        obtain ⟨a, ha⟩ := hx
        exact ⟨c * a, by rw [mul_smul, ha, smul_mulVec]⟩

    obtain ⟨i₀, hi₀⟩ : ∃ i, v₁ i ≠ 0 := by
      by_contra h'; push Not at h'; exact hu (funext h')
    obtain ⟨a, ha⟩ := hline (vecMulVec u (Pi.single i₀ (v₁ i₀)⁻¹)) (hspan ▸ Submodule.mem_top)
    have hxu : vecMulVec u (Pi.single i₀ (v₁ i₀)⁻¹) *ᵥ v₁ = u := by
      ext i
      simp [vecMulVec, mulVec, dotProduct, Pi.single_apply, hi₀]
    rw [hxu] at ha
    apply hu
    have : n *ᵥ u = n *ᵥ (a • v₁) := by rw [ha]
    rw [← hv₁] at this
    rw [this, mulVec_smul, hnv₁, smul_zero]
  set w₂ := h₁ *ᵥ v₁ with hw₂
  have hv₁0 : v₁ ≠ 0 := hu
  have hli : LinearIndependent k ![v₁, w₂] := (LinearIndependent.pair_iff' hv₁0).mpr hh₁
  let B : Module.Basis (Fin 2) k (Fin 2 → k) :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  have hB0 : B 0 = v₁ := by
    simp [B, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hB1 : B 1 = w₂ := by
    simp [B, coe_basisOfLinearIndependentOfCardEqFinrank]

  let m : M₂ → M₂ := fun x => LinearMap.toMatrix B B (Matrix.toLin' x)
  have hm_apply : ∀ x i j, m x i j = B.repr (x *ᵥ B j) i := fun x i j => by
    simp only [m, LinearMap.toMatrix_apply, Matrix.toLin'_apply]
  have hm_mul : ∀ x y, m (x * y) = m x * m y := fun x y => by
    simp only [m, Matrix.toLin'_mul, LinearMap.toMatrix_comp B B B]
  have hm_tr : ∀ x, trace (m x) = trace x := fun x => by
    rw [← LinearMap.trace_eq_matrix_trace k B (Matrix.toLin' x),
      LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin 2)), LinearMap.toMatrix_eq_toMatrix',
      LinearMap.toMatrix'_toLin']
  refine ⟨B, ?_⟩

  have h1_00 : m h₁ 0 0 = 0 := by rw [hm_apply, hB0, ← hw₂, ← hB1, B.repr_self]; simp
  have h1_10 : m h₁ 1 0 = 1 := by rw [hm_apply, hB0, ← hw₂, ← hB1, B.repr_self]; simp

  have hn_i0 : ∀ i, m n i 0 = 0 := fun i => by rw [hm_apply, hB0, hnv₁, map_zero]; rfl
  set γ := m n 0 1 with hγ
  have hn_11 : m n 1 1 = 0 := by
    have hsum : n *ᵥ w₂ = γ • v₁ + (m n 1 1) • w₂ := by
      have := B.sum_repr (n *ᵥ w₂)
      rw [Fin.sum_univ_two, hB0, hB1] at this
      rw [hγ, hm_apply, hm_apply, hB1]
      exact this.symm
    have h0 : (m n 1 1 * γ) • v₁ + (m n 1 1 * m n 1 1) • w₂ = 0 := by
      have : n *ᵥ (n *ᵥ w₂) = 0 := by rw [mulVec_mulVec, hnn, zero_mulVec]
      rw [hsum, mulVec_add, mulVec_smul, mulVec_smul, hnv₁, smul_zero, zero_add, hsum, smul_add,
        smul_smul, smul_smul] at this
      exact this
    exact mul_self_eq_zero.mp ((LinearIndependent.pair_iff.mp hli _ _ h0).2)
  have hγtr : ∀ y, trace (n * y) = γ * m y 1 0 := fun y => by
    rw [← hm_tr, hm_mul, trace_fin_two, mul_apply, mul_apply, Fin.sum_univ_two, Fin.sum_univ_two,
      hn_i0, hn_i0, hn_11]
    ring
  have hγ0 : γ ≠ 0 := by
    intro h
    apply hn0
    have : m n = 0 := by
      ext i j
      fin_cases i <;> fin_cases j
      · exact hn_i0 0
      · exact h
      · exact hn_i0 1
      · exact hn_11
    have : Matrix.toLin' n = 0 := (LinearMap.toMatrix B B).map_eq_zero_iff.mp this
    exact Matrix.toLin'.map_eq_zero_iff.mp this
  have hγk₀ : γ ∈ k₀ := by
    have := hγtr h₁
    rw [h1_10, mul_one] at this
    rw [← this]
    exact trace_mul_mem_of_mem_span k₀ S htr hnA (Submodule.subset_span hh₁S)

  have hc : ∀ y ∈ S, m y 1 0 ∈ k₀ := fun y hy => by
    have h := trace_mul_mem_of_mem_span k₀ S htr hnA (Submodule.subset_span hy)
    rw [hγtr] at h
    have : m y 1 0 = γ⁻¹ * (γ * m y 1 0) := by rw [← mul_assoc, inv_mul_cancel₀ hγ0, one_mul]
    rw [this]
    exact k₀.mul_mem (k₀.inv_mem hγk₀) h
  have hd : ∀ s ∈ S, m s 1 1 ∈ k₀ := fun s hs => by
    have := hc (s * h₁) (S.mul_mem hs hh₁S)
    rwa [hm_mul, mul_apply, Fin.sum_univ_two, h1_00, h1_10, mul_zero, zero_add, mul_one] at this
  have ha : ∀ s ∈ S, m s 0 0 ∈ k₀ := fun s hs => by
    have h := htr s hs
    rw [← hm_tr, trace_fin_two] at h
    have : m s 0 0 = (m s 0 0 + m s 1 1) - m s 1 1 := by ring
    rw [this]
    exact k₀.sub_mem h (hd s hs)
  have hb : ∀ s ∈ S, m s 0 1 ∈ k₀ := fun s hs => by
    have := ha (s * h₁) (S.mul_mem hs hh₁S)
    rwa [hm_mul, mul_apply, Fin.sum_univ_two, h1_00, h1_10, mul_zero, zero_add, mul_one] at this
  intro s hs i j
  fin_cases i <;> fin_cases j
  · exact ha s hs
  · exact hb s hs
  · exact hc s hs
  · exact hd s hs

end Core

section R5steal

open LinearMap

variable {k : Type} [Field k]

theorem end_eq_zero_of_forall_trace_mul_eq_zero
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (X : Module.End k V) (hX : ∀ Y : Module.End k V, trace k V (Y * X) = 0) :
    X = 0 := by
  classical
  let b := Module.Free.chooseBasis k V
  apply (LinearMap.toMatrix b b).injective
  rw [map_zero]
  ext i j
  have h := hX ((LinearMap.toMatrix b b).symm (Matrix.single j i 1))
  rw [trace_eq_matrix_trace k b, Module.End.mul_eq_comp, LinearMap.toMatrix_comp b b b,
    LinearEquiv.apply_symm_apply, Matrix.trace_single_mul, one_smul] at h
  simpa using h

theorem span_range_eq_top_of_trace_eq (ρ₁ ρ₂ : ResidualGaloisRep k)
    (htr : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      trace k ρ₁.V (ρ₁.ρ σ) = trace k ρ₂.V (ρ₂.ρ σ))
    (h₂ : Submodule.span k (Set.range ⇑ρ₂.ρ) = ⊤) :
    Submodule.span k (Set.range ⇑ρ₁.ρ) = ⊤ := by
  classical
  by_contra hne
  set W : Submodule k (Module.End k ρ₁.V) := Submodule.span k (Set.range ⇑ρ₁.ρ) with hWdef
  have hEnd1 : Module.finrank k (Module.End k ρ₁.V) = 4 := by
    rw [Module.finrank_linearMap, ρ₁.finrank_eq]
  have hEnd2 : Module.finrank k (Module.End k ρ₂.V) = 4 := by
    rw [Module.finrank_linearMap, ρ₂.finrank_eq]
  have hWlt : Module.finrank k W < 4 := by
    rcases eq_or_lt_of_le (Submodule.finrank_le W) with h | h
    · exact absurd (Submodule.eq_top_of_finrank_eq h) hne
    · rwa [hEnd1] at h
  obtain ⟨t, hts, hspan, hli⟩ := exists_linearIndependent k (Set.range ⇑ρ₂.ρ)
  rw [h₂] at hspan
  let b : Module.Basis t k (Module.End k ρ₂.V) := Module.Basis.mk hli (by
    rw [Subtype.range_coe, hspan])
  haveI : Fintype t := FiniteDimensional.fintypeBasisIndex b
  have hcard : Fintype.card t = 4 := by
    rw [← Module.finrank_eq_card_basis b, hEnd2]
  choose g hg using fun w : t => hts w.2
  let x : t → W := fun w => ⟨ρ₁.ρ (g w), Submodule.subset_span ⟨g w, rfl⟩⟩
  have hdep : ¬ LinearIndependent k x := by
    intro hx
    have := hx.fintype_card_le_finrank
    omega
  obtain ⟨c, hcsum, w₀, hw₀⟩ := Fintype.not_linearIndependent_iff.mp hdep
  have hsum1 : ∑ w, c w • ρ₁.ρ (g w) = 0 := by
    have h := congrArg (Subtype.val) hcsum
    simpa using h
  set X₂ : Module.End k ρ₂.V := ∑ w, c w • (w : Module.End k ρ₂.V) with hX₂def
  have hvan : ∀ w' : t, trace k ρ₂.V ((w' : Module.End k ρ₂.V) * X₂) = 0 := by
    intro w'
    have step : trace k ρ₂.V ((w' : Module.End k ρ₂.V) * X₂) =
        ∑ w, c w * trace k ρ₁.V (ρ₁.ρ (g w') * ρ₁.ρ (g w)) := by
      rw [hX₂def, Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [mul_smul_comm, map_smul, smul_eq_mul, ← hg w', ← hg w, ← map_mul, ← map_mul,
        htr (g w' * g w), map_mul]
    rw [step]
    have : ∑ w, c w * trace k ρ₁.V (ρ₁.ρ (g w') * ρ₁.ρ (g w)) =
        trace k ρ₁.V (ρ₁.ρ (g w') * ∑ w, c w • ρ₁.ρ (g w)) := by
      rw [Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [mul_smul_comm, map_smul, smul_eq_mul]
    rw [this, hsum1, mul_zero, map_zero]
  have hall : (trace k ρ₂.V).comp (LinearMap.mulRight k X₂) = 0 :=
    LinearMap.ext_on hspan (fun Y hY => by simpa using hvan ⟨Y, hY⟩)
  have hX₂0 : X₂ = 0 := by
    refine end_eq_zero_of_forall_trace_mul_eq_zero X₂ (fun Y => ?_)
    simpa using DFunLike.congr_fun hall Y
  have hb0 : ∑ w, c w • b w = 0 := by
    have hbw : ∀ w : t, b w = (w : Module.End k ρ₂.V) := fun w => Module.Basis.mk_apply hli _ w
    calc ∑ w, c w • b w = ∑ w, c w • (w : Module.End k ρ₂.V) :=
          Finset.sum_congr rfl fun w _ => by rw [hbw]
      _ = X₂ := hX₂def.symm
      _ = 0 := hX₂0
  exact hw₀ (Fintype.linearIndependent_iff.mp b.linearIndependent c hb0 w₀)

theorem trace_eq_of_charpoly_eq (ρ₁ ρ₂ : ResidualGaloisRep k)
    (hcp : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      LinearMap.charpoly (ρ₁.ρ σ) = LinearMap.charpoly (ρ₂.ρ σ))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    trace k ρ₁.V (ρ₁.ρ σ) = trace k ρ₂.V (ρ₂.ρ σ) := by
  classical
  let b₁ := Module.finBasisOfFinrankEq k ρ₁.V ρ₁.finrank_eq
  let b₂ := Module.finBasisOfFinrankEq k ρ₂.V ρ₂.finrank_eq
  rw [trace_eq_matrix_trace k b₁, trace_eq_matrix_trace k b₂,
    Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff,
    LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix, hcp σ]

theorem isAbsolutelyIrreducible_of_charpoly_eq (ρ₁ ρ₂ : ResidualGaloisRep k)
    (hcp : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      LinearMap.charpoly (ρ₁.ρ σ) = LinearMap.charpoly (ρ₂.ρ σ))
    (h₂ : ρ₂.IsAbsolutelyIrreducible) :
    ρ₁.IsAbsolutelyIrreducible := by
  rw [ResidualGaloisRep.isAbsolutelyIrreducible_iff_span_eq_top] at h₂ ⊢
  exact span_range_eq_top_of_trace_eq ρ₁ ρ₂ (trace_eq_of_charpoly_eq ρ₁ ρ₂ hcp) h₂

end R5steal

section Wrap

open LinearMap

variable {k : Type} [Field k]

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem finite_range_rho (ρ : ResidualGaloisRep k) : (Set.range ⇑ρ.ρ).Finite := by
  classical
  obtain ⟨L, hL, hker⟩ := ρ.factorsThroughFiniteLevel
  haveI := hL
  let r : Γℚ → (L →ₐ[ℚ] AlgebraicClosure ℚ) := fun σ => σ.toAlgHom.comp L.val
  have hr : ∀ σ τ, r σ = r τ → ρ.ρ σ = ρ.ρ τ := by
    intro σ τ h
    have hfix : ∀ x ∈ L, (τ⁻¹ * σ) x = x := by
      intro x hx
      have := congrArg (fun f => f ⟨x, hx⟩) h
      change σ x = τ x at this
      rw [AlgEquiv.mul_apply, this, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    have h1 := hker _ hfix
    calc ρ.ρ σ = ρ.ρ (τ * (τ⁻¹ * σ)) := by rw [mul_inv_cancel_left]
      _ = ρ.ρ τ := by rw [map_mul, h1, mul_one]
  let F : Set.range r → Module.End k ρ.V := fun f => ρ.ρ f.2.choose
  refine (Set.finite_range F).subset ?_
  rintro _ ⟨σ, rfl⟩
  refine ⟨⟨r σ, σ, rfl⟩, ?_⟩
  exact hr _ _ (Exists.choose_spec (⟨σ, rfl⟩ : r σ ∈ Set.range r))

theorem residual_descent (k₀ : Subfield k) [Finite k₀]
    (ρbar : ResidualGaloisRep k) (habs : ρbar.IsAbsolutelyIrreducible)
    (hcoeff : ∀ σ : Γℚ, ∀ i : ℕ, (LinearMap.charpoly (ρbar.ρ σ)).coeff i ∈ k₀) :
    ∃ ρ₀ : ResidualGaloisRep ↥k₀, (ρ₀.baseChangeAlong k₀.subtype).IsEquiv ρbar := by
  classical
  let b := Module.finBasisOfFinrankEq k ρbar.V ρbar.finrank_eq
  let φ : Module.End k ρbar.V →* Matrix (Fin 2) (Fin 2) k :=
    (LinearMap.toMatrixAlgEquiv b).toAlgHom.toRingHom.toMonoidHom
  have hφ : ∀ f, φ f = LinearMap.toMatrix b b f := fun f => rfl
  let S : Submonoid (Matrix (Fin 2) (Fin 2) k) := MonoidHom.mrange (φ.comp ρbar.ρ)
  have hSset : (S : Set (Matrix (Fin 2) (Fin 2) k)) =
      (LinearMap.toMatrix b b : Module.End k ρbar.V →ₗ[k] Matrix (Fin 2) (Fin 2) k) ''
        Set.range ⇑ρbar.ρ := by
    ext s
    simp only [S, MonoidHom.coe_mrange, Set.mem_range, MonoidHom.coe_comp, Function.comp_apply,
      Set.mem_image, exists_exists_eq_and, hφ]
    rfl
  have hSmem : ∀ σ, LinearMap.toMatrix b b (ρbar.ρ σ) ∈ S := fun σ => ⟨σ, rfl⟩
  have hfin : (S : Set (Matrix (Fin 2) (Fin 2) k)).Finite := by
    rw [hSset]; exact (finite_range_rho ρbar).image _
  have htr : ∀ s ∈ S, Matrix.trace s ∈ k₀ := by
    rintro _ ⟨σ, rfl⟩
    change Matrix.trace (LinearMap.toMatrix b b (ρbar.ρ σ)) ∈ k₀
    rw [Matrix.trace_eq_neg_charpoly_coeff, LinearMap.charpoly_toMatrix]
    exact neg_mem (hcoeff σ _)
  have hspan : Submodule.span k (S : Set (Matrix (Fin 2) (Fin 2) k)) = ⊤ := by
    rw [hSset, Submodule.span_image,
      (ResidualGaloisRep.isAbsolutelyIrreducible_iff_span_eq_top ρbar).mp habs, Submodule.map_top]
    exact LinearEquiv.range (LinearMap.toMatrix b b)
  obtain ⟨n, hnA, hn0, hnn⟩ := exists_sq_eq_zero_mem_adjoin k₀ S hfin htr hspan
  have hnA' : n ∈ Submodule.span k₀ (S : Set (Matrix (Fin 2) (Fin 2) k)) := by
    rw [← Subalgebra.mem_toSubmodule, Algebra.adjoin_eq_span, Submonoid.closure_eq] at hnA
    exact hnA
  obtain ⟨B, hB⟩ := exists_basis_entries_mem k₀ S htr hspan hnA' hn0 hnn

  let m : Γℚ → Matrix (Fin 2) (Fin 2) k := fun σ =>
    LinearMap.toMatrix B B (Matrix.toLin' (LinearMap.toMatrix b b (ρbar.ρ σ)))
  have hm_mem : ∀ σ i j, m σ i j ∈ k₀ := fun σ => hB _ (hSmem σ)
  have hm_one : m 1 = 1 := by
    show LinearMap.toMatrix B B (Matrix.toLin' (LinearMap.toMatrix b b (ρbar.ρ 1))) = 1
    rw [map_one, LinearMap.toMatrix_one, Matrix.toLin'_one, LinearMap.toMatrix_id]
  have hone : ∀ i j, (((1 : Matrix (Fin 2) (Fin 2) ↥k₀) i j : ↥k₀) : k) =
      (1 : Matrix (Fin 2) (Fin 2) k) i j := fun i j => by
    rcases eq_or_ne i j with h | h <;> simp [Matrix.one_apply, h]
  have hm_mul : ∀ σ τ, m (σ * τ) = m σ * m τ := fun σ τ => by
    show LinearMap.toMatrix B B (Matrix.toLin' (LinearMap.toMatrix b b (ρbar.ρ (σ * τ)))) = _
    rw [map_mul, LinearMap.toMatrix_mul, Matrix.toLin'_mul, LinearMap.toMatrix_comp B B B]
  let M₀ : Γℚ →* Matrix (Fin 2) (Fin 2) k₀ :=
    { toFun := fun σ => Matrix.of fun i j => ⟨m σ i j, hm_mem σ i j⟩
      map_one' := by
        ext i j
        change m 1 i j = (((1 : Matrix (Fin 2) (Fin 2) ↥k₀) i j : ↥k₀) : k)
        rw [hm_one, hone]
      map_mul' := fun σ τ => by
        ext i j
        change m (σ * τ) i j = ((((Matrix.of fun i j => (⟨m σ i j, hm_mem σ i j⟩ : ↥k₀)) *
          Matrix.of fun i j => (⟨m τ i j, hm_mem τ i j⟩ : ↥k₀)) i j : ↥k₀) : k)
        rw [hm_mul, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
        simp }
  have hM₀ : ∀ σ, (M₀ σ).map k₀.subtype = m σ := fun σ => by ext i j; rfl
  obtain ⟨L, hL, hker⟩ := ρbar.factorsThroughFiniteLevel
  let ρ₀ : ResidualGaloisRep ↥k₀ :=
    { V := Fin 2 → ↥k₀
      finrank_eq := by simp
      ρ := (Matrix.toLinAlgEquiv' : Matrix (Fin 2) (Fin 2) ↥k₀ ≃ₐ[↥k₀] _).toAlgHom.toRingHom
        |>.toMonoidHom.comp M₀
      factorsThroughFiniteLevel := ⟨L, hL, fun σ hσ => by
        have h1 : M₀ σ = 1 := by
          ext i j
          change m σ i j = (((1 : Matrix (Fin 2) (Fin 2) ↥k₀) i j : ↥k₀) : k)
          rw [hone]
          change LinearMap.toMatrix B B (Matrix.toLin' (LinearMap.toMatrix b b (ρbar.ρ σ))) i j = _
          rw [hker σ hσ, LinearMap.toMatrix_one, Matrix.toLin'_one, LinearMap.toMatrix_id]
        change Matrix.toLin' (M₀ σ) = 1
        rw [h1, Matrix.toLin'_one]
        rfl⟩ }
  have hρ₀ : ∀ σ, ρ₀.ρ σ = Matrix.toLin' (M₀ σ) := fun σ => rfl
  have hcp : ∀ σ : Γℚ, LinearMap.charpoly ((ρ₀.baseChangeAlong k₀.subtype).ρ σ) =
      LinearMap.charpoly (ρbar.ρ σ) := fun σ => by
    have h1 : LinearMap.charpoly ((ρ₀.baseChangeAlong k₀.subtype).ρ σ) =
        (LinearMap.charpoly (ρ₀.ρ σ)).map k₀.subtype := by
      letI : Algebra ↥k₀ k := k₀.subtype.toAlgebra
      exact LinearMap.charpoly_baseChange _ _
    rw [h1, hρ₀, Matrix.charpoly_toLin', ← Matrix.charpoly_map, hM₀]
    simp only [m, LinearMap.charpoly_toMatrix, Matrix.charpoly_toLin']
  refine ⟨ρ₀, ResidualGaloisRep.isEquiv_of_isAbsolutelyIrreducible_of_charpoly_eq _ _
    (isAbsolutelyIrreducible_of_charpoly_eq _ ρbar hcp habs) habs hcp⟩

end Wrap

end W3ResdescSol

theorem solution {k : Type} [Field k] (k₀ : Subfield k) [Finite ↥k₀]
    (ρbar : ResidualGaloisRep k) (habs : ρbar.IsAbsolutelyIrreducible)
    (hcoeff : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ i : ℕ,
      (LinearMap.charpoly (ρbar.ρ σ)).coeff i ∈ k₀) :
    ∃ ρ₀ : ResidualGaloisRep ↥k₀,
      (ρ₀.baseChangeAlong k₀.subtype).IsEquiv ρbar :=
  W3ResdescSol.residual_descent k₀ ρbar habs hcoeff

end S_ResidualGaloisRep_exists_baseChangeAlong_subtype_isEquiv_of_forall_charpoly_coeff_mem
end P2MW
export P2MW.S_ResidualGaloisRep_exists_baseChangeAlong_subtype_isEquiv_of_forall_charpoly_coeff_mem (solution)
