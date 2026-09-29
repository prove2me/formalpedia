-- Prove2me | solution 1 for ResidualGaloisRep.exists_index_two_stable_line_of_trace_frobenius_eq_zero_of_modEq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/c2a618ef-e1d5-5c3c-bccd-0b24e8c21363

import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Theorems.Thm_Subgroup_exists_prime_isFrobeniusAt_conj_pow_mem_conj_mem_of_isOpen
import Theorems.Thm_ValuationSubring_IsFrobeniusAt_apply_eq_pow_of_pow_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_exists_index_two_stable_line_of_trace_frobenius_eq_zero_of_modEq_two
p2m_attr_erase "instance" "FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false

section PieceSliceThree

namespace TraceVanishingCoset

open Module

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

private theorem pair_linearIndependent_of_notMem_span {x y : V} (hx : x ≠ 0) (hy : y ∉ Submodule.span K {x}) :
    LinearIndependent K ![x, y] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have ht : t = 0 := by
    by_contra ht
    apply hy
    rw [Submodule.mem_span_singleton]
    refine ⟨-(s / t), ?_⟩
    have : t • y = -(s • x) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hst
    calc (-(s / t)) • x = t⁻¹ • (-(s • x)) := by rw [neg_smul, smul_neg, smul_smul, div_eq_inv_mul]
      _ = t⁻¹ • (t • y) := by rw [this]
      _ = y := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
  subst ht
  simp only [zero_smul, add_zero, smul_eq_zero] at hst
  exact ⟨hst.resolve_right hx, rfl⟩

private theorem exists_notMem_span_singleton (hV : finrank K V = 2) (x : V) :
    ∃ y : V, y ∉ Submodule.span K {x} := by
  by_contra hcon
  have h : ∀ y, y ∈ Submodule.span K {x} := fun y => by_contra fun hy => hcon ⟨y, hy⟩
  have htop : Submodule.span K {x} = ⊤ := Submodule.eq_top_iff'.mpr h
  have h1 : finrank K (Submodule.span K {x}) ≤ 1 := by
    simpa using finrank_span_le_card ({x} : Set V)
  rw [htop, finrank_top, hV] at h1
  omega

private theorem span_singleton_ne_bot_ne_top_stable (hV : finrank K V = 2) {v : V} (hv : v ≠ 0)
    (S : Set (Module.End K V)) (hS : ∀ f ∈ S, ∃ μ : K, f v = μ • v) :
    ∃ L : Submodule K V, L ≠ ⊥ ∧ L ≠ ⊤ ∧ ∀ f ∈ S, ∀ x ∈ L, f x ∈ L := by
  refine ⟨Submodule.span K {v}, ?_, ?_, ?_⟩
  · rwa [Ne, Submodule.span_singleton_eq_bot]
  · intro htop
    have h1 := finrank_span_singleton (K := K) hv
    rw [htop, finrank_top, hV] at h1
    omega
  · intro f hf x hx
    obtain ⟨μ, hμ⟩ := hS f hf
    rw [Submodule.mem_span_singleton] at hx ⊢
    obtain ⟨t, rfl⟩ := hx
    exact ⟨t * μ, by rw [map_smul, hμ, smul_smul]⟩

variable [IsAlgClosed K] {G : Type*} [Group G]

private theorem exists_basis_eigen (hV : finrank K V = 2) (h2 : (2 : K) ≠ 0) (Z : Module.End K V)
    (hZinj : Function.Injective Z) (htr : LinearMap.trace K V Z = 0) :
    ∃ (b : Basis (Fin 2) K V) (α : K), α ≠ 0 ∧ Z (b 0) = α • b 0 ∧ Z (b 1) = (-α) • b 1 := by
  haveI : FiniteDimensional K V := Module.finite_of_finrank_eq_succ hV
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by rw [hV]; norm_num)
  obtain ⟨α, hα⟩ := Module.End.exists_eigenvalue Z
  obtain ⟨u, hu⟩ := hα.exists_hasEigenvector
  have hu0 : u ≠ 0 := hu.2
  have hZu : Z u = α • u := hu.apply_eq_smul
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hZu
    exact hu0 (hZinj (by rw [hZu, map_zero]))
  obtain ⟨w, hw⟩ := exists_notMem_span_singleton hV u
  have hli : LinearIndependent K ![u, w] := pair_linearIndependent_of_notMem_span hu0 hw
  let b₁ : Basis (Fin 2) K V :=
    basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hV])
  have hb₁ : ⇑b₁ = ![u, w] := coe_basisOfLinearIndependentOfCardEqFinrank hli _
  have hb₁0 : b₁ 0 = u := by rw [hb₁]; rfl
  have hb₁1 : b₁ 1 = w := by rw [hb₁]; rfl

  set β : K := b₁.repr (Z w) 0 with hβ
  set γ : K := b₁.repr (Z w) 1 with hγ
  have hZw : Z w = β • u + γ • w := by
    have := b₁.sum_repr (Z w)
    rw [Fin.sum_univ_two, hb₁0, hb₁1] at this
    exact this.symm

  have hru : b₁.repr u 0 = 1 := by rw [← hb₁0, b₁.repr_self]; simp
  have htrace : α + γ = 0 := by
    have h := htr
    rw [LinearMap.trace_eq_matrix_trace K b₁, Matrix.trace_fin_two, LinearMap.toMatrix_apply,
      LinearMap.toMatrix_apply, hb₁0, hb₁1, hZu, map_smul, Finsupp.smul_apply, hru, smul_eq_mul,
      mul_one] at h
    exact h
  have hγα : γ = -α := by linear_combination htrace

  set u' : V := Z w - α • w with hu'
  have hu'eq : u' = β • u + (-(2 * α)) • w := by
    rw [hu', hZw, hγα]; module
  have hZu' : Z u' = (-α) • u' := by
    rw [hu'eq, map_add, map_smul, map_smul, hZu, hZw, hγα]; module
  have hli' : LinearIndependent K ![u, u'] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [hu'eq] at hst
    have hst' : (s + t * β) • u + (t * (-(2 * α))) • w = 0 := by
      rw [← hst]; module
    obtain ⟨h1, h2'⟩ := LinearIndependent.pair_iff.mp hli _ _ hst'
    have ht : t = 0 := by
      rcases mul_eq_zero.mp h2' with h | h
      · exact h
      · exact absurd h (by simpa [h2] using hα0)
    subst ht
    exact ⟨by simpa using h1, rfl⟩
  let b : Basis (Fin 2) K V :=
    basisOfLinearIndependentOfCardEqFinrank hli' (by rw [Fintype.card_fin, hV])
  have hb : ⇑b = ![u, u'] := coe_basisOfLinearIndependentOfCardEqFinrank hli' _
  refine ⟨b, α, hα0, ?_, ?_⟩
  · rw [show b 0 = u by rw [hb]; rfl]; exact hZu
  · rw [show b 1 = u' by rw [hb]; rfl]; exact hZu'

private theorem exists_submodule_ne_bot_ne_top_of_forall_notMem_trace_eq_zero (hV : finrank K V = 2)
    (h2 : (2 : K) ≠ 0) (ρ : G →* Module.End K V) (H : Subgroup G) {z : G} (hz : z ∉ H)
    (htr : ∀ g : G, g ∉ H → LinearMap.trace K V (ρ g) = 0) :
    ∃ L : Submodule K V, L ≠ ⊥ ∧ L ≠ ⊤ ∧ ∀ h ∈ H, ∀ x ∈ L, ρ h x ∈ L := by

  have hZinj : Function.Injective (ρ z) := by
    intro x y hxy
    have := congrArg (ρ z⁻¹) hxy
    rwa [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply, Module.End.one_apply] at this
  obtain ⟨b, α, hα0, hb0, hb1⟩ := exists_basis_eigen hV h2 (ρ z) hZinj (htr z hz)

  set A : G → Matrix (Fin 2) (Fin 2) K := fun g => LinearMap.toMatrix b b (ρ g) with hA
  have hAmul : ∀ g g' : G, A (g * g') = A g * A g' := fun g g' => by
    simp only [hA, map_mul, LinearMap.toMatrix_mul]
  have hAtr : ∀ g : G, LinearMap.trace K V (ρ g) = (A g).trace := fun g =>
    LinearMap.trace_eq_matrix_trace K b (ρ g)
  have hAz : ∀ i j, A z i j = if i = j then (if i = 0 then α else -α) else 0 := by
    intro i j
    simp only [hA, LinearMap.toMatrix_apply]
    fin_cases i <;> fin_cases j <;> simp [hb0, hb1, Basis.repr_self]

  have hzh : ∀ h ∈ H, z * h ∉ H := fun h hh hzh => hz (by simpa using H.mul_mem hzh (H.inv_mem hh))

  have hdiag : ∀ h ∈ H, A h 0 0 = A h 1 1 := by
    intro h hh
    have := htr (z * h) (hzh h hh)
    rw [hAtr, hAmul, Matrix.trace_fin_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Fin.sum_univ_two, hAz, hAz, hAz, hAz] at this
    simp only [if_true, if_false, zero_mul, add_zero, zero_add, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one,
      neg_mul, Fin.isValue, one_ne_zero] at this
    have : α * (A h 0 0 - A h 1 1) = 0 := by linear_combination this
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hα0
    · linear_combination h'

  have hoff : ∀ h ∈ H, ∀ h' ∈ H, A h 0 1 * A h' 1 0 = A h 1 0 * A h' 0 1 := by
    intro h hh h' hh'
    have htr' := htr (z * (h * h')) (hzh _ (H.mul_mem hh hh'))
    rw [hAtr, hAmul, hAmul, Matrix.trace_fin_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Fin.sum_univ_two, hAz, hAz, hAz, hAz] at htr'
    simp only [if_true, if_false, zero_mul, add_zero, zero_add, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one,
      neg_mul, Fin.isValue, one_ne_zero, Matrix.mul_apply, Fin.sum_univ_two] at htr'
    have hd := hdiag h hh
    have hd' := hdiag h' hh'
    have : α * (A h 0 1 * A h' 1 0 - A h 1 0 * A h' 0 1) = 0 := by
      linear_combination htr' - α * (A h' 0 0) * hd - α * (A h 1 1) * hd'
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hα0
    · linear_combination h0

  have happly : ∀ (h : G) (x y : K), ρ h (x • b 0 + y • b 1) =
      (A h 0 0 * x + A h 0 1 * y) • b 0 + (A h 1 0 * x + A h 1 1 * y) • b 1 := by
    intro h x y
    have key : ∀ j, ρ h (b j) = A h 0 j • b 0 + A h 1 j • b 1 := by
      intro j
      have := b.sum_repr (ρ h (b j))
      rw [Fin.sum_univ_two] at this
      rw [← this]
      simp only [hA, LinearMap.toMatrix_apply]
    rw [map_add, map_smul, map_smul, key 0, key 1]; module

  by_cases hcase : ∀ h ∈ H, A h 1 0 = 0
  ·
    refine span_singleton_ne_bot_ne_top_stable hV (b.ne_zero 0) {f | ∃ h ∈ H, f = ρ h} ?_ |>.imp
      fun L hL => ⟨hL.1, hL.2.1, fun h hh x hx => hL.2.2 (ρ h) ⟨h, hh, rfl⟩ x hx⟩
    rintro f ⟨h, hh, rfl⟩
    refine ⟨A h 0 0, ?_⟩
    have := happly h 1 0
    rw [one_smul, zero_smul, add_zero] at this
    rw [this, hcase h hh]; simp
  · obtain ⟨h₀, hh₀, hc₀⟩ : ∃ h₀ ∈ H, A h₀ 1 0 ≠ 0 := by
      simpa only [not_forall, exists_prop] using hcase
    obtain ⟨δ, hδ⟩ : ∃ δ : K, δ * δ = A h₀ 0 1 * A h₀ 1 0 := by
      obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq (A h₀ 0 1 * A h₀ 1 0) two_pos
      exact ⟨δ, by rw [← hδ]; ring⟩
    have hv0 : δ • b 0 + A h₀ 1 0 • b 1 ≠ 0 := by
      intro h0
      have h1 := congrArg (fun x => b.repr x 1) h0
      exact hc₀ (by simpa [Finsupp.single_apply] using h1)
    refine span_singleton_ne_bot_ne_top_stable hV hv0 {f | ∃ h ∈ H, f = ρ h} ?_ |>.imp
      fun L hL => ⟨hL.1, hL.2.1, fun h hh x hx => hL.2.2 (ρ h) ⟨h, hh, rfl⟩ x hx⟩
    rintro f ⟨h, hh, rfl⟩
    have hprop : A h 0 1 * A h₀ 1 0 = A h 1 0 * A h₀ 0 1 := hoff h hh h₀ hh₀
    have hd : A h 1 1 = A h 0 0 := (hdiag h hh).symm
    refine ⟨(A h 1 0 * δ + A h 1 1 * A h₀ 1 0) / A h₀ 1 0, ?_⟩
    have e1 : (A h 1 0 * δ + A h 1 1 * A h₀ 1 0) / A h₀ 1 0 * A h₀ 1 0 = A h 1 0 * δ + A h 1 1 * A h₀ 1 0 :=
      div_mul_cancel₀ _ hc₀
    have e0 : (A h 1 0 * δ + A h 1 1 * A h₀ 1 0) / A h₀ 1 0 * δ = A h 0 0 * δ + A h 0 1 * A h₀ 1 0 := by
      rw [div_mul_eq_mul_div, div_eq_iff hc₀]
      linear_combination A h 1 0 * hδ + (A h₀ 1 0 * δ) * hd - A h₀ 1 0 * hprop
    rw [happly, smul_add, smul_smul, smul_smul, e0, e1]

end TraceVanishingCoset

namespace ResidualGaloisRep
p2m_export "ResidualGaloisRep" "baseChange factorsThroughFiniteLevel finrank_eq V ρ"
p2m_open "ResidualGaloisRep"

open scoped TensorProduct

private theorem false_of_index_eq_two_of_forall_notMem_trace_eq_zero {k : Type} [Field k] (ρbar : ResidualGaloisRep k)
    (h2 : (2 : k) ≠ 0)
    (h3 : ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
        ∀ V : Submodule K (ρbar.baseChange K).V,
          (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤)
    (Gs : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hGs : Gs.index = 2)
    {z : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hz : z ∉ Gs)
    (htr : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∉ Gs →
      LinearMap.trace k ρbar.V (ρbar.ρ σ) = 0) : False := by
  set K : Type := AlgebraicClosure k
  have h2K : (2 : K) ≠ 0 := by
    intro h
    apply h2
    apply (algebraMap k K).injective
    rw [map_ofNat, map_zero]
    exact h
  have htrK : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∉ Gs →
      LinearMap.trace K (ρbar.baseChange K).V ((ρbar.baseChange K).ρ σ) = 0 := by
    intro σ hσ
    show LinearMap.trace K (K ⊗[k] ρbar.V) ((ρbar.ρ σ).baseChange K) = 0
    rw [LinearMap.trace_baseChange, htr σ hσ, map_zero]
  obtain ⟨L, hLbot, hLtop, hL⟩ := TraceVanishingCoset.exists_submodule_ne_bot_ne_top_of_forall_notMem_trace_eq_zero
    (ρbar.baseChange K).finrank_eq h2K (ρbar.baseChange K).ρ Gs hz htrK
  rcases h3 K Gs hGs L hL with h | h
  · exact hLbot h
  · exact hLtop h

end ResidualGaloisRep

open Polynomial

namespace ResidualGaloisRep
p2m_export "ResidualGaloisRep" "baseChange factorsThroughFiniteLevel finrank_eq V ρ"
p2m_open "ResidualGaloisRep"

namespace CubicTwist

section Plane

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V]

private theorem exists_mul_self_eq_smul_one (hV : Module.finrank k V = 2) (f : Module.End k V)
    (hf : LinearMap.trace k V f = 0) : ∃ c : k, f * f = c • (1 : Module.End k V) := by
  haveI : Module.Finite k V := Module.finite_of_finrank_eq_succ hV
  let b : Module.Basis (Fin 2) k V := Module.finBasisOfFinrankEq k V hV
  rw [LinearMap.trace_eq_matrix_trace k b, Matrix.trace_fin_two] at hf
  set A := LinearMap.toMatrix b b f with hA
  refine ⟨-(A 0 0 * A 1 1 - A 0 1 * A 1 0), ?_⟩
  apply (LinearMap.toMatrix b b).injective
  rw [LinearMap.toMatrix_mul b, map_smul, LinearMap.toMatrix_one b, ← hA]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (A 0 0) * hf
  · linear_combination (A 0 1) * hf
  · linear_combination (A 1 0) * hf
  · linear_combination (A 1 1) * hf

private theorem trace_pow_eq_zero_of_odd (hV : Module.finrank k V = 2) (f : Module.End k V)
    (hf : LinearMap.trace k V f = 0) {n : ℕ} (hn : Odd n) : LinearMap.trace k V (f ^ n) = 0 := by
  obtain ⟨c, hc⟩ := exists_mul_self_eq_smul_one hV f hf
  obtain ⟨m, rfl⟩ := hn
  rw [pow_succ, pow_mul, sq, hc, _root_.smul_pow, one_pow, smul_mul_assoc, one_mul, map_smul, hf, smul_zero]

end Plane

section CubeRoot

private theorem exists_isPrimitiveRoot_three : ∃ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ 3 := by
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (cyclotomic 3 (AlgebraicClosure ℚ))
    (degree_cyclotomic_pos 3 _ (by norm_num)).ne'
  exact ⟨ζ, isRoot_cyclotomic_iff.mp hζ⟩

variable {ζ : AlgebraicClosure ℚ}

private theorem pow_apply_eq_self (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ζ = ζ) (j : ℕ) :
    (σ ^ j) ζ = ζ := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, hσ, ih]

private theorem apply_eq_self_or_eq_sq (hζ : IsPrimitiveRoot ζ 3) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    σ ζ = ζ ∨ σ ζ = ζ ^ 2 := by
  obtain ⟨i, hi, hiζ⟩ := hζ.eq_pow_of_pow_eq_one (ξ := σ ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one])
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi' with rfl | rfl | rfl
  · rw [pow_zero] at hiζ
    exact absurd hiζ.symm ((hζ.map_of_injective σ.injective).ne_one (by norm_num))
  · exact Or.inl (by rw [← hiζ, pow_one])
  · exact Or.inr hiζ.symm

private theorem sq_ne_self (hζ : IsPrimitiveRoot ζ 3) : ζ ^ 2 ≠ ζ := fun h =>
  absurd (hζ.pow_inj (by norm_num) (by norm_num) (h.trans (pow_one ζ).symm)) (by norm_num)

private theorem orbit_eq (hζ : IsPrimitiveRoot ζ 3) :
    MulAction.orbit (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ζ = {ζ, ζ ^ 2} := by
  ext y
  constructor
  · rintro ⟨σ, rfl⟩
    show σ ζ ∈ ({ζ, ζ ^ 2} : Set (AlgebraicClosure ℚ))
    rcases apply_eq_self_or_eq_sq hζ σ with h | h
    · rw [h]; exact Set.mem_insert ζ _
    · rw [h]; exact Set.mem_insert_of_mem ζ (Set.mem_singleton _)
  · intro hy
    have key : ∀ y : AlgebraicClosure ℚ, IsPrimitiveRoot y 3 →
        y ∈ MulAction.orbit (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ζ := fun y hy =>
      (Normal.minpoly_eq_iff_mem_orbit (F := ℚ) (E := AlgebraicClosure ℚ)).mp
        (by rw [← cyclotomic_eq_minpoly_rat hy (by norm_num), ← cyclotomic_eq_minpoly_rat hζ (by norm_num)])
    rcases hy with h | h
    · rw [h]; exact MulAction.mem_orbit_self ζ
    · rw [Set.mem_singleton_iff] at h
      rw [h]; exact key _ (hζ.pow_of_coprime 2 (by norm_num))

private theorem index_stabilizer_eq_two (hζ : IsPrimitiveRoot ζ 3) :
    (MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ζ).index = 2 := by
  rw [MulAction.index_stabilizer, orbit_eq hζ, Set.ncard_pair (sq_ne_self hζ).symm]

private theorem exists_notMem_stabilizer (hζ : IsPrimitiveRoot ζ 3) :
    ∃ z : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      z ∉ MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ζ := by
  by_contra hall
  push Not at hall
  have htop : MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ζ = ⊤ :=
    (Subgroup.eq_top_iff' _).mpr hall
  have h := index_stabilizer_eq_two hζ
  rw [htop, Subgroup.index_top] at h
  exact absurd h (by norm_num)

end CubeRoot

section Transfer

variable {k : Type} [Field k]

private theorem trace_conj_eq (ρbar : ResidualGaloisRep k) (g τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.trace k ρbar.V (ρbar.ρ (g * τ * g⁻¹)) = LinearMap.trace k ρbar.V (ρbar.ρ τ) := by
  rw [ρbar.ρ.map_mul, ρbar.ρ.map_mul, LinearMap.trace_mul_comm, ← mul_assoc, ← ρbar.ρ.map_mul,
    inv_mul_cancel, ρbar.ρ.map_one, one_mul]

private theorem trace_eq_zero_of_apply_ne (N : ℕ) [NeZero N] (S : Finset ℕ) (ρbar : ResidualGaloisRep k)
    (htr0 : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ N → ℓ % 3 = 2 →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
          LinearMap.trace k ρbar.V (ρbar.ρ τ) = 0)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ 3)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ζ ≠ ζ) :
    LinearMap.trace k ρbar.V (ρbar.ρ σ) = 0 := by
  classical

  obtain ⟨L, hLfd, hL⟩ := ρbar.factorsThroughFiniteLevel
  haveI : FiniteDimensional ℚ L := hLfd
  have hζint : IsIntegral ℚ ζ :=
    IsIntegral.of_pow (by norm_num : 0 < 3) (by rw [hζ.pow_eq_one]; exact isIntegral_one)
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {ζ} : IntermediateField ℚ (AlgebraicClosure ℚ)) :=
    IntermediateField.adjoin.finiteDimensional hζint
  let F : IntermediateField ℚ (AlgebraicClosure ℚ) := L ⊔ IntermediateField.adjoin ℚ {ζ}
  haveI : FiniteDimensional ℚ F := IntermediateField.finiteDimensional_sup L _
  have hFopen : IsOpen (F.fixingSubgroup : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :=
    IntermediateField.fixingSubgroup_isOpen F
  have hζF : ζ ∈ F :=
    (le_sup_right : IntermediateField.adjoin ℚ {ζ} ≤ F) (IntermediateField.subset_adjoin ℚ {ζ} rfl)
  have hρfix : ∀ u ∈ F.fixingSubgroup, ρbar.ρ u = 1 := fun u hu =>
    hL u fun x hx => (IntermediateField.mem_fixingSubgroup_iff F u).mp hu x ((le_sup_left : L ≤ F) hx)
  have hζfix : ∀ u ∈ F.fixingSubgroup, u ζ = ζ := fun u hu =>
    (IntermediateField.mem_fixingSubgroup_iff F u).mp hu ζ hζF

  have hM : 0 < 3 * N * (S.erase 0).prod id :=
    Nat.mul_pos (Nat.mul_pos (by norm_num) (Nat.pos_of_ne_zero (NeZero.ne N)))
      (Finset.prod_pos fun s hs => Nat.pos_of_ne_zero (Finset.ne_of_mem_erase hs))

  obtain ⟨ℓ, A, τ, g, n, j, hℓ, hℓM, hA, hτ, hmem, -⟩ :=
    Subgroup.exists_prime_isFrobeniusAt_conj_pow_mem_conj_mem_of_isOpen F.fixingSubgroup hFopen σ hM
  have h3M : 3 ∣ 3 * N * (S.erase 0).prod id := dvd_mul_of_dvd_left (dvd_mul_right 3 N) _
  have hNM : N ∣ 3 * N * (S.erase 0).prod id := dvd_mul_of_dvd_left (dvd_mul_left N 3) _
  have hℓN : ¬ ℓ ∣ N := fun h => hℓM (h.trans hNM)
  have hℓS : ℓ ∉ S := fun hS => hℓM (dvd_mul_of_dvd_right
    (Finset.dvd_prod_of_mem id (Finset.mem_erase.mpr ⟨hℓ.ne_zero, hS⟩)) (3 * N))
  have h3ℓ : ¬ 3 ∣ ℓ := fun h =>
    hℓM (((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).mp h) ▸ h3M)
  have hcop : Nat.Coprime 3 ℓ := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3ℓ

  have hτu : τ (g⁻¹ ζ) = (g⁻¹ ζ) ^ ℓ :=
    ValuationSubring.IsFrobeniusAt.apply_eq_pow_of_pow_eq_one A τ ℓ 3 hA hτ hcop (g⁻¹ ζ)
      (by rw [← map_pow, hζ.pow_eq_one, map_one])
  have hτ'ζ : (g * τ * g⁻¹) ζ = ζ ^ ℓ := by
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hτu, map_pow, ← AlgEquiv.mul_apply, mul_inv_cancel,
      AlgEquiv.one_apply]

  have hconj : g * τ ^ n * g⁻¹ = (g * τ ^ n * g⁻¹ * σ⁻¹) * σ := by group
  have hmove : ((g * τ * g⁻¹) ^ n) ζ ≠ ζ := by
    intro h
    rw [conj_pow, hconj, AlgEquiv.mul_apply] at h
    apply hσ
    calc σ ζ = ((g * τ ^ n * g⁻¹ * σ⁻¹)⁻¹ * (g * τ ^ n * g⁻¹ * σ⁻¹)) (σ ζ) := by
          rw [inv_mul_cancel, AlgEquiv.one_apply]
      _ = (g * τ ^ n * g⁻¹ * σ⁻¹)⁻¹ ζ := by rw [AlgEquiv.mul_apply, h]
      _ = ζ := hζfix _ (F.fixingSubgroup.inv_mem hmem)
  have hτ'ne : (g * τ * g⁻¹) ζ ≠ ζ := fun h => hmove (pow_apply_eq_self _ h n)

  have hℓmod : ℓ % 3 = 2 := by
    have h0 : ℓ % 3 ≠ 0 := fun h => h3ℓ (Nat.dvd_of_mod_eq_zero h)
    have h1 : ℓ % 3 ≠ 1 := fun h => hτ'ne (by
      rw [hτ'ζ, ← Nat.div_add_mod ℓ 3, h, pow_succ, pow_mul, hζ.pow_eq_one, one_pow, one_mul])
    have h2 : ℓ % 3 < 3 := Nat.mod_lt ℓ (by norm_num)
    omega

  have hτ'sq : (g * τ * g⁻¹) ζ = ζ ^ 2 := (apply_eq_self_or_eq_sq hζ _).resolve_left hτ'ne
  have hodd : Odd n := by
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ho
    · exfalso
      apply hmove
      have hsq : ((g * τ * g⁻¹) ^ 2) ζ = ζ := by
        rw [pow_two, AlgEquiv.mul_apply, hτ'sq, map_pow, hτ'sq, ← pow_mul,
          show (2 * 2 : ℕ) = 3 + 1 by norm_num, pow_succ, hζ.pow_eq_one, one_mul]
      rw [hm, ← two_mul, pow_mul]
      exact pow_apply_eq_self _ hsq m
    · exact ho

  have hτtr : LinearMap.trace k ρbar.V (ρbar.ρ (g * τ * g⁻¹)) = 0 := by
    rw [trace_conj_eq]
    exact htr0 ℓ hℓ hℓS hℓN hℓmod A hA τ hτ
  have hσeq : ρbar.ρ σ = ρbar.ρ (g * τ * g⁻¹) ^ n := by
    rw [← map_pow, conj_pow, hconj, map_mul, hρfix _ hmem, one_mul]
  rw [hσeq]
  exact trace_pow_eq_zero_of_odd ρbar.finrank_eq _ hτtr hodd

end Transfer

end CubicTwist

private theorem false_of_forall_trace_frobenius_eq_zero_of_modEq_two (N : ℕ) [NeZero N] (S : Finset ℕ)
    (k : Type) [Field k] [CharP k 3] (ρbar : ResidualGaloisRep k)
    (h3 : ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
        ∀ V : Submodule K (ρbar.baseChange K).V,
          (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤)
    (htr0 : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ N → ℓ % 3 = 2 →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
          LinearMap.trace k ρbar.V (ρbar.ρ τ) = 0) : False := by
  obtain ⟨ζ, hζ⟩ := CubicTwist.exists_isPrimitiveRoot_three
  obtain ⟨z, hz⟩ := CubicTwist.exists_notMem_stabilizer hζ
  have h2 : (2 : k) ≠ 0 := fun h => by
    have h' : ((2 : ℕ) : k) = 0 := by exact_mod_cast h
    have h'' := (CharP.cast_eq_zero_iff k 3 2).mp h'
    omega
  exact false_of_index_eq_two_of_forall_notMem_trace_eq_zero ρbar h2 h3
    (MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ζ)
    (CubicTwist.index_stabilizer_eq_two hζ) hz
    fun σ hσ => CubicTwist.trace_eq_zero_of_apply_ne N S ρbar htr0 hζ σ
      (by rwa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at hσ)

end ResidualGaloisRep

end PieceSliceThree

namespace Ws23
namespace E3

theorem main
    (k : Type) [Field k] [CharP k 3] (ρbar : ResidualGaloisRep k)
    (n : ℕ → ℤ) (S : Set ℕ) (hS : S.Finite)
    (htr : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.trace k ρbar.V (ρbar.ρ σ) = (n ℓ : k))
    (h0 : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ℓ ≡ 2 [MOD 3] → (n ℓ : k) = 0) :
    ¬ ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
        ∀ V : Submodule K (ρbar.baseChange K).V,
          (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤ := by
  intro h3
  refine ResidualGaloisRep.false_of_forall_trace_frobenius_eq_zero_of_modEq_two 1 hS.toFinset k ρbar h3 ?_
  intro ℓ hℓ hℓS _ hmod A hA τ hτ
  have hℓS' : ℓ ∉ S := fun h => hℓS (hS.mem_toFinset.2 h)
  rw [htr ℓ hℓ hℓS' A hA τ hτ]
  exact h0 ℓ hℓ hℓS' (show ℓ % 3 = 2 % 3 by rw [hmod])

end Ws23.E3

theorem solution
    (k : Type) [Field k] [CharP k 3] (ρbar : ResidualGaloisRep k)
    (n : ℕ → ℤ) (S : Set ℕ) (hS : S.Finite)
    (htr : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.trace k ρbar.V (ρbar.ρ σ) = (n ℓ : k))
    (h0 : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ℓ ≡ 2 [MOD 3] → (n ℓ : k) = 0) :
    ¬ ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
        ∀ V : Submodule K (ρbar.baseChange K).V,
          (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤ :=
  Ws23.E3.main k ρbar n S hS htr h0

end S_ResidualGaloisRep_exists_index_two_stable_line_of_trace_frobenius_eq_zero_of_modEq_two
end P2MW
export P2MW.S_ResidualGaloisRep_exists_index_two_stable_line_of_trace_frobenius_eq_zero_of_modEq_two (solution)
