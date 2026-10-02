-- Prove2me | solution 1 for Transcendence.hermite_basis
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-02T10:12:10.033496+00:00
-- url     : https://prove2.me/submissions/24ff80ab-a856-4516-b0aa-77f051ad2b23

import Mathlib

/-!
# Hermite interpolation over a field of characteristic `0`

For a finite set `E` of nodes and `S₀ ∈ ℕ`, the jet map `q ↦ (q^{(k)}(ζ))_{ζ ∈ E, k < S₀}` on
polynomials of degree `< |E|·S₀` is injective: a nonzero such `q` would have every `ζ ∈ E` as a
root of multiplicity `≥ S₀` (characteristic `0`), hence at least `|E|·S₀` roots. Both sides have
dimension `|E|·S₀`, so the jet map is a linear isomorphism, and the Hermite basis `b_{ζ,k}` is the
preimage of the standard basis.
-/

namespace HermiteBasis

open Polynomial

variable {K : Type*} [Field K]

/-- The jet map on polynomials of degree `< card E * S₀`. -/
noncomputable def jetMap (E : Finset K) (S₀ : ℕ) :
    degreeLT K (E.card * S₀) →ₗ[K] (↥E × Fin S₀ → K) :=
  LinearMap.pi fun x => leval (x.1 : K) ∘ₗ (derivative ^ (x.2 : ℕ)) ∘ₗ
    (degreeLT K (E.card * S₀)).subtype

lemma jetMap_apply (E : Finset K) (S₀ : ℕ) (q : degreeLT K (E.card * S₀)) (x : ↥E × Fin S₀) :
    jetMap E S₀ q x = (derivative^[x.2] (q : K[X])).eval (x.1 : K) := by
  simp [jetMap, Module.End.pow_apply]

/-- A polynomial of degree `< card E * S₀` whose jets of order `< S₀` vanish on `E` is zero. -/
lemma eq_zero_of_jets [CharZero K] {E : Finset K} {S₀ : ℕ} {q : K[X]}
    (hq : q ∈ degreeLT K (E.card * S₀)) (hj : ∀ ζ ∈ E, ∀ k < S₀, (derivative^[k] q).eval ζ = 0) :
    q = 0 := by
  classical
  by_contra h0
  have hmult : ∀ ζ ∈ E, S₀ ≤ q.rootMultiplicity ζ := by
    intro ζ hζ
    rcases Nat.eq_zero_or_pos S₀ with hS | hS
    · simp [hS]
    · have := (lt_rootMultiplicity_iff_isRoot_iterate_derivative (n := S₀ - 1) h0).mpr
        (fun m hm => hj ζ hζ m (by omega))
      omega
  have hle : S₀ • E.val ≤ q.roots := by
    rw [Multiset.le_iff_count]
    intro a
    rw [Multiset.count_nsmul, count_roots]
    by_cases ha : a ∈ E
    · rw [Multiset.count_eq_one_of_mem E.nodup ha, mul_one]
      exact hmult a ha
    · rw [Multiset.count_eq_zero_of_notMem ha, mul_zero]
      exact Nat.zero_le _
  have h1 := Multiset.card_le_card hle
  rw [Multiset.card_nsmul, Finset.card_val] at h1
  have h2 := card_roots' q
  have h3 : q.natDegree < E.card * S₀ := (natDegree_lt_iff_degree_lt h0).mpr (mem_degreeLT.mp hq)
  rw [mul_comm] at h1
  omega

lemma jetMap_injective [CharZero K] (E : Finset K) (S₀ : ℕ) : Function.Injective (jetMap E S₀) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro q hq
  have h := eq_zero_of_jets q.2 fun ζ hζ k hk => by
    have := congrFun hq (⟨ζ, hζ⟩, ⟨k, hk⟩)
    rwa [jetMap_apply] at this
  exact Subtype.ext h

instance finiteDimensional_degreeLT (p : ℕ) : FiniteDimensional K (degreeLT K p) :=
  (degreeLTEquiv K p).symm.finiteDimensional

/-- The jet map is a linear isomorphism (Hermite interpolation). -/
noncomputable def jetEquiv [CharZero K] (E : Finset K) (S₀ : ℕ) :
    degreeLT K (E.card * S₀) ≃ₗ[K] (↥E × Fin S₀ → K) :=
  (jetMap E S₀).linearEquivOfInjective (jetMap_injective E S₀) (by
    rw [(degreeLTEquiv K _).finrank_eq, Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card,
      Fintype.card_prod, Fintype.card_coe, Fintype.card_fin])

end HermiteBasis

open Polynomial HermiteBasis in
/-- **Hermite interpolation** over a field of characteristic `0`. -/
theorem solution {K : Type*} [Field K] [CharZero K] [DecidableEq K] (E : Finset K) (S₀ : ℕ) :
    ∃ b : ↥E × Fin S₀ → K[X], (∀ x, b x ∈ degreeLT K (E.card * S₀)) ∧
      (∀ x y : ↥E × Fin S₀,
        (derivative^[y.2] (b x)).eval (y.1 : K) = if x = y then 1 else 0) ∧
      ∀ q ∈ degreeLT K (E.card * S₀),
        q = ∑ x : ↥E × Fin S₀, C ((derivative^[x.2] q).eval (x.1 : K)) * b x := by
  refine ⟨fun x => ((jetEquiv E S₀).symm (Pi.single x 1) : degreeLT K (E.card * S₀)),
    fun x => Subtype.prop _, fun x y => ?_, fun q hq => ?_⟩
  · rw [← jetMap_apply]
    change jetEquiv E S₀ ((jetEquiv E S₀).symm (Pi.single x 1)) y = _
    rw [LinearEquiv.apply_symm_apply, Pi.single_apply]
    simp [eq_comm]
  · have hjet : jetEquiv E S₀ ⟨q, hq⟩ = fun x => (derivative^[x.2] q).eval (x.1 : K) :=
      funext fun x => jetMap_apply E S₀ ⟨q, hq⟩ x
    have h := congrArg (fun v => ((jetEquiv E S₀).symm v : K[X])) hjet
    simp only [LinearEquiv.symm_apply_apply] at h
    refine h.trans ?_
    rw [← Finset.univ_sum_single (fun x : ↥E × Fin S₀ => (derivative^[x.2] q).eval (x.1 : K)),
      map_sum, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← smul_eq_C_mul, ← Submodule.coe_smul, ← map_smul, ← Pi.single_smul, smul_eq_mul, mul_one]
