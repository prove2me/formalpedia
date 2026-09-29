-- Prove2me | solution 1 for WeierstrassCurve.exists_residual_eigensystem_of_isResiduallyModularOfLevel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/e8637d38-95ee-5078-89c8-ab17572819b9

import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_FLTPrelim_ModularRep
import Theorems.Thm_WeierstrassCurve_isResiduallyModularOfLevel_iff_exists_ideal_heckeAlgebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_residual_eigensystem_of_isResiduallyModularOfLevel

noncomputable section

private theorem heckeAlgebra_le_of_forall_prime {N : ℕ} [NeZero N] {k : ℤ} {S S' : Set ℕ}
    (h : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∈ S → ℓ ∈ S') :
    CuspForm.heckeAlgebra N k S' ≤ CuspForm.heckeAlgebra N k S := by
  apply Algebra.adjoin_mono
  rintro T (⟨ℓ, hℓ, hℓN, hℓS', rfl⟩ | ⟨q, hqN, hq, hqS', rfl⟩)
  · exact CuspForm.heckeTLin_mem_heckeGenerators hℓ hℓN fun hS => hℓS' (h ℓ hℓ hS)
  · exact CuspForm.heckeULin_mem_heckeGenerators hq hqN fun hS => hqS' (h q hq hS)

set_option synthInstance.maxHeartbeats 1600000 in

private theorem exists_residualEigensystem_of_ideal {N : ℕ} [NeZero N] {p : ℕ} (hp : p.Prime)
    (a : ℕ → ℤ) {S : Set ℕ} {S₀ : Set ℕ} (hS₀ : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∈ S₀ → ℓ ∈ S)
    (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (𝔪 : Ideal (CuspForm.heckeAlgebra N 2 S₀)) (h𝔪 : 𝔪 ≠ ⊤)
    (hp𝔪 : (p : CuspForm.heckeAlgebra N 2 S₀) ∈ 𝔪)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS₀ : ℓ ∉ S₀),
      CuspForm.heckeAlgebra.T hℓ hℓN hℓS₀ - (a ℓ : CuspForm.heckeAlgebra N 2 S₀) ∈ 𝔪)
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] (hp𝒪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪) :
    ∃ θ : CuspForm.heckeAlgebra N 2 S →+* IsLocalRing.ResidueField 𝒪,
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
        θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) = IsLocalRing.residue 𝒪 ((a ℓ : ℤ) : 𝒪) := by
  classical
  have hle : CuspForm.heckeAlgebra N 2 S ≤ CuspForm.heckeAlgebra N 2 S₀ :=
    heckeAlgebra_le_of_forall_prime hS₀
  let ι : CuspForm.heckeAlgebra N 2 S →+* CuspForm.heckeAlgebra N 2 S₀ :=
    (Subalgebra.inclusion hle).toRingHom
  let 𝔪' : Ideal (CuspForm.heckeAlgebra N 2 S) := 𝔪.comap ι
  let Q := CuspForm.heckeAlgebra N 2 S ⧸ 𝔪'
  let mk : CuspForm.heckeAlgebra N 2 S →+* Q := Ideal.Quotient.mk 𝔪'
  have hTQ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
      mk (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) = ((a ℓ : ℤ) : Q) := by
    intro ℓ hℓ hℓN hℓS
    have hℓS₀ : ℓ ∉ S₀ := fun h => hℓS (hS₀ ℓ hℓ h)
    have hι : ι (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) = CuspForm.heckeAlgebra.T hℓ hℓN hℓS₀ :=
      Subtype.ext rfl
    rw [← map_intCast mk]
    refine Ideal.Quotient.eq.mpr (Ideal.mem_comap.mpr ?_)
    rw [map_sub, map_intCast, hι]
    exact hT ℓ hℓ hℓN hℓS₀
  have hint : ∀ t : CuspForm.heckeAlgebra N 2 S, ∃ n : ℤ, mk t = (n : Q) := by
    rintro ⟨x, hx⟩
    refine Algebra.adjoin_induction
      (p := fun x hx => ∃ n : ℤ, mk ⟨x, hx⟩ = (n : Q)) ?_ ?_ ?_ ?_ hx
    · rintro x (⟨ℓ, hℓ, hℓN, hℓS, rfl⟩ | ⟨q, hqN, hq, hqS, rfl⟩)
      · exact ⟨a ℓ, hTQ ℓ hℓ hℓN hℓS⟩
      · exact (hqS (hNS q hq hqN)).elim
    · intro r
      refine ⟨r, ?_⟩
      have : (⟨algebraMap ℤ _ r, Subalgebra.algebraMap_mem _ r⟩ : CuspForm.heckeAlgebra N 2 S) =
          (r : CuspForm.heckeAlgebra N 2 S) :=
        Subtype.ext (by simp)
      rw [this, map_intCast]
    · rintro x y hx hy ⟨m, hm⟩ ⟨n, hn⟩
      refine ⟨m + n, ?_⟩
      have : (⟨x + y, add_mem hx hy⟩ : CuspForm.heckeAlgebra N 2 S) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [this, map_add, hm, hn, Int.cast_add]
    · rintro x y hx hy ⟨m, hm⟩ ⟨n, hn⟩
      refine ⟨m * n, ?_⟩
      have : (⟨x * y, mul_mem hx hy⟩ : CuspForm.heckeAlgebra N 2 S) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [this, map_mul, hm, hn, Int.cast_mul]
  let ψ : ℤ →+* Q := Int.castRingHom Q
  have hψ : Function.Surjective ψ := by
    intro q
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨n, hn⟩ := hint t
    exact ⟨n, hn.symm⟩
  haveI : Nontrivial (CuspForm.heckeAlgebra N 2 S₀ ⧸ 𝔪) := Ideal.Quotient.nontrivial_iff.mpr h𝔪
  haveI : CharP (CuspForm.heckeAlgebra N 2 S₀ ⧸ 𝔪) p :=
    (CharP.charP_iff_prime_eq_zero hp).mpr (by
      rw [← map_natCast (Ideal.Quotient.mk 𝔪)]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hp𝔪)
  let g : ℤ →+* IsLocalRing.ResidueField 𝒪 := Int.castRingHom _
  have hker : RingHom.ker ψ ≤ RingHom.ker g := by
    intro n hn
    rw [RingHom.mem_ker] at hn ⊢
    have h1 : ((n : CuspForm.heckeAlgebra N 2 S)) ∈ 𝔪' := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_intCast]
      exact hn
    have h2 : (n : CuspForm.heckeAlgebra N 2 S₀) ∈ 𝔪 := by
      have := Ideal.mem_comap.mp h1
      rwa [map_intCast] at this
    have h3 : ((n : ℤ) : CuspForm.heckeAlgebra N 2 S₀ ⧸ 𝔪) = 0 := by
      rw [← map_intCast (Ideal.Quotient.mk 𝔪)]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr h2
    obtain ⟨m, rfl⟩ := (CharP.intCast_eq_zero_iff _ p n).mp h3
    have hpk : ((p : ℤ) : IsLocalRing.ResidueField 𝒪) = 0 := by
      rw [Int.cast_natCast, ← map_natCast (IsLocalRing.residue 𝒪)]
      exact (IsLocalRing.residue_eq_zero_iff _).mpr hp𝒪
    show ((p * m : ℤ) : IsLocalRing.ResidueField 𝒪) = 0
    rw [Int.cast_mul, hpk, zero_mul]
  refine ⟨(ψ.liftOfSurjective hψ ⟨g, hker⟩).comp mk, fun ℓ hℓ hℓN hℓS => ?_⟩
  rw [RingHom.comp_apply, hTQ ℓ hℓ hℓN hℓS, ← eq_intCast ψ, RingHom.liftOfSurjective_comp_apply,
    map_intCast]
  rfl

theorem solution (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℤ) {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] (hp𝒪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪) (S : Finset ℕ) (_hS : ∀ q ∈ S, q.Prime) (hpS : p ∈ S) (hbadS : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ W.Δ → q ∈ S) {N : ℕ} [NeZero N] (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S) (hres : W.IsResiduallyModularOfLevel p N) (hint : CuspForm.HasIntegralStructure N 2) : ∃ θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* IsLocalRing.ResidueField 𝒪, ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)), θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) = IsLocalRing.residue 𝒪 ((W.apOfModel ℓ : ℤ) : 𝒪) := by
  obtain ⟨𝔪, h𝔪, hp𝔪, hT⟩ :=
    (W.isResiduallyModularOfLevel_iff_exists_ideal_heckeAlgebra (p := p) hint).mp hres
  refine exists_residualEigensystem_of_ideal (Fact.out) W.apOfModel ?_ hNS 𝔪 h𝔪.ne_top hp𝔪 hT hp𝒪
  rintro ℓ hℓ (h | rfl | h)
  · exact Finset.mem_coe.mpr (hbadS ℓ hℓ (by by_contra h'; exact h h'))
  · exact Finset.mem_coe.mpr hpS
  · exact Finset.mem_coe.mpr (hNS ℓ hℓ h)

end

end S_WeierstrassCurve_exists_residual_eigensystem_of_isResiduallyModularOfLevel
end P2MW
export P2MW.S_WeierstrassCurve_exists_residual_eigensystem_of_isResiduallyModularOfLevel (solution)
