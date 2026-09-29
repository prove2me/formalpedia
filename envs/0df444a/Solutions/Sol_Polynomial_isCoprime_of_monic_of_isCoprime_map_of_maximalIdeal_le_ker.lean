-- Prove2me | solution 1 for Polynomial.isCoprime_of_monic_of_isCoprime_map_of_maximalIdeal_le_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/baa68103-b215-5ea3-8e26-5b82e5651d9c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Polynomial_isCoprime_of_monic_of_isCoprime_map_of_maximalIdeal_le_ker
set_option autoImplicit false

p2m_open_scoped "Polynomial P2MW.S_Polynomial_isCoprime_of_monic_of_isCoprime_map_of_maximalIdeal_le_ker.Polynomial"

namespace Ws31
namespace N5

private theorem isCoprime_of_monic_of_isCoprime_map_residue
    {R : Type*} [CommRing R] [IsLocalRing R]
    (f g : R[X]) (hf : f.Monic)
    (h : IsCoprime (f.map (IsLocalRing.residue R)) (g.map (IsLocalRing.residue R))) :
    IsCoprime f g := by
  classical

  obtain ⟨A, B, hAB⟩ := h
  obtain ⟨a, rfl⟩ := Polynomial.map_surjective (IsLocalRing.residue R) Ideal.Quotient.mk_surjective A
  obtain ⟨b, rfl⟩ := Polynomial.map_surjective (IsLocalRing.residue R) Ideal.Quotient.mk_surjective B
  set e : R[X] := a * f + b * g - 1 with he
  have hecoeff : ∀ i, e.coeff i ∈ IsLocalRing.maximalIdeal R := by
    intro i
    have h0 : e.map (IsLocalRing.residue R) = 0 := by
      simp only [he, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one, hAB, sub_self]
    have := congrArg (fun p => p.coeff i) h0
    simpa [Polynomial.coeff_map, IsLocalRing.residue_eq_zero_iff] using this
  have hemem : e ∈ (IsLocalRing.maximalIdeal R).map (Polynomial.C : R →+* R[X]) :=
    Ideal.mem_map_C_iff.mpr hecoeff

  let S := AdjoinRoot f
  haveI : Module.Finite R S := (AdjoinRoot.powerBasis' hf).finite
  let N : Submodule R S := (Ideal.span {AdjoinRoot.mk f g}).restrictScalars R
  have hkey : (⊤ : Submodule R S) ≤ N ⊔ (IsLocalRing.maximalIdeal R) • ⊤ := by
    intro s _
    have h1 : (1 : S) = AdjoinRoot.mk f b * AdjoinRoot.mk f g - AdjoinRoot.mk f e := by
      have : AdjoinRoot.mk f (a * f + b * g - e) = 1 := by
        simp [he]
      rw [← this]
      simp [map_sub, map_add, map_mul, AdjoinRoot.mk_self]
    have hs : s = s * AdjoinRoot.mk f b * AdjoinRoot.mk f g - s * AdjoinRoot.mk f e := by
      calc s = s * 1 := (mul_one s).symm
        _ = _ := by rw [h1]; ring
    rw [hs]
    refine Submodule.sub_mem _ ?_ ?_
    · exact Submodule.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))
    · refine Submodule.mem_sup_right ?_
      rw [Ideal.smul_top_eq_map]
      change s * AdjoinRoot.mk f e ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R S)
      refine Ideal.mul_mem_left _ _ ?_
      have : (IsLocalRing.maximalIdeal R).map (algebraMap R S) =
          ((IsLocalRing.maximalIdeal R).map (Polynomial.C : R →+* R[X])).map (AdjoinRoot.mk f) := by
        rw [Ideal.map_map]; rfl
      rw [this]
      exact Ideal.mem_map_of_mem _ hemem
  have htop : (⊤ : Submodule R S) ≤ N :=
    Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
      (IsLocalRing.maximalIdeal_le_jacobson ⊥) hkey

  have h1N : (1 : S) ∈ Ideal.span {AdjoinRoot.mk f g} := htop Submodule.mem_top
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h1N
  obtain ⟨c', rfl⟩ := AdjoinRoot.mk_surjective c
  have : AdjoinRoot.mk f (c' * g - 1) = 0 := by simp [map_sub, map_mul, hc]
  rw [AdjoinRoot.mk_eq_zero] at this
  obtain ⟨d, hd⟩ := this
  refine ⟨-d, c', ?_⟩
  linear_combination hd

end Ws31.N5

namespace Polynomial p2m_export "Polynomial" "C X coeff_map coeff map_surjective factor map_map map Monic comp algebra module mod ext isCoprime_map ring lifts" end Polynomial
p2m_open_scoped "Polynomial" in

private theorem Polynomial.isCoprime_of_monic_of_isCoprime_map_of_maximalIdeal_le_ker
    {R k : Type*} [CommRing R] [IsLocalRing R] [Field k] (φ : R →+* k)
    (hφ : IsLocalRing.maximalIdeal R ≤ RingHom.ker φ)
    (f g : R[X]) (hf : f.Monic) (h : IsCoprime (f.map φ) (g.map φ)) :
    IsCoprime f g := by
  classical

  let ι : IsLocalRing.ResidueField R →+* k :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) φ (fun a ha => hφ ha)
  have hφι : φ = ι.comp (IsLocalRing.residue R) := by
    ext a; rfl
  rw [hφι, ← Polynomial.map_map, ← Polynomial.map_map, Polynomial.isCoprime_map] at h
  exact Ws31.N5.isCoprime_of_monic_of_isCoprime_map_residue f g hf h

theorem solution
    {R k : Type*} [CommRing R] [IsLocalRing R] [Field k] (φ : R →+* k)
    (hφ : IsLocalRing.maximalIdeal R ≤ RingHom.ker φ)
    (f g : R[X]) (hf : f.Monic) (h : IsCoprime (f.map φ) (g.map φ)) :
    IsCoprime f g :=
  Polynomial.isCoprime_of_monic_of_isCoprime_map_of_maximalIdeal_le_ker φ hφ f g hf h

end S_Polynomial_isCoprime_of_monic_of_isCoprime_map_of_maximalIdeal_le_ker
end P2MW
export P2MW.S_Polynomial_isCoprime_of_monic_of_isCoprime_map_of_maximalIdeal_le_ker (solution)
