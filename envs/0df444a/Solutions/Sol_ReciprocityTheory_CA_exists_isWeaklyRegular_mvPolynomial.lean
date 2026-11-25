-- Prove2me | solution 1 for ReciprocityTheory.CA.exists_isWeaklyRegular_mvPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:26:33.529864+00:00
-- url     : https://prove2.me/submissions/526beed9-ecfd-4ca9-9052-f2c3f5e75540

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolyStep
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolyMax
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolySeq
import Theorems.Thm_ReciprocityTheory_CA_exists_monic_aeval_mem_of_isMaximal
import Theorems.Thm_ReciprocityTheory_CA_isMaximal_comap_of_isMaximal_of_comap_eq
import Theorems.Thm_ReciprocityTheory_CA_isWeaklyRegular_map_C_append_monic
import Theorems.Thm_ReciprocityTheory_CA_isWeaklyRegular_map_ringEquiv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence
namespace ReciprocityTheory.CA
theorem _root_.solution {P : Type*} [CommRing P] [IsLocalRing P] {rs : List P}
    (hmem : ∀ r ∈ rs, r ∈ maximalIdeal P) (hrs : IsWeaklyRegular P rs) (N : ℕ)
    (𝔑 : Ideal (MvPolynomial (Fin N) P)) [𝔑.IsMaximal]
    (h : 𝔑.comap MvPolynomial.C = maximalIdeal P) :
    ∃ ss : List (MvPolynomial (Fin N) P), ss.length = rs.length + N ∧ (∀ s ∈ ss, s ∈ 𝔑) ∧
      IsWeaklyRegular (MvPolynomial (Fin N) P) ss := by
  induction N with
  | zero =>
    let e : P ≃ₐ[P] MvPolynomial (Fin 0) P := (MvPolynomial.isEmptyAlgEquiv P (Fin 0)).symm
    have he : ∀ r, e r = MvPolynomial.C r := fun r => by simpa using e.commutes r
    refine ⟨rs.map MvPolynomial.C, by simp, ?_, ?_⟩
    · intro s hs
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hs
      have hr' : r ∈ 𝔑.comap MvPolynomial.C := h.symm ▸ hmem r hr
      exact Ideal.mem_comap.1 hr'
    · have hmap : rs.map (e.toRingEquiv : P → MvPolynomial (Fin 0) P) = rs.map MvPolynomial.C :=
        List.map_congr_left fun r _ => he r
      have := isWeaklyRegular_map_ringEquiv e.toRingEquiv hrs
      rw [hmap] at this
      exact this
  | succ N ih =>
    let e : MvPolynomial (Fin (N + 1)) P ≃ₐ[P] Polynomial (MvPolynomial (Fin N) P) :=
      MvPolynomial.finSuccEquiv P N
    haveI : Algebra.FiniteType P (Polynomial (MvPolynomial (Fin N) P)) :=
      Algebra.FiniteType.trans (S := MvPolynomial (Fin N) P) inferInstance inferInstance
    let 𝔑' : Ideal (Polynomial (MvPolynomial (Fin N) P)) := 𝔑.map e.toRingEquiv
    haveI : 𝔑'.IsMaximal := Ideal.map_isMaximal_of_equiv e.toRingEquiv
    have hc' : 𝔑'.comap (algebraMap P (Polynomial (MvPolynomial (Fin N) P))) = maximalIdeal P := by
      have hA : algebraMap P (Polynomial (MvPolynomial (Fin N) P)) =
          (e.toRingEquiv : MvPolynomial (Fin (N + 1)) P →+* Polynomial (MvPolynomial (Fin N) P)).comp
            (algebraMap P (MvPolynomial (Fin (N + 1)) P)) :=
        RingHom.ext fun r => (e.commutes r).symm
      rw [hA, ← Ideal.comap_comap]
      show Ideal.comap _ (Ideal.comap (e.toRingEquiv : MvPolynomial (Fin (N + 1)) P →+* Polynomial (MvPolynomial (Fin N) P))
        (Ideal.map e.toRingEquiv 𝔑)) = _
      rw [Ideal.comap_coe, Ideal.comap_map_of_bijective _ e.toRingEquiv.bijective]
      exact h
    let 𝔐 : Ideal (MvPolynomial (Fin N) P) := 𝔑'.comap (algebraMap (MvPolynomial (Fin N) P) (Polynomial (MvPolynomial (Fin N) P)))
    haveI : 𝔐.IsMaximal := isMaximal_comap_of_isMaximal_of_comap_eq (S' := MvPolynomial (Fin N) P) 𝔑' hc'
    have hc'' : 𝔐.comap MvPolynomial.C = maximalIdeal P := by
      show (𝔑'.comap (algebraMap (MvPolynomial (Fin N) P) (Polynomial (MvPolynomial (Fin N) P)))).comap
        (algebraMap P (MvPolynomial (Fin N) P)) = maximalIdeal P
      rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
      exact hc'
    obtain ⟨ss', hlen, hmem', hreg'⟩ := ih 𝔐 hc''
    obtain ⟨g, hg, hgN⟩ := exists_monic_aeval_mem_of_isMaximal 𝔑' hc' (Polynomial.X)
    rw [Polynomial.aeval_X_left_eq_map] at hgN
    have hgm : (g.map (algebraMap P (MvPolynomial (Fin N) P))).Monic := hg.map _
    have hreg := isWeaklyRegular_map_C_append_monic hreg' hgm
    refine ⟨(ss'.map Polynomial.C ++ [g.map (algebraMap P (MvPolynomial (Fin N) P))]).map e.symm.toRingEquiv,
      ?_, ?_, isWeaklyRegular_map_ringEquiv e.symm.toRingEquiv hreg⟩
    · simp [hlen]
      omega
    · intro s hs
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hs
      have hy' : y ∈ 𝔑' := by
        rcases List.mem_append.1 hy with h1 | h1
        · obtain ⟨s', hs', rfl⟩ := List.mem_map.1 h1
          exact Ideal.mem_comap.1 (hmem' s' hs')
        · rw [List.mem_singleton] at h1
          rw [h1]
          exact hgN
      obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_of_equiv e.toRingEquiv y).1 hy'
      simpa using hx
end ReciprocityTheory.CA
