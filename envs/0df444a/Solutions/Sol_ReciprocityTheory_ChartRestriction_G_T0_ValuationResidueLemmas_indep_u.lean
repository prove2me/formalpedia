-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.indep_u
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:11:10.350825+00:00
-- url     : https://prove2.me/submissions/5461beb8-cd32-472d-9b9d-af1432387d23

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IsUnitOfValEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValuationResidueLemmas_mem_max_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValuationResidueLemmas_surj_res

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas
namespace ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas
theorem _root_.solution {K Ω U τ : Type} [Field K] [NumberField K] [Field Ω] [Field U] [Algebra K Ω]
    [Algebra Ω U] (w : AddValuation U (WithTop ℤ)) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (u : τ → vRing w)
    (h0 : ∀ P : MvPolynomial τ (𝓞 K), 0 < w (MvPolynomial.eval₂ ((algebraMap Ω U).comp
      ((algebraMap K Ω).comp (algebraMap (𝓞 K) K))) (fun j => (u j : U)) P) ↔
        ∀ α, P.coeff α ∈ la.asIdeal)
    (h1 : ∀ a : 𝓞 K, 0 ≤ w (((algebraMap Ω U).comp ((algebraMap K Ω).comp (algebraMap (𝓞 K) K))) a)) :
    letI _iW := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (vRing w) (algebraMap Ω U)
    letI _io := ReciprocityTheory.MultiplicativeHeights.residueAlgebra ((vRing w).comap (algebraMap Ω U)) (algebraMap K Ω)
    letI : Algebra (ResidueField (((vRing w).comap (algebraMap Ω U)).comap (algebraMap K Ω)))
        (ResidueField (vRing w)) :=
      ((algebraMap _ (ResidueField (vRing w))).comp
        (algebraMap _ (ResidueField ((vRing w).comap (algebraMap Ω U))))).toAlgebra
    AlgebraicIndependent (ResidueField (((vRing w).comap (algebraMap Ω U)).comap (algebraMap K Ω)))
      (fun j => residue (vRing w) (u j)) := by
  classical
  letI _iW := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (vRing w) (algebraMap Ω U)
  letI _io := ReciprocityTheory.MultiplicativeHeights.residueAlgebra ((vRing w).comap (algebraMap Ω U)) (algebraMap K Ω)
  letI : Algebra (ResidueField (((vRing w).comap (algebraMap Ω U)).comap (algebraMap K Ω)))
      (ResidueField (vRing w)) :=
    ((algebraMap _ (ResidueField (vRing w))).comp
      (algebraMap _ (ResidueField ((vRing w).comap (algebraMap Ω U))))).toAlgebra
  let ν : AddValuation K (WithTop ℤ) := (w.comap (algebraMap Ω U)).comap (algebraMap K Ω)
  have hpos : ∀ a : 𝓞 K, 0 < ν (algebraMap (𝓞 K) K a) ↔ a ∈ la.asIdeal := by
    intro a
    have := h0 (MvPolynomial.C a)
    simp only [MvPolynomial.eval₂_C] at this
    refine this.trans ?_
    constructor
    · intro h; simpa using h 0
    · intro h α; rw [MvPolynomial.coeff_C]; split_ifs <;> simp [h]
  have h1' : ∀ a : 𝓞 K, algebraMap (𝓞 K) K a ∈ vRing ν := h1
  have h1o : ∀ a : 𝓞 K, algebraMap (𝓞 K) K a ∈ ((vRing w).comap (algebraMap Ω U)).comap (algebraMap K Ω) := h1
  have hsurj : Function.Surjective ((residue (((vRing w).comap (algebraMap Ω U)).comap (algebraMap K Ω))).comp
      ((algebraMap (𝓞 K) K).codRestrict _ h1o)) := surj_res ν la h1' hpos
  rw [algebraicIndependent_iff]
  intro P hP
  by_contra hne
  obtain ⟨P', rfl⟩ := MvPolynomial.map_surjective _ hsurj P
  obtain ⟨α, hα⟩ : ∃ α, P'.coeff α ∉ la.asIdeal := by
    by_contra hall
    push Not at hall
    apply hne
    ext α
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero, RingHom.comp_apply, residue_eq_zero_iff]
    exact (mem_max_iff ν _).mpr ((hpos _).mpr (hall α))
  have hw0 : ¬ 0 < w (MvPolynomial.eval₂ ((algebraMap Ω U).comp
      ((algebraMap K Ω).comp (algebraMap (𝓞 K) K))) (fun j => (u j : U)) P') := by
    rw [h0]; intro h; exact hα (h α)
  let ψ : 𝓞 K →+* vRing w :=
    ((algebraMap Ω U).comp ((algebraMap K Ω).comp (algebraMap (𝓞 K) K))).codRestrict (vRing w) h1
  let y : vRing w := MvPolynomial.eval₂ ψ u P'
  have hy : (y : U) = MvPolynomial.eval₂ ((algebraMap Ω U).comp
      ((algebraMap K Ω).comp (algebraMap (𝓞 K) K))) (fun j => (u j : U)) P' :=
    MvPolynomial.eval₂_comp_left (vRing w).subtype ψ u P'
  have hres : residue (vRing w) y = 0 := by
    have e := MvPolynomial.eval₂_comp_left (residue (vRing w)) ψ u P'
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map] at hP
    refine e.trans (Eq.trans ?_ hP)
    congr 1
  rw [residue_eq_zero_iff, mem_max_iff, hy] at hres
  exact hw0 hres
end ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas
