-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_exists_mcPts_not_mem_mcPts_dd9f6b21ff26
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:30:19.051398+00:00
-- url     : https://prove2.me/submissions/35de6ff0-96e0-4cd8-aae3-e6531b77544d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_GenericComplexPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_exists_ringHom_complex_of_charZero_94a0d11369fc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Cardinal
noncomputable section
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P J : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d) (hJ : ¬ J ≤ P) :
    ∃ z, z ∈ mcPts P ∧ z ∉ mcPts J := by
  obtain ⟨_, ⟨hprime, -, hrel⟩, hhor, -⟩ := hP
  obtain ⟨g, hgJ, hgP⟩ := SetLike.not_le_iff_exists.mp hJ
  have := hprime
  let Q := MRing ι ⧸ P
  let F := FractionRing Q
  have hQ : Function.Injective (algebraMap ℤ Q) := by
    have e : algebraMap ℤ Q = (Ideal.Quotient.mk P).comp C := RingHom.ext_int _ _
    rw [e, injective_iff_map_eq_zero]
    intro n hn
    have hn0 : (C n : MRing ι) ∈ P := Ideal.Quotient.eq_zero_iff_mem.mp hn
    have hn' : n ∈ P.comap (C : ℤ →+* MRing ι) := hn0
    rw [IsHorizontal] at hhor
    rw [hhor] at hn'
    exact (Ideal.mem_bot).mp hn'
  have : CharZero Q := charZero_of_injective_algebraMap hQ
  have : CharZero F := charZero_of_injective_algebraMap (R := Q) (IsFractionRing.injective Q F)
  have hcard : #F ≤ 𝔠 := by
    rw [Cardinal.mk_fractionRing]
    refine (Cardinal.mk_le_of_surjective (Ideal.Quotient.mk_surjective (I := P))).trans ?_
    refine MvPolynomial.cardinalMk_le_max.trans ?_
    exact max_le (max_le (mk_int.le.trans aleph0_le_continuum)
      (Cardinal.mk_le_aleph0.trans aleph0_le_continuum)) aleph0_le_continuum
  obtain ⟨ψ⟩ := exists_ringHom_complex_of_charZero F hcard
  let φ : MRing ι →+* ℂ := (ψ.comp (algebraMap Q F)).comp (Ideal.Quotient.mk P)
  have hker : ∀ f, φ f = 0 ↔ f ∈ P := by
    intro f
    have hi : Function.Injective (ψ.comp (algebraMap Q F)) :=
      ψ.injective.comp (IsFractionRing.injective Q F)
    rw [show φ f = (ψ.comp (algebraMap Q F)) (Ideal.Quotient.mk P f) from rfl,
      map_eq_zero_iff _ hi, Ideal.Quotient.eq_zero_iff_mem]
  let z : (Σ k, ι k) → ℂ := fun p => φ (X p)
  have hev : ∀ f : MRing ι, eval z (map (Int.castRingHom ℂ) f) = φ f := by
    intro f
    have h : (eval z).comp (map (Int.castRingHom ℂ)) = φ := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
      · exact RingHom.congr_fun
          (RingHom.ext_int (((eval z).comp (map (Int.castRingHom ℂ))).comp C) (φ.comp C)) r
      · simp [z]
    exact RingHom.congr_fun h f
  refine ⟨z, ⟨fun k => ?_, fun f hf => ?_⟩, fun hz => ?_⟩
  · obtain ⟨i, hi⟩ := hrel k
    exact ⟨i, fun h => hi ((hker _).mp h)⟩
  · rw [hev]
    exact (hker f).mpr hf
  · exact hgP ((hker g).mp (by rw [← hev]; exact hz.2 g hgJ))
end GroundTheory.Heights₂.Heights.HilbertSamuel
