-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.isUnit_algebraMap_locRing_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:06:16.234108+00:00
-- url     : https://prove2.me/submissions/398fa21c-0bb6-40f6-b9e6-0b64013cf984

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ClosureFromSpecMemCompsH
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace
noncomputable section
variable {m : ℕ}
namespace ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
theorem _root_.solution (K : Ideal (MvPolynomial (Fin m) ℂ)) (p : Fin m → ℂ)
    (hp : ∀ h ∈ K, eval p h = 0) (g : MvPolynomial (Fin m) ℂ) :
    IsUnit (algebraMap _ (locRing K p) g) ↔ eval p g ≠ 0 := by
  have hK : K ≤ ptIdeal p := fun h hh => (RingHom.mem_ker).2 (hp h hh)
  have hJ : Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt p)) K ≤
      Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt p)) (ptIdeal p) := Ideal.map_mono hK
  have hne : Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt p)) (ptIdeal p) ≠ ⊤ := by
    rw [Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.IsMaximal.ne_top inferInstance
  change IsUnit (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt p)) K)
    (algebraMap _ (locPt p) g)) ↔ _
  constructor
  · intro hu hg
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective v
    have h0 : (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt p)) K))
        (algebraMap (MvPolynomial (Fin m) ℂ) (locPt p) g * b - 1) = 0 := by
      rw [map_sub, map_mul, map_one, hv, sub_self]
    have h2 := hJ (Ideal.Quotient.eq_zero_iff_mem.1 h0)
    have h1 : algebraMap (MvPolynomial (Fin m) ℂ) (locPt p) g * b ∈
        Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt p)) (ptIdeal p) :=
      Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ((RingHom.mem_ker).2 hg))
    apply hne
    rw [Ideal.eq_top_iff_one]
    have h3 := Ideal.sub_mem _ h1 h2
    rwa [sub_sub_cancel] at h3
  · intro hg
    refine IsUnit.map _ ?_
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (locPt p) (ptIdeal p) g).2
      (Ideal.mem_primeCompl_iff.2 fun hk => hg ((RingHom.mem_ker).1 hk))
end ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
