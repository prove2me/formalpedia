-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.exists_poly_of_locRing_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:16:23.001842+00:00
-- url     : https://prove2.me/submissions/bd6213d6-8177-4638-b7b3-e80db7e47812

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsAtlas
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SNCstep
import Theorems.Thm_ReciprocityTheory_AnForm_R_locEvalPt_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial ReciprocityTheory.AnForm.M
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (I : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    (hp : ∀ g ∈ I, eval p g = 0) (F G : MvPolynomial (Fin n) ℂ) (u : locRing I p) (hu : IsUnit u)
    (h : algebraMap _ (locRing I p) F = u * algebraMap _ (locRing I p) G) :
    ∃ a b c : MvPolynomial (Fin n) ℂ, eval p a ≠ 0 ∧ eval p b ≠ 0 ∧ eval p c ≠ 0 ∧
      c * (b * F - a * G) ∈ I := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective u
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (ptIdeal p).primeCompl z
  have hs : eval p (s : MvPolynomial (Fin n) ℂ) ≠ 0 := fun h0 => s.2 (RingHom.mem_ker.2 h0)
  have key : ∀ x : MvPolynomial (Fin n) ℂ, algebraMap _ (locRing I p) x =
      Ideal.Quotient.mk _ (algebraMap _ (locPt p) x) := fun x => by rw [Ideal.Quotient.mk_algebraMap]
  have hspec : IsLocalization.mk' (locPt p) a s * algebraMap _ (locPt p) (s : MvPolynomial (Fin n) ℂ) =
      algebraMap _ (locPt p) a := IsLocalization.mk'_spec _ _ _
  have ha : eval p a ≠ 0 := by
    intro h0
    have h1 := congrArg (locEvalPt I p hp)
      (congrArg (Ideal.Quotient.mk (Ideal.map (algebraMap _ (locPt p)) I)) hspec)
    rw [map_mul, map_mul, locEvalPt_algebraMap, locEvalPt_algebraMap, h0] at h1
    exact (hu.map (locEvalPt I p hp)).ne_zero (by simpa [hs] using h1)
  rw [key, key] at h
  have hmem : algebraMap _ (locPt p) ((s : MvPolynomial (Fin n) ℂ) * F - a * G) ∈
      Ideal.map (algebraMap _ (locPt p)) I := by
    have h2 := Ideal.Quotient.eq.1 (h.trans (map_mul _ _ _).symm)
    have h3 := Ideal.mul_mem_left _ (algebraMap _ (locPt p) (s : MvPolynomial (Fin n) ℂ)) h2
    convert h3 using 1
    rw [map_sub, map_mul, map_mul, ← hspec]
    ring
  obtain ⟨m, hm, hmI⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (ptIdeal p).primeCompl (locPt p) I _).1 hmem
  exact ⟨a, s, m, ha, hs, fun h0 => hm (RingHom.mem_ker.2 h0), hmI⟩
end ReciprocityTheory.AnForm.R
