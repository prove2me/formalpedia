-- Prove2me | solution 1 for P2M_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_X_mem_supported__ad5886e30d80
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:46:19.943685+00:00
-- url     : https://prove2.me/submissions/1cb895d6-3ff1-41f4-9521-4da06015c183

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_MaxTwistDegreePderivLeAddOne
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TwistSubXMemSupported

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.TestSideWords Formalism.MainNotions.TestSideWords.TwistedFiltration Formalism.MainNotions.TestSideWords.TwistedFiltration.G3
open Formalism.MainNotions.G Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
variable {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
open Classical
namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G3
theorem _root_.solution {B : Type*} [CommRing B] (w : Set ι) (v : ι × Fin n) (hv : v.1 ∉ w) :
    (X v : MvPolynomial (ι × Fin n) B) ∈ supported B {x : ι × Fin n | x.1 ∉ w} := by
  classical
  rw [mem_supported]
  intro x hx
  rw [Finset.mem_coe, mem_vars] at hx
  obtain ⟨d, hd, hxd⟩ := hx
  have h1 := support_monomial_subset (R := B) hd
  rw [Finset.mem_singleton] at h1
  subst h1
  have h2 := Finsupp.support_single_subset hxd
  rw [Finset.mem_singleton] at h2
  subst h2
  exact hv
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G3
