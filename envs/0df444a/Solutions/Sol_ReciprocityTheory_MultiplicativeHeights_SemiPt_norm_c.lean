-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.norm_c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:26:46.333707+00:00
-- url     : https://prove2.me/submissions/61312d76-81c0-4339-aca7-633a9dc3e14a

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegR
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegH

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (z : K) :
    Algebra.norm ℚ (S.c z) = Algebra.norm ℚ z := by
  have hs : Function.Surjective S.c := fun x => ⟨S.c x, S.c_invol x⟩
  let e : K ≃+* K := RingEquiv.ofBijective S.c ⟨S.c.injective, hs⟩
  let e' : K ≃ₐ[ℚ] K := AlgEquiv.ofRingEquiv (f := e) (fun q => by simp [e])
  exact Algebra.norm_eq_of_algEquiv e' z
end ReciprocityTheory.MultiplicativeHeights.SemiPt
