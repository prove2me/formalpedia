-- Prove2me | solution 1 for UpperTheory.Mu.pow_torsionOrder_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:18:50.973682+00:00
-- url     : https://prove2.me/submissions/4ebaf167-7680-4cb6-9053-86dd3b7d83ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_TorsionTotientBound
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_Monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open UpperTheory UpperTheory.Mu
variable {K : Type} [Field K] [NumberField K]
namespace UpperTheory.Mu
theorem _root_.solution {x : K} (hx : IsIntegral ℤ x) (h : ∀ φ : K →+* ℂ, ‖φ x‖ = 1) :
    x ^ Units.torsionOrder K = 1 := by
  obtain ⟨n, hn, hxn⟩ := Embeddings.pow_eq_one_of_norm_eq_one K ℂ hx h
  obtain ⟨y, rfl⟩ : ∃ y : 𝓞 K, (y : K) = x := ⟨⟨x, hx⟩, rfl⟩
  have hyn : y ^ n = 1 := by
    apply RingOfIntegers.coe_injective
    simpa using hxn
  have hmem : Units.ofPowEqOne y n hyn hn.ne' ∈ Units.torsion K := by
    rw [Units.torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    exact ⟨n, hn, Units.ext (by simpa using hyn)⟩
  rw [← Units.rootsOfUnity_eq_torsion, mem_rootsOfUnity] at hmem
  have := congrArg (fun v : (𝓞 K)ˣ => ((v : 𝓞 K) : K)) hmem
  simpa using this
end UpperTheory.Mu
