-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_twLocMod_subsingleton_be78395e6bcf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:20:45.736432+00:00
-- url     : https://prove2.me/submissions/0250d7c3-8472-4988-93e9-3b7b6d0adc73

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistSplitChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistSplitLoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Pointwise AddMonoidAlgebra
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {r : ℕ} (η : Fin (r + 1) → Ω)
variable (M₀ : FinGradedSub (S := S) (x := x) Ω)
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {J : Finset (Fin (N + 1))} (hJ : ¬ J ⊆ support x) :
    Subsingleton (LocMod (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀) J) := by
  obtain ⟨i, hiJ, hi⟩ := Finset.not_subset.mp hJ
  have hxi : x i = 0 := by
    by_contra h; exact hi ((mem_support x).mpr h)
  have hX : ∀ m : TwM η M₀, (X i : Poly (MvPolynomial (Fin (r + 1)) S) N) • m = 0 := fun m =>
    TwM.val_injective (by rw [TwM.val_smul, xyHom_X, hxi, single_zero, zero_mul, TwM.val_zero])
  have hz : ∀ w : LocMod (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀) J, w = 0 := by
    intro w
    induction w using LocalizedModule.induction_on with
    | h m s =>
      change (LocalizedModule.mk m s : LocalizedModule (monos J) (TwM η M₀)) =
        (0 : LocalizedModule (monos J) (TwM η M₀))
      rw [← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
      refine ⟨⟨X i, X_mem_monos hiJ⟩, ?_⟩
      rw [smul_zero, smul_zero]
      exact hX _
  exact ⟨fun w w' => by rw [hz w, hz w']⟩
end GroundTheory.Heights₂.Heights.Kleiman
