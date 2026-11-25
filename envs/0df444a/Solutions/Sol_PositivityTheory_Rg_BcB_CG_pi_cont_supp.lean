-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.CG.pi_cont_supp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:35:17.29416+00:00
-- url     : https://prove2.me/submissions/8a6fb279-2559-46f8-bbcb-1b105ba81494

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_HeckeFubiniCompatibility_PActPi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.CG
variable {X : Type} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
namespace PositivityTheory.Rg.BcB.CG
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {Idx : ι → Type} [∀ v, Fintype (Idx v)]
    (e : ∀ v, X → Idx v → Idx v → ℂ) (u : (∀ v, Idx v) → (ι → X) → ℂ) (I : ∀ v, Idx v)
    (he : ∀ v a b, Continuous (fun t => e v t a b) ∧ HasCompactSupport (fun t => e v t a b))
    (hu : ∀ J, Continuous (u J)) :
    Continuous (fun y : ι → X => ∑ J, (∏ v, e v (y v) (I v) (J v)) * u J y) ∧
      HasCompactSupport (fun y : ι → X => ∑ J, (∏ v, e v (y v) (I v) (J v)) * u J y) := by
  refine ⟨continuous_finsetSum _ fun J _ => Continuous.mul ?_ (hu J), ?_⟩
  · exact continuous_finsetProd (f := fun v (y : ι → X) => e v (y v) (I v) (J v)) _
      fun v _ => (he v (I v) (J v)).1.comp (continuous_apply v)
  let K : ι → Set X := fun v => ⋃ a, ⋃ b, tsupport (fun t => e v t a b)
  have hK : ∀ v, IsCompact (K v) := fun v => isCompact_iUnion fun a => isCompact_iUnion fun b => (he v a b).2
  refine HasCompactSupport.intro (isCompact_univ_pi hK) fun y hy => ?_
  rw [Set.mem_univ_pi] at hy
  push_neg at hy
  obtain ⟨v, hv⟩ := hy
  refine Finset.sum_eq_zero fun J _ => ?_
  have h0 : e v (y v) (I v) (J v) = 0 := image_eq_zero_of_notMem_tsupport (f := fun t => e v t (I v) (J v)) fun h =>
    hv (Set.mem_iUnion.2 ⟨I v, Set.mem_iUnion.2 ⟨J v, h⟩⟩)
  rw [Finset.prod_eq_zero (Finset.mem_univ v) h0, zero_mul]
end PositivityTheory.Rg.BcB.CG
