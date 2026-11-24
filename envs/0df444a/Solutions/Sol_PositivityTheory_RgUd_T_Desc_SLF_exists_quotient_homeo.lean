-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Desc.SLF.exists_quotient_homeo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:10:24.037798+00:00
-- url     : https://prove2.me/submissions/3f794b1f-cdba-4fbf-b0d7-c3d572dc73e6

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_Descent_SliceVanishing_ExistsQuotientHomeo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc PositivityTheory.RgUd.T.Desc.SLF
open MulAction
variable {G T : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SigmaCompactSpace G]
  [TopologicalSpace T] [T2Space T] [BaireSpace T] [MulAction G T] [ContinuousSMul G T] [IsPretransitive G T]
namespace PositivityTheory.RgUd.T.Desc.SLF
theorem _root_.solution (t : T) :
    ∃ e : G ⧸ stabilizer G t ≃ₜ T, ∀ g : G, e (g : G ⧸ stabilizer G t) = g • t := by
  let f : G ⧸ stabilizer G t → T := ofQuotientStabilizer G t
  have hinj : Function.Injective f := injective_ofQuotientStabilizer G t
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨g, hg⟩ := exists_smul_eq G t y
    exact ⟨(g : G ⧸ stabilizer G t), by simp [f, hg]⟩
  have hmk : ∀ g : G, f (g : G ⧸ stabilizer G t) = g • t := fun g => ofQuotientStabilizer_mk G t g
  have hcont : Continuous f := by
    rw [(QuotientGroup.isQuotientMap_mk (stabilizer G t)).continuous_iff]
    have : f ∘ (QuotientGroup.mk : G → G ⧸ stabilizer G t) = fun g => g • t := funext hmk
    rw [this]
    exact continuous_id.smul continuous_const
  have hopen : IsOpenMap f := by
    intro U hU
    have : f '' U = (fun g : G => g • t) '' ((QuotientGroup.mk : G → G ⧸ stabilizer G t) ⁻¹' U) := by
      ext y
      constructor
      · rintro ⟨c, hc, rfl⟩
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
        exact ⟨g, hc, (hmk g).symm⟩
      · rintro ⟨g, hg, rfl⟩
        exact ⟨_, hg, hmk g⟩
    rw [this]
    exact isOpenMap_smul_of_sigmaCompact t _ (hU.preimage QuotientGroup.continuous_mk)
  exact ⟨(Equiv.ofBijective f ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen hcont hopen, hmk⟩
end PositivityTheory.RgUd.T.Desc.SLF
