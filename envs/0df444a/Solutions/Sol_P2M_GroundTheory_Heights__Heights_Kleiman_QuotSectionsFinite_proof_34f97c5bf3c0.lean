-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_QuotSectionsFinite_proof_34f97c5bf3c0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:07:39.084227+00:00
-- url     : https://prove2.me/submissions/44f9c7fe-7e6e-44e7-93fd-11c3ef92e9a9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsIdealTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotSectionsFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TildeFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotientH0FiniteHypothesesLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PQuotSectionsFinite

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
open MvPolynomial
noncomputable section
universe u w
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace QuotSectionsFinite
theorem _root_.solution (hE : Extension.Statement.{u, w, w})
    (hI : IdealTwistFamily.Statement.{u, w}) (hT : TildeFinite.Statement.{u, w})
    (hQ : QuotientH0Finite.Statement.{u, w, w}) : QuotSectionsFinite.Statement.{u, w} := by
  intro k _ Ω _ _ N x Q J

  let J' : Ideal (Poly k N) := Ideal.span {f | f ∈ J ∧ ∃ e, f.IsHomogeneous e}
  have hJ'hom : ∀ p ∈ J', ∀ d : ℕ, homogeneousComponent d p ∈ J' := by
    have h : J'.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) k) :=
      Ideal.homogeneous_span _ _ fun f hf =>
        ⟨_, (mem_homogeneousSubmodule _ f).mpr hf.2.choose_spec⟩
    exact fun p hp d => homogeneousComponent_mem_of_mem h hp d
  have hforms : ∀ (f : Poly k N) (e : ℕ), f.IsHomogeneous e → (f ∈ J ↔ f ∈ J') := fun f e hf =>
    ⟨fun h => Ideal.subset_span ⟨h, e, hf⟩, fun h => (Ideal.span_le.mpr fun _ hg => hg.1) h⟩
  have hsys : idealSys x J = idealSys x J' := SubSystem.ext_sub fun I => by
    change idealMod J I = idealMod J' I
    unfold idealMod
    congr 1
    ext a
    constructor <;> rintro ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
    · exact ⟨f, s, e, (hforms f e hfe).mp hf, hs, hfe, hse, rfl⟩
    · exact ⟨f, s, e, (hforms f e hfe).mpr hf, hs, hfe, hse, rfl⟩

  obtain ⟨F, hF, hFfg⟩ := hI k Ω N x Q J' hJ'hom
  obtain ⟨M, -, hM⟩ := hE k Ω N x Ω Q.toSubFamily Q.fg
  obtain ⟨M', -, hM'⟩ := hE k Ω N x Ω F hFfg
  have h0 : M.tildeSys 0 = Q.toSubSystem := SubSystem.ext_sub hM
  have h1 : M'.tildeSys 0 = Q.toSubSystem.twist (idealSys x J) := by
    rw [hsys, ← hF]
    exact SubSystem.ext_sub hM'

  have hle : ∀ I, (Q.toSubSystem.twist (idealSys x J)).sub I ≤ Q.toSubSystem.sub I := by
    intro I
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    refine Submodule.span_induction (p := fun q _ => q • y ∈ Q.sub I) ?_ ?_ ?_ ?_ hq
    · rintro _ ⟨f, s, e, _, hs, hf, hse, rfl⟩
      exact (Q.sub I).smul_mem ⟨_, ⟨f, s, e, hs, hf, hse, rfl⟩⟩ hy
    · rw [zero_smul]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [add_smul]; exact Submodule.add_mem _ ha hb
    · intro a q _ hq'; rw [smul_assoc]; exact Submodule.smul_mem _ a hq'
  have hH0 : Module.Finite k (Q.toSubSystem.H 0) := by
    rw [← h0]; exact hT k Ω N x M 0 0
  have hH1 : Module.Finite k ((Q.toSubSystem.twist (idealSys x J)).H 1) := by
    rw [← h1]; exact hT k Ω N x M' 1 0
  exact hQ k Ω N x Ω Q.toSubSystem (Q.toSubSystem.twist (idealSys x J)) hle hH0 hH1
end QuotSectionsFinite
end GroundTheory.Heights₂.Heights.Kleiman
