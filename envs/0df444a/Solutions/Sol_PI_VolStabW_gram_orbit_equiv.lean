-- Prove2me | solution 1 for PI.VolStabW.gram_orbit_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:11:05.415142+00:00
-- url     : https://prove2.me/submissions/a6086531-9d0f-4bc7-96b6-3963ff0e345f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_Unfold
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnfoldMain
import Theorems.Thm_Formalism_UG_P_hform_mulVec
import Theorems.Thm_PI_VolStabW_ratElA_mem
import Theorems.Thm_PI_VolStabW_ratElA_smul
import Theorems.Thm_PI_VolStabW_ratTup_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Set
open scoped TensorProduct ENNReal Pointwise
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
namespace PI.VolStabW
theorem _root_.solution {a : ℕ} (X0 : Fin a → Fin M → E)
    (hW : ∀ X : Fin a → Fin M → E, gramE σ J X = gramE σ J X0 →
      ∃ g ∈ Formalism.UG.UJ (σ : E →+* E) J, ∀ i, (g : Matrix (Fin M) (Fin M) E).mulVec (X0 i) = X i) :
    ∃ e : {X : Fin a → Fin M → E | gramE σ J X = gramE σ J X0} ≃
        orbS (GamA σ J) (ratTup (F := F) (AF F) X0),
      ∀ X, (e X : Fin a → Fin M → AF F ⊗[F] E) = ratTup (F := F) (AF F) (X : Fin a → Fin M → E) := by
  let f : {X : Fin a → Fin M → E | gramE σ J X = gramE σ J X0} →
      orbS (GamA σ J) (ratTup (F := F) (AF F) X0) := fun X =>
    ⟨ratTup (F := F) (AF F) (X : Fin a → Fin M → E), by
      obtain ⟨g, hg, hgX⟩ := hW X X.2
      refine ⟨ratElA σ J g hg, ratElA_mem σ J g hg, ?_⟩
      rw [ratElA_smul]
      congr 1
      funext i
      exact hgX i⟩
  have hinj : Function.Injective f := fun X X' h =>
    Subtype.ext (ratTup_injective (congrArg Subtype.val h))
  have hsurj : Function.Surjective f := by
    rintro ⟨x, ⟨γ, hγ, rfl⟩⟩
    obtain ⟨g, hg, hgγ⟩ := Subgroup.mem_map.1
      (Subgroup.mem_subgroupOf.1 (show (show HR (AF F) σ J from γ) ∈ HFinIn (AF F) σ J from hγ))
    have hγe : γ = ratElA σ J g hg := Subtype.ext hgγ.symm
    have hg' : Formalism.UG.cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J *
        (g : Matrix (Fin M) (Fin M) E) = J := hg
    refine ⟨⟨fun i => (g : Matrix (Fin M) (Fin M) E).mulVec (X0 i), ?_⟩, ?_⟩
    · show gramE σ J _ = gramE σ J X0
      ext i j
      show Formalism.UG.hform (σ : E →+* E) J _ _ = Formalism.UG.hform (σ : E →+* E) J _ _
      rw [Formalism.UG.P.hform_mulVec, hg']
    · apply Subtype.ext
      show ratTup (F := F) (AF F) _ = γ • ratTup (F := F) (AF F) X0
      rw [hγe, ratElA_smul]
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun X => rfl⟩
end PI.VolStabW
