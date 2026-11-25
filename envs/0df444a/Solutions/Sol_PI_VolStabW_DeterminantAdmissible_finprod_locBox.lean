-- Prove2me | solution 1 for PI.VolStabW.DeterminantAdmissible.finprod_locBox
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:06:56.696108+00:00
-- url     : https://prove2.me/submissions/3c9ffbf3-00b5-4ea7-acfa-6a27cbcd3029

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdmB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DetAdmC
import Theorems.Thm_PI_VolStabW_DeterminantAdmissible_finprod_ite
import Theorems.Thm_PI_VolStabW_PositiveNearLattice_crd_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.DeterminantAdmissible
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Topology Filter Set
  PI.VolStabW.PositiveNearLattice MeasurableSpace PI.VolFromSW PI.VolStabW
open scoped TensorProduct ENNReal RestrictedProduct CompactlySupported
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) {a M : ℕ}
variable {b}
namespace PI.VolStabW.DeterminantAdmissible
theorem _root_.solution {D : Fin a × Fin M × Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (hD : IsBoxD D) (W : Fin a → Fin M → Af F ⊗[F] E) :
    ∏ᶠ v, (locBox b D v).indicator (1 : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ) (projV v W) =
      (boxS D).indicator 1 (crdH b (Af F) W) := by
  classical
  set q := crdH b (Af F) W
  have hv : ∀ v, (locBox b D v).indicator (1 : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ) (projV v W) =
      if (∀ c, q c v ∈ D c v) then 1 else 0 := by
    intro v
    have e : ∀ c, crdH b (Fv F v) (projV v W) c = q c v := fun c =>
      crd_map b (evalV F v) (W c.1 c.2.1) c.2.2
    rw [Set.indicator_apply]
    simp only [locBox, mem_preimage, Set.mem_univ_pi, e, Pi.one_apply]
  rw [finprod_congr hv, finprod_ite _ ?_]
  · rw [Set.indicator_apply]
    by_cases hq : q ∈ boxS D
    · rw [if_pos hq, if_pos (fun v c => hq c v)]
      rfl
    · rw [if_neg hq, if_neg (fun h' => hq (fun c v => h' v c))]
  · filter_upwards [hD.2, eventually_all.2 fun c => (q c).eventually] with v h1 h2 c
    rw [h1 c]
    exact h2 c
end PI.VolStabW.DeterminantAdmissible
