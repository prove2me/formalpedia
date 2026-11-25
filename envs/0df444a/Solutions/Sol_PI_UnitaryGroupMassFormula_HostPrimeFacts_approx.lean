-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.HostPrimeFacts.approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:54:04.325823+00:00
-- url     : https://prove2.me/submissions/ef707732-5299-4804-bffe-db6fc7eab7f1

import Definitions.Def_Formalism_PeriodIntegrals_EtaHostFacts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HostPrimeSplitting_FinrankOE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host
open scoped Pointwise
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.HostPrimeFacts
variable {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R)
namespace PI.UnitaryGroupMassFormula.HostPrimeFacts
theorem _root_.solution (P : HeightOneSpectrum (𝓞 H.E)) (hf : P.asIdeal.inertiaDeg (𝓞 H.F) = 1)
    (x : 𝓞 H.E) : ∃ a : 𝓞 H.F, x - algebraMap (𝓞 H.F) (𝓞 H.E) a ∈ P.asIdeal := by
  set v := P.under (𝓞 H.F)
  haveI : P.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  haveI := v.isMaximal
  haveI := P.isMaximal
  rw [Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal P.asIdeal] at hf
  letI : Field (𝓞 H.F ⧸ v.asIdeal) := Ideal.Quotient.field _
  letI : Field (𝓞 H.E ⧸ P.asIdeal) := Ideal.Quotient.field _
  have htop : (⊥ : Subalgebra (𝓞 H.F ⧸ v.asIdeal) (𝓞 H.E ⧸ P.asIdeal)) = ⊤ :=
    Subalgebra.bot_eq_top_iff_finrank_eq_one.mpr hf
  have hx : Ideal.Quotient.mk P.asIdeal x ∈ (⊥ : Subalgebra (𝓞 H.F ⧸ v.asIdeal) (𝓞 H.E ⧸ P.asIdeal)) :=
    htop ▸ Algebra.mem_top
  obtain ⟨y, hy⟩ := Algebra.mem_bot.mp hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨a, ?_⟩
  rw [← Ideal.Quotient.eq, ← hy]
  rfl
end PI.UnitaryGroupMassFormula.HostPrimeFacts
