-- Prove2me | solution 1 for PI.VolStabW.goodV_aa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:25:57.169531+00:00
-- url     : https://prove2.me/submissions/fb03156f-34cb-4f1e-a6bf-8c812b5ba0c9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVDx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHH
import Theorems.Thm_PI_VolStabW_aaInt

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
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
variable {b v}
namespace PI.VolStabW
theorem _root_.solution (b : Module.Basis (Fin d) F E) (σ : E →ₐ[F] E) {M a : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (Tinv : Matrix (Fin a) (Fin a) E) :
    ∀ᶠ v in cofinite, GoodV b v σ J Tinv := by
  have k1 : ∀ᶠ v in cofinite, ∀ k l m : Fin d,
      algebraMap F (Fv F v) (b.repr (b k * b l) m) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun l =>
      Filter.eventually_all.2 fun m => aaInt _
  have k2 : ∀ᶠ v in cofinite, ∀ k m : Fin d,
      algebraMap F (Fv F v) (b.repr (σ (b k)) m) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun m => aaInt _
  have k3 : ∀ᶠ v in cofinite, ∀ (i j : Fin M) (m : Fin d),
      algebraMap F (Fv F v) (b.repr (J i j) m) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      Filter.eventually_all.2 fun m => aaInt _
  have k4 : ∀ᶠ v in cofinite, ∀ m : Fin d,
      algebraMap F (Fv F v) (b.repr (1 / 2 : E) m) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun m => aaInt _
  have k5 : ∀ᶠ v in cofinite, ∀ (i j : Fin a) (m : Fin d),
      algebraMap F (Fv F v) (b.repr (Tinv i j) m) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      Filter.eventually_all.2 fun m => aaInt _
  filter_upwards [k1, k2, k3, k4, k5] with v h1 h2 h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩
end PI.VolStabW
