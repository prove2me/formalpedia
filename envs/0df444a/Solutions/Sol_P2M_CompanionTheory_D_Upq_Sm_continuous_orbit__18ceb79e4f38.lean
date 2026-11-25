-- Prove2me | solution 1 for P2M_CompanionTheory_D_Upq_Sm_continuous_orbit__18ceb79e4f38
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:30:07.766576+00:00
-- url     : https://prove2.me/submissions/dd487a6f-b9cf-41fc-8de4-891cd6d23756

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_ModExists
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Theorems.Thm_CompanionTheory_D_Upq_Sm_continuous_ex
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smOn_mul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_SmOn_continuousOn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Sm
open PI CompanionTheory.D.Upq.ModEx
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
variable {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}
variable {hG : IsMatGroup G}
namespace CompanionTheory.D.Upq.Sm
theorem _root_.solution (h : RepOn G σ) {v : H} (hv : IsSm G σ v) {W : List (Mat n)}
    (hW : LieW G W) {X : Mat n} (hX : ∀ t, ex X t ∈ G) :
    Continuous fun p : ℝ × MG G hG => σ (ex X p.1) (dsW σ W (σ p.2.mat v)) :=
  (smOn_dsW h (u := fun x => σ x v) (hv.smOn_mul h) hW).continuousOn.comp_continuous
    (f := fun p : ℝ × MG G hG => (ex X p.1, p.2.mat))
    (((continuous_ex X).comp continuous_fst).prodMk (MG.continuous_mat.comp continuous_snd))
    fun p => ⟨hX _, p.2.mem⟩
end CompanionTheory.D.Upq.Sm
