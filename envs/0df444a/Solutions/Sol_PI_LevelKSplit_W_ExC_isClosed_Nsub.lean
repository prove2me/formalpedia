-- Prove2me | solution 1 for PI.LevelKSplit.W.ExC.isClosed_Nsub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:37:21.280618+00:00
-- url     : https://prove2.me/submissions/67a36e36-4212-40f9-9bc7-9cffe369759c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_RatVMemSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnitaryGroupSecondCountableT2
import Theorems.Thm_PI_LevelKSplit_W_ExC_dual_e
import Theorems.Thm_PI_LevelKSplit_W_ExC_isClosed_spanR
import Theorems.Thm_PI_LevelKSplit_W_ExC_continuous_lin
import Theorems.Thm_PI_LevelKSplit_W_ExC_isClosed_uniFlag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.ExC
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain PI.LevelKSplit PI.LevelKSplit.W.Glob
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
namespace PI.LevelKSplit.W.ExC
theorem _root_.solution (hJ : IsHermND σ J) (hinv : ∀ x, σ (σ x) = x) {r : ℕ} (P : Frame E n r)
    (T : F) (hP : P.IsStd σ J T) :
    IsClosed (Nsub (Af F) σ J P : Set (HA (Af F) σ J)) := by
  have h : (Nsub (Af F) σ J P : Set (HA (Af F) σ J)) =
      (uniFlag (Af F) σ J P.e : Set (HA (Af F) σ J)) ∩
        ⋂ v, ⋂ (_ : InXperp (Af F) σ J P v), (fun g => lin (Af F) σ J g v - v) ⁻¹'
          (spanR (F := F) (Af F) P.e Set.univ : Set (Fin n → Af F ⊗[F] E)) := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    exact Iff.rfl
  rw [h]
  refine (isClosed_uniFlag P.e P.f (dual_e hJ hinv P T hP)).inter
    (isClosed_iInter fun v => isClosed_iInter fun _ => ?_)
  exact (isClosed_spanR P.e P.f (dual_e hJ hinv P T hP) _).preimage
    ((continuous_lin _).sub continuous_const)
end PI.LevelKSplit.W.ExC
