-- Prove2me | solution 1 for PI.LevelKSplit.W.ExC.isClosed_uniFlag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:25:11.145406+00:00
-- url     : https://prove2.me/submissions/cac7824d-0746-46de-b92d-48bfd767accb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_RatVMemSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnitaryGroupSecondCountableT2
import Theorems.Thm_PI_LevelKSplit_W_ExC_isClosed_spanR
import Theorems.Thm_PI_LevelKSplit_W_ExC_continuous_lin

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
theorem _root_.solution {m : ℕ} (Y D : Fin m → Fin n → E)
    (hD : ∀ a a', hE σ J (D a') (Y a) = if a = a' then 1 else 0) :
    IsClosed (uniFlag (Af F) σ J Y : Set (HA (Af F) σ J)) := by
  have h : (uniFlag (Af F) σ J Y : Set (HA (Af F) σ J)) =
      ⋂ b, (fun g => lin (Af F) σ J g (ratV (F := F) (Af F) (Y b)) - ratV (F := F) (Af F) (Y b)) ⁻¹'
        (spanR (F := F) (Af F) Y {a | a < b} : Set (Fin n → Af F ⊗[F] E)) := by
    ext g
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    exact Iff.rfl
  rw [h]
  exact isClosed_iInter fun b =>
    (isClosed_spanR Y D hD _).preimage ((continuous_lin _).sub continuous_const)
end PI.LevelKSplit.W.ExC
