-- Prove2me | solution 1 for PI.LevelKSplit.W.NCL.isClosed_Asub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:43:47.730829+00:00
-- url     : https://prove2.me/submissions/7ff1916e-4dd4-4f08-8110-9a46c669f2d0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LeviInfUnipotentEqOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCIface
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnitaryGroupSecondCountableT2
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_IsClosedAsub
import Theorems.Thm_PI_LevelKSplit_W_NCL_mem_Asub
import Theorems.Thm_PI_LevelKSplit_W_ExC_closed_SNH
import Theorems.Thm_PI_LevelKSplit_W_ExC_isClosed_spanR
import Theorems.Thm_PI_VolSemiDirect_W_Md_continuous_linear_action


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCL
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField PI.LevelKSplit.W.NC PI.VolSemiDirect.W
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ}
namespace PI.LevelKSplit.W.NCL
theorem _root_.solution (hJ : IsHermND σ J) (hinv : ∀ x, σ (σ x) = x) (P : Frame E M r) (T : F)
    (hP : P.IsStd σ J T) : IsClosed (Asub (Af F) σ J P : Set (HA (Af F) σ J)) := by
  have hD : ∀ a a', hE σ J (P.e a') (P.f a) = if a = a' then 1 else 0 := fun a a' => by
    rw [hP.2.2.1 a' a]
    by_cases h : a = a'
    · subst h; simp
    · simp [h, Ne.symm h]
  have hF : IsClosed (spanR (F := F) (Af F) P.f Set.univ : Set (Fin M → Af F ⊗[F] E)) :=
    PI.LevelKSplit.W.ExC.isClosed_spanR P.f P.e hD Set.univ
  have e : (Asub (Af F) σ J P : Set (HA (Af F) σ J)) =
      (Nsub (Af F) σ J P : Set (HA (Af F) σ J)) ∩
        ((⋂ w ∈ Wp (Af F) σ J P, {g : HA (Af F) σ J | lin (Af F) σ J g w = w}) ∩
        ((⋂ b, {g : HA (Af F) σ J | lin (Af F) σ J g (ratV (F := F) (Af F) (P.f b)) ∈
            spanR (F := F) (Af F) P.f Set.univ}) ∩
          (⋂ b, {g : HA (Af F) σ J | lin (Af F) σ J g⁻¹ (ratV (F := F) (Af F) (P.f b)) ∈
            spanR (F := F) (Af F) P.f Set.univ}))) := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    exact mem_Asub
  rw [e]
  refine (PI.LevelKSplit.W.ExC.closed_SNH hJ hinv P T hP).2.1.inter
    ((isClosed_biInter fun w _ => ?_).inter ((isClosed_iInter fun b => ?_).inter
      (isClosed_iInter fun b => ?_)))
  · exact isClosed_eq (Md.continuous_linear_action (Af F) σ J continuous_id continuous_const) continuous_const
  · exact hF.preimage (Md.continuous_linear_action (Af F) σ J continuous_id continuous_const)
  · exact hF.preimage (Md.continuous_linear_action (Af F) σ J continuous_inv continuous_const)
end PI.LevelKSplit.W.NCL
