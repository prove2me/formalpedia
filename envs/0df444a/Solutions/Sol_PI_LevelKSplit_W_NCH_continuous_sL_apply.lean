-- Prove2me | solution 1 for PI.LevelKSplit.W.NCH.continuous_sL_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:53:54.910917+00:00
-- url     : https://prove2.me/submissions/bacd5759-9784-4cf6-a16e-3d9c42e1251a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnipotentRadicalActionFormula
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCHeisC
import Theorems.Thm_PI_VolSemiDirect_W_Md_continuous_hR
import Theorems.Thm_PI_VolStabSW_continuous_hR


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R] [IsTopologicalRing (R ⊗[F] E)]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} (P : Frame E M r) (T : F)
namespace PI.LevelKSplit.W.NCH
theorem _root_.solution (half : R ⊗[F] E) {X : Type} [TopologicalSpace X]
    {y : X → Fin r → Fin M → R ⊗[F] E} (hy : Continuous y) (v : Fin M → R ⊗[F] E) :
    Continuous fun x => sL (PI.VolSemiDirect.W.datR R σ J P T) half (y x) v := by
  have hh : ∀ {u w : X → Fin M → R ⊗[F] E}, Continuous u → Continuous w →
      Continuous fun x => (PI.VolSemiDirect.W.datR R σ J P T).h (u x) (w x) :=
    fun hu hw => PI.VolSemiDirect.W.Md.continuous_hR _ σ J (hu := hu) (hv := hw)
  simp only [sL, uv, cf, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.sum_apply, Finset.sum_apply, LinearMap.smulRight_apply, PI.VolSemiDirect.W.PG.Dat.hL,
    LinearMap.coe_mk, AddHom.coe_mk]
  refine (continuous_const.add (continuous_finset_sum _ fun a _ => ?_)).sub
    (continuous_finset_sum _ fun b _ => ?_)
  · exact (hh continuous_const continuous_const).smul (((continuous_apply a).comp hy).add
      (continuous_finset_sum _ fun b _ => ((continuous_const.mul
        (hh ((continuous_apply b).comp hy) ((continuous_apply a).comp hy))).neg).smul continuous_const))
  · exact (hh ((continuous_apply b).comp hy) continuous_const).smul continuous_const
end PI.LevelKSplit.W.NCH
