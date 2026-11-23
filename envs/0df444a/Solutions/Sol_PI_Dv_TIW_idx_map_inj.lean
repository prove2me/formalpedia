-- Prove2me | solution 1 for PI.Dv.TIW.idx_map_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:30.537802+00:00
-- url     : https://prove2.me/submissions/321923a3-e622-4fb3-97ba-52c7cafa14bf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxNonnegOfLe
import Theorems.Thm_PI_Dv_TIW_idx_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.TIW
theorem _root_.solution (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {V' : Type} [AddCommGroup V'] [Module K V']
    [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (φ : V →ₗ[K] V') (M N : Submodule (𝓞 K) V) (hM : M.FG)
    (hN : N.FG) (h1 : Submodule.span K (M : Set V) = Submodule.span K (N : Set V))
    (hinjM : ∀ x ∈ M, φ x = 0 → x = 0) (hinjN : ∀ x ∈ N, φ x = 0 → x = 0) :
    idxAt w M N = idxAt w (M.map (φ.restrictScalars (𝓞 K))) (N.map (φ.restrictScalars (𝓞 K))) := by
  refine idx_map hI w φ M N hM hN h1 ?_
  have hb : ∀ P : Submodule (𝓞 K) V, (∀ x ∈ P, φ x = 0 → x = 0) →
      P ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) = ⊥ := by
    intro P hP
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    exact (Submodule.mem_bot _).mpr (hP x hx1 hx2)
  rw [hb M hinjM, hb N hinjN]
end PI.Dv.TIW
