-- Prove2me | solution 1 for PI.LevelKSplit.W.NCL.unipotent_radical_normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:43:18.711008+00:00
-- url     : https://prove2.me/submissions/60231b22-77e0-4627-bde6-84f3d02944ff

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevLSubPerp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LeviInfUnipotentEqOne
import Theorems.Thm_Formalism_L2_SG_Sub_mem_stabT
import Theorems.Thm_PI_LevelKSplit_W_Glob_lin_fix_span
import Theorems.Thm_PI_LevelKSplit_W_Glob_spanR_univ


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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub PI.LevelKSplit.W.NC PI.VolSemiDirect.W
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r) (T : F)
variable {R σ J P T}
variable (R σ J P)
variable {R σ J P}
namespace PI.LevelKSplit.W.NCL
theorem _root_.solution (n m : HA R σ J) (hn : n ∈ Nsub R σ J P) (hm : m ∈ LevelUnipotentSubgroup R σ J P) :
    n * m * n⁻¹ ∈ LevelUnipotentSubgroup R σ J P := by
  have hm' := Subgroup.mem_inf.1 hm
  refine Subgroup.mem_inf.2 ⟨(Nsub R σ J P).mul_mem ((Nsub R σ J P).mul_mem hn hm'.1)
    ((Nsub R σ J P).inv_mem hn), (mem_stabT R σ J P.e _).2 fun b => ?_⟩
  have hmS := (mem_stabT R σ J P.e m).1 hm'.2
  have h1 : lin R σ J n⁻¹ (ratV (F := F) R (P.e b)) ∈
      Submodule.span (R ⊗[F] E) (Set.range fun a => ratV (F := F) R (P.e a)) := by
    have := uni_map_le ((Nsub R σ J P).inv_mem hn).1 Set.univ (fun _ _ _ _ => Set.mem_univ _)
      (Submodule.mem_map_of_mem (Submodule.subset_span ⟨b, Set.mem_univ _, rfl⟩))
    rw [PI.LevelKSplit.W.Glob.spanR_univ] at this
    exact this
  rw [lin_mul, lin_mul, PI.LevelKSplit.W.Glob.lin_fix_span m P.e hmS _ h1, lin_lin_inv]
end PI.LevelKSplit.W.NCL
