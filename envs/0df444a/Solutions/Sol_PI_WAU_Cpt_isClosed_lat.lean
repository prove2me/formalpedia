-- Prove2me | solution 1 for PI.WAU.Cpt.isClosed_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:49:29.459054+00:00
-- url     : https://prove2.me/submissions/a7335858-75fb-4ad5-92e2-c84137557c21

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_MulVecMemLf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_IsCompactCset
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_WAU_Cpt_isClosed_LfC
import Theorems.Thm_PI_WAU_ctsA_const
import Theorems.Thm_PI_WAU_ctsA_mul
import Theorems.Thm_PI_WAU_ctsA_sum
import Theorems.Thm_PI_WAU_emb_coord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WAU
open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix
open PI.WAU.Cpt
variable (I : AutInst)
namespace PI.WAU.Cpt
theorem _root_.solution (d : ℕ) (hd : 0 < d)
    (hlow : ∀ y : Fin I.n → I.E ⊗[I.F] Af I.F, (∀ j, IntC (bs I) (y j)) → d • y ∈ I.Lf)
    {f : Co I × Co I → Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)}
    (hf : ∀ i j, CtsA (bs I) (fun p => f p i j)) :
    IsClosed {p | ∀ l ∈ I.L, f p *ᵥ inclV (F := I.F) l ∈ I.Lf} := by
  have : {p | ∀ l ∈ I.L, f p *ᵥ inclV (F := I.F) l ∈ I.Lf} =
      ⋂ l ∈ I.L, {p | f p *ᵥ inclV (F := I.F) l ∈ I.Lf} := by
    ext; simp
  rw [this]
  refine isClosed_biInter fun l _ => ?_
  have hc : Continuous (fun p => fun j => coord (bs I) ((f p *ᵥ inclV (F := I.F) l) j)) := by
    refine continuous_pi fun j => ?_
    have : CtsA (bs I) (fun p => (f p *ᵥ inclV (F := I.F) l) j) := by
      simp only [Matrix.mulVec, dotProduct]
      exact ctsA_sum _ fun k _ => ctsA_mul (hf j k) (ctsA_const _)
    exact this
  have := (isClosed_LfC I d hd hlow).preimage hc
  convert this using 1
  ext p
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, emb_coord]
end PI.WAU.Cpt
