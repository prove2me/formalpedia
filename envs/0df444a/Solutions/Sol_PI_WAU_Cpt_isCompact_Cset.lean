-- Prove2me | solution 1 for PI.WAU.Cpt.isCompact_Cset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:02:40.806488+00:00
-- url     : https://prove2.me/submissions/2d99ca8e-3f51-4784-98e4-31463eba072f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_MulVecMemLf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_IsCompactCset
import Theorems.Thm_PI_WAU_Cpt_isCompact_Bx
import Theorems.Thm_PI_WAU_Cpt_ctsA_fst
import Theorems.Thm_PI_WAU_Cpt_ctsA_snd
import Theorems.Thm_PI_WAU_Cpt_ctsA_mulE
import Theorems.Thm_PI_WAU_Cpt_ctsA_constE
import Theorems.Thm_PI_WAU_Cpt_ctsA_cTE
import Theorems.Thm_PI_WAU_Cpt_isClosed_matEq
import Theorems.Thm_PI_WAU_Cpt_isClosed_lat
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
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
theorem _root_.solution (N d : ℕ) (hd : 0 < d)
    (hlow : ∀ y : Fin I.n → I.E ⊗[I.F] Af I.F, (∀ j, IntC (bs I) (y j)) → d • y ∈ I.Lf) :
    IsCompact (Cset I N) := by
  have hbox : IsCompact {p : Co I × Co I | ∀ i j k, p.1 i j k ∈ Bx I N ∧ p.2 i j k ∈ Bx I N} := by
    have : {p : Co I × Co I | ∀ i j k, p.1 i j k ∈ Bx I N ∧ p.2 i j k ∈ Bx I N} =
        (Set.univ.pi fun _ => Set.univ.pi fun _ => Set.univ.pi fun _ => Bx I N) ×ˢ
          (Set.univ.pi fun _ => Set.univ.pi fun _ => Set.univ.pi fun _ => Bx I N) := by
      ext p
      simp only [Set.mem_prod, Set.mem_univ_pi, Set.mem_ofPred_eq]
      exact ⟨fun h => ⟨fun i j k => (h i j k).1, fun i j k => (h i j k).2⟩,
        fun h i j k => ⟨h.1 i j k, h.2 i j k⟩⟩
    rw [this]
    have h3 := isCompact_univ_pi fun _ : Fin I.n => isCompact_univ_pi fun _ : Fin I.n =>
      isCompact_univ_pi fun _ : ιb I => isCompact_Bx I N
    exact h3.prod h3
  have hf := ctsA_fst I
  have hs := ctsA_snd I
  have hc1 := isClosed_matEq I (ctsA_mulE I hf hs) (ctsA_constE I 1)
  have hc2 := isClosed_matEq I (ctsA_mulE I hs hf) (ctsA_constE I 1)
  have hc3 := isClosed_matEq I (ctsA_mulE I (ctsA_mulE I (ctsA_cTE I hf) (ctsA_constE I (Jf I))) hf)
    (ctsA_constE I (Jf I))
  have hc4 := isClosed_lat I d hd hlow hf
  have hc5 := isClosed_lat I d hd hlow hs
  exact hbox.inter_right (hc1.inter (hc2.inter (hc3.inter (hc4.inter hc5))))
end PI.WAU.Cpt
