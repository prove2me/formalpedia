-- Prove2me | solution 1 for PI.WAU.Cpt.ctsA_cTE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:31:21.436087+00:00
-- url     : https://prove2.me/submissions/d81e948e-dbb4-4811-a56d-5a970400b07b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_MulVecMemLf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_IsCompactCset
import Theorems.Thm_PI_WAU_ctsA_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU
open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix
open PI.WAU.Cpt
variable (I : AutInst)
namespace PI.WAU.Cpt
theorem _root_.solution {f : Co I × Co I → Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)}
    (hf : ∀ i j, CtsA (bs I) (fun p => f p i j)) (i j : Fin I.n) :
    CtsA (bs I) (fun p => Formalism.UG.cT (sg I) (f p) i j) := by
  show CtsA (bs I) (fun p => Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Af I.F)) (f p j i))
  exact ctsA_map _ (hf j i)
end PI.WAU.Cpt
