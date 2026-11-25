-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_A_subst_one__7b65fa7ad290
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:51:06.380487+00:00
-- url     : https://prove2.me/submissions/bfce263e-ba1e-4c30-b889-3d035858b8be

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementZ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_LogExp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
variable {R : Type u} [CommRing R]
namespace Formalism.L2.Th1.A
theorem _root_.solution {a : R⟦X⟧} (ha : HasSubst a) : (1 : R⟦X⟧).subst a = 1 := by
  first
    | (rw [← PowerSeries.coe_substAlgHom ha]; exact map_one _)
    | simp
end Formalism.L2.Th1.A
