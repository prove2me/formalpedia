-- Prove2me | solution 1 for P2M_Formalism_L2_Pj_QAt_TieLDB_smul_comm__12647fffb386
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:09:48.195923+00:00
-- url     : https://prove2.me/submissions/fcdf8eba-8d27-4f56-8201-729f84521c14

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.L2.Pj.QAt.TieLDB
open Module
variable {A : Type*} [CommRing A] (p : Ideal A) [p.IsPrime]
  {V : Type*} [AddCommGroup V] [Module A V] [Module (Localization.AtPrime p) V]
  [IsScalarTower A (Localization.AtPrime p) V]
namespace Formalism.L2.Pj.QAt.TieLDB
theorem _root_.solution (s : A) (o : Localization.AtPrime p) (v : V) : s • (o • v) = o • (s • v) := by
  rw [← smul_assoc, Algebra.smul_def, mul_comm, mul_smul, algebraMap_smul]
end Formalism.L2.Pj.QAt.TieLDB
