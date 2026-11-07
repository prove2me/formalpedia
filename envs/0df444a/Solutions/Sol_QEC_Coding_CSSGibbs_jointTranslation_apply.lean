-- Prove2me | solution 1 for QEC.Coding.CSSGibbs.jointTranslation_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:31:56.931545+00:00
-- url     : https://prove2.me/submissions/0829a6f6-67d7-4e71-8ddd-23eabcdf8d5b

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Selection
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.CSSGibbs
open Classical PauliSymplectic StabilizerCode Semantics
open scoped BigOperators
variable {ι κP κQ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κP] [Fintype κQ] [DecidableEq κP] [DecidableEq κQ]
variable (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
  (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
  (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
attribute [local instance] QEC.Coding.CSSGibbs._p2m_local_instance_22196e9987_17
attribute [local instance] QEC.Coding.CSSGibbs._p2m_local_instance_22196e9987_18
namespace QEC.Coding.CSSGibbs
theorem _root_.solution (E : Binary ι) (s : Realizable P Q) :
    jointTranslation P Q E s =
      (rangeShift P E.vector.xPart s.1, rangeShift Q E.vector.zPart s.2) := rfl
end QEC.Coding.CSSGibbs
