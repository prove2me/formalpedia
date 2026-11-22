-- Prove2me | solution 1 for PES.toLTSI_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:09:50.150057+00:00
-- url     : https://prove2.me/submissions/78c3d093-93d0-4e62-a06a-2b9eb1f2d6ea

import Definitions.Def_EventStructures_Prime_Basic
import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_LTS_Basic
import Definitions.Def_EventStructures_Stable_LTSI
import Definitions.Def_EventStructures_Family_LTSI
import Definitions.Def_EventStructures_Prime_LTSI
import Theorems.Thm_PES_esStep_iff
import Theorems.Thm_PES_esIndep_iff
import Theorems.Thm_Bisimilar_symm
import Theorems.Thm_ConfFamily_Indep_symm


set_option autoImplicit true
variable {L : Type*}
open PES
variable (es : PES L)
open Configuration
local infix:50 " ⊢ " => enables es
local infixl:50 " ⋈ " => es.concurrent
namespace PES
theorem _root_.solution : toLTSI es = ConfFamily.toLTSI es.toFamily := by
  unfold toLTSI ConfFamily.toLTSI
  congr 1
  · funext c a c'; exact propext (Iff.symm (esStep_iff es))
  · funext c a c₁ b c₂; exact propext (Iff.symm (esIndep_iff es))
end PES
