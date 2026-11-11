-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.combine_full_words
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:18:06.636199+00:00
-- url     : https://prove2.me/submissions/9de0756f-7195-42e3-9df7-31b3814a1639

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_word_add_self

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open scoped Classical
universe u v w
namespace QEC.Coding.BDL26HistoryErrorTelescoping
theorem _root_.solution {I : Type u} {J : Type v} {K : Type w}
    (f : Word BDL26Field I →ₗ[BDL26Field] Word BDL26Field J)
    (g : Word BDL26Field K →ₗ[BDL26Field] Word BDL26Field J)
    (u e d d' : Word BDL26Field J) (y y' : Word BDL26Field I)
    (p p' : Word BDL26Field K)
    (h : f y=u+d+g p) (h' : f y'=u+e+d'+g p') :
    e+d+d'=f (y+y')+g (p+p') := by
  rw [map_add,map_add,h,h']
  calc
    e+d+d' = (u+u)+(e+d+d')+((g p+g p)+(g p'+g p')) := by
      rw [word_add_self,word_add_self,word_add_self,zero_add,zero_add,add_zero]
    _ = (u+d+g p)+(u+e+d'+g p')+(g p+g p') := by ac_rfl
end QEC.Coding.BDL26HistoryErrorTelescoping
