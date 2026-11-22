-- Prove2me | solution 1 for PES.label_mem_labelLog
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:19:35.344654+00:00
-- url     : https://prove2.me/submissions/ffd85621-0c71-47f5-acc5-e1031c866802

import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_Family_Log
import Definitions.Def_EventStructures_Prime_Log
import Theorems.Thm_Log_label_mem_labelLog


set_option autoImplicit true
variable {L : Type*} (es : PES L)
open PES
open Configuration
local infixl:50 " ## " => es.minimalConflict
open PES
namespace PES
theorem _root_.solution {c : Conf es} {e : es.Event} (h : e ∈ log es c) :
    es.label e ∈ labelLog es c :=
  Log.label_mem_labelLog es.toFamily h
end PES
