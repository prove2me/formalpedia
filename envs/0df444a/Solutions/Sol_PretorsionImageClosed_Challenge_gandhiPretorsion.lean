-- Prove2me | solution 1 for PretorsionImageClosed.Challenge.gandhiPretorsion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:31:05.679808+00:00
-- url     : https://prove2.me/submissions/3c6fb6bf-be05-4f1f-984f-457d65c046de

module
public import Definitions.Def_PretorsionImageClosed
public import Definitions.Def_PretorsionImageClosed_Solution
public import Theorems.Thm_PretorsionImageClosed_gandhiPretorsion


set_option autoImplicit true
@[expose] public section
public section
universe u
namespace PretorsionImageClosed.Challenge
theorem _root_.solution :
    PretorsionImageClosed.Statement.GandhiPretorsion.{u} :=
  PretorsionImageClosed.gandhiPretorsion
end PretorsionImageClosed.Challenge
