-- Prove2me | solution 1 for PretorsionImageClosed.Challenge.gandhiImageClosed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:18:05.92022+00:00
-- url     : https://prove2.me/submissions/56150cfc-54a1-4bf8-9eab-0e879af4a68d

module
public import Definitions.Def_PretorsionImageClosed
public import Definitions.Def_PretorsionImageClosed_Solution
public import Theorems.Thm_PretorsionImageClosed_gandhiImageClosed


set_option autoImplicit true
@[expose] public section
public section
universe u
namespace PretorsionImageClosed.Challenge
theorem _root_.solution :
    PretorsionImageClosed.Statement.GandhiImageClosed.{u} :=
  PretorsionImageClosed.gandhiImageClosed
end PretorsionImageClosed.Challenge
