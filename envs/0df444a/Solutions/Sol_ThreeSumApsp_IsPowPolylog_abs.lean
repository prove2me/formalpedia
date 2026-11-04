-- Prove2me | solution 1 for ThreeSumApsp.IsPowPolylog.abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:16:33.269193+00:00
-- url     : https://prove2.me/submissions/292ef4b3-98a9-4a56-80b0-7ef6add7b64a

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog

set_option autoImplicit false
section
open Filter Asymptotics
open ThreeSumApsp
variable {f g : ℕ → ℝ} {a b : ℝ}
open ThreeSumApsp.IsPowPolylog
namespace ThreeSumApsp.IsPowPolylog
theorem _root_.solution (hf : IsPowPolylog f a) : IsPowPolylog (fun n => |f n|) a := by
  obtain ⟨e, hf⟩ := hf
  exact ⟨e, hf.norm_left⟩
end ThreeSumApsp.IsPowPolylog
