-- Prove2me | solution 1 for ObfImpossibility.RiceSimulator.stage_answer_sound
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T10:59:18.545167+00:00
-- url     : https://prove2.me/submissions/2024e604-c077-4da4-bdfc-28a0fe4ec487

import Mathlib
import Definitions.Def_ObfImpossibility_RiceSimulator_Setting
namespace ObfImpossibility.RiceSimulator

/-- p. A:41: if the simulator halts (at some stage `n` with answer `σ`) then it returns the
same answer as `T(M)`. -/
theorem _root_.solution (T M : Machine) (n σ : ℕ) (h : StageAnswer T M n σ) :
    σ ∈ T.eval (Encodable.encode M) := by
  apply Nat.Partrec.Code.evaln_sound
  exact h M ⟨rfl, fun _ _ _ _ => rfl⟩

end ObfImpossibility.RiceSimulator
