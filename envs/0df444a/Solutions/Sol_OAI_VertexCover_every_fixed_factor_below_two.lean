-- Prove2me | solution 1 for OAI.VertexCover.every_fixed_factor_below_two
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T00:19:35.172827+00:00
-- url     : https://prove2.me/submissions/b2f8e2f1-f8af-4eb2-bdbb-f718475f239c

import Mathlib
import Definitions.Def_VertexCover
import Definitions.Def_OAIQ028V008

section
-- module Solutions.OAIQ028_VC.VertexCover_Machines_Approximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                             
section

namespace VertexCover
open Machine

theorem exists_separating_integer {α : ℝ} (hα : α < 2) :
    ∃ m : ℕ, 4 ≤ m ∧ α*(1/2+1/(m:ℝ)) < 1-1/(m:ℝ) := by
  have hden : 0 < 2-α := sub_pos.mpr hα
  obtain ⟨m,hm⟩ := exists_nat_gt (max (4:ℝ) (2*(α+1)/(2-α)))
  have hm4 : 4 ≤ m := by
    have h := (le_max_left (4:ℝ) (2*(α+1)/(2-α))).trans_lt hm
    exact_mod_cast h.le
  have hb : 2*(α+1) < (m:ℝ)*(2-α) :=
    (div_lt_iff₀ hden).mp ((le_max_right (4:ℝ) _).trans_lt hm)
  have hmp : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  refine ⟨m,hm4,?_⟩
  apply (mul_lt_mul_iff_left₀ hmp).mp
  have hs : (1/2+1/(m:ℝ))*(m:ℝ) = (m:ℝ)/2+1 := by field_simp
  have hn : (1-1/(m:ℝ))*(m:ℝ) = (m:ℝ)-1 := by field_simp
  rw [mul_assoc,hs,hn]
  nlinarith

end VertexCover
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ028_VC.VertexCover_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                  
section

namespace VertexCover
 theorem every_fixed_factor_below_two_oai (α : ℝ) (hα : 1 ≤ α) (hα2 : α < 2)
    (algorithm : Approximation α) : Nonempty ThreeSATDecision := by
  obtain ⟨m,hm,hsep⟩ := exists_separating_integer hα2
  exact ⟨decisionOfGap hα m hm hsep (Machine.MainReduction.reduction m hm) algorithm⟩
end VertexCover
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

theorem solution : type_of% @OAI.VertexCover.every_fixed_factor_below_two_oai := @OAI.VertexCover.every_fixed_factor_below_two_oai
