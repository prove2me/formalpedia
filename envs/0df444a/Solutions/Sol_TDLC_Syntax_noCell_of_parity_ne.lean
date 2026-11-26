-- Prove2me | solution 1 for TDLC.Syntax.noCell_of_parity_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:27:52.950606+00:00
-- url     : https://prove2.me/submissions/04a525ce-1b10-4cfc-ad68-53c08f505ed1

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Syntax
import Theorems.Thm_TDLC_Syntax_interpret_parity
import Theorems.Thm_TDLC_Path_parity_lEmbed
import Theorems.Thm_TDLC_path2PreservesParity
attribute [local simp] TDLC.Path.parity_lEmbed



set_option autoImplicit true
open TDLC TDLC.Syntax
namespace TDLC.Syntax
theorem _root_.solution {t s : Tm Γ a} (c d : Conv t s)
    (hne : c.parity ≠ d.parity) (ρ : Env U Γ) :
    ¬ Nonempty (TDLC.Path2 (TDLC.Path.lEmbed (interpret c ρ))
      (TDLC.Path.lEmbed (interpret d ρ))) := by
  intro ⟨cells⟩
  have h := TDLC.path2PreservesParity cells
  rw [TDLC.Path.parity_lEmbed, TDLC.Path.parity_lEmbed,
    interpret_parity, interpret_parity] at h
  exact hne h
end TDLC.Syntax
