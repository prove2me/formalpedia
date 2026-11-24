-- Prove2me | solution 1 for ULHC.Ends.merge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:10:53.55557+00:00
-- url     : https://prove2.me/submissions/6cd51d26-428e-4415-bf3c-ae985617af3a

import Definitions.Def_ULHC_Flip
import Definitions.Def_ULHC_AFlip
import Theorems.Thm_ULHC_Ends_conn_iff
import Theorems.Thm_ULHC_ncomp_insert_merge


set_option autoImplicit true
open ULHC
open Finset Classical
variable {e : Edge} {u v : Pt}
namespace ULHC
namespace Ends
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} (h : Ends e u v) (hu : u ∈ V) (hv : v ∈ V)
    (hn : ¬ Conn F u v) : ncomp V (insert e F) + 1 = ncomp V F := by
  apply ncomp_insert_merge
  · rcases h with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;> assumption
  · rcases h with ⟨_, h2⟩ | ⟨_, h2⟩ <;> rw [h2] <;> assumption
  · rwa [h.conn_iff]
end Ends
end ULHC
