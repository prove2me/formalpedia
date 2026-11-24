-- Prove2me | solution 1 for ULHC.cell_prev
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:25:46.97598+00:00
-- url     : https://prove2.me/submissions/3933913f-21a3-4415-a675-8408ff6a1208

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Touch
import Theorems.Thm_ULHC_nb_cellJ
import Theorems.Thm_ULHC_nb_nb_opp


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge} {c : Pt} {s : Side} {k : ℕ}
  (hF : Deg2 V F) (hT : NoTypeIII V F) (hk : k % 2 = 0)
  (hcell : ∀ j ≤ k + 1, IsCell V (cellJ c s j)) (hpat : StripPat F c s (k + 2))
  (hsep : ¬ Conn F (back1 c s) (front1 c s))
  {z : Pt} {tf : Side} {m i i0 : ℕ} (hz : SigFrom F z tf m i0) (hi0 : i0 ≤ i) (hi : i < m)
namespace ULHC
theorem _root_.solution {z : Pt} {tf : Side} {i : ℕ} (hi : 1 ≤ i) :
    cellJ z tf (i - 1) = nb (cellJ z tf i) tf.opp := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [show j + 1 - 1 = j by omega, ← nb_cellJ, nb_nb_opp]
end ULHC
