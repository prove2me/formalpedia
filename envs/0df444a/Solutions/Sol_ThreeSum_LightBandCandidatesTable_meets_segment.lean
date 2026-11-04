-- Prove2me | solution 1 for ThreeSum.LightBandCandidatesTable.meets_segment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:23:39.997929+00:00
-- url     : https://prove2.me/submissions/9cac1f8c-7703-42e3-92f7-22fed480ee50

import Definitions.Def_Submission_ThreeSum_LightBandCandidatesRow
import Definitions.Def_Submission_ThreeSum_BandCandidateRowsMemory
import Definitions.Def_Submission_ThreeSum_LightBandCandidatesTable
import Definitions.Def_WeightedCache3SUM_Alias_66a9a0be433f5f2b
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Definitions.Def_WeightedCache3SUM_Alias_68aebfd4f850b67e
import Definitions.Def_WeightedCache3SUM_Alias_be05f096c8d0157a
import Definitions.Def_WeightedCache3SUM_Alias_887023f6a62327ec
import Definitions.Def_WeightedCache3SUM_Alias_4c62aff33317338c
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_f2e191e7f7b92ebc
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Definitions.Def_WeightedCache3SUM_Alias_eb65baeba73fd57c
import Definitions.Def_WeightedCache3SUM_Alias_3b3552e2795ab46d
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Theorems.Thm_ThreeSum_LightScaleArray_meets
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandCandidatesTable
open Light BandCandidateRows
set_option maxHeartbeats 1800000
set_option maxRecDepth 7000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {src dst m n U : ℕ} {f : ℕ → ℕ → ℕ}
namespace ThreeSum.LightBandCandidatesTable
theorem _root_.solution {pMain pRow pCell : ℕ} (mode : Mode) (hmain : P[pMain]? = some (body pRow))
    (hrow : P[pRow]? = some (LightBandCandidatesRow.body pCell))
    (hcell : P[pCell]? = some (LightBandCandidatesCell.body mode)) (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d + 1 < lim.depth) (hsrc : src + m * n ≤ dst) (hspace : dst + 4 * (m * n) ≤ lim.space)
    (hword : ((U + 10 : ℕ) : ℤ) ≤ lim.word) (hm : m ≤ U) (hn : n ≤ U) (hf : ∀ i < m, ∀ j < n, f i j ≤ U)
    (hread : ∀ i < m, ∀ j < n, μ (src + i * n + j) = (f i j : ℤ)) :
    Meets lim P pMain d [src, dst, m, n] μ (time m n)
      (fun _ ν =>
        Seg ν dst (cells (rect m n (fun i j => make mode i j (f i j)))) ∧ SameOutside μ ν dst (4 * (m * n))) :=
  (meets mode hmain hrow hcell hw hd hsrc hspace hword hm hn hf hread).mono le_rfl (fun _ _ h => ⟨seg_rect _ h.1, h.2⟩)
end ThreeSum.LightBandCandidatesTable
