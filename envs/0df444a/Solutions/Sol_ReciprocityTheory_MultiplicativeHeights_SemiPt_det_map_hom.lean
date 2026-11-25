-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.det_map_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:44:51.096261+00:00
-- url     : https://prove2.me/submissions/67a14a7d-3b43-477a-9453-5d13d6bb718c

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegZ
import Definitions.Def_Lemmata_GeneralBFactSecondAlt_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegZA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
theorem _root_.solution {K L : Type} [Field K] [Field L] {r : ℕ} (f : K →+* L)
    (A : Matrix (Fin r) (Fin r) K) : (A.map f).det = f A.det := (RingHom.map_det f A).symm
end ReciprocityTheory.MultiplicativeHeights.SemiPt
