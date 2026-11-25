-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.lminor_submatrix_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:00:28.182326+00:00
-- url     : https://prove2.me/submissions/41bdf84f-10e4-4833-ae2f-ae4b39233b29

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open Matrix NumberField
open scoped ComplexOrder ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i : Fin (n + 1)) :
    lminor (A.submatrix Fin.castSucc Fin.castSucc) i = lminor A i.castSucc := by
  unfold lminor
  rw [Matrix.submatrix_submatrix]
  rfl
end ReciprocityTheory.ChartRestriction.G.FD
