-- Prove2me | solution 1 for ThreeSum.TernaryPairedMinorReindex.paired_rowWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:29:05.371581+00:00
-- url     : https://prove2.me/submissions/daba20cc-160c-4384-9b75-4ab4ae4182dc

import Definitions.Def_Submission_ThreeSum_TernaryPairedPotential
import Definitions.Def_Submission_ThreeSum_TernaryPairedMinorReindex
import Theorems.Thm_ThreeSum_TernaryPairedMinorReindex_rowWeight_equiv

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedMinorReindex
open Matrix Finset TernaryPairedPotential
open scoped BigOperators
namespace ThreeSum.TernaryPairedMinorReindex
theorem _root_.solution {K Λ : ℕ} (L R : Fin K→Fin Λ→ℤ) :
    rowWeight (Sum.elim L R)=
      minorWeight (fun i => Sum.elim L R (finSumFinEquiv.symm i)) :=
  rowWeight_equiv _ finSumFinEquiv.symm
end ThreeSum.TernaryPairedMinorReindex
