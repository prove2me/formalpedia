-- Prove2me | solution 1 for ThreeSum.TernaryPairedMinorReindex.minorWeight_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:20:42.991414+00:00
-- url     : https://prove2.me/submissions/b25b59f5-469d-4722-ad46-6da72d5e84f9

import Definitions.Def_Submission_ThreeSum_TernaryPairedPotential
import Definitions.Def_Submission_ThreeSum_TernaryPairedMinorReindex

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedMinorReindex
open Matrix Finset TernaryPairedPotential
open scoped BigOperators
namespace ThreeSum.TernaryPairedMinorReindex
theorem _root_.solution {d Λ : ℕ} (A : Matrix (Fin d) (Fin Λ) ℤ) (e : Equiv.Perm (Fin d)) :
    minorWeight (fun i => A (e i))=minorWeight A := by
  unfold minorWeight
  apply sum_congr rfl
  intro f hf
  congr 1
  have hh := Matrix.abs_det_submatrix_equiv_equiv e (Equiv.refl (Fin d)) (A.submatrix id f)
  have he : (fun i j => A (e i) (f j))=(A.submatrix id f).submatrix e (Equiv.refl _) := rfl
  change (Matrix.submatrix (fun i => A (e i)) id f).det.natAbs=(A.submatrix id f).det.natAbs
  change |(Matrix.submatrix (fun i => A (e i)) id f).det|=|(A.submatrix id f).det| at hh
  rw [←Int.natCast_natAbs,←Int.natCast_natAbs] at hh
  exact Int.ofNat_inj.mp hh
end ThreeSum.TernaryPairedMinorReindex
