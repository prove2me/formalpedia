-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_isMultiHomog_linForm_67474a920261
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:45:22.89883+00:00
-- url     : https://prove2.me/submissions/86dbdb37-f20b-40f6-8083-cfe1915f0871

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LinFormOneZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PDivSuppHorizontalArithVar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ObjectsChow
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal divSupp Xc)
namespace GroundTheory.Heights₂.Heights.ObjectsChow
theorem _root_.solution {n : ℕ} (u : Fin n → ℤ) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (IndefiniteRowSideFullHecke.ArithBezout.linForm u) (fun _ => 1) := by
  classical
  intro m hm k
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  rw [C_mul_X_eq_monomial] at hi
  have hmi := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hi)
  subst hmi
  cases k
  simp [Finsupp.single_apply]
end GroundTheory.Heights₂.Heights.ObjectsChow
