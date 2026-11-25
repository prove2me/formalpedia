-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_chowDegree_eq_573b7e6f4160
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:45:09.558609+00:00
-- url     : https://prove2.me/submissions/87edcca5-33b5-4849-a634-ce8a971e79b6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_IsMultiHomogOfIsChowForm

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
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk Xc IsMultihomog)
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ObjectsChow
theorem _root_.solution {F : Type*} [Field F] {I : Ideal (MvPolynomial (Fin n) F)} {k δ : ℕ}
    (hk : 0 < k) {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f)
    (hδ : IsMultiHomog δ f) : chowDegree I k = δ := by
  have key : ∀ δ', (∃ g, IsChowForm I k g ∧ IsMultiHomog δ' g) → δ' = δ := by
    rintro δ' ⟨g, hg, hδ'⟩
    obtain ⟨a, rfl⟩ : f ∣ g := (hf.2 g).mp ((hg.2 g).mpr dvd_rfl)
    obtain ⟨b, hb⟩ : f * a ∣ f := (hg.2 f).mp ((hf.2 f).mpr dvd_rfl)
    have hab : a * b = 1 := by
      apply mul_left_cancel₀ hf.1
      rw [mul_one, ← mul_assoc, ← hb]
    obtain ⟨r, hr, rfl⟩ := (isUnit_iff_eq_C_of_isReduced (P := a)).mp (isUnit_iff_exists_inv.mpr ⟨b, hab⟩)
    obtain ⟨d, hd⟩ := ne_zero_iff.mp hf.1
    have h1 := hδ hd
    have h2 := hδ' (show coeff d (f * C r) ≠ 0 by rw [mul_comm, coeff_C_mul]; exact mul_ne_zero hr.ne_zero hd)
    exact congrFun (h2.symm.trans h1) ⟨0, hk⟩
  exact le_antisymm (Nat.sInf_le ⟨f, hf, hδ⟩) (le_csInf ⟨δ, f, hf, hδ⟩ fun δ' h => (key δ' h).ge)
end GroundTheory.Heights₂.Heights.ObjectsChow
