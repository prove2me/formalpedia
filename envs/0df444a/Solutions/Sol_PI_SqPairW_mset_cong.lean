-- Prove2me | solution 1 for PI.SqPairW.mset_cong
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:28:44.499989+00:00
-- url     : https://prove2.me/submissions/6df77d2c-8334-4321-b7e1-f2150a34e68d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_SplitPairEquations_SplitPairGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairGluing_ConjTransposeMemLam
import Theorems.Thm_PI_SqPairW_star_cong
import Theorems.Thm_PI_SqPairW_sq_cong

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairW
open Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
namespace PI.SqPairW
theorem _root_.solution {R : Subring (Matrix (Fin N) (Fin N) E)} (hstar : ∀ x ∈ R, xᴴ ∈ R)
    {a d : Matrix (Fin N) (Fin N) E} (ha : a ∈ R) (hd : d ∈ R) (P : ℤ) :
    ∀ M ∈ mset (a + P • d), ∃ M' ∈ mset a, ∃ r ∈ R, M = M' + P • r := by
  rintro M (rfl | rfl | rfl)
  · refine ⟨a * a - a, Or.inl rfl, a * d + d * a + P • (d * d) - d, ?_, sq_cong a d P⟩
    exact R.sub_mem (R.add_mem (R.add_mem (R.mul_mem ha hd) (R.mul_mem hd ha))
      (zsmul_mem (R.mul_mem hd hd) P)) hd
  · refine ⟨aᴴ * a, Or.inr (Or.inl rfl), aᴴ * d + dᴴ * a + P • (dᴴ * d), ?_, star_cong a d P⟩
    exact R.add_mem (R.add_mem (R.mul_mem (hstar a ha) hd) (R.mul_mem (hstar d hd) ha))
      (zsmul_mem (R.mul_mem (hstar d hd) hd) P)
  · have e1 : 1 - (a + P • d) = (1 - a) + P • (-d) := by
      rw [smul_neg]
      abel
    have h1a : 1 - a ∈ R := R.sub_mem R.one_mem ha
    have hnd : -d ∈ R := R.neg_mem hd
    refine ⟨(1 - a)ᴴ * (1 - a), Or.inr (Or.inr rfl),
      (1 - a)ᴴ * (-d) + (-d)ᴴ * (1 - a) + P • ((-d)ᴴ * (-d)), ?_, ?_⟩
    · exact R.add_mem (R.add_mem (R.mul_mem (hstar _ h1a) hnd) (R.mul_mem (hstar _ hnd) h1a))
        (zsmul_mem (R.mul_mem (hstar _ hnd) hnd) P)
    · rw [e1]
      exact star_cong (1 - a) (-d) P
end PI.SqPairW
