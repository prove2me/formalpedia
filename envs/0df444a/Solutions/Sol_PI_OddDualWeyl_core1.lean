-- Prove2me | solution 1 for PI.OddDualWeyl.core1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:11:22.177297+00:00
-- url     : https://prove2.me/submissions/1bb0ee1a-f8fb-451b-b7ab-e9b9aceed0ed

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_RevColOneTranspose
import Theorems.Thm_PI_OddDualWeyl_rel_add
import Theorems.Thm_PI_OddDualWeyl_rel_smul
import Theorems.Thm_PI_OddDualWeyl_rel_zero
import Theorems.Thm_PI_OddDualWeyl_rel_natMul
import Theorems.Thm_PI_OddDualWeyl_weyl_rowDiv
import Theorems.Thm_PI_OddDualWeyl_applyWord_cons
import Theorems.Thm_PI_OddDualWeyl_mem_of_pm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPolynomial Matrix
noncomputable section
namespace PI.OddDualWeyl
section Lin
variable {R : Type} [CommRing R] {k M : ℕ}
end Lin
private theorem mh_applyWord_hw (hMh : MHhw) (hMd : MHdiv)
    (R : Type) [CommRing R] (k : ℕ) (ν : Fin k → ℕ) (w : List (Fin k × Fin k × ℕ)) :
    MH R (applyWord R w (hw R (le_refl k) ν)) := by
  induction w with
  | nil => exact hMh R k ν
  | cons x w ih => exact hMd R k x.1 x.2.1 x.2.2 _ ih
section Top
variable {K : Type} [Field K]
end Top
end PI.OddDualWeyl
end
end

set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl
namespace PI.OddDualWeyl
theorem _root_.solution (h1 : W1) (hMh : MHhw) (hMd : MHdiv) (hD : Diag) (hL : LowMem) (h4 : W4hw)
    (R : Type) [CommRing R] (m : ℕ) (lam : Fin (m + 1) → ℤ) (hl : Antitone lam) :
    ∀ f ∈ weyl R (m + 1) (m + 1) le_rfl (nuOf lam), ∃ f' ∈ weyl R (m + 1) (m + 1) le_rfl (nuOf (lamStar lam)),
      Rel R (m + 1) (expM lam) f f' := by
  have hCu : ∀ u : R, (u = 1 ∨ u = -1) → (C u : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) = 1 ∨
      (C u : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) = -1 := by
    intro u hu
    rcases hu with rfl | rfl
    · left; exact C_1
    · right; rw [C_neg, C_1]
  have key : ∀ w : List (Fin (m + 1) × Fin (m + 1) × ℕ),
      ∃ f' ∈ weyl R (m + 1) (m + 1) le_rfl (nuOf (lamStar lam)),
        Rel R (m + 1) (expM lam)
          (applyWord R w (hw R le_rfl (nuOf lam))) f' := by
    intro w
    induction w with
    | nil =>
      obtain ⟨u, hu, hrel⟩ := h4 R m lam hl
      exact ⟨C u * low R (nuOf (lamStar lam)),
        mem_of_pm _ (hCu u hu) (hL R (m + 1) _), hrel⟩
    | cons x w ih =>
      obtain ⟨f', hf', hrel⟩ := ih
      obtain ⟨a, b, j⟩ := x
      rw [applyWord_cons]
      dsimp only
      rcases eq_or_ne a b with rfl | hab
      · obtain ⟨d, hd⟩ := mh_applyWord_hw hMh hMd R (m + 1) (nuOf lam) w a
        rw [hD R (m + 1) a j d _ hd]
        refine ⟨((d.choose j : ℕ) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) * f', ?_,
          (rel_natMul (h := hrel)) _⟩
        rw [← nsmul_eq_mul]
        exact nsmul_mem hf' _
      · exact ⟨(-1) ^ j * rowDiv R b a j f',
          mem_of_pm _ (neg_one_pow_eq_or _ j) (weyl_rowDiv b a j hf'),
          h1 R (m + 1) (expM lam) a b j _ f' hab hrel⟩
  intro f hf
  let S : Submodule R (MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) :=
    { carrier := {f | ∃ f' ∈ weyl R (m + 1) (m + 1) le_rfl (nuOf (lamStar lam)),
        Rel R (m + 1) (expM lam) f f'}
      add_mem' := by
        rintro f g ⟨f', hf', h⟩ ⟨g', hg', h'⟩
        exact ⟨f' + g', Submodule.add_mem _ hf' hg', (rel_add h) h'⟩
      zero_mem' := ⟨0, Submodule.zero_mem _, rel_zero⟩
      smul_mem' := by
        rintro c f ⟨f', hf', h⟩
        exact ⟨c • f', Submodule.smul_mem _ c hf', (rel_smul (h := h)) c⟩ }
  have hle : weyl R (m + 1) (m + 1) le_rfl (nuOf lam) ≤ S := by
    unfold weyl
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    exact key w
  exact hle hf
end PI.OddDualWeyl
