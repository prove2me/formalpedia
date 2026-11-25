-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity.swap1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:26:01.152571+00:00
-- url     : https://prove2.me/submissions/4f0a4852-8846-4557-ad94-2b878733805b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_RightRegularActionListDLREqAppend
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_GrothendieckCommutativity_fderiv_apply_lin
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dx_congr_loc
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dx_hasDerivAt
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_dirL_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
attribute [local instance] PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity.clmNACG
attribute [local instance] PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity.clmNS
namespace PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity
theorem _root_.solution {X Y : B.Mat k r} (hX : B.inLie k r X) (hY : B.inLie k r Y) {h : B.Mat k r → E}
    (hh : B.CkOn 2 (B.GV k r) h) {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    Dx (false, X) (Dx (true, Y) h) g = Dx (true, Y) (Dx (false, X) h) g := by
  have hdx : ∀ (x : Bool × B.Mat k r), B.inLie k r x.2 → ∀ {f f' : B.Mat k r → E} {U : Set (B.Mat k r)},
      IsOpen U → (∀ y ∈ U, y ∈ B.GV k r → f y = f' y) → ∀ y ∈ U, y ∈ B.GV k r →
      DifferentiableAt ℝ f' y → Dx x f y = fderiv ℝ f' y (dirL x y) := by
    intro x hx f f' U hU hff y hyU hy hd
    rw [Dx_eq, dirL_apply]
    exact (Dx_hasDerivAt hx hU hyU hy hd hff).deriv
  obtain ⟨U, h', hU, hgU, hc, heq⟩ := hh g hg
  have hc2 : ContDiffOn ℝ 2 h' U := by exact_mod_cast hc
  have hdiff : ∀ y ∈ U, DifferentiableAt ℝ h' y := fun y hy =>
    (hc2.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hy)
  obtain ⟨hdL, hfL⟩ := fderiv_apply_lin hU hc2 hgU (dirL (true, Y))
  obtain ⟨hdR, hfR⟩ := fderiv_apply_lin hU hc2 hgU (dirL (false, X))
  have e1 : Dx (false, X) (Dx (true, Y) h) g =
      Dx (false, X) (fun y => fderiv ℝ h' y (dirL (true, Y) y)) g :=
    Dx_congr_loc (x := (false, X)) hX hU
      (fun y hy hyU => hdx (true, Y) hY hU heq y hyU hy (hdiff y hyU)) g hg hgU
  have e2 : Dx (true, Y) (Dx (false, X) h) g =
      Dx (true, Y) (fun y => fderiv ℝ h' y (dirL (false, X) y)) g :=
    Dx_congr_loc (x := (true, Y)) hY hU
      (fun y hy hyU => hdx (false, X) hX hU heq y hyU hy (hdiff y hyU)) g hg hgU
  rw [e1, e2, hdx (false, X) hX hU (fun _ _ _ => rfl) g hgU hg hdL,
    hdx (true, Y) hY hU (fun _ _ _ => rfl) g hgU hg hdR, hfL, hfR]
  have hsymm : IsSymmSndFDerivAt ℝ h' g :=
    (hc2.contDiffAt (hU.mem_nhds hgU)).isSymmSndFDerivAt (by simp)
  rw [show dirL (true, Y) (dirL (false, X) g) = dirL (false, X) (dirL (true, Y) g) by
      simp [dirL_apply, dirv, mul_assoc]]
  congr 1
  exact hsymm _ _
end PI.UnitaryGroupMassFormula.UsCost.GrothendieckCommutativity
