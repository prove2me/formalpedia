-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundNumeric.ClosureCertificate.nodes_sound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T20:55:17.07619+00:00
-- url     : https://prove2.me/submissions/12d01953-01b2-44de-9561-bfd250bba848

import Definitions.Def_Sensitivity213981Formal_ClosureCertificate
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Supplement_FullProfileClosure
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Ring
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundNumeric_ClosureCertificate_rule_sound_two


namespace Sensitivity213981Formal
section
/- Soundness of the complete finite five-profile closure procedure.
The update schedule is the one in graded2_union_recurrence.IntegerModel.close.
It does not establish the raw sensitivity transfer preceding that procedure. -/


set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace ThreeBoundFullProfile
open ThreeBoundProfiles
open scoped Classical
noncomputable section

variable {n : ℕ} {I : Type} [Fintype I]

























theorem sem_mono (F : Fin n → (I → Bool) → Bool) (c : Coord n) (a b : ℕ)
    (hab : a ≤  b) (ha : Sem F c a) : Sem F c b := by
  cases c with
  | a i j => exact fun hij x hx => (ha hij x hx).trans hab
  | b i j => exact fun hij x hx => (ha hij x hx).trans hab
  | m i j => exact fun hij hn x hx hy => (ha hij hn x hx hy).trans hab
  | p j l => exact fun hjl x hx hy => (ha hjl x hx hy).trans hab
  | d i j l => exact fun hij hjl x hx hy => (ha hij hjl x hx hy).trans hab













































end
end ThreeBoundFullProfile




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- A small trusted checker for exact closure certificates.

Each node cites either an input bound or one of the already proved semantic
closure rules, with references strictly earlier in the finite program. The
checker validates coordinates and integer inequalities. A successful check
therefore proves a semantic upper profile for every natural scaling of the
input. No executable output is used as an unverified premise. -/


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ThreeBoundNumeric.ClosureCertificate
open ThreeBoundProfiles ThreeBoundFullProfile

variable {n : ℕ}







theorem combine_scale (r : Rule n) (c x y : ℕ) :
    combine r (c*x) (c*y) = c*combine r x y := by
  cases r <;> simp [combine,Nat.mul_add,Nat.mul_max_mul_left]



















theorem nodes_sound {I : Type} [Fintype I]
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (input : Profile n) (nodes : ℕ → Node n) (count c : ℕ)
    (hi : Upper F (scale c input))
    (hn : ∀ k, k< count → checkNode input nodes k = true) :
    ∀ k, k< count → Sem F (nodes k).coord (c*(nodes k).value) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hk
      have hcheck := hn k hk
      cases hr : (nodes k).reason with
      | input =>
          have hle : input (nodes k).coord ≤  (nodes k).value := by
            simpa [checkNode,hr] using hcheck
          exact sem_mono F (nodes k).coord _ _ (Nat.mul_le_mul_left c hle) (hi _)
      | step r a b =>
          have hs : (nodes k).coord = r.target ∧ a< k ∧ b< k ∧
              (nodes a).coord = source₀ r ∧ (nodes b).coord = source₁ r ∧
              combine r (nodes a).value (nodes b).value ≤  (nodes k).value := by
            simpa [checkNode,hr] using hcheck
          obtain ⟨hcoord,ha,hb,hca,hcb,hvalue⟩ := hs
          have hsa : Sem F (source₀ r) (c*(nodes a).value) := by
            rw [← hca]
            exact ih a ha (ha.trans hk)
          have hsb : Sem F (source₁ r) (c*(nodes b).value) := by
            rw [← hcb]
            exact ih b hb (hb.trans hk)
          rw [hcoord]
          apply sem_mono F r.target _ _ (Nat.mul_le_mul_left c hvalue)
          rw [← combine_scale]
          exact rule_sound_two F hF r _ _ hsa hsb

















end ThreeBoundNumeric.ClosureCertificate



end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {n : Nat} {I : Type} [inst : Fintype.{0} I] (F : Fin n → (I → Bool) → Bool)
  (hF :
    @Sensitivity213981Formal.ThreeBoundProfiles.Nested (Fin n) I
      (@PartialOrder.toPreorder.{0} (Fin n) (@Fin.instPartialOrder n)) F)
  (input : Sensitivity213981Formal.ThreeBoundFullProfile.Profile n)
  (nodes : Nat → Sensitivity213981Formal.ThreeBoundNumeric.ClosureCertificate.Node n) (count c : Nat)
  (hi :
    @Sensitivity213981Formal.ThreeBoundFullProfile.Upper n I inst F
      (@Sensitivity213981Formal.ThreeBoundFullProfile.scale n c input))
  (hn :
    ∀ (k : Nat),
      @LT.lt.{0} Nat instLTNat k count →
        @Eq.{1} Bool (@Sensitivity213981Formal.ThreeBoundNumeric.ClosureCertificate.checkNode n input nodes k)
          Bool.true)
  (k : Nat),
  @LT.lt.{0} Nat instLTNat k count →
    @Sensitivity213981Formal.ThreeBoundFullProfile.Sem n I inst F
      (@Sensitivity213981Formal.ThreeBoundNumeric.ClosureCertificate.Node.coord n (nodes k))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) c
        (@Sensitivity213981Formal.ThreeBoundNumeric.ClosureCertificate.Node.value n (nodes k))) := @Sensitivity213981Formal.ThreeBoundNumeric.ClosureCertificate.nodes_sound
