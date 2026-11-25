-- Prove2me | solution 1 for PositivityTheory.CW.EigenspaceOrthogonality.key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:43:07.530705+00:00
-- url     : https://prove2.me/submissions/2a103fb6-1bef-46f5-8db4-ec57dab0c787

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_EigenspacesOrthogonalOfCalculus
import Theorems.Thm_PositivityTheory_CW_EigenspaceOrthogonality_nc_sum
import Theorems.Thm_PositivityTheory_CW_EigenspaceOrthogonality_s1
import Theorems.Thm_PositivityTheory_CW_EigenspaceOrthogonality_s2
import Theorems.Thm_PositivityTheory_CW_EigenspaceOrthogonality_pt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.EigenspaceOrthogonality
variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {A : Module.End ℂ V}
namespace PositivityTheory.CW.EigenspaceOrthogonality
theorem _root_.solution (hgl : IsGlRep E) (huni : IsInfUnitary ε E)
    (hA : ∀ c d, ε c = ε d → ∀ z, A (E c d z) = E c d (A z))
    {c d : Fin n} (hcd : ε c = ε d) (x y : V) :
    beta ε E A (E c d x) y = beta ε E A x (E d c y) := by
  have e : ∀ a b, (if ε a ≠ ε b then inner ℂ (E a b (E c d x)) (A (E a b y)) else 0) =
      (if ε a ≠ ε b then inner ℂ (E a b x) (A (E a b (E d c y))) else 0)
      + (if ε a ≠ ε b then (if c = a then inner ℂ (E a b x) (A (E d b y)) else 0) else 0)
      - (if ε a ≠ ε b then (if b = d then inner ℂ (E a b x) (A (E a c y)) else 0) else 0)
      + (if ε a ≠ ε b then (if b = c then inner ℂ (E a d x) (A (E a b y)) else 0) else 0)
      - (if ε a ≠ ε b then (if d = a then inner ℂ (E c b x) (A (E a b y)) else 0) else 0) := by
    intro a b
    by_cases hab : ε a ≠ ε b
    · simp only [if_pos hab]
      exact pt hgl huni hA hcd a b x y
    · simp only [if_neg hab]
      simp
  have h1 := s1 (ε := ε) (fun a b => inner ℂ (E a b x) (A (E d b y))) c
  have h4 := s1 (ε := ε) (fun a b => inner ℂ (E c b x) (A (E a b y))) d
  have h2 := s2 (ε := ε) (fun a b => inner ℂ (E a b x) (A (E a c y))) d
  have h3 := s2 (ε := ε) (fun a b => inner ℂ (E a d x) (A (E a b y))) c
  simp only [beta, nc_sum]
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [h1, h2, h3, h4, hcd]
  ring
end PositivityTheory.CW.EigenspaceOrthogonality
