-- Prove2me | solution 1 for P2M_GlobalTheory_Published_BernsteinUnitaryProductIrreducible_prod__detRep_462f64e927a8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:31:39.961736+00:00
-- url     : https://prove2.me/submissions/b8898d36-b4f8-43b6-a557-40154c1be92e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Theorems.Thm_GlobalTheory_Published_BernsteinUnitaryProductIrreducible_detRep_hyp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.BernsteinUnitaryProductIrreducible
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.Published.BernsteinUnitaryProductIrreducible
theorem _root_.solution (H : BernsteinUnitaryProductIrreducible) {r : ℕ} (t : ℕ)
    {π : Representation ℂ (GL (Fin r) k) V} (s : IsSmooth π) (i : π.IsIrreducible)
    (u : IsUnitarisable π) {χ : kˣ →* ℂˣ} (hs : IsSmoothChar χ) (hu : IsUnitaryChar χ) :
    (prod₂ π (detRep (Fin t) χ)).IsIrreducible :=
  have h := detRep_hyp t hs hu
  H k r t V ℂ π _ s i u h.1 h.2.1 h.2.2
end GlobalTheory.Published.BernsteinUnitaryProductIrreducible
