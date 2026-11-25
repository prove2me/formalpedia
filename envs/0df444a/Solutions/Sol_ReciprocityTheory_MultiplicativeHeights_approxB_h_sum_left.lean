-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.approxB_h_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:40:26.351818+00:00
-- url     : https://prove2.me/submissions/79ee3b15-bb30-4fcb-912f-660039f35bf9

import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisA
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField ComplexConjugate
private theorem hermForm_h_add_left {K : Type} [Field K] [NumberField K] {r : ℕ}
    (S : HermForm K r) (x y z : Fin r → K) : S.h (x + y) z = S.h x z + S.h y z := by
  unfold ReciprocityTheory.MultiplicativeHeights.HermForm.h
  simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
end ReciprocityTheory.MultiplicativeHeights
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField ComplexConjugate
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    {α : Type*} (s : Finset α) (y : Fin r → K) (f : α → Fin r → K) :
    S.h (∑ j ∈ s, f j) y = ∑ j ∈ s, S.h (f j) y := by
  exact map_sum (AddMonoidHom.mk' (fun z => S.h z y) (fun a b => (hermForm_h_add_left S) a b y)) f s
end ReciprocityTheory.MultiplicativeHeights
