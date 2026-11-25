-- Prove2me | solution 1 for P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_diag__8d2131252cf9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:11:53.773452+00:00
-- url     : https://prove2.me/submissions/a54a4666-dc92-47b3-83e4-1900fb37ecbd

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvariantSeriesBidegreeOneOne
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HyperbolicPlaneSplit
import Theorems.Thm_P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_phi_add__97db315ad562
import Theorems.Thm_P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_cob_zero_right__b09b3a439bc2
import Theorems.Thm_P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_phi_zero__cfc66c2ced32
import Theorems.Thm_P2M_Formalism_HermitianLattices_IntegralLatticeDensity_PD_cross__eb1de562b740

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.IntegralLatticeDensity Formalism.HermitianLattices.IntegralLatticeDensity.PD
open Finset Formalism.HermitianLattices.IntegralLatticeDensity
variable {M Q : Type} [AddCommGroup M] [AddCommGroup Q] {φ : M → Q}
variable {O : Type} [CommRing O] [StarRing O] [Module O M]
variable {Z : Type} [CommRing Z] [Module Z Q] {nm : O → Z}
namespace Formalism.HermitianLattices.IntegralLatticeDensity.PD
theorem _root_.solution (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b)
    (h2 : ∀ (α : O) a b, cob φ (α • a) b = cob φ a (star α • b))
    (h3 : ∀ (α : O) u, φ (α • u) = nm α • φ u)
    {n J : Type} [Fintype n] (c : n → J → O)
    (hG : ∀ a j, a ≠ j → ∑ i, star (c i a) * c i j = 0) (u : J → M) (s : Finset J) :
    ∑ i, φ (∑ j ∈ s, c i j • u j) = ∑ j ∈ s, (∑ i, nm (c i j)) • φ (u j) := by
  induction s using Finset.cons_induction with
  | empty => simp [phi_zero' h1]
  | cons k s hk ih =>
    have hcross : ∑ i, cob φ (c i k • u k) (∑ j ∈ s, c i j • u j) = 0 := by
      rw [cross' h1 h2 (fun i => c i k) c (u k) s u]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hne : k ≠ j := by
        rintro rfl
        exact hk hj
      rw [hG k j hne, zero_smul, cob_zero_right' h1]
    simp only [Finset.sum_cons]
    simp only [phi_add', Finset.sum_add_distrib, h3]
    rw [hcross, ih, ← Finset.sum_smul, add_zero]
end Formalism.HermitianLattices.IntegralLatticeDensity.PD
