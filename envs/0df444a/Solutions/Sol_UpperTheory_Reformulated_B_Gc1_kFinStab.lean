-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Gc1.kFinStab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:05:26.106928+00:00
-- url     : https://prove2.me/submissions/1ee1b481-80cc-4ddb-8c29-20d19df0ecab

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsInvariantSubspace
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_KsetSubset
import Theorems.Thm_UpperTheory_exists_invariant_subspace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private theorem UpperTheory.Reformulated.B.Gc1.kset_subset {n : ℕ} (ε : Fin n → Bool) :
    PI.UpqRep.Kset ε ⊆ PI.UpqRep.UJset ε := by
  intro g hg
  have h1 : star g * g = 1 := (Matrix.mem_unitaryGroup_iff' ).1 hg.1
  show g.conjTranspose * PI.UpqRep.Jm ε * g = PI.UpqRep.Jm ε
  rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose, h1, Matrix.one_mul]
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Gc1
theorem _root_.solution :
    CompanionTheory.D.DSIC.KFinStab := by
  intro n ε H _ _ σ S E _ hS
  obtain ⟨V₀, h1, h2⟩ := UpperTheory.exists_invariant_subspace H (Matrix (Fin n) (Fin n) ℂ) (Fin n × Fin n) (PI.UpqRep.Kset ε)
    (fun g => (σ g : H →ₗ[ℂ] H)) S (fun p => E p.1 p.2)
    (fun g p q => g q.1 p.1 * g⁻¹ p.2 q.2)
    (fun g hg v hv => hS.stab g (UpperTheory.Reformulated.B.Gc1.kset_subset ε hg) v hv)
    (fun g hg p v w hw => by
      rw [Fintype.sum_prod_type]
      exact hS.conj g (UpperTheory.Reformulated.B.Gc1.kset_subset ε hg) p.1 p.2 v w hw)
  exact ⟨V₀, h1, fun a b => h2 (a, b)⟩
end UpperTheory.Reformulated.B.Gc1
